"""Convert one independently compressed section of the verified kernel export.

Usage: python render_shard.py SOURCE.ndjson.zst shards.json ID OUTPUT_DIRECTORY

Requires Python 3.15+, kernel_tex.py in this directory, and a manifest from
the preparation job. Outputs shard-NNNN.tar.zst and shard-NNNN.json. The tar
contains complete standalone .tex volumes, not raw source records.
"""
import argparse
import hashlib
import io
import json
import os
import tarfile
from collections import Counter
from compression import zstd
from pathlib import Path

from kernel_tex import LAYOUT, LEGEND, Notation


TARGETS = {
    "riemannHypothesis",
    "riemannZeta_eq_zero_re",
    "LFunction_ne_zero_of_half_lt_re",
    "LFunction_eq_zero_re",
    "LFunction_eq_zero_re_of_isPrimitive",
}
INITIAL = {"N": 1, "U": 1, "E": 0}
CATEGORIES = {"N", "U", "E"}


def digest_file(path):
    with path.open("rb") as source:
        return hashlib.file_digest(source, "sha256").hexdigest()


def id_state(value):
    if not isinstance(value, dict) or set(value) != CATEGORIES:
        raise ValueError("missing N, U, or E index counter")
    if any(type(value[key]) is not int or value[key] < INITIAL[key] for key in CATEGORIES):
        raise ValueError("invalid index counters")
    return value


def check_manifest(manifest):
    if manifest.get("version") != 1:
        raise ValueError("unsupported shard manifest version")
    parts = manifest["shards"]
    if not parts:
        raise ValueError("empty shard inventory")
    previous_line, previous_state = 0, INITIAL
    for index, part in enumerate(parts):
        if part["id"] != index or part["first_line"] != previous_line + 1:
            raise ValueError(f"discontinuous source record numbering at shard {index}")
        if part["last_line"] < part["first_line"] or id_state(part["start"]) != previous_state:
            raise ValueError(f"invalid source interval or starting counters at shard {index}")
        end = id_state(part["end"])
        if any(end[k] < previous_state[k] for k in CATEGORIES):
            raise ValueError(f"decreasing index counter at shard {index}")
        previous_line, previous_state = part["last_line"], end
    if sum(x["raw_bytes"] for x in parts) != manifest["source"]["bytes"]:
        raise ValueError("source shard sizes do not sum to verified raw input size")
    targets = {int(k): v for k, v in manifest["targets"].items()}
    if set(targets.values()) != TARGETS or len(targets) != len(TARGETS):
        raise ValueError("missing or duplicate requested theorem names in verified name map")
    if any(i <= 0 or i >= previous_state["N"] for i in targets):
        raise ValueError("requested theorem name ID outside source name range")
    return targets


def add_volume(archive, text, prefix, index, first, last):
    payload = text.getvalue().encode("utf-8")
    name = f"{prefix}/volume-{index:05}.tex"
    member = tarfile.TarInfo(name)
    member.size = len(payload)
    member.mode = 0o644
    member.mtime = 0
    archive.addfile(member, io.BytesIO(payload))
    return {"name": name, "first_line": first, "last_line": last,
            "bytes": len(payload), "sha256": hashlib.sha256(payload).hexdigest()}


def render_records(lines, part, targets, tar, per_volume=5000, cache_size=16384):
    if per_volume < 1 or cache_size < 1:
        raise ValueError("volume length and cache size must be positive")
    prefix = f"shard-{part['id']:04}"
    book = Notation(cache_size)
    book.next = dict(part["start"])
    first, last = part["first_line"], part["last_line"]
    counts = Counter()
    volumes, theorems, names_seen = [], [], []
    raw_hash = hashlib.sha256()
    nbytes = 0
    current = None
    previous = first - 1
    for line, raw in enumerate(lines, first):
        if line > last:
            raise ValueError(f"source shard has excess records beyond {last}")
        raw_hash.update(raw)
        nbytes += len(raw)
        try:
            row = json.loads(raw)
            kind, body = book.render(row, line)
        except (TypeError, ValueError, KeyError, IndexError) as exc:
            raise ValueError(f"invalid export at record {line}: {exc}") from exc
        counts[kind] += 1
        # These are unqualified names. Verify their definitions at the exact
        # node, even when the declaration itself is in a different shard.
        if "in" in row and row["in"] in targets:
            idx = row["in"]
            if row.get("str") != {"pre": 0, "str": targets[idx]}:
                raise ValueError(f"invalid target name reference N{idx} at line {line}")
            names_seen.append({"name": targets[idx], "name_index": idx, "line": line})
        if kind in {"thm", "def", "axiom", "opaque", "quot"}:
            d = row[kind]
            if d["name"] in targets:
                if kind != "thm":
                    raise ValueError(f"target {targets[d['name']]} is {kind}, expected a theorem")
                theorems.append({"name": targets[d["name"]], "kind": kind, "line": line,
                                 "name_index": d["name"], "type_index": d["type"],
                                 "value_index": d["value"]})
        if current is None:
            start = line
            number = len(volumes) + 1
            current = io.StringIO()
            current.write(LAYOUT)
            current.write(r"\section*{Kernel export in dependent type theory}" + "\n")
            current.write(f"Shard {part['id']}, volume {number}, beginning at global record {line}.\n\n")
            current.write(LEGEND)
        current.write(r"\record{" + str(line) + "}" + body[0] + "\n")
        for item in body[1:]:
            current.write(r"\subrow " + item + "\n")
        if (line - start + 1 == per_volume) or line == last:
            current.write(r"\end{document}" + "\n")
            volumes.append(add_volume(tar, current, prefix, number, start, line))
            current.close()
            current = None
        previous = line
    digest = raw_hash.hexdigest()
    if previous != last or current is not None:
        raise ValueError(f"shard ended at record {previous}, expected {last}")
    if book.next != part["end"]:
        raise ValueError(f"shard ending types disagree: {book.next} != {part['end']}")
    if nbytes != part["raw_bytes"] or digest != part["raw_sha256"]:
        raise ValueError("uncompressed source size or SHA-256 differs from preparation manifest")
    return {"version": 1, "id": part["id"], "first_line": first, "last_line": last,
            "start": part["start"], "end": book.next, "records": sum(counts.values()),
            "raw_bytes": nbytes, "raw_sha256": digest, "record_kinds": dict(counts),
            "volumes": volumes, "theorems": theorems, "target_names": names_seen}


def convert(source, manifest_path, shard_id, output, per_volume):
    manifest = json.loads(manifest_path.read_bytes())
    targets = check_manifest(manifest)
    if shard_id < 0 or shard_id >= len(manifest["shards"]):
        raise ValueError(f"shard {shard_id} does not exist")
    part = manifest["shards"][shard_id]
    if source.stat().st_size != part["compressed_bytes"]:
        raise ValueError("compressed input size mismatch")
    if digest_file(source) != part["compressed_sha256"]:
        raise ValueError("compressed input SHA-256 mismatch")
    output.mkdir(exist_ok=True, parents=True)
    prefix = f"shard-{shard_id:04}"
    dest = output / (prefix + ".tar.zst")
    report = output / (prefix + ".json")
    archive_tmp = dest.with_suffix(".zst.part")
    report_tmp = report.with_suffix(".json.part")
    if any(p.exists() for p in (dest, report, archive_tmp, report_tmp)):
        raise FileExistsError("requested output already exists; use an empty output location")
    with zstd.open(source, "rb", options={zstd.DecompressionParameter.window_log_max: 30}) as incoming:
        with zstd.open(archive_tmp, "xb", level=4) as compressed:
            with tarfile.open(fileobj=compressed, mode="w|", format=tarfile.USTAR_FORMAT) as tar:
                data = render_records(incoming, part, targets, tar, per_volume)
    if archive_tmp.stat().st_size >= 2**31:
        raise ValueError("output exceeds the GitHub release asset size limit")
    data.update({"source_asset": part["asset"], "source_bytes": part["compressed_bytes"],
                 "source_sha256": part["compressed_sha256"], "archive": dest.name,
                 "archive_bytes": archive_tmp.stat().st_size,
                 "archive_sha256": digest_file(archive_tmp)})
    report_tmp.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    os.replace(archive_tmp, dest)
    os.replace(report_tmp, report)
    print(f"Converted {data['records']:,} records into {len(data['volumes'])} volumes.", flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("manifest", type=Path)
    parser.add_argument("id", type=int)
    parser.add_argument("output", type=Path)
    parser.add_argument("--records-per-volume", type=int, default=5000)
    options = parser.parse_args()
    convert(options.source, options.manifest, options.id, options.output, options.records_per_volume)
