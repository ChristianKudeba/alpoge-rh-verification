"""Prepare a pinned Lean export on the hosted runner without materializing its 62 GB text."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile

from release_store import TAG, download, info, listing, matches, put, release, write_json

SOURCE = {
    "url": "https://math.mit.edu/~drew/grh/solution.ndjson.zst",
    "sha256": "5ea74b912147c5c93cc2b6d70cc727cf908df2f62ac6a20480a3fa02f6be244e",
    "bytes": 61570595788,
    "compressed_sha256": "61a8938ad5f5e57397c1c0e3b954916af546d9004ade01c3555744a681b05381",
    "compressed_bytes": 7699933588,
}
TARGETS = {"riemannHypothesis", "riemannZeta_eq_zero_re", "LFunction_ne_zero_of_half_lt_re",
           "LFunction_eq_zero_re", "LFunction_eq_zero_re_of_isPrimitive"}
BASE = Path(__file__).resolve().parent
SHARD_SIZE = 512 * 1024 * 1024
INITIAL = {"N": 1, "U": 1, "E": 0}


def renderer_hashes():
    return {name: info(BASE / name)[0] for name in ("render_shard.py", "kernel_tex.py")}


def get_line(buf, pos):
    a = buf.rfind(b"\n", 0, pos) + 1
    b = buf.find(b"\n", pos)
    return a, buf[a:b if b >= 0 else len(buf)]


def end_table(buf, start):
    """The final record in each table supplies its final explicit index.
    Workers validate every intervening record and the continuity of the table."""
    end = dict(start)
    for name, key in (("N", "in"), ("U", "il"), ("E", "ie")):
        needle = b'"' + key.encode("ascii") + b'"'
        stop = len(buf)
        while (pos := buf.rfind(needle, 0, stop)) >= 0:
            stop, row = get_line(buf, pos)
            val = json.loads(row).get(key)
            if type(val) is int:
                if val < start[name]:
                    raise ValueError(f"nonmonotone {name} index {val}")
                end[name] = val + 1
                break
    return end


def find_targets(buf, ids):
    for name in TARGETS:
        needle = b'"' + name.encode("ascii") + b'"'
        pos = 0
        while (pos := buf.find(needle, pos)) >= 0:
            _, line = get_line(buf, pos)
            pos += len(needle)
            row = json.loads(line)
            if row.get("str") == {"pre": 0, "str": name}:
                idx = row["in"]
                if type(idx) is not int or idx < 1 or str(idx) in ids or name in ids.values():
                    raise ValueError("invalid or repeated root name " + name)
                ids[str(idx)] = name


def verify_manifest(data, assets):
    if (data["version"] != 1 or data["source"] != SOURCE or
            data["renderer"] != renderer_hashes() or len(data["targets"]) != len(TARGETS) or
            set(data["targets"].values()) != TARGETS):
        raise ValueError("published manifest and requested source or renderer differ")
    nxt, last, length = INITIAL, 0, 0
    if not 1 <= len(data["shards"]) <= 250:
        raise ValueError("invalid matrix size")
    for i, entry in enumerate(data["shards"]):
        if (entry["id"] != i or entry["asset"] != f"source-{i:04d}.ndjson.zst" or
                entry["first_line"] != last + 1 or entry["last_line"] < entry["first_line"] or
                entry["start"] != nxt or set(entry["end"]) != set(INITIAL) or
                any(entry["end"][t] < nxt[t] for t in nxt) or
                not matches(assets.get(entry["asset"]), entry["compressed_sha256"],
                            entry["compressed_bytes"])):
            raise ValueError(f"invalid source shard {i}")
        nxt, last = entry["end"], entry["last_line"]
        length += entry["raw_bytes"]
    if length != SOURCE["bytes"] or last < 1:
        raise ValueError("manifest is incomplete")


def prepare(folder, rel, assets):
    compressed = folder / "solution.zst"
    subprocess.run(["curl", "--proto", "=https", "--location", "--fail", "--silent",
                    "--show-error", "--retry", "5", "--retry-all-errors", "--continue-at", "-",
                    "--output", str(compressed), SOURCE["url"]], check=True)
    if info(compressed) != (SOURCE["compressed_sha256"], SOURCE["compressed_bytes"]):
        raise ValueError("compressed source failed MIT checksum")
    digest = hashlib.sha256()
    length, last, nxt, rows, targets = 0, 0, dict(INITIAL), [], {}
    with subprocess.Popen(["zstd", "-q", "-d", "--long=30", "--stdout", str(compressed)],
                          stdout=subprocess.PIPE) as dec:
        try:
            while raw := dec.stdout.read(SHARD_SIZE):
                if not raw.endswith(b"\n"):
                    raw += dec.stdout.readline()
                i = len(rows)
                size = len(raw)
                count = raw.count(b"\n") + int(not raw.endswith(b"\n"))
                digest.update(raw)
                length += size
                find_targets(raw, targets)
                end = end_table(raw, nxt)
                dst = folder / f"source-{i:04d}.ndjson.zst"
                with dst.open("wb") as out:
                    subprocess.run(["zstd", "-q", "-3", "-T1", "-c"],
                                   input=raw, stdout=out, check=True)
                sha, cbytes = info(dst)
                entry = dict(id=i, asset=dst.name, first_line=last + 1, last_line=last + count,
                             start=nxt, end=end, raw_sha256=hashlib.sha256(raw).hexdigest(),
                             raw_bytes=size, compressed_sha256=sha, compressed_bytes=cbytes)
                del raw
                put(rel, assets, dst)
                dst.unlink()
                rows.append(entry)
                last, nxt = entry["last_line"], end
                print(f"verified and staged shard {i}: {length:,} source bytes", flush=True)
        finally:
            dec.stdout.close()
        if dec.wait() != 0:
            raise ValueError("input decompression failed")
    if (digest.hexdigest(), length) != (SOURCE["sha256"], SOURCE["bytes"]):
        raise ValueError("unpacked source failed MIT checksum")
    return dict(version=1, source=SOURCE, renderer=renderer_hashes(), targets=targets, shards=rows)


def main():
    rel = release(create=True)
    assets = listing(rel["id"])
    with tempfile.TemporaryDirectory() as work:
        folder = Path(work)
        manifest = folder / "shards.json"
        if "shards.json" in assets:
            download(assets["shards.json"], manifest)
            data = json.loads(manifest.read_bytes())
        else:
            data = prepare(folder, rel, assets)
            write_json(manifest, data)
        verify_manifest(data, assets)
        put(rel, assets, manifest)
        ids = [s["id"] for s in data["shards"]]
        with open(os.environ["GITHUB_OUTPUT"], "a", encoding="utf-8") as f:
            print("matrix=" + json.dumps(ids, separators=(",", ":")), file=f)
        print(f"{TAG}: {len(ids)} source shards verified")


if __name__ == "__main__":
    main()
