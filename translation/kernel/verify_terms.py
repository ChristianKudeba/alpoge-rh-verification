"""Compare the mathematical TeX records with the published source and index declarations."""
import argparse
from compression import zstd
import gzip
import hashlib
import io
import json
import os
from pathlib import Path
import sqlite3
import tarfile
import tempfile

from prepare import SOURCE, verify_manifest
from make_endpoints import make_endpoints
from prose_records import add_volume, annotated_volume, meaning
from publish import check_report, read_back
from read_terms import iter_records
from recover_stage import ACTIVE_EDITION, core_edition, recover_staged
from release_store import REPO, api, download, info, listing, matches, put, release, write_json


AUDIT_TAG = "rh-literal-audit-v1"
RENDER_COMMIT = "4e22ad3692dae97711b2d3c7ee465719b7545828"
BASE = Path(__file__).resolve().parent
EXPECTED_CORE_RELEASE = ACTIVE_EDITION
DECLARATIONS = {"axiom", "def", "opaque", "thm", "quot"}


def supplemental(create=False):
    return release(create, tag=AUDIT_TAG, target="main",
                   title="Riemann hypothesis: reverse translation audit and declaration index",
                   body="Exact record comparisons and a name-to-declaration index for the literal mathematical edition.")


def load_asset_json(assets, name, folder):
    path = folder / name
    download(assets[name], path)
    return json.loads(path.read_bytes())


def check_core(rel):
    if rel["id"] != EXPECTED_CORE_RELEASE or rel["author"]["login"] != "github-actions[bot]":
        raise ValueError("unexpected literal edition release")
    return rel


def plan(folder):
    core = check_core(core_edition())
    recover_staged(folder, core)
    core_assets = listing(core["id"])
    work = []
    complete = False
    if "shards.json" in core_assets:
        parts = load_asset_json(core_assets, "shards.json", folder)
        verify_manifest(parts, core_assets)
        candidates = [s["id"] for s in parts["shards"] if f"shard-{s['id']:04d}.json" in core_assets]
        complete = not core["draft"] and "edition-index.json" in core_assets
        if candidates:
            supp = supplemental(create=True)
            staged = listing(supp["id"])
            work = [i for i in candidates if f"audit-{i:04d}.json" not in staged]
    with open(os.environ["GITHUB_OUTPUT"], "a", encoding="utf-8") as out:
        print("matrix=" + json.dumps(work or [0]), file=out)
        print("has_work=" + str(bool(work)).lower(), file=out)
        print("complete=" + str(complete).lower(), file=out)
    print(f"{len(work)} available shards to check; whole edition published: {complete}", flush=True)


def declaration_entries(row):
    if "inductive" in row:
        for group, kind in (("types", "type"), ("ctors", "ctor"), ("recs", "rec")):
            for declaration in row["inductive"][group]:
                yield declaration["name"], kind
    elif len(row) == 1:
        kind = next(iter(row))
        if kind in DECLARATIONS:
            yield row[kind]["name"], kind


def canonical(row):
    # JSON spelling distinguishes booleans from numbers even where Python's
    # native container equality would accept them as the same value.
    return json.dumps(row, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("ascii")


def verify_records(source, archive, part, report, index, prose_archive):
    canonical_hash, raw_hash = hashlib.sha256(), hashlib.sha256()
    count, declarations, size = 0, 0, 0
    volumes = []
    with zstd.open(source, "rb", options={zstd.DecompressionParameter.window_log_max: 30}) as raw, \
         zstd.open(archive, "rb") as terms, tarfile.open(fileobj=terms, mode="r|") as tar, \
         index.open("wb") as packed, gzip.GzipFile(fileobj=packed, mode="wb", filename="", mtime=0) as names, \
         zstd.open(prose_archive, "wb", level=3) as output, \
         tarfile.open(fileobj=output, mode="w|", format=tarfile.USTAR_FORMAT) as prose:
        for vol in report["volumes"]:
            member = tar.next()
            if member is None or not member.isfile() or (
                    member.name, member.size) != (vol["name"], vol["bytes"]):
                raise ValueError("unexpected typeset volume")
            file = tar.extractfile(member)
            if file is None:
                raise ValueError("unreadable typeset volume")
            tex = file.read()
            if hashlib.sha256(tex).hexdigest() != vol["sha256"]:
                raise ValueError("volume contents failed checksum")
            last_vol_line = vol["first_line"] - 1
            annotations = []
            for line, reconstructed in iter_records(io.BytesIO(tex)):
                expected_line = part["first_line"] + count
                if line != expected_line or line != last_vol_line + 1:
                    raise ValueError(f"unexpected record number {line}, expected {expected_line}")
                original = raw.readline()
                if not original:
                    raise EOFError(f"source ended before record {line}")
                raw_hash.update(original)
                size += len(original)
                expected = json.loads(original)
                payload = canonical(reconstructed)
                if payload != canonical(expected):
                    raise ValueError(f"record {line} in {member.name} differs from the published expression")
                annotations.append((line, meaning(reconstructed)))
                canonical_hash.update(payload)
                canonical_hash.update(b"\n")
                for name_id, kind in declaration_entries(reconstructed):
                    names.write(f"{name_id}\t{line}\t{kind}\n".encode("ascii"))
                    declarations += 1
                count += 1
                last_vol_line = line
            if last_vol_line != vol["last_line"]:
                raise ValueError(f"missing records in {member.name}")
            annotated = annotated_volume(tex, annotations)
            volumes.append(add_volume(prose, vol, annotated))
        if raw.read(1) or tar.next() is not None:
            raise ValueError("unlisted source records or typeset volumes")
    if (raw_hash.hexdigest(), size, count) != (part["raw_sha256"], part["raw_bytes"], report["records"]):
        raise ValueError("raw source or coverage mismatch")
    read_back(prose_archive, {"volumes": volumes})
    digest, total = info(prose_archive)
    return dict(records=count, declarations=declarations, canonical_sha256=canonical_hash.hexdigest(),
                prose_archive=prose_archive.name, prose_bytes=total, prose_sha256=digest, prose_volumes=volumes)


def verify_one(folder, index):
    core = check_core(core_edition())
    assets = listing(core["id"])
    parts = load_asset_json(assets, "shards.json", folder)
    verify_manifest(parts, assets)
    part = parts["shards"][index]
    report_name = f"shard-{index:04d}.json"
    report = load_asset_json(assets, report_name, folder)
    check_report(part, report, assets[report["archive"]], parts["targets"])
    src, arc = folder / part["asset"], folder / report["archive"]
    download(assets[part["asset"]], src)
    download(assets[report["archive"]], arc)
    ids = folder / f"declarations-{index:04d}.tsv.gz"
    prose = folder / f"prose-{index:04d}.tar.zst"
    result = verify_records(src, arc, part, report, ids, prose)
    result.update(id=index, raw_sha256=part["raw_sha256"], first_line=part["first_line"],
                  last_line=part["last_line"], source_report_sha256=info(folder / report_name)[0],
                  archive_sha256=report["archive_sha256"], reader_sha256=info(BASE / "read_terms.py")[0],
                  prose_writer_sha256=info(BASE / "prose_records.py")[0],
                  declarations_asset=ids.name, declarations_sha256=info(ids)[0], declarations_bytes=info(ids)[1])
    target = supplemental()
    existing = listing(target["id"])
    put(target, existing, prose, tag=AUDIT_TAG)
    put(target, existing, ids, tag=AUDIT_TAG)
    summary = folder / f"audit-{index:04d}.json"
    write_json(summary, result)
    put(target, existing, summary, tag=AUDIT_TAG)
    print(f"Checked every field of {result['records']:,} decoded records in shard {index}.", flush=True)


def export_lookup(conn, folder, target, assets):
    maximum = conn.execute("SELECT max(name) FROM declarations").fetchone()[0]
    if maximum is None:
        raise ValueError("empty declaration index")
    width = max(1, (maximum + 32) // 32)
    ranges = []
    for low in range(0, maximum + 1, width):
        high = min(maximum, low + width - 1)
        path = folder / f"names-{low}-{high}.tsv.gz"
        count = 0
        with path.open("wb") as out, gzip.GzipFile(fileobj=out, mode="wb", filename="", mtime=0) as compressed:
            for name, record, kind in conn.execute(
                    "SELECT name, record, kind FROM declarations WHERE name BETWEEN ? AND ? ORDER BY name",
                    (low, high)):
                compressed.write(f"{name}\t{record}\t{kind}\n".encode("ascii"))
                count += 1
        if count:
            put(target, assets, path, tag=AUDIT_TAG)
            digest, size = info(path)
            ranges.append(dict(low=low, high=high, count=count, asset=path.name, bytes=size, sha256=digest))
        path.unlink()
    return ranges


def finish(folder):
    core = check_core(core_edition())
    if core["draft"]:
        raise ValueError("full term publication has not completed")
    cores = listing(core["id"])
    parts = load_asset_json(cores, "shards.json", folder)
    verify_manifest(parts, cores)
    edition = load_asset_json(cores, "edition-index.json", folder)
    if edition["source"] != SOURCE or len(parts["shards"]) != len(edition["shards"]):
        raise ValueError("unexpected final edition")
    target = supplemental()
    assets = listing(target["id"])
    reader_hash = info(BASE / "read_terms.py")[0]
    prose_hash = info(BASE / "prose_records.py")[0]
    totals = {"records": 0, "declarations": 0}
    total_volumes, total_print_bytes = 0, 0
    by_shard = []
    with sqlite3.connect(folder / "names.db") as conn:
        conn.execute("CREATE TABLE declarations(name INTEGER PRIMARY KEY,record INTEGER NOT NULL,kind TEXT NOT NULL)")
        for part, published in zip(parts["shards"], edition["shards"], strict=True):
            i = part["id"]
            name = f"audit-{i:04d}.json"
            result = load_asset_json(assets, name, folder)
            table = result["declarations_asset"]
            prose_file = result["prose_archive"]
            if (result["id"] != i or published["id"] != i or result["reader_sha256"] != reader_hash
                    or (result["first_line"], result["last_line"]) != (part["first_line"], part["last_line"])
                    or result["records"] != part["last_line"] - part["first_line"] + 1
                    or result["raw_sha256"] != part["raw_sha256"]
                    or result["archive_sha256"] != published["archive_sha256"]
                    or result["source_report_sha256"] != published["report_sha256"]
                    or result["prose_writer_sha256"] != prose_hash or prose_file != f"prose-{i:04d}.tar.zst"
                    or not matches(assets.get(prose_file), result["prose_sha256"], result["prose_bytes"])
                    or len(result["prose_volumes"]) != published["volume_count"]
                    or table != f"declarations-{i:04d}.tsv.gz"
                    or not matches(assets.get(table), result["declarations_sha256"], result["declarations_bytes"])):
                raise ValueError(f"audit provenance mismatch in shard {i}")
            path = folder / table
            download(assets[table], path)
            before = conn.total_changes
            with gzip.open(path, "rt", encoding="ascii") as rows:
                for row in rows:
                    name_id, record, kind = row.rstrip("\n").split("\t")
                    name_id, record = int(name_id), int(record)
                    if name_id < 1 or not part["first_line"] <= record <= part["last_line"]:
                        raise ValueError(f"invalid declaration at global record {record}")
                    conn.execute("INSERT INTO declarations VALUES(?,?,?)", (name_id, record, kind))
            if conn.total_changes - before != result["declarations"]:
                raise ValueError("declaration count mismatch")
            path.unlink()
            by_shard.append(dict(id=i, report=name, sha256=info(folder / name)[0],
                                 canonical_sha256=result["canonical_sha256"], prose_archive=prose_file,
                                 prose_sha256=result["prose_sha256"], prose_bytes=result["prose_bytes"]))
            total_volumes += len(result["prose_volumes"])
            total_print_bytes += sum(v["bytes"] for v in result["prose_volumes"])
            for key in totals:
                totals[key] += result[key]
        if totals["records"] != edition["records"]:
            raise ValueError("independent check did not cover the whole edition")
        for t in edition["targets"]:
            if conn.execute("SELECT record,kind FROM declarations WHERE name=?", (t["name_index"],)).fetchone() != (t["line"], "thm"):
                raise ValueError("target theorem missing from decoded declarations: " + t["name"])
        ranges = export_lookup(conn, folder, target, assets)
    extracts = []
    for path in make_endpoints(folder, edition, parts, cores):
        put(target, assets, path, tag=AUDIT_TAG)
        digest, size = info(path)
        extracts.append(dict(asset=path.name, sha256=digest, bytes=size))
    index = folder / "reverse-audit.json"
    write_json(index, dict(version=1, source=SOURCE, reader_sha256=reader_hash, render_commit=RENDER_COMMIT,
                           core_index_sha256=info(folder / "edition-index.json")[0], totals=totals,
                           terms=edition["targets"], ranges=ranges, shards=by_shard, endpoint_extract=extracts,
                           prose_writer_sha256=prose_hash, prose_volumes=total_volumes, prose_tex_bytes=total_print_bytes))
    put(target, assets, index, tag=AUDIT_TAG)
    if target["draft"]:
        body = (f"All {totals['records']:,} numbered solution-export records were independently decoded "
                f"from the mathematical LaTeX volumes and matched field for field with the MIT-published "
                f"source export. The lookup tables locate {totals['declarations']:,} declarations. "
                f"The {total_volumes:,} annotated LaTeX volumes in the prose archives retain each mathematical "
                "record and give its reading in dependent type theory. The five terminal declarations and their "
                "immediate type and value records are printed in rh-theorem-records.pdf and .tex. "
                "This verifies fidelity of the formal typesetting. The prose paper has its own coverage statement.")
        api(f"repos/{REPO}/releases/{target['id']}", "--method", "PATCH", "-F", "draft=false",
            "-f", "tag_name=" + AUDIT_TAG, "-f", "target_commitish=main", "-f", "make_latest=false", "-f", "body=" + body)
    print(f"Verified all {totals['records']:,} records; indexed {totals['declarations']:,} declarations.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=("plan", "verify", "finish"))
    parser.add_argument("id", type=int, nargs="?")
    args = parser.parse_args()
    with tempfile.TemporaryDirectory() as work:
        folder = Path(work)
        if args.mode == "plan" and args.id is None:
            plan(folder)
        elif args.mode == "verify" and args.id is not None:
            verify_one(folder, args.id)
        elif args.mode == "finish" and args.id is None:
            finish(folder)
        else:
            parser.error("verify requires exactly one shard number")


if __name__ == "__main__":
    main()
