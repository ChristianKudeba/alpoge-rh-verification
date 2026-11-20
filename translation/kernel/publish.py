"""Render one verified source shard or close a complete edition on the hosted runner."""
import argparse
from collections import Counter
from compression import zstd
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tarfile
import tempfile

from prepare import BASE, TARGETS, verify_manifest
from release_store import REPO, TAG, api, download, info, listing, matches, put, release, write_json


def is_digest(s):
    return isinstance(s, str) and re.fullmatch(r"[0-9a-f]{64}", s) is not None


def check_report(part, report, archive_asset, targets):
    i = part["id"]
    archive = f"shard-{i:04d}.tar.zst"
    expected = dict(version=1, id=i, first_line=part["first_line"], last_line=part["last_line"],
                    start=part["start"], end=part["end"], raw_bytes=part["raw_bytes"],
                    raw_sha256=part["raw_sha256"], source_asset=part["asset"],
                    source_bytes=part["compressed_bytes"], source_sha256=part["compressed_sha256"],
                    archive=archive, records=part["last_line"] - part["first_line"] + 1)
    if any(report.get(k) != v for k, v in expected.items()):
        raise ValueError(f"shard {i}: record metadata mismatch")
    if not matches(archive_asset, report["archive_sha256"], report["archive_bytes"]):
        raise ValueError("typeset volume archive was not uploaded with the recorded checksum")
    counts = report["record_kinds"]
    if (not isinstance(counts, dict) or any(type(v) is not int or v < 1 for v in counts.values())
            or sum(counts.values()) != expected["records"]):
        raise ValueError("invalid record-kind inventory")
    line = part["first_line"]
    for j, vol in enumerate(report["volumes"], 1):
        if (vol["name"] != f"shard-{i:04d}/volume-{j:05d}.tex" or
                vol["first_line"] != line or vol["last_line"] < line or
                vol["bytes"] <= 0 or not is_digest(vol["sha256"])):
            raise ValueError("invalid volume ranges or digest")
        line = vol["last_line"] + 1
    if line != part["last_line"] + 1:
        raise ValueError("LaTeX volumes do not cover the source shard")
    for entry in report["target_names"] + report["theorems"]:
        if (targets.get(str(entry["name_index"])) != entry["name"] or
                not part["first_line"] <= entry["line"] <= part["last_line"]):
            raise ValueError("target name or record position mismatch")
    for entry in report["target_names"]:
        if not part["start"]["N"] <= entry["name_index"] < part["end"]["N"]:
            raise ValueError("target name comes from the wrong source shard")
    for entry in report["theorems"]:
        if (entry["kind"] != "thm" or type(entry["type_index"]) is not int or
                type(entry["value_index"]) is not int or
                not 0 <= entry["type_index"] < part["end"]["E"] or
                not 0 <= entry["value_index"] < part["end"]["E"]):
            raise ValueError("missing theorem statement or proof expression")


def read_back(archive, report):
    """Independently unpack and hash every generated volume before marking the shard ready."""
    with zstd.open(archive, "rb") as compressed, tarfile.open(fileobj=compressed, mode="r|") as tf:
        for spec in report["volumes"]:
            member = tf.next()
            if member is None or not member.isfile() or (member.name, member.size) != (
                    spec["name"], spec["bytes"]):
                raise ValueError("unexpected tar member")
            data = tf.extractfile(member)
            if data is None or hashlib.file_digest(data, "sha256").hexdigest() != spec["sha256"]:
                raise ValueError("mismatched LaTeX volume")
        if tf.next() is not None:
            raise ValueError("additional unlisted tar members")


def render(i, manifest_file, data, folder, rel, assets):
    if not 0 <= i < len(data["shards"]):
        raise ValueError("invalid matrix index")
    part = data["shards"][i]
    report_file = folder / f"shard-{i:04d}.json"
    if report_file.name in assets:
        download(assets[report_file.name], report_file)
        report = json.loads(report_file.read_bytes())
        check_report(part, report, assets.get(report["archive"]), data["targets"])
        print(f"Reused previously published, digest-verified shard {i}")
        return
    source = folder / part["asset"]
    download(assets[part["asset"]], source)
    subprocess.run([sys.executable, str(BASE / "render_shard.py"), str(source),
                    str(manifest_file), str(i), str(folder)], check=True)
    report = json.loads(report_file.read_bytes())
    archive = folder / report["archive"]
    read_back(archive, report)
    asset = put(rel, assets, archive)
    check_report(part, report, asset, data["targets"])
    put(rel, assets, report_file)


def finalize(data, folder, rel, assets):
    inventory = []
    names, thms = [], []
    kind_counts = Counter()
    total_records = total_volumes = total_tex = 0
    for part in data["shards"]:
        i = part["id"]
        filename = f"shard-{i:04d}.json"
        path = folder / filename
        download(assets[filename], path)
        rep = json.loads(path.read_bytes())
        check_report(part, rep, assets.get(rep["archive"]), data["targets"])
        names.extend(rep["target_names"])
        thms.extend(rep["theorems"])
        kind_counts.update(rep["record_kinds"])
        total_records += rep["records"]
        total_volumes += len(rep["volumes"])
        total_tex += sum(v["bytes"] for v in rep["volumes"])
        inventory.append({"id": i, "report": filename, "report_sha256": info(path)[0],
                          "archive": rep["archive"], "archive_sha256": rep["archive_sha256"],
                          "archive_bytes": rep["archive_bytes"], "first_record": rep["first_line"],
                          "last_record": rep["last_line"], "volume_count": len(rep["volumes"])})
    once = Counter({s: 1 for s in TARGETS})
    if Counter(t["name"] for t in thms) != once or Counter(t["name"] for t in names) != once:
        raise ValueError("the five root names and the five proof-bearing theorem declarations are required")
    name_pos = {a["name_index"]: a["line"] for a in names}
    for t in thms:
        if name_pos[t["name_index"]] >= t["line"]:
            raise ValueError("theorem precedes its name")
    if total_records != data["shards"][-1]["last_line"]:
        raise ValueError("global record range mismatch")
    manifest = folder / "edition-index.json"
    write_json(manifest, dict(version=1, source=data["source"], renderer=data["renderer"],
               source_manifest_sha256=info(folder / "shards.json")[0], targets=thms,
               records=total_records, record_kinds=dict(kind_counts), volumes=total_volumes,
               tex_bytes=total_tex, index_counters_end=data["shards"][-1]["end"], shards=inventory))
    put(rel, assets, manifest)
    if rel["draft"]:
        body = (f"Literal mathematical term edition of the MIT-published Lean export. "
                f"{total_records:,} source records translated into {total_volumes:,} independent "
                f"LaTeX volumes. All five requested theorem declarations have statements and proof terms. "
                f"Start with **edition-index.json**; for each numbered archive the corresponding "
                f"JSON report indexes individual volumes and their SHA-256 hashes. "
                f"The source NDJSON shards and shards.json are included. "
                f"This edition renders kernel expressions in dependent type theory. "
                f"The accompanying human-readable manuscript has its own coverage statement.")
        api(f"repos/{REPO}/releases/{rel['id']}", "--method", "PATCH", "-F", "draft=false",
            "-f", "body=" + body)
    url = f"https://github.com/{REPO}/releases/tag/{TAG}"
    print(f"Verified {total_records:,} records in {total_volumes:,} volumes; {url}", flush=True)
    if "GITHUB_STEP_SUMMARY" in os.environ:
        with open(os.environ["GITHUB_STEP_SUMMARY"], "a", encoding="utf-8") as f:
            print(f"[Complete literal edition]({url}): {total_records:,} records, "
                  f"{total_volumes:,} volumes, five theorem targets.", file=f)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("action", choices=("render", "finalize"))
    parser.add_argument("index", type=int, nargs="?")
    args = parser.parse_args()
    rel = release()
    assets = listing(rel["id"])
    with tempfile.TemporaryDirectory() as tmp:
        folder = Path(tmp)
        manifest = folder / "shards.json"
        download(assets["shards.json"], manifest)
        data = json.loads(manifest.read_bytes())
        verify_manifest(data, assets)
        if args.action == "render" and args.index is not None:
            render(args.index, manifest, data, folder, rel, assets)
        elif args.action == "finalize" and args.index is None:
            finalize(data, folder, rel, assets)
        else:
            parser.error("render needs a shard id; finalize takes no shard id")


if __name__ == "__main__":
    main()
