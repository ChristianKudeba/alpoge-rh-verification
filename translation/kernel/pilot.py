"""Remote pilot using real records of a staged source asset before full publication."""
from compression import zstd
import hashlib
import io
import json
import os
from pathlib import Path
import subprocess
import tarfile
import tempfile
import time

from prepare import INITIAL, end_table
from prose_records import annotated_volume, meaning
from read_terms import iter_records
from release_store import download, listing, release
from render_shard import render_records
from verify_terms import verify_records


def pilot(folder):
    assets = listing(release()["id"])
    staged = assets.get("source-0000.ndjson.zst")
    if staged is None:
        raise LookupError("the first verified source asset is required for the pilot")
    source = folder / staged["name"]
    download(staged, source)
    limit = 150_000
    with zstd.open(source, "rb") as stream:
        lines = [stream.readline() for _ in range(limit)]
    if not all(lines):
        raise EOFError("short source asset")
    raw = b"".join(lines)
    shortened = folder / "pilot.ndjson.zst"
    shortened.write_bytes(zstd.compress(raw))
    part = dict(id=0, first_line=1, last_line=limit, start=INITIAL, end=end_table(raw, INITIAL),
                raw_bytes=len(raw), raw_sha256=hashlib.sha256(raw).hexdigest())
    archive = folder / "pilot.tar.zst"
    since = time.monotonic()
    with zstd.open(archive, "wb", level=4) as compressed, tarfile.open(fileobj=compressed, mode="w|") as tar:
        report = render_records(lines, part, {}, tar)
    elapsed = time.monotonic() - since
    before = time.monotonic()
    check = verify_records(shortened, archive, part, report, folder / "pilot.tsv.gz", folder / "prose.tar.zst")
    audit_time = time.monotonic() - before
    print(f"Records: {limit:,}. Source bytes: {len(raw):,}. Expressions: {part['end']['E']:,}. "
          f"Declarations: {check['declarations']:,}. Render {elapsed:.2f} s; readback and prose {audit_time:.2f} s.",
          flush=True)
    print("Record kinds: " + json.dumps(report["record_kinds"], sort_keys=True), flush=True)
    sample = Path(__file__).with_name("sample").joinpath("kernel-00001.tex").read_bytes()
    out = Path(os.environ["RUNNER_TEMP"]) / "rh-prose-sample"
    out.mkdir(exist_ok=True)
    file = out / "reading-equality.tex"
    file.write_bytes(annotated_volume(sample, ((n, meaning(row)) for n, row in iter_records(io.BytesIO(sample)))))
    env = dict(os.environ, SOURCE_DATE_EPOCH="946684800", FORCE_SOURCE_DATE="1")
    subprocess.run(["pdflatex", "-no-shell-escape", "-interaction=nonstopmode", "-halt-on-error", file.name],
                   cwd=out, env=env, check=True, stdout=subprocess.DEVNULL)
    print(f"Typeset the annotated equality example in {out}.", flush=True)


if __name__ == "__main__":
    with tempfile.TemporaryDirectory() as work:
        pilot(Path(work))
