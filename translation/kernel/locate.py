"""Find a printed record in the published mathematical term volumes, without Lean.

Requires Python 3.14+ for zstd support. Reads release assets in memory. Examples:
  python locate.py riemannHypothesis
  python locate.py E12
  python locate.py R60
  python locate.py --sample declaration:N9
"""
import argparse
import gzip
import hashlib
import io
import json
import re
import sys
import tarfile
from urllib.error import HTTPError
from urllib.request import Request, urlopen


REPOSITORY = "https://github.com/ChristianKudeba/alpoge-rh-verification"
RELEASE = REPOSITORY + "/releases/download/rh-literal-kernel-v1/"
AUDIT = REPOSITORY + "/releases/download/rh-literal-audit-v1/"
SAMPLE = ("https://raw.githubusercontent.com/ChristianKudeba/alpoge-rh-verification/"
          "4e22ad3692dae97711b2d3c7ee465719b7545828/translation/kernel/sample/kernel-00001.tex")
SOURCE_SHA = "5ea74b912147c5c93cc2b6d70cc727cf908df2f62ac6a20480a3fa02f6be244e"
ROW = re.compile(rb"^\\record\{([0-9]+)\}(.*)$", re.MULTILINE)
TITLES = (b"Axiom|Definition|Opaque|Theorem|Quotient primitive|"
          b"Inductive type|Constructor|Recursor")


def fetch(url, expected_hash=None):
    request = Request(url, headers={"User-Agent": "alpoge-rh-latex-reader"})
    with urlopen(request, timeout=120) as response:
        data = response.read()
    if expected_hash and hashlib.sha256(data).hexdigest() != expected_hash:
        raise ValueError("SHA-256 mismatch: " + url)
    return data


def decode_query(text):
    match = re.fullmatch(r"(declaration:)?([RENU])([0-9]+)", text)
    if not match:
        return "target", text
    prefix, category, digits = match.groups()
    if prefix and category != "N":
        raise ValueError("a declaration lookup takes a name index, e.g. declaration:N9")
    return ("declaration" if prefix else category), int(digits)


def find_in_volume(data, category, index):
    if category == "R":
        needle = re.compile(rb"^\\record\{" + str(index).encode() + rb"\}", re.MULTILINE)
    elif category == "declaration":
        needle = re.compile(rb"^\\(?:record\{[0-9]+\}|subrow )\\textbf\{(?:" + TITLES
                            + rb")\} \\\(N_\{" + str(index).encode() + rb"\}\\\)", re.MULTILINE)
    else:
        needle = re.compile(rb"^\\record\{[0-9]+\}\\\(" + category.encode() + rb"_\{"
                            + str(index).encode() + rb"\}=", re.MULTILINE)
    found = needle.search(data)
    if found is None:
        return None
    start = found.start()
    if data.startswith(b"\\subrow", start):
        start = data.rfind(b"\n\\record{", 0, start) + 1
    row = ROW.match(data, start)
    if row is None:
        raise ValueError("invalid record boundary")
    later = ROW.search(data, row.end())
    end = later.start() if later else data.index(b"\\end{document}", row.end())
    return int(row.group(1)), data[start:end].decode("utf-8").rstrip()


def search_archive(item, category, index):
    from compression import zstd
    report = json.loads(fetch(RELEASE + item["report"], item["report_sha256"]))
    archive = fetch(RELEASE + item["archive"], item["archive_sha256"])
    if len(archive) != item["archive_bytes"]:
        raise ValueError("archive length mismatch")
    with zstd.open(io.BytesIO(archive), "rb") as dec, tarfile.open(fileobj=dec, mode="r|") as tar:
        for vol in report["volumes"]:
            member = tar.next()
            if member is None or not member.isfile() or (
                    member.name, member.size) != (vol["name"], vol["bytes"]):
                raise ValueError("volume inventory mismatch")
            if category == "R" and not vol["first_line"] <= index <= vol["last_line"]:
                continue
            file = tar.extractfile(member)
            if file is None:
                raise ValueError("unreadable volume")
            data = file.read()
            if hashlib.sha256(data).hexdigest() != vol["sha256"]:
                raise ValueError("volume hash mismatch")
            result = find_in_volume(data, category, index)
            if result:
                return vol["name"], result
    return None


def declaration_record(name_id, edition_bytes):
    try:
        audit = json.loads(fetch(AUDIT + "reverse-audit.json"))
    except HTTPError as exc:
        if exc.code == 404:
            return None
        raise
    if audit["core_index_sha256"] != hashlib.sha256(edition_bytes).hexdigest():
        raise ValueError("declaration index belongs to a different edition")
    for part in audit["ranges"]:
        if part["low"] <= name_id <= part["high"]:
            data = fetch(AUDIT + part["asset"], part["sha256"])
            for line in gzip.decompress(data).splitlines():
                number, record, _ = line.split(b"\t")
                if int(number) == name_id:
                    return int(record)
            break
    raise LookupError(f"N{name_id} does not name an exported declaration")


def locate(query, sample=False):
    category, value = decode_query(query)
    if category in {"N", "U"} and value == 0:
        return "Built-in convention", (0, "anonymous root" if category == "N" else "universe zero")
    if sample:
        if category == "target":
            raise ValueError("the sample contains records 1 through 105; use an index")
        result = find_in_volume(fetch(SAMPLE), category, value)
        if result:
            return "kernel-00001.tex", result
        raise LookupError("no matching record in the 105-record sample")
    edition_bytes = fetch(RELEASE + "edition-index.json")
    edition = json.loads(edition_bytes)
    if edition["source"]["sha256"] != SOURCE_SHA:
        raise ValueError("unexpected source edition")
    if category == "target":
        found = [x for x in edition["targets"] if x["name"] == value]
        if len(found) != 1:
            choices = ", ".join(x["name"] for x in edition["targets"])
            raise LookupError("named endpoints are " + choices)
        target = found[0]
        print(f"{value}: type E{target['type_index']}, proof E{target['value_index']}", file=sys.stderr)
        category, value = "R", target["line"]
    if category == "declaration":
        record = declaration_record(value, edition_bytes)
        if record is not None:
            category, value = "R", record
    parts = json.loads(fetch(RELEASE + "shards.json", edition["source_manifest_sha256"]))["shards"]
    if len(parts) != len(edition["shards"]):
        raise ValueError("source and volume inventories differ")
    for part, item in zip(parts, edition["shards"], strict=True):
        if part["id"] != item["id"]:
            raise ValueError("shard numbering mismatch")
        if category == "R":
            keep = item["first_record"] <= value <= item["last_record"]
        elif category == "declaration":
            # The declaration may occur in any shard after its name was constructed.
            keep = value < part["end"]["N"]
        else:
            keep = part["start"][category] <= value < part["end"][category]
        if keep:
            result = search_archive(item, category, value)
            if result:
                volume, row = result
                return item["archive"] + "/" + volume, row
    raise LookupError("no matching record in the verified edition")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("query", help="R<record>, E<expr>, U<level>, N<name>, declaration:N<name>, or endpoint")
    parser.add_argument("--sample", action="store_true", help="use the pinned, 105-record sample")
    args = parser.parse_args()
    volume, (line, content) = locate(args.query, args.sample)
    print(f"{volume} (global record {line})", file=sys.stderr)
    print(content)


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, LookupError) as exc:
        raise SystemExit(str(exc))
