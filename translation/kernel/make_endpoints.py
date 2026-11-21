"""Build the printable extract of five theorem entry points on the hosted runner.

make_endpoints(folder, edition, parts, assets) returns (tex_path, pdf_path).
edition is edition-index.json, parts is shards.json and assets is release_store's
release-asset map. No Lean source, compiled library or Lean toolchain is used.
"""
from collections import defaultdict
import hashlib
import io
import json
import os
from pathlib import Path
import re
import subprocess
import tarfile
import tempfile

from read_terms import iter_records


HEADINGS = {
    "riemannHypothesis": "The Riemann hypothesis",
    "riemannZeta_eq_zero_re": "Real parts of zeta zeros",
    "LFunction_ne_zero_of_half_lt_re": "Nonvanishing to the right of the critical line",
    "LFunction_eq_zero_re": "Real parts of Dirichlet $L$-function zeros",
    "LFunction_eq_zero_re_of_isPrimitive": "The primitive-character case",
}
RECORD = re.compile(rb"\\record\{([1-9][0-9]*)\}")
INDEXED = re.compile(rb"\\\(([NE])_\{([0-9]+)\}=")
VOLNAME = re.compile(r"shard-([0-9]{4})/volume-([0-9]{5})\.tex")
SHA = re.compile(r"[0-9a-f]{64}")
ROLES = ("Theorem declaration", "Declaration name", "Statement expression", "Proof expression")
PREAMBLE = r"""\documentclass[10pt]{article}
\usepackage[letterpaper,margin=.85in]{geometry}
\usepackage{amsmath,amssymb}
\ifdefined\pdfinfoomitdate\pdfinfoomitdate=1\fi
\ifdefined\pdftrailerid\pdftrailerid{}\fi
\ifdefined\pdfsuppressptexinfo\pdfsuppressptexinfo=15\fi
\setlength{\parindent}{0pt}
\setlength{\parskip}{3pt}
\setlength{\emergencystretch}{4em}
\newcommand{\record}[1]{\par\hangindent=6.1em\hangafter=1%
\makebox[5.8em][r]{\scriptsize #1}\hspace{.3em}}
\newcommand{\subrow}{\par\noindent\hspace*{6.1em}}
\begin{document}
"""
INTRO = r"""{\LARGE\bfseries The Riemann hypothesis in the kernel export\par}
\medskip
Five theorem declarations and the first expression nodes of their
statements and proofs, transcribed verbatim from the indexed mathematical
edition of the MIT-distributed Lean export. To follow a proof beyond
its first node, look up the numbered references in the full edition.

The left margin gives global record numbers. \(N_i\) is a name,
\(U_i\) a universe and \(E_i\) an expression. The theorem row names its
statement and proof by expression index. A dependent product
\(\prod\) binds a variable, \(\lambda\) introduces a function, and
\(E_i\,(E_j)\) applies one term to another.
"""


def record_keys(t):
    return (("R", t["line"]), ("N", t["name_index"]), ("E", t["type_index"]),
            ("E", t["value_index"]))


def plan(edition, parts):
    targets = edition["targets"]
    if ({t["name"] for t in targets} != HEADINGS.keys() or len(targets) != len(HEADINGS)
            or parts["source"] != edition["source"] or len(parts["shards"]) != len(edition["shards"])):
        raise ValueError("unexpected theorem roots or edition/source mismatch")
    registry = {p["id"]: p for p in parts["shards"]}
    if len(registry) != len(parts["shards"]) or set(registry) != {x["id"] for x in edition["shards"]}:
        raise ValueError("inconsistent source and edition shard ids")
    by_shard = defaultdict(set)
    for t in targets:
        if t["kind"] != "thm":
            raise ValueError("the target must be a theorem")
        for family, i in record_keys(t):
            if type(i) is not int or i < (1 if family != "E" else 0):
                raise ValueError("invalid theorem record or index")
            if family == "R":
                owners = [p["id"] for p in registry.values() if p["first_line"] <= i <= p["last_line"]]
            else:
                owners = [p["id"] for p in registry.values() if p["start"][family] <= i < p["end"][family]]
            if len(owners) != 1:
                raise ValueError(f"{family}{i} has {len(owners)} candidate shards")
            by_shard[owners[0]].add((family, i))
    return by_shard


def search_pattern(keys):
    """Match only requested objects at physical row starts, without decoding every row."""
    branches = []
    for kind in ("R", "N", "E"):
        ids = sorted(i for family, i in keys if family == kind)
        if not ids:
            continue
        digits = b"(?:" + b"|".join(str(i).encode("ascii") for i in ids) + b")"
        if kind == "R":
            branches.append(rb"\\record\{" + digits + rb"\}")
        else:
            branches.append(rb"\\record\{[0-9]+\}\\\(" + kind.encode("ascii")
                            + rb"_\{" + digits + rb"\}=")
    return re.compile(b"^(?:" + b"|".join(branches) + b")", re.MULTILINE)


def collect_volume(data, spec, keys, pattern, found):
    for hit in pattern.finditer(data):
        start = hit.start()
        row = RECORD.match(data, start)
        number = int(row[1])
        if not spec["first_line"] <= number <= spec["last_line"]:
            raise ValueError("record outside verified volume range")
        stop = data.find(b"\n", row.end())
        if stop < 0:
            raise ValueError("unterminated record")
        stop += 1
        while data.startswith(b"\\subrow ", stop):
            newline = data.find(b"\n", stop)
            if newline < 0:
                raise ValueError("unterminated declaration subrow")
            stop = newline + 1
        chunk = data[start:stop]
        decoded = list(iter_records(io.BytesIO(chunk), rows_only=True))
        if len(decoded) != 1 or decoded[0][0] != number:
            raise ValueError("exact row cannot be decoded")
        indexed = INDEXED.match(data, row.end())
        candidates = [("R", number)]
        if indexed:
            family, index = indexed[1].decode("ascii"), int(indexed[2])
            if decoded[0][1].get({"N": "in", "E": "ie"}[family]) != index:
                raise ValueError("indexed equation and decoded reference disagree")
            candidates.append((family, index))
        for key in candidates:
            if key in keys:
                if key in found:
                    raise ValueError(f"duplicate record for {key}")
                found[key] = (number, spec["name"], chunk.decode("utf-8"), decoded[0][1])


def scan_archive(stream, report, keys, found):
    """Read and hash each listed TeX member once, with no unpacked archive on disk."""
    pattern = search_pattern(keys)
    next_line = report["first_line"]
    with tarfile.open(fileobj=stream, mode="r|") as package:
        for j, spec in enumerate(report["volumes"], 1):
            name = f"shard-{report['id']:04d}/volume-{j:05d}.tex"
            size = spec["bytes"]
            if (spec["name"] != name or spec["first_line"] != next_line
                    or not next_line <= spec["last_line"] <= report["last_line"]
                    or type(size) is not int or size <= 0 or not SHA.fullmatch(spec["sha256"])):
                raise ValueError("invalid per-volume report")
            member = package.next()
            if member is None or not member.isfile() or member.name != name or member.size != size:
                raise ValueError(f"archive does not contain expected member {name}")
            with package.extractfile(member) as fp:
                data = fp.read()
            if len(data) != size or hashlib.sha256(data).hexdigest() != spec["sha256"]:
                raise ValueError(f"volume failed SHA-256/size check: {name}")
            collect_volume(data, spec, keys, pattern, found)
            next_line = spec["last_line"] + 1
        if package.next() is not None or next_line != report["last_line"] + 1:
            raise ValueError("archive membership or volume range not exhausted")
    if not keys.issubset(found):
        raise ValueError(f"missing selected records: {sorted(keys - found.keys())}")


def tex_document(targets, found):
    output = [PREAMBLE, INTRO]
    for pos, t in enumerate(targets):
        name = t["name"]
        declaration, name_record, statement, proof = [found[key] for key in record_keys(t)]
        if declaration[3].get("thm", {}).get("name") != t["name_index"]:
            raise ValueError(f"{name}: theorem name pointer differs")
        value = declaration[3]["thm"]
        if (value["type"] != t["type_index"] or value["value"] != t["value_index"]
                or name_record[3] != {"in": t["name_index"], "str": {"pre": 0, "str": name}}
                or statement[3].get("ie") != t["type_index"] or proof[3].get("ie") != t["value_index"]
                or max(name_record[0], statement[0], proof[0]) >= declaration[0]):
            raise ValueError(f"{name}: mismatched direct references")
        if pos:
            output.append("\\clearpage\n")
        output.append("\\section*{" + HEADINGS[name] + "}\n")
        # Fixed allowlist of target identifiers. Break at underscores for narrow columns.
        label = name.replace("_", r"\_\allowbreak{}")
        output.append("\\texttt{" + label + "}\n")
        for role, (record, volume, raw, _) in zip(ROLES, (declaration, name_record, statement, proof)):
            origin = VOLNAME.fullmatch(volume)
            if origin is None:
                raise ValueError("invalid source volume locator")
            output.append("\\par\\medskip\\textbf{" + role + "}\\hfill"
                          + f"{{\\small Shard {int(origin[1])}, volume {int(origin[2])}}}\n")
            output.append(raw)
    output.append("\\end{document}\n")
    return "".join(output)


def make_endpoints(folder, edition, parts, assets):
    """Download each needed release archive once and typeset in hosted temporary storage."""
    from compression import zstd
    from release_store import download, matches, info

    folder = Path(folder)
    wanted = plan(edition, parts)
    inventory = {row["id"]: row for row in edition["shards"]}
    roots = {t["name"]: t for t in edition["targets"]}
    found = {}
    with tempfile.TemporaryDirectory(dir=folder) as scratch:
        scratch = Path(scratch)
        for i, keys in sorted(wanted.items()):
            item = inventory[i]
            rn = f"shard-{i:04d}.json"
            an = f"shard-{i:04d}.tar.zst"
            if (item["report"] != rn or item["archive"] != an
                    or not matches(assets.get(an), item["archive_sha256"], item["archive_bytes"])):
                raise ValueError(f"release archive differs from edition for shard {i}")
            report_path = scratch / rn
            download(assets[rn], report_path)
            if info(report_path)[0] != item["report_sha256"]:
                raise ValueError(f"shard {i} report digest differs from edition")
            report = json.loads(report_path.read_bytes())
            if (report["id"] != i or report["first_line"] != item["first_record"]
                    or report["last_line"] != item["last_record"] or report["archive"] != an
                    or report["archive_bytes"] != item["archive_bytes"]
                    or report["archive_sha256"] != item["archive_sha256"]
                    or len(report["volumes"]) != item["volume_count"]):
                raise ValueError(f"shard {i} report identity mismatch")
            archive_path = scratch / an
            download(assets[an], archive_path)  # verifies the actual file hash and size
            with zstd.open(archive_path, "rb", options={zstd.DecompressionParameter.window_log_max:30}) as stream:
                scan_archive(stream, report, keys, found)
            archive_path.unlink()
        stem = "rh-theorem-records"
        source, pdf = scratch / (stem + ".tex"), scratch / (stem + ".pdf")
        source.write_text(tex_document([roots[n] for n in HEADINGS], found), encoding="utf-8", newline="\n")
        env = dict(os.environ, SOURCE_DATE_EPOCH="946684800", FORCE_SOURCE_DATE="1")
        subprocess.run(["pdflatex", "-no-shell-escape", "-interaction=nonstopmode", "-halt-on-error",
                        source.name], cwd=scratch, env=env, check=True, stdout=subprocess.DEVNULL)
        if not pdf.is_file() or not pdf.read_bytes().startswith(b"%PDF-"):
            raise ValueError("typesetter produced no PDF")
        result = (folder / source.name, folder / pdf.name)
        os.replace(source, result[0])
        os.replace(pdf, result[1])
    return result
