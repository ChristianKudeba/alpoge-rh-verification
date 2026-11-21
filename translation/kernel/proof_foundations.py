"""Recover and identify the three foundational axioms from the mathematical edition."""
from collections import defaultdict
import json
from pathlib import Path
import tempfile

from make_endpoints import scan_archive
from release_store import download, info, matches


EXPECTED = {"propext", "Classical.choice", "Quot.sound"}


def foundations(folder, edition, parts, assets, axioms):
    from compression import zstd
    if len(axioms) != 3:
        raise ValueError("the decoded environment must contain exactly three axioms")
    found, scanned, output = {}, {}, []
    inventory = {s["id"]: s for s in edition["shards"]}
    needed = {key for n, row, _ in axioms for key in (("N", n), ("R", row))}

    def namestring(i):
        pieces, seen = [], set()
        while i:
            if i in seen:
                raise ValueError("cyclic name")
            seen.add(i)
            row = found[("N", i)][3]
            if "str" in row:
                value = row["str"]
                pieces.append(value["str"])
            else:
                value = row["num"]
                pieces.append(str(value["i"]))
            i = value["pre"]
        return ".".join(reversed(pieces))

    with tempfile.TemporaryDirectory(dir=folder) as temp:
        root = Path(temp)
        while needed:
            by_shard = defaultdict(set)
            for kind, number in needed - found.keys():
                choices = [p["id"] for p in parts["shards"] if
                           (p["first_line"] <= number <= p["last_line"] if kind == "R" else
                            p["start"][kind] <= number < p["end"][kind])]
                if len(choices) != 1:
                    raise ValueError("ambiguous foundation record")
                by_shard[choices[0]].add((kind, number))
            if not by_shard:
                break
            for i, keys in sorted(by_shard.items()):
                item = inventory[i]
                if i not in scanned:
                    report_path, archive = root / item["report"], root / item["archive"]
                    if not matches(assets.get(item["archive"]), item["archive_sha256"], item["archive_bytes"]):
                        raise ValueError("foundation archive digest mismatch")
                    download(assets[item["report"]], report_path)
                    if info(report_path)[0] != item["report_sha256"]:
                        raise ValueError("foundation report digest mismatch")
                    report = json.loads(report_path.read_bytes())
                    if (report["id"] != i or report["first_line"] != item["first_record"]
                            or report["last_line"] != item["last_record"]
                            or len(report["volumes"]) != item["volume_count"]):
                        raise ValueError("foundation report interval mismatch")
                    download(assets[item["archive"]], archive)
                    scanned[i] = archive, report
                archive, report = scanned[i]
                with zstd.open(archive, "rb") as stream:
                    scan_archive(stream, report, keys, found)
            needed = {("N", found[k][3].get("str", found[k][3].get("num"))["pre"])
                      for k in found if k[0] == "N"} - {("N", 0)} - found.keys()
        for n, line, kind in axioms:
            record = found[("R", line)]
            row = record[3]
            if kind != "axiom" or set(row) != {"axiom"} or row["axiom"]["name"] != n:
                raise ValueError("wrong declaration in foundation index")
            name = namestring(n)
            output.append(dict(name=name, line=line, name_index=n, type_index=row["axiom"]["type"],
                               volume=record[1], tex=record[2]))
        if {a["name"] for a in output} != EXPECTED:
            raise ValueError("unexpected foundational axioms")
    return output


def appendix(entries):
    tex = [r"\clearpage\section*{Foundational axioms}" + "\n",
           "The full decoded declaration index contains precisely the following three axioms. "
           "Their records and type references are copied from the mathematical edition. "
           "The quotient primitives and inductive computation rules are recorded separately "
           "in that edition.\n"]
    for a in sorted(entries, key=lambda x: x["line"]):
        tex.append("\\par\\medskip\\textbf{" + a["name"] + "}\n")
        tex.append(a["tex"])
    return "".join(tex)
