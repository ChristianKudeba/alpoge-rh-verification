"""Round-trip all constructors through the TeX and independently parsed records."""
import hashlib
import io
import json
from pathlib import Path
import tarfile
import unittest
from contextlib import contextmanager
from unittest.mock import patch
from kernel_tex import LEGEND, LAYOUT, Notation
from read_terms import FormatError, iter_input, iter_records


def canonical(x):
    return json.dumps(x, ensure_ascii=True, sort_keys=True, separators=(",", ":"))


def synthetic():
    # The identifiers and types test the wire grammar; these are not proposed Lean declarations.
    strange = '\x00\t\n\rΩ😀\u2028"\\{}%#$&_~^  ' + r"\allowbreak{}\texttt{\end{document}}"
    records = [{"meta": {"exporter": {"name": "fixture", "version": "1"},
                          "format": {"version": "3.1.0"}, "lean": {"version": "x"},
                          "other": [True, 2, None, {strange: strange}]}}]
    counts = {"in": 1, "il": 1, "ie": 0}

    def put(family, kind, value):
        i = counts[family]
        records.append({family: i, kind: value})
        counts[family] += 1
        return i

    n = put("in", "str", {"pre": 0, "str": strange})
    m = put("in", "num", {"pre": n, "i": 4321})
    put("in", "str", {"pre": m, "str": ""})
    p = put("il", "param", n)
    q = put("il", "succ", p)
    put("il", "max", [q, 0])
    put("il", "imax", [p, q])
    t = put("ie", "sort", 0)
    b = put("ie", "bvar", 913)
    for us in ([], [q, p, q]):
        put("ie", "const", {"name": m, "us": us})
    for key in ("lam", "forallE"):
        for mode in ("default", "strictImplicit", "instImplicit", "implicit"):
            put("ie", key, {"name": n, "type": t, "body": b, "binderInfo": mode})
    put("ie", "app", {"fn": t, "arg": b})
    for flag in (True, False):
        put("ie", "letE", {"name": m, "type": t, "value": b, "body": t, "nondep": flag})
    put("ie", "proj", {"typeName": m, "idx": 196, "struct": b})
    put("ie", "natVal", "000" + "984732" * 67)
    for text in (strange, "", " " * 47, "\ud800", "\udfff", "abc\\u1234"):
        put("ie", "strVal", text)
    put("ie", "mdata", {"data": {"payload": [True, False, None, -3, "]}"]}, "expr": b})
    put("ie", "mdata", {"data": {}, "expr": t})
    base = {"name": n, "type": t, "levelParams": []}
    records.append({"axiom": dict(base, isUnsafe=True)})
    records.append({"thm": dict(base, value=b, all=[m, n, m])})
    records.append({"opaque": dict(base, value=t, all=[], isUnsafe=False)})
    for hint, safety in (("abbrev", "safe"), ("opaque", "unsafe"), ({"regular": 314}, "partial")):
        records.append({"def": dict(base, value=b, all=[n], hints=hint, safety=safety)})
    for k in ("type", "ctor", "lift", "ind"):
        records.append({"quot": dict(base, kind=k)})
    ty = dict(base, numParams=2, numIndices=3, all=[n, m], ctors=[m, n, m],
              numNested=4, isRec=False, isUnsafe=True, isReflexive=False)
    ctor = dict(base, induct=n, cidx=1, numParams=4, numFields=3, isUnsafe=False)
    rec = dict(base, all=[m, n], numParams=1, numIndices=2, numMotives=3,
               numMinors=4, rules=[{"ctor": m, "nfields": 2, "rhs": b},
                                     {"ctor": n, "nfields": 0, "rhs": t}],
               k=False, isUnsafe=True)
    records.append({"inductive": {"types": [ty, dict(ty, name=m, ctors=[])], "ctors": [ctor],
                                  "recs": [rec, dict(rec, name=m, rules=[])]}})
    records.append({"inductive": {"types": [], "ctors": [], "recs": []}})
    return records


def render_rows(records, size=3):
    encoder = Notation(size)  # deliberately evict many optional cached names/expansions
    lines = []
    for i, source in enumerate(records, 1):
        _, rows = encoder.render(source, i)
        lines.append(r"\record{" + str(i) + "}" + rows[0])
        lines.extend(r"\subrow " + extra for extra in rows[1:])
    return "\n".join(lines) + "\n"


class ReaderTests(unittest.TestCase):
    def test_roundtrip(self):
        original = synthetic()
        body = render_rows(original)
        numbered = list(iter_records(io.StringIO(body), rows_only=True))
        self.assertEqual([i for i, _ in numbered], list(range(1, len(original) + 1)))
        self.assertEqual([canonical(x) for _, x in numbered], list(map(canonical, original)))
        head = body.index(r"\record{21}")
        for a, b, expected in [(0, head, numbered[:20]), (head, len(body), numbered[20:])]:
            volume = (LAYOUT + LEGEND + body[a:b] + "\\end{document}\n").encode("utf-8")
            self.assertEqual(list(iter_records(io.BytesIO(volume))), expected)


    def test_published_reference(self):
        path = Path(__file__).with_name("sample") / "kernel-00001.tex"
        digest = hashlib.sha256()
        total = 0
        with path.open("rb") as stream:
            for number, row in iter_records(stream):
                total += 1
                self.assertEqual(number, total)
                digest.update((canonical(row) + "\n").encode("ascii"))
        self.assertEqual(total, 105)
        # Independent canonicalization of the first 105 decoded MIT NDJSON lines,
        # https://math.mit.edu/~drew/grh/solution.ndjson.zst; LF after each object.
        self.assertEqual(digest.hexdigest(),
                         "29e9053083190b112d38072481548db0b4e5cd0b9caa1061e7f44c6889e4de31")

    def test_streaming_archive(self):
        original = synthetic()
        body = render_rows(original)
        cut = body.index(r"\record{21}")
        data = io.BytesIO()
        with tarfile.open(fileobj=data, mode="w|") as tar:
            for i, section in enumerate((body[:cut], body[cut:]), 1):
                tex = (LAYOUT + LEGEND + section + "\\end{document}\n").encode()
                info = tarfile.TarInfo(f"shard-0000-volume-{i:05}.tex")
                info.size = len(tex)
                tar.addfile(info, io.BytesIO(tex))
        data.seek(0)

        @contextmanager
        def in_memory(_):
            yield data

        with patch("read_terms.open_input", in_memory):
            result = list(iter_input("shard-0000.tar"))
        self.assertEqual([i for i, _ in result], list(range(1, len(original) + 1)))
        self.assertEqual([canonical(x) for _, x in result], list(map(canonical, original)))

    def test_corrupt_records(self):
        examples = (
            r"\record{9}\(E_{9}=\operatorname{unknown}(E_{1})\)",
            r"\record{9}\(N_{2}=N_{0}\mathbin{\cdot_{\rm str}}\) \texttt{\bad{}}",
            r"\record{9}\textbf{Theorem} \(N_{1}\) \(\colon E_{0}\)",
            r"\record{9}\(E_{10}=\operatorname{let}\ N_{0}:E_{0}:=E_{0}\ \operatorname{in}\ E_{1}\quad\mathrm{nondep}=\mathrm{maybe}\)",
            r"\record{9}\(E_{9}=b_{3}\)" + "\n" + r"\record{11}\(E_{10}=b_{0}\)",
        )
        for example in examples:
            with self.subTest(row=example), self.assertRaises(FormatError):
                list(iter_records(io.StringIO(example), rows_only=True))
        with self.assertRaises(FormatError):
            list(iter_records(io.StringIO(LAYOUT + r"\record{9}\(E_{9}=b_{3}\)")))


if __name__ == "__main__":
    unittest.main()
