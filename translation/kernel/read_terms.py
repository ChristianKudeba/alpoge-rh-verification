"""Read the exact numbered equations of the published lean4export 3.1.0 TeX edition.

iter_records(lines) accepts a single full volume and yields (global row, JSON object).
iter_records(lines, rows_only=True) accepts numbered rows with no document wrapper.
The reader never evaluates TeX. Optional explanatory type expansions and cached
display names do not supply any kernel fields. The input grammar is the edition's
TeX source, not a general LaTeX dialect or text extracted from a PDF.
"""
import argparse
from contextlib import contextmanager
import json
import re
import sys
import tarfile


class FormatError(ValueError):
    """A numbered row or its container is outside the published grammar."""


ESCAPES = {
    r"\textbackslash{}": "\\", r"\textasciicircum{}": "^", r"\textasciitilde{}": "~",
    r"\{": "{", r"\}": "}", r"\%": "%", r"\#": "#", r"\$": "$", r"\&": "&",
    r"\_": "_", r"\allowbreak{}": "",
}
ESCAPE = re.compile("|".join(re.escape(key) for key in ESCAPES))
TEXT_RUN = re.compile(r"[^\\{}]+")
DIGITS = re.compile(r"(?:0|[1-9][0-9]*)")
NAT_LITERAL = re.compile(r"[0-9]+")
RECORD = re.compile(r"\\record\{([1-9][0-9]*)\}")
INDEX = re.compile(r"\\\(([NUE])_\{(0|[1-9][0-9]*)\}=")
# Applications dominate the full solution. Keep the common case in one regex.
APP = re.compile(r"\\\(E_\{([0-9]+)\}=E_\{([0-9]+)\}\\,\(E_\{([0-9]+)\}\)\\\)")
BINDERS = (
    (r"\{\!\{", r"\}\!\}", "strictImplicit"),
    (r"\{", r"\}", "implicit"), ("[", "]", "instImplicit"), ("(", ")", "default"),
)
DECL_NAMES = {
    "Axiom": "axiom", "Definition": "def", "Opaque": "opaque", "Theorem": "thm",
    "Quotient primitive": "quot", "Inductive type": "type", "Constructor": "ctor",
    "Recursor": "rec",
}
SCHEMAS = {
    "axiom": ("isUnsafe",),
    "def": ("value", "hints", "safety", "all"),
    "opaque": ("value", "isUnsafe", "all"),
    "thm": ("value", "all"),
    "quot": ("kind",),
    "type": ("numParams", "numIndices", "all", "ctors", "numNested",
             "isRec", "isUnsafe", "isReflexive"),
    "ctor": ("induct", "cidx", "numParams", "numFields", "isUnsafe"),
    "rec": ("all", "numParams", "numIndices", "numMotives", "numMinors", "k", "isUnsafe"),
}
GROUPS = {"type": "types", "ctor": "ctors", "rec": "recs"}
TITLES = re.compile(r"\\textbf\{([^{}]+)\} ")


class Cursor:
    __slots__ = ("s", "pos")

    def __init__(self, s, pos=0):
        self.s = s
        self.pos = pos

    def take(self, token):
        if self.s.startswith(token, self.pos):
            self.pos += len(token)
            return True
        return False

    def need(self, token):
        if not self.take(token):
            raise FormatError(f"expected {token!r} at column {self.pos + 1}")

    def number(self):
        m = DIGITS.match(self.s, self.pos)
        if m is None:
            raise FormatError(f"expected a natural number at column {self.pos + 1}")
        self.pos = m.end()
        return int(m[0])

    def ref(self, kind):
        self.need(kind + "_{")
        value = self.number()
        self.need("}")
        return value

    def refs(self, kind):
        self.need("[")
        if self.take("]"):
            return []
        values = [self.ref(kind)]
        while self.take(r",\allowbreak{} "):
            values.append(self.ref(kind))
        self.need("]")
        return values

    def literal(self):
        self.need(r"\texttt{")
        result = []
        while not self.take("}"):
            m = TEXT_RUN.match(self.s, self.pos)
            if m:
                result.append(m[0])
            else:
                m = ESCAPE.match(self.s, self.pos)
                if m is None:
                    raise FormatError(f"invalid literal at column {self.pos + 1}")
                result.append(ESCAPES[m[0]])
            self.pos = m.end()
        return "".join(result)

    def json_literal(self, kind):
        value = json.loads(self.literal())
        if not isinstance(value, kind):
            raise FormatError("JSON literal has the wrong type")
        return value

    def boolean(self):
        if self.take("true"):
            return True
        self.need("false")
        return False

    def end(self, suffix=""):
        self.need(suffix)
        if self.pos != len(self.s):
            raise FormatError(f"trailing content at column {self.pos + 1}")


def indexed(row):
    fast = APP.fullmatch(row)
    if fast:
        i, f, a = map(int, fast.groups())
        return {"ie": i, "app": {"fn": f, "arg": a}}
    m = INDEX.match(row)
    if m is None:
        raise FormatError("expected an indexed equation")
    family, num = m[1], int(m[2])
    c = Cursor(row, m.end())
    tail = r"\)"
    if family == "N":
        parent = c.ref("N")
        if c.take(r"\mathbin{\cdot_{\rm str}}\) "):
            key, value = "str", {"pre": parent, "str": c.json_literal(str)}
            tail = ""
        else:
            c.need(r"\mathbin{\cdot_{\rm num}}")
            key, value = "num", {"pre": parent, "i": c.number()}
    elif family == "U":
        if c.take(r"\operatorname{param}("):
            key, value = "param", c.ref("N")
            c.need(")")
        elif c.take(r"\operatorname{max}(") or c.take(r"\operatorname{imax}("):
            key = "imax" if "{imax}" in row else "max"
            a = c.ref("U")
            c.need(",")
            value = [a, c.ref("U")]
            c.need(")")
        else:
            key, value = "succ", c.ref("U")
            c.need("+1")
    elif c.take("b_{"):
        key, value = "bvar", c.number()
        c.need("}")
    elif c.take(r"\operatorname{Sort}("):
        key, value = "sort", c.ref("U")
        c.need(")")
    elif c.take(r"\operatorname{const}("):
        n = c.ref("N")
        c.need(",")
        key, value = "const", {"name": n, "us": c.refs("U")}
        c.need(")")
    elif c.take(r"\lambda_{") or c.take(r"\prod_{"):
        key = "lam" if row.startswith(r"\lambda_{", m.end()) else "forallE"
        for left, right, mode in BINDERS:
            if c.take(left):
                break
        else:
            raise FormatError("unknown binder brackets")
        n = c.ref("N")
        c.need(":")
        t = c.ref("E")
        c.need(right + r"}\,")
        value = {"name": n, "type": t, "body": c.ref("E"), "binderInfo": mode}
    elif c.take(r"\operatorname{let}\ "):
        n = c.ref("N")
        c.need(":")
        t = c.ref("E")
        c.need(":=")
        v = c.ref("E")
        c.need(r"\ \operatorname{in}\ ")
        body = c.ref("E")
        c.need(r"\quad\mathrm{nondep}=\mathrm{")
        key, value = "letE", {"name": n, "type": t, "value": v, "body": body,
                              "nondep": c.boolean()}
        c.need("}")
    elif c.take(r"\pi_{"):
        n = c.ref("N")
        c.need(",")
        i = c.number()
        c.need("}(")
        key, value = "proj", {"typeName": n, "idx": i, "struct": c.ref("E")}
        c.need(")")
    elif c.take(r"\operatorname{nat}\) "):
        key, value, tail = "natVal", c.literal(), ""
        if not NAT_LITERAL.fullmatch(value):
            raise FormatError("invalid natural-number literal")
    elif c.take(r"\operatorname{string}\) "):
        key, value, tail = "strVal", c.json_literal(str), ""
    elif c.take(r"\operatorname{annotate}("):
        e = c.ref("E")
        c.need(r")\) ")
        key, value, tail = "mdata", {"expr": e, "data": c.json_literal(dict)}, ""
    else:
        raise FormatError("unknown expression operation")
    c.end(tail)
    return {{"N": "in", "U": "il", "E": "ie"}[family]: num, key: value}


def field(c, key):
    if key in ("all", "ctors", "induct"):
        c.need(r"\(")
        value = c.ref("N") if key == "induct" else c.refs("N")
        c.need(r"\)")
        return value
    if key in ("isUnsafe", "isReflexive", "isRec", "k"):
        return c.boolean()
    if key == "hints":
        v = json.loads(c.literal())
        if v in ("opaque", "abbrev"):
            return v
        if (isinstance(v, dict) and set(v) == {"regular"}
                and type(v["regular"]) is int and v["regular"] >= 0):
            return v
        raise FormatError("invalid reducibility hints")
    if key in ("safety", "kind"):
        v = c.literal()
        choices = {"safe", "unsafe", "partial"} if key == "safety" else {"type", "ctor", "lift", "ind"}
        if v not in choices:
            raise FormatError(f"invalid {key}")
        return v
    return c.number()


def declaration(rows, start):
    m = TITLES.match(rows[start])
    if m is None or m[1] not in DECL_NAMES:
        raise FormatError("unknown declaration heading")
    kind = DECL_NAMES[m[1]]
    c = Cursor(rows[start], m.end())
    c.need(r"\(")
    name = c.ref("N")
    c.need(r"\) ")
    if c.s.startswith(r"\texttt{", c.pos):
        c.json_literal(str)  # optional cached name, including escaped spaces/TeX
        c.need(" ")
    c.need(r"\(\colon ")
    decl = {"name": name, "type": c.ref("E")}
    c.end(r"\)")
    i = start + 1

    def nextrow():
        nonlocal i
        if i >= len(rows):
            raise FormatError(f"incomplete {kind} declaration")
        c = Cursor(rows[i])
        i += 1
        return c

    c = nextrow()
    c.need(r"Universe parameters \(")
    decl["levelParams"] = c.refs("N")
    c.end(r"\).")
    orientation = nextrow().s
    if not (orientation.startswith(r"Type expansion \(") and orientation.endswith(r"\).")):
        raise FormatError("missing optional-expansion display row")
    for key in SCHEMAS[kind]:
        c = nextrow()
        if key == "value":
            c.need(("Proof " if kind == "thm" else "Body ") + r"\(")
            decl[key] = c.ref("E")
            c.end(r"\).")
        else:
            if c.literal() != key:
                raise FormatError(f"expected declaration field {key!r}")
            c.need(" ")
            decl[key] = field(c, key)
            c.end(".")
    if kind == "rec":
        rules = []
        while i < len(rows) and rows[i].startswith("Reduction at constructor "):
            c = nextrow()
            c.need(r"Reduction at constructor \(")
            n = c.ref("N")
            c.need(r"\) with ")
            num = c.number()
            c.need(r" fields has right-hand side \(")
            rules.append({"ctor": n, "nfields": num, "rhs": c.ref("E")})
            c.end(r"\).")
        decl["rules"] = rules
    return kind, decl, i


def read_row(number, rows):
    head = rows[0]
    if head.startswith(r"\("):
        if len(rows) != 1:
            raise FormatError("an indexed equation has extra subrows")
        return indexed(head)
    if head.startswith("Export metadata "):
        if number != 1 or len(rows) != 1:
            raise FormatError("metadata must be a single first record")
        c = Cursor(head, len("Export metadata "))
        meta = c.json_literal(dict)
        c.end()
        if not isinstance(meta.get("format"), dict) or meta["format"].get("version") != "3.1.0":
            raise FormatError("unknown export format")
        return {"meta": meta}
    if head == r"\textbf{Inductive group}":
        out = {"types": [], "ctors": [], "recs": []}
        order = {"type": 0, "ctor": 1, "rec": 2}
        i, previous = 1, -1
        while i < len(rows):
            kind, decl, i = declaration(rows, i)
            if kind not in order or order[kind] < previous:
                raise FormatError("inductive declarations out of order")
            previous = order[kind]
            out[GROUPS[kind]].append(decl)
        return {"inductive": out}
    kind, decl, end = declaration(rows, 0)
    if kind in GROUPS or end != len(rows):
        raise FormatError("orphan inductive declaration or unexpected subrows")
    return {kind: decl}

def iter_records(lines, *, rows_only=False):
    """Yield (global line, reconstructed object) from one volume or a row fragment."""
    entered = rows_only
    ended = False
    number = None
    rows = []

    def finished():
        try:
            if number == 1 and not rows[0].startswith("Export metadata "):
                raise FormatError("first record must contain export metadata")
            return number, read_row(number, rows)
        except (ValueError, TypeError, KeyError, IndexError) as exc:
            raise FormatError(f"record {number}: {exc}") from exc

    for line in lines:
        if isinstance(line, bytes):
            line = line.decode("utf-8")
        line = line.rstrip("\r\n")
        if ended:
            if line.strip():
                raise FormatError("content after end of volume")
            continue
        if not entered:
            if line == r"\begin{document}":
                entered = True
            elif line.startswith(r"\record{"):
                raise FormatError("record before document; use rows_only for a fragment")
            continue
        if line.startswith(r"\record{"):
            m = RECORD.match(line)
            if m is None:
                raise FormatError("invalid record number")
            n = int(m[1])
            if number is not None:
                if n != number + 1:
                    raise FormatError(f"expected record {number + 1}, saw {n}")
                yield finished()
            number = n
            rows = [line[m.end():]]
        elif line.startswith(r"\subrow "):
            if number is None:
                raise FormatError("subrow before a record")
            rows.append(line[8:])
        elif line == r"\end{document}" and not rows_only:
            if number is None:
                raise FormatError("volume has no records")
            yield finished()
            ended = True
        elif number is not None or (rows_only and line):
            raise FormatError(f"unexpected line inside rows near record {number}")
    if rows_only and number is not None:
        yield finished()
    elif not ended:
        raise FormatError("volume is empty or missing its end marker")


@contextmanager
def open_input(path):
    if path == "-":
        yield sys.stdin.buffer
    elif path.endswith(".zst"):
        from compression import zstd
        options = {zstd.DecompressionParameter.window_log_max: 30}
        with zstd.open(path, "rb", options=options) as f:
            yield f
    else:
        with open(path, "rb") as f:
            yield f


def iter_input(path, rows_only=False):
    """Use a plain volume, rows fragment or an ordered published tar[.zst] shard."""
    with open_input(path) as f:
        if path.endswith((".tar", ".tar.zst")):
            members = 0
            with tarfile.open(fileobj=f, mode="r|") as package:
                for item in package:
                    if not item.isfile() or not item.name.endswith(".tex"):
                        raise FormatError(f"unexpected archive member {item.name!r}")
                    with package.extractfile(item) as member:
                        yield from iter_records(member)
                    members += 1
            if members == 0:
                raise FormatError("empty TeX archive")
        else:
            yield from iter_records(f, rows_only=rows_only)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("inputs", nargs="+", help="TeX volumes or tar[.zst] shards in record order; - is stdin")
    parser.add_argument("--rows", action="store_true", help="plain inputs contain only numbered rows and subrows")
    parser.add_argument("--first", type=int, help="require this first global record number")
    parser.add_argument("--last", type=int, help="require this final global record number")
    args = parser.parse_args()
    previous = None
    for path in args.inputs:
        try:
            for number, record in iter_input(path, args.rows):
                expected = args.first if previous is None else previous + 1
                if expected is not None and number != expected:
                    raise FormatError(f"expected record {expected}, saw {number}")
                # ASCII-safe NDJSON preserves Unicode strings, including UTF-16 escape pairs.
                print(json.dumps(record, ensure_ascii=True, separators=(",", ":"), allow_nan=False))
                previous = number
        except (ValueError, OSError, EOFError) as exc:
            parser.exit(1, f"{path}: {exc}\n")
    if previous is None or (args.last is not None and previous != args.last):
        parser.exit(1, f"unexpected final record {previous}\n")


if __name__ == "__main__":
    main()
