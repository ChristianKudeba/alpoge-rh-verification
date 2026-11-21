"""Attach a reading in mathematical prose to every numbered kernel record."""
import hashlib
import io
import re
import tarfile


# Each note is exactly one line and has a reserved prefix. Removing the notes
# and their one preamble definition must reproduce the checked TeX byte for byte.
MACRO = (b"\\newcommand{\\recordreading}[1]{\\par\\noindent\\hspace*{1em}"
         b"\\begin{minipage}[t]{.93\\linewidth}\\small #1\\end{minipage}\\par}\n")
NOTE = b"\\recordreading{"
BEGIN = b"\\begin{document}\n"
END = b"\\end{document}"
MARK = re.compile(rb"(?m)^\\record\{(\d+)\}")
BINDERS = {"default": "explicit", "implicit": "implicit", "strictImplicit": "strict implicit",
           "instImplicit": "instance-implicit"}
QUOTIENT = {"type": "quotient type former", "ctor": "quotient constructor",
            "lift": "operation induced by a function respecting the relation",
            "ind": "induction rule for the quotient"}


def ref(family, i):
    return rf"\({family}_{{{i}}}\)"


def names(values):
    return ", ".join(ref("N", x) for x in values)


def meaning(row):
    if "ie" in row:
        i = row["ie"]
        e = ref("E", i)
        if "app" in row:
            a = row["app"]
            return f"Apply {ref('E', a['fn'])} to {ref('E', a['arg'])}. The result is {e}."
        if "bvar" in row:
            depth = row["bvar"]
            if depth == 0:
                return f"In the current context, {e} denotes the variable bound most recently."
            return f"For {e}, pass over the {depth} innermost binders and take the next bound variable."
        if "const" in row:
            v = row["const"]
            levels = ", ".join(ref("U", u) for u in v["us"])
            inst = (" with universe arguments " + levels + " in that order") if levels else ""
            return f"Use the constant {ref('N', v['name'])}{inst}. This occurrence is {e}."
        if "lam" in row or "forallE" in row:
            key = "lam" if "lam" in row else "forallE"
            v = row[key]
            name, domain, body = ref("N", v["name"]), ref("E", v["type"]), ref("E", v["body"])
            arg = f"an {BINDERS[v['binderInfo']]} argument" if v["binderInfo"] != "strictImplicit" else "a strict implicit argument"
            if key == "lam":
                return (f"Take {arg} {name} of type {domain}. The function {e} returns {body} "
                        "in the context extended by that argument.")
            return (f"Form the dependent function type {e} with {arg} {name} of type {domain}. "
                    f"The result type under this binder is {body}.")
        if "sort" in row:
            u = row["sort"]
            return f"The expression {e} is the sort of propositions." if u == 0 else f"The expression {e} is the sort at universe level {ref('U', u)}."
        if "letE" in row:
            v = row["letE"]
            return (f"Bind {ref('N', v['name'])} of type {ref('E', v['type'])} to "
                    f"{ref('E', v['value'])}. Read {ref('E', v['body'])} in the extended context to obtain {e}.")
        if "proj" in row:
            v = row["proj"]
            return (f"From {ref('E', v['struct'])} of the structure named {ref('N', v['typeName'])}, "
                    f"select field {v['idx']} with numbering beginning at zero. Its value is {e}.")
        if "natVal" in row:
            return f"The displayed nonnegative integer gives the value of {e}."
        if "strVal" in row:
            return f"The displayed string, with the indicated escapes interpreted, gives the value of {e}."
        if "mdata" in row:
            return f"The underlying expression of {e} is {ref('E', row['mdata']['expr'])}. The displayed metadata accompanies it."
    if "in" in row:
        n = ref("N", row["in"])
        if "str" in row:
            return f"Append the displayed string as one component of {ref('N', row['str']['pre'])} to obtain the name {n}."
        v = row["num"]
        return f"Append the numerical component {v['i']} to {ref('N', v['pre'])} to obtain the name {n}."
    if "il" in row:
        u = ref("U", row["il"])
        if "succ" in row:
            return f"The level {u} is one above {ref('U', row['succ'])}."
        if "param" in row:
            return f"The level {u} is the universe parameter named {ref('N', row['param'])}."
        if "max" in row:
            a, b = (ref("U", k) for k in row["max"])
            return f"The level {u} is the larger of {a} and {b}."
        a, b = (ref("U", k) for k in row["imax"])
        return f"The level {u} is zero when {b} is zero. Otherwise take the larger of {a} and {b}."
    if "meta" in row:
        return "This opening record identifies the proof export, its producer, and the format of the records that follow."
    if "inductive" in row:
        block = row["inductive"]
        sentences = ["Introduce together the displayed inductive declarations."]
        for d in block["types"]:
            sentences.append(f"The inductive family {ref('N', d['name'])} has type {ref('E', d['type'])}.")
        for d in block["ctors"]:
            sentences.append(f"Use {ref('N', d['name'])} as a constructor of {ref('N', d['induct'])} with type {ref('E', d['type'])}.")
        for d in block["recs"]:
            sentences.append(f"Eliminate by {ref('N', d['name'])} of type {ref('E', d['type'])}.")
            for rule in d["rules"]:
                sentences.append(f"The computation rule on {ref('N', rule['ctor'])} has right-hand side {ref('E', rule['rhs'])}.")
        return "\n".join(sentences)
    op, v = next(iter(row.items()))
    n, t = ref("N", v["name"]), ref("E", v["type"])
    if op == "thm":
        return f"The proof {ref('E', v['value'])} establishes {t}. The resulting theorem is named {n}."
    if op in {"def", "opaque"}:
        adjective = "opaque " if op == "opaque" else ""
        return f"Introduce the {adjective}constant {n} of type {t} with defining term {ref('E', v['value'])}."
    if op == "axiom":
        return f"Take {n} of type {t} as an axiom of this environment."
    if op == "quot":
        return f"Introduce {n} of type {t} as the primitive {QUOTIENT[v['kind']]}."
    raise ValueError("no reading rule for exported record")


def annotated_volume(tex, readings):
    """Insert the readings after their records, preserving every original byte."""
    if tex.count(BEGIN) != 1 or NOTE in tex or MACRO in tex:
        raise ValueError("unexpected source volume layout")
    pos = tex.index(BEGIN)
    out = io.BytesIO()
    out.write(tex[:pos])
    out.write(MACRO)
    starts = iter(MARK.finditer(tex))
    current = next(starts, None)
    for number, explanation in readings:
        if current is None or int(current[1]) != number:
            raise ValueError("reading does not match the numbered record")
        following = next(starts, None)
        stop = following.start() if following is not None else tex.rindex(END)
        out.write(tex[pos:stop])
        for paragraph in explanation.split("\n"):
            out.write(NOTE + paragraph.encode("ascii") + b"}\n")
        pos = stop
        current = following
    if current is not None or pos <= tex.index(BEGIN):
        raise ValueError("volume readings are incomplete")
    out.write(tex[pos:])
    payload = out.getvalue()
    restored = b"".join(line for line in payload.splitlines(keepends=True)
                        if line != MACRO and not line.startswith(NOTE))
    if restored != tex:
        raise ValueError("annotations altered the checked mathematical record")
    return payload


def add_volume(archive, vol, payload):
    member = tarfile.TarInfo(vol["name"])
    member.size = len(payload)
    member.mode = 0o644
    member.mtime = 0
    archive.addfile(member, io.BytesIO(payload))
    return dict(name=member.name, bytes=member.size, sha256=hashlib.sha256(payload).hexdigest(),
                first_line=vol["first_line"], last_line=vol["last_line"])
