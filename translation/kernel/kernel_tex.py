"""Render a lean4export 3.1.0 NDJSON stream as numbered mathematical TeX volumes.

Python 3.15+ supports .zst input using compression.zstd. Plain NDJSON works
on Python 3.10+. The output directory must be new or empty. For an intentionally
truncated .zst frame use --prefix. Use --limit N to typeset a shorter prefix.
An incomplete run can leave finished volumes and an unfinished .part file.
Only a manifest whose status is "complete" records clean end-of-input.
"""
import argparse
from collections import Counter, OrderedDict
import json
import sys
from pathlib import Path


LAYOUT = r"""\documentclass[10pt]{article}
\usepackage[margin=0.83in]{geometry}
\usepackage{amsmath,amssymb}
\setlength{\parindent}{0pt}\setlength{\parskip}{2pt}
\setlength{\emergencystretch}{4em}
\newcommand{\record}[1]{\par\hangindent=4.4em\hangafter=1%
\makebox[4.1em][r]{\scriptsize #1}\hspace{.3em}}
\newcommand{\subrow}{\par\noindent\hspace*{4.4em}}
\begin{document}
"""
LEGEND = r"""The row numbers are lines of the export. \(N_i\), \(U_i\) and \(E_i\)
denote names, universe levels and expressions. Their indices are global across
the volumes. \(N_0\) is the anonymous root and \(U_0=0\).
An expression is a shared syntactic object and is interpreted in the binder
context of its use. The index \(b_0\) denotes the innermost variable.
In a dependent product \(\prod\), lambda \(\lambda\), or let, the body is
interpreted one binder deeper. Binder brackets denote explicit \((\,)\),
implicit \(\{\,\}\), strict implicit \(\{\!\{\,\}\!\}\), or instance
\([\,]\). Bracketed references in a universe instantiation are ordered.
Literal text uses JSON string escapes, including UTF-16 escape pairs.
A name extension by a string differs from an extension by a natural number.
The exact indexed forms are primary. Short expansions below declarations
use fresh variable names and can refer back to indexed subexpressions.
\par\medskip
"""
DECS = {"axiom", "def", "opaque", "thm", "quot", "inductive"}
LEVELS = {"succ", "param", "max", "imax"}
EXPRS = {"bvar", "sort", "const", "app", "lam", "forallE", "letE", "proj",
         "natVal", "strVal", "mdata"}
DELIM = {"default": ("(", ")"), "implicit": (r"\{", r"\}"),
         "strictImplicit": (r"\{\!\{", r"\}\!\}"), "instImplicit": ("[", "]")}
TEX_ESC = dict(zip("\\{}%#$&_~^", [r"\textbackslash{}",r"\{",r"\}",r"\%",
                                      r"\#",r"\$",r"\&",r"\_",r"\textasciitilde{}",
                                      r"\textasciicircum{}"]))


def fmt_json(value):
    return json.dumps(value, ensure_ascii=True, separators=(",", ":"))


def literal(s):
    # Breaks between groups of original characters work even inside a long key.
    return r"\texttt{" + r"\allowbreak{}".join(
        "".join(TEX_ESC.get(c, c) for c in s[i:i+14]) for i in range(0,len(s),14)) + "}"


def require_fields(value, *keys):
    if not isinstance(value, dict) or set(value) != set(keys):
        raise ValueError(f"expected {keys}, found {list(value) if isinstance(value,dict) else value!r}")


def natural(x):
    if type(x) is not int or x < 0:
        raise ValueError(f"expected a natural number, got {x!r}")
    return x


def truth(x):
    if type(x) is not bool:
        raise ValueError(f"expected a Boolean, got {x!r}")
    return "true" if x else "false"


def math(expr):
    return r"\(" + expr + r"\)"


def sequence(values, fn):
    if not isinstance(values,list):
        raise ValueError("expected an array")
    return "[" + (r",\allowbreak{} ".join(fn(x) for x in values)) + "]"


def recent_put(cache, key, value, limit):
    cache[key] = value
    if len(cache) > limit:
        cache.popitem(last=False)


class Notation:
    def __init__(self, cache_size):
        self.next = {"N":1, "U":1, "E":0}
        self.names = OrderedDict()
        self.expressions = OrderedDict()
        self.levels = OrderedDict()
        self.cache_size = cache_size

    def ref(self, kind, idx):
        if natural(idx) >= self.next[kind]:
            raise ValueError(f"forward or unknown reference {kind}{idx}")
        return kind + "_{" + str(idx) + "}"

    def name(self,x): return self.ref("N",x)
    def level(self,x): return self.ref("U",x)
    def expr(self,x): return self.ref("E",x)

    def expansion(self, i, context=(), budget=None):
        # This is a short orientation aid; the indexed equation is always exact.
        if budget is None:
            budget=[13]
        if i not in self.expressions or budget[0] < 1:
            return self.expr(i)
        budget[0] -= 1
        kind, v = self.expressions[i]
        if kind == "bvar":
            return context[-1-v] if v < len(context) else "b_{"+str(v)+"}"
        if kind == "sort":
            return r"\mathrm{Prop}" if v == 0 else r"\mathrm{Sort}("+self.level(v)+")"
        if kind == "app":
            return (r"\bigl("+self.expansion(v["fn"],context,budget)+r"\,"
                    +self.expansion(v["arg"],context,budget)+r"\bigr)")
        if kind in ("lam","forallE"):
            x="x_{"+str(len(context))+"}"
            l,r=DELIM[v["binderInfo"]]
            op=r"\lambda" if kind=="lam" else r"\prod"
            return (op+"_{"+l+x+":"+self.expansion(v["type"],context,budget)+r+"}"+r"\,"
                    +self.expansion(v["body"],context+(x,),budget))
        if kind=="const":
            # Only insert short ASCII identifiers in math; any name has its N_i.
            name=self.names.get(v["name"],"")
            pretty_name=(r"\mathrm{"+name+"}" if name.isascii()
                         and name.replace(".","").isalpha() and len(name)<=27
                         else self.name(v["name"]))
            return pretty_name + ("^{"+sequence(v["us"],self.level)+"}" if v["us"] else "")
        return self.expr(i)

    def indexed(self, kind, index, op, v):
        if type(index) is not int or index != self.next[kind]:
            raise ValueError(f"expected index {self.next[kind]} for {kind}, found {index}")
        lhs=kind+"_{"+str(index)+"}="
        if kind=="N":
            key="str" if op=="str" else "i"
            require_fields(v,"pre",key)
            pre=self.name(v["pre"])
            part=v[key]
            if op=="str":
                if not isinstance(part,str): raise ValueError("expected string name")
                term=math(lhs+pre+r"\mathbin{\cdot_{\rm str}}")+" "+literal(fmt_json(part))
            else:
                natural(part)
                term=math(lhs+pre+r"\mathbin{\cdot_{\rm num}}"+str(part))
            parent="" if v["pre"]==0 else self.names.get(v["pre"])
            if parent is not None and len(parent)+len(str(part)) <= 500:
                recent_put(self.names,index,(parent+"." if parent else "")+str(part),self.cache_size)
        elif kind=="U":
            if op=="succ": rhs=self.level(v)+"+1"
            elif op=="param": rhs=r"\operatorname{param}("+self.name(v)+")"
            else:
                if not isinstance(v,list) or len(v)!=2: raise ValueError("universe pair expected")
                rhs=r"\operatorname{"+op+"}("+self.level(v[0])+","+self.level(v[1])+")"
            term=math(lhs+rhs)
        else:
            if op=="bvar": rhs="b_{"+str(natural(v))+"}"
            elif op=="sort": rhs=r"\operatorname{Sort}("+self.level(v)+")"
            elif op=="const":
                require_fields(v,"name","us")
                rhs=r"\operatorname{const}("+self.name(v["name"])+","+sequence(v["us"],self.level)+")"
            elif op=="app":
                require_fields(v,"fn","arg");rhs=self.expr(v["fn"])+r"\,("+self.expr(v["arg"])+")"
            elif op in ("lam","forallE"):
                require_fields(v,"name","type","body","binderInfo")
                if v["binderInfo"] not in DELIM: raise ValueError("unknown binder mode")
                l,r=DELIM[v["binderInfo"]]
                rhs=((r"\lambda" if op=="lam" else r"\prod")+"_{"+l+self.name(v["name"])
                     +":"+self.expr(v["type"])+r+"}"+r"\,"+self.expr(v["body"]))
            elif op=="letE":
                require_fields(v,"name","type","value","body","nondep")
                rhs=(r"\operatorname{let}\ "+self.name(v["name"])+":"+self.expr(v["type"])
                     +":="+self.expr(v["value"])+r"\ \operatorname{in}\ "+self.expr(v["body"])
                     +r"\quad\mathrm{nondep}="+r"\mathrm{"+truth(v["nondep"])+"}")
            elif op=="proj":
                require_fields(v,"typeName","idx","struct")
                rhs=(r"\pi_{"+self.name(v["typeName"])+","+str(natural(v["idx"]))+"}("
                     +self.expr(v["struct"])+")")
            elif op=="natVal":
                if not isinstance(v,str) or not v.isascii() or not v.isdigit():
                    raise ValueError("invalid numeral literal")
                rhs=None;term=math(lhs+r"\operatorname{nat}")+" "+literal(v)
            elif op=="strVal":
                if not isinstance(v,str): raise ValueError("invalid string literal")
                rhs=None;term=math(lhs+r"\operatorname{string}")+" "+literal(fmt_json(v))
            elif op=="mdata":
                require_fields(v,"data","expr")
                if not isinstance(v["data"],dict): raise ValueError("invalid expression metadata")
                rhs=None;term=math(lhs+r"\operatorname{annotate}("+self.expr(v["expr"])+")")+" "+literal(fmt_json(v["data"]))
            else: raise ValueError(f"unknown expression kind {op}")
            if rhs is not None: term=math(lhs+rhs)
            recent_put(self.expressions,index,(op,v),self.cache_size)
        self.next[kind]+=1
        return term

    def declaration(self,op,v):
        fields={
            "axiom":"isUnsafe", "def":"value hints safety all", "opaque":"value isUnsafe all",
            "thm":"value all", "quot":"kind",
            "type":"numParams numIndices all ctors numNested isRec isUnsafe isReflexive",
            "ctor":"induct cidx numParams numFields isUnsafe",
            "rec":"all numParams numIndices numMotives numMinors rules k isUnsafe",
        }
        require_fields(v,"name","type","levelParams",*fields[op].split())
        title={"type":"Inductive type","ctor":"Constructor","rec":"Recursor","thm":"Theorem",
               "def":"Definition","quot":"Quotient primitive"}.get(op,op.capitalize())
        n,t=v["name"],v["type"]
        header=(r"\textbf{"+title+"} "+math(self.name(n)))
        if n in self.names: header+=" "+literal(fmt_json(self.names[n]))
        rows=[header+" "+math(r"\colon "+self.expr(t)),
              "Universe parameters "+math(sequence(v["levelParams"],self.name))+"."]
        rows.append("Type expansion "+math(self.expansion(t))+".")
        if "value" in v:
            rows.append(("Proof" if op=="thm" else "Body")+" "+math(self.expr(v["value"]))+".")
        for key in fields[op].split():
            if key in ("value","rules"):continue
            value=v[key]
            if key in ("all","ctors"): txt=math(sequence(value,self.name))
            elif key=="induct": txt=math(self.name(value))
            elif key in ("isRec","isUnsafe","isReflexive","k"): txt=truth(value)
            elif key=="hints":
                if isinstance(value,dict): require_fields(value,"regular"); natural(value["regular"])
                elif value not in ("opaque","abbrev"): raise ValueError("unknown reducibility hint")
                txt=literal(fmt_json(value))
            elif key=="kind":
                if value not in ("type","ctor","lift","ind"): raise ValueError("unknown quotient kind")
                txt=literal(value)
            elif key=="safety":
                if value not in ("safe","unsafe","partial"): raise ValueError("unknown definition safety")
                txt=literal(value)
            else: txt=str(natural(value))
            rows.append(literal(key)+" "+txt+".")
        for rule in v.get("rules",[]):
            require_fields(rule,"ctor","nfields","rhs")
            rows.append("Reduction at constructor "+math(self.name(rule["ctor"]))+" with "
                        +str(natural(rule["nfields"]))+" fields has right-hand side "
                        +math(self.expr(rule["rhs"]))+".")
        return rows

    def render(self,r,line):
        if not isinstance(r,dict): raise ValueError("record must be an object")
        if line==1:
            require_fields(r,"meta")
            if r["meta"].get("format",{}).get("version")!="3.1.0":
                raise ValueError("this renderer requires export format 3.1.0")
            return "meta",["Export metadata "+literal(fmt_json(r["meta"]))]
        for field,kind,ops in [("in","N",{"str","num"}),("il","U",LEVELS),("ie","E",EXPRS)]:
            if field in r:
                keys=set(r)-{field}
                if len(keys)!=1 or not keys<=ops:raise ValueError(f"unknown {field} record {keys}")
                op=next(iter(keys))
                return op,[self.indexed(kind,r[field],op,r[op])]
        if len(r)!=1 or not set(r)<=DECS: raise ValueError(f"unknown declaration record {list(r)}")
        op=next(iter(r));v=r[op]
        if op!="inductive": return op,self.declaration(op,v)
        require_fields(v,"types","ctors","recs")
        rows=[r"\textbf{Inductive group}"]
        for key,tag in [("types","type"),("ctors","ctor"),("recs","rec")]:
            if not isinstance(v[key],list): raise ValueError(f"{key} must be an array")
            for item in v[key]:
                rows.extend(self.declaration(tag,item))
        return op,rows


def input_lines(path, allow_prefix):
    if path.suffix.lower()!=".zst":
        with path.open("rb") as f:
            yield from f
        return
    from compression import zstd
    options={zstd.DecompressionParameter.window_log_max:30}
    pending=b""
    dec=None
    with path.open("rb") as f:
        while chunk:=f.read(131072):
            while chunk or (dec is not None and not dec.needs_input and not dec.eof):
                if dec is None or dec.eof: dec=zstd.ZstdDecompressor(options=options)
                data=dec.decompress(chunk,1048576)
                chunk=dec.unused_data if dec.eof else b""
                parts=(pending+data).split(b"\n")
                pending=parts.pop()
                yield from parts
    if dec is None: raise ValueError("empty compressed input")
    if not dec.eof:
        if not allow_prefix: raise EOFError("truncated compressed input; explicitly select --prefix for an excerpt")
        return
    if pending: yield pending


def export(path,out,per_volume,limit,prefix,cache_size):
    if per_volume<1 or cache_size<1 or (limit is not None and limit<1):
        raise ValueError("numeric arguments must be positive")
    out.mkdir(exist_ok=True,parents=True)
    if any(out.iterdir()): raise ValueError("output directory must be empty")
    label="Selected prefix" if prefix or limit is not None else "Kernel export"
    book=Notation(cache_size)
    counts=Counter()
    volume=rows=0
    file=None
    tmp=None
    manifest=out/"manifest.json"

    def status(state):
        manifest.write_text(json.dumps({"status":state,"source":str(path),"records":rows,
                "volumes_opened":volume,"records_per_volume":per_volume,
                "record_kinds":dict(counts)},indent=2)+"\n",encoding="utf-8")
    def finish():
        file.write("\\end{document}\n");file.close()
        tmp.rename(tmp.with_suffix(""))

    status("running")
    try:
        for line,raw in enumerate(input_lines(path,prefix),1):
            if file is None:
                volume+=1; tmp=out/f"kernel-{volume:05}.tex.part"
                file=tmp.open("x",encoding="utf-8",newline="\n",buffering=1048576)
                file.write(LAYOUT+"\\section*{"+label+" in dependent type theory}\n"
                           +"Volume "+str(volume)+", beginning at record "+str(line)+".\n\n"
                           +LEGEND)
            try: op,items=book.render(json.loads(raw),line)
            except (TypeError,ValueError,KeyError,IndexError) as e:
                raise ValueError(f"record {line}: {e}") from e
            file.write("\\record{"+str(line)+"}"+items[0]+"\n")
            for item in items[1:]:file.write("\\subrow "+item+"\n")
            counts[op]+=1;rows=line
            if line%per_volume==0:
                finish();file=None;status("running")
            if line==limit:break
        if rows==0:raise ValueError("missing metadata")
        if file is not None:finish();file=None
        status("prefix" if prefix or limit is not None else "complete")
    except BaseException:
        if file is not None and not file.closed:file.close()
        status("failed")
        raise


if __name__=="__main__":
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("input",type=Path);p.add_argument("output",type=Path)
    p.add_argument("--records-per-volume",type=int,default=5000)
    p.add_argument("--cache-size",type=int,default=16384,help="bounded cache for optional readable names and expansions")
    p.add_argument("--limit",type=int,help="produce a labelled initial excerpt of at most N records")
    p.add_argument("--prefix",action="store_true",help="accept intentionally incomplete compressed frame and drop its last incomplete line")
    a=p.parse_args()
    export(a.input,a.output,a.records_per_volume,a.limit,a.prefix,a.cache_size)
