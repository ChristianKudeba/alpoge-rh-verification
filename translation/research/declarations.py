"""Locate declarations by their source spelling. Imports are not proof-term dependencies."""
import re
import sqlite3
import sys
from archive import BASE, Library

INDEX = BASE / "input" / "declarations.sqlite"
declaration = re.compile(r"^(?:@\[[^\n]*?\]\s*)*(?:(?:protected|private|noncomputable|partial|unsafe|nonrec|opaque)\s+)*(theorem|lemma|def|abbrev|structure|class|inductive|instance|opaque|axiom)\s+([^\s(:{\[=]+)")

def build():
    if INDEX.exists():
        raise FileExistsError(INDEX)
    tmp = INDEX.with_suffix(".building")
    if tmp.exists():
        raise FileExistsError(tmp)
    db = sqlite3.connect(tmp)
    db.executescript("""
    pragma journal_mode=off;
    create table modules(id integer primary key,name text not null);
    create table symbols(leaf text not null,mod integer not null,line integer not null);
    """)
    for i, (module, source) in enumerate(Library().items()):
        db.execute("insert into modules values(?,?)", (i,module))
        rows=[]
        for n, line in enumerate(source.splitlines(),1):
            if m := declaration.match(line):
                rows.append((m[2].rsplit(".",1)[-1],i,n))
        db.executemany("insert into symbols values(?,?,?)", rows)
    db.execute("create index symbol_lookup on symbols(leaf)")
    db.commit()
    print(db.execute("select count(*) from symbols").fetchone()[0], "named declaration lines")
    db.close()
    tmp.replace(INDEX)

def find(name):
    db=sqlite3.connect(f"{INDEX.as_uri()}?mode=ro",uri=True)
    yield from db.execute("""select m.name,s.line from symbols s join modules m on m.id=s.mod
        where s.leaf=? order by m.name,s.line""",(name,))

if __name__=="__main__":
    if sys.argv[1:]==["build"]:
        build()
    else:
        lib=Library()
        for term in sys.argv[1:]:
            for name,line in find(term):
                print(f"{name}:{line}")
                lines=lib.get(name).splitlines()
                stop=next((i for i in range(line,min(len(lines),line+125)) if declaration.match(lines[i]) or lines[i].startswith("end ")),min(len(lines),line+125))
                print("\n".join(lines[line-1:stop]))
