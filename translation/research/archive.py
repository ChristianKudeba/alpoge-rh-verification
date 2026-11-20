"""Random reads of the published source, with a size-bounded, compressed working index."""
import argparse
import contextlib
import hashlib
import io
import sqlite3
import sys
import tarfile
import zlib
from functools import lru_cache
from pathlib import Path

BASE = Path(__file__).resolve().parent
PARTS = BASE / "input"
DATABASE = PARTS / "modules.sqlite"
ARCHIVE_SHA256 = "9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc"


class JoinedParts(io.RawIOBase):
    def __init__(self, files):
        self.files = iter(files)
        self.current = None

    def readable(self):
        return True

    def readinto(self, buffer):
        while True:
            if self.current is None:
                path = next(self.files, None)
                if path is None:
                    return 0
                self.current = path.open("rb")
            size = self.current.readinto(buffer)
            if size:
                return size
            self.current.close()
            self.current = None

    def close(self):
        if self.current:
            self.current.close()
        super().close()


def index():
    paths = [PARTS / f"lean.tar.gz.part{i:02d}" for i in range(1, 15)]
    digest = hashlib.sha256()
    for path in paths:
        with path.open("rb") as part:
            while data := part.read(1024 * 1024):
                digest.update(data)
    if digest.hexdigest() != ARCHIVE_SHA256:
        raise ValueError(f"Unexpected source digest {digest.hexdigest()}")
    print("Verified joined archive", digest.hexdigest(), flush=True)
    if DATABASE.exists():
        with contextlib.closing(sqlite3.connect(DATABASE)) as connection:
            if connection.execute("select count(*) from module").fetchone()[0] == 175187:
                print("The complete working index is already present.")
                return
        raise ValueError("An incomplete working index exists")
    temporary = DATABASE.with_suffix(".building")
    if temporary.exists():
        raise ValueError("Found an unfinished index build.")
    with contextlib.closing(sqlite3.connect(temporary)) as db:
        db.executescript("""
        pragma journal_mode=off;
        pragma synchronous=off;
        create table block (id integer primary key, data blob);
        create table module (name text primary key, block integer, at integer, size integer) without rowid;
        """)
        chunk = bytearray()
        rows = []
        block = total = 0
        def flush():
            nonlocal block
            if rows:
                db.execute("insert into block values (?,?)", (block, zlib.compress(chunk,6)))
                db.executemany("insert into module values (?,?,?,?)", rows)
                chunk.clear()
                rows.clear()
                block += 1
        with io.BufferedReader(JoinedParts(paths)) as joined:
            with tarfile.open(fileobj=joined, mode="r|gz", bufsize=256*1024) as tar:
                for item in tar:
                    if not item.isfile() or not item.name.endswith(".lean"):
                        continue
                    path = item.name.split("/")
                    if "src" not in path:
                        continue
                    name = ".".join(path[path.index("src")+1:])[:-5]
                    content = tar.extractfile(item).read()
                    rows.append((name, block, len(chunk), len(content)))
                    chunk.extend(content)
                    total += 1
                    if len(chunk) >= 512 * 1024:
                        flush()
                    if total % 25000 == 0:
                        print(total, "modules indexed", flush=True)
        flush()
        if total != 175187:
            raise ValueError(f"Unexpected Lean module count: {total}")
        db.commit()
    temporary.replace(DATABASE)
    print("Indexed", total, "modules in", DATABASE.stat().st_size, "bytes", flush=True)


class Library:
    def __init__(self):
        self.db = sqlite3.connect(f"{DATABASE.as_uri()}?mode=ro", uri=True)

    @lru_cache(maxsize=20)
    def block(self, idx):
        return zlib.decompress(self.db.execute("select data from block where id=?", (idx,)).fetchone()[0])

    def get(self, name):
        entry = self.db.execute("select block,at,size from module where name=?", (name,)).fetchone()
        if entry is None:
            raise KeyError(name)
        idx, at, size = entry
        return self.block(idx)[at:at+size].decode("utf-8")

    def items(self):
        cursor = self.db.execute("select id,data from block order by id")
        entries = iter(self.db.execute("select block,at,size,name from module order by block,at"))
        item = next(entries, None)
        for idx, compressed in cursor:
            data = zlib.decompress(compressed)
            while item and item[0] == idx:
                _, at, size, name = item
                yield name, data[at:at+size].decode("utf-8")
                item = next(entries, None)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=["index", "find", "get"])
    parser.add_argument("query", nargs="?")
    args = parser.parse_args()
    if args.action == "index":
        index()
    elif args.action == "get":
        sys.stdout.write(Library().get(args.query))
    else:
        for (name,) in Library().db.execute("select name from module where name like ? order by name", (args.query,)):
            print(name)
