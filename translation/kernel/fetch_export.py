"""Fetch ranges of the immutable public MIT export into one hosted file."""
from concurrent.futures import ThreadPoolExecutor
import os
import time
from urllib.request import Request, urlopen


def fetch_export(path, source):
    total = source["compressed_bytes"]
    segment = 128 << 20
    with path.open("w+b") as target:
        target.truncate(total)
        fd = target.fileno()

        def retrieve(start):
            stop = min(total, start + segment) - 1
            for attempt in range(5):
                try:
                    request = Request(source["url"], headers={
                        "User-Agent": "alpoge-rh-latex-publication/1",
                        "Range": f"bytes={start}-{stop}", "Accept-Encoding": "identity"})
                    with urlopen(request, timeout=150) as response:
                        expected = f"bytes {start}-{stop}/{total}"
                        if response.status != 206 or response.headers.get("Content-Range") != expected:
                            raise ValueError(f"unexpected MIT response for {start}-{stop}: {response.status}")
                        offset = start
                        while block := response.read(2 << 20):
                            if offset + len(block) > stop + 1:
                                raise ValueError("oversized range")
                            view = memoryview(block)
                            while view:
                                n = os.pwrite(fd, view, offset)
                                if n < 1:
                                    raise OSError("hosted write did not progress")
                                offset += n
                                view = view[n:]
                        if offset != stop + 1:
                            raise EOFError("short MIT range")
                    return stop - start + 1
                except (OSError, EOFError, ValueError) as error:
                    if attempt == 4:
                        raise
                    print(f"Retrying range at {start}: {error}", flush=True)
                    time.sleep(2 ** attempt)
        received = 0
        with ThreadPoolExecutor(max_workers=4) as pool:
            for size in pool.map(retrieve, range(0, total, segment)):
                received += size
                if received == total or received % (1 << 30) == 0:
                    print(f"Fetched {received:,} of {total:,} compressed source bytes.", flush=True)
