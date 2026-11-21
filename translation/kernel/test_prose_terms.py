"""Exercise the complete shard comparison on an exact excerpt and reject a changed proof."""
from compression import zstd
import gzip
import hashlib
import io
import json
from pathlib import Path
import tarfile
import tempfile
import unittest

from kernel_tex import LAYOUT, LEGEND
from prose_records import MACRO, NOTE, annotated_volume, meaning
from read_terms import iter_records
from test_read_terms import render_rows, synthetic
from verify_terms import verify_records


def fixture(folder, tex, rows):
    raw = b"".join(json.dumps(row, ensure_ascii=True).encode("ascii") + b"\n" for _, row in rows)
    source, archive = folder / "source.zst", folder / "terms.tar.zst"
    source.write_bytes(zstd.compress(raw))
    name = "shard-0000/volume-00001.tex"
    with zstd.open(archive, "wb") as compressed, tarfile.open(fileobj=compressed, mode="w|") as tar:
        m = tarfile.TarInfo(name)
        m.size = len(tex)
        tar.addfile(m, io.BytesIO(tex))
    part = dict(first_line=1, raw_sha256=hashlib.sha256(raw).hexdigest(), raw_bytes=len(raw))
    volume = dict(name=name, bytes=len(tex), first_line=1, last_line=len(rows), sha256=hashlib.sha256(tex).hexdigest())
    return source, archive, part, dict(volumes=[volume], records=len(rows))


class ProseTests(unittest.TestCase):
    def test_every_constructor_has_reading_and_exact_equation(self):
        records = synthetic()
        original = (LAYOUT + LEGEND + render_rows(records) + "\\end{document}\n").encode()
        notes = [(i, meaning(r)) for i, r in enumerate(records, 1)]
        annotated = annotated_volume(original, notes)
        self.assertIn(b"The proof ", annotated)
        self.assertIn(b"The computation rule on ", annotated)
        restored = b"".join(x for x in annotated.splitlines(keepends=True)
                            if x != MACRO and not x.startswith(NOTE))
        self.assertEqual(restored, original)
        with self.assertRaises(ValueError):
            annotated_volume(original, notes[:-1])

    def test_checked_sample_and_corrupt_witness(self):
        tex = (Path(__file__).with_name("sample") / "kernel-00001.tex").read_bytes()
        rows = list(iter_records(io.BytesIO(tex)))
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            args = fixture(root, tex, rows)
            result = verify_records(*args, root / "names.gz", root / "prose.tar.zst")
            self.assertEqual(result["records"], 105)
            self.assertEqual(result["canonical_sha256"], "29e9053083190b112d38072481548db0b4e5cd0b9caa1061e7f44c6889e4de31")
            self.assertIsNotNone(result["prose_sha256"])
            self.assertIn(b"9\t60\tctor\n", gzip.decompress((root / "names.gz").read_bytes()))
            index = next(i for i, (_, row) in enumerate(rows) if "app" in row)
            line, row = rows[index]
            altered = {**row, "app": {**row["app"], "fn": row["app"]["fn"] + 1}}
            rows[index] = line, altered
            args = fixture(root, tex, rows)
            with self.assertRaisesRegex(ValueError, f"record {line} .* differs"):
                verify_records(*args, root / "bad.gz", root / "bad.tar.zst")


if __name__ == "__main__":
    unittest.main()
