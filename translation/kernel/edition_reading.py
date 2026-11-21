"""Make the publication's reading guide from the checked final inventory."""
from release_store import REPO, TAG

def reading_guide(edition, totals, prose_volumes, print_bytes, axioms):
    base = f"https://github.com/{REPO}"
    rows = "\n".join(
        f"| {t['name']} | {t['line']:,} | E{t['type_index']} | E{t['value_index']} |"
        for t in edition["targets"])
    names = ", ".join(f"`{a['name']}`" for a in axioms)
    return f"""# The full mathematical proof-term translation

The edition covers all **{totals['records']:,} numbered records** of the MIT-published solution export.
The explanatory edition contains **{prose_volumes:,} LaTeX volumes**, with {print_bytes:,} bytes of LaTeX source.
Its declaration index contains **{totals['declarations']:,} declarations**.

[Read the five endpoint records and foundational axioms](rh-theorem-records.pdf).
[Download their LaTeX](rh-theorem-records.tex).
[Open the annotated edition]({base}/releases/tag/rh-literal-audit-v1).
[Open the literal equations]({base}/releases/tag/{TAG}).

## Files to use

Start with [reverse-audit.json](reverse-audit.json). Each entry under `shards` identifies a
`prose-NNNN.tar.zst` archive and its SHA-256 digest. The entry's audit report lists the names,
record intervals and SHA-256 digests of every LaTeX volume in that archive. Each volume is
a complete LaTeX document. Its mathematical records retain the global expression and name
references, and its accompanying sentences describe the corresponding proof operations.

The [core manifest]({base}/releases/download/{TAG}/edition-index.json) indexes the
unannotated mathematical equations. The checked records are identical after the explanatory
lines and their single presentation macro are removed. The independent reverse converter
reconstructed every field of those equations and compared it with the published source.

## The theorem entry points

| Endpoint | Global record | Statement | Proof |
|---|---:|---|---|
{rows}

Each proof expression refers to earlier expression equations or declared constants.
Their shared numbering continues across volume boundaries. To follow a reference use
[the record finder]({base}/blob/main/translation/kernel/locate.py). It reads the public
LaTeX archives in memory, validates their recorded hashes, and supports the five endpoint
names, expression indices, name indices and global record numbers. A query of the form
`declaration:N9` follows a constant name to its declaration using the supplemental index.

## Source and foundations

The uncompressed source contains {edition['source']['bytes']:,} bytes. Its SHA-256 is

`{edition['source']['sha256']}`

All exported axioms were identified directly in the decoded mathematical records.
They are {names}. The endpoint PDF includes their declarations. The quotient primitives
and inductive constructor and recursor rules are included in the numbered volumes.

[The independent kernel-verification report](https://math.mit.edu/~drew/grh/) describes the
checks of the original proof. The comparison published here establishes fidelity of the
LaTeX translation to that export.

## The mathematical exposition

The [working manuscript]({base}/tree/main/translation) gives the argument in conventional
mathematical prose and identifies its outstanding proof obligations in its final section.
The formal volumes give the complete translation in dependent type theory. Compaction and
further conversion to conventional mathematical prose can use this full edition as a
fixed reference.

[Grammar and reading conventions]({base}/blob/main/translation/kernel/reading.md).
"""
