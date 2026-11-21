# Checked mathematical compaction, 21 November 2026

[Research note](research-notes.pdf) · [LaTeX source](research-notes.tex) ·
[Whole-source audit](source-audit.json)

This pass changes 13 existing Lean modules and adds one reusable module. It
removes **8,863 physical lines** from `src`, with the public theorem types,
independent Challenge/Solution, five final statements, permitted axioms and
dependency pins preserved. The baseline is
`6fc3615fcae0da5c47c04aa1ff1441b4f0e05948`; its Lean source is identical to
the earlier research base `6186b8d5c`.

The source counts distinguish mathematical arguments from expanded-statement
cleanup:

| Mathematical family | Net physical lines removed |
| --- | ---: |
| Isotypic separation and embedding, including the complete new helper | 231 |
| Shared projective-addition polynomial certificate | 440 |
| Subspace extension, projective splitting and duality | 165 |
| Torsion finiteness and subgroup identities | 31 |
| **Subtotal** | **867** |

There is also a six-line proof-body saving in the product stabilizer helper.
Its surrounding module contracts from 8,029 to 33 lines, principally through
the concise interface proposed by mmmbeer in PR44. We classify the other
7,990 lines as interface/inference cleanup, rather than mathematical progress.
The original already contained the general product-subgroup argument.

The isotypic argument uses decomposition into copies of one simple module.
Coordinate projections detect nonzero vectors; intertwining maps transport
subgroup-fixed vectors. This replaces averaging, finite-sum induction and
separate cyclic-submodule/complement constructions. The new helper has weaker
requirements than the old cores. Public compatibility premises are retained.

The polynomial argument changes expanded certificates by a zero syzygy before
factoring them. Three projective-addition minors then share a single alternating
cubic residual. Lean verifies the identities over arbitrary commutative rings.
The 440-line saving includes the new cubic definition.

Detailed mechanisms and receipts:

- [Shared fixed-vector family](fixed-vectors/README.md),
  [metrics](fixed-vectors/metrics.json), and [axiom reports](fixed-vectors/axioms.log).
- [IsoSep consumer](isotypic/verification.md), including direct original-type
  comparison and empty-kernel replay.
- [Linear algebra](covariant/README.md) and [per-proof counts](covariant/manifest.json).
- [Torsion and subgroups](algebra/README.md).
- [Polynomial derivation](community/diagz-research-note.tex) and
  [final verification](community/diagz-final-verification.json).
- [Product stabilizer verification](verification/FixPiIff-verification.md) and
  [actual-source summary](verification/fixpi-actual-validation-summary.json).
- [Independent mathematical review](algebra/independent-review.json).

All final edited modules passed focused native Lean checks with Lean 4.33.1
and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. Audited endpoints use
only `propext`, `Classical.choice`, and `Quot.sound`. Public statements are
either byte-identical or directly compared against the original compiled
expression. The two-copy type comparisons for the linear-algebra family
also passed. Empty-kernel replay checked 38,790 declarations for `mem_UC`
and 12,291 for `GlobalTheory.IsoSep.main`.

The complete static source audit found no missing imports, no import cycles,
and no source modules outside the Main closure. It confirms 165,125 project
modules and 16,615,437 physical lines after this pass. These counts exclude
Mathlib, verification fixtures and the research note.

These focused results do not establish a complete Main or Comparator verdict.
Exploratory failing trials remain in the evidence directories; the named final
summaries bind successful checks to the final source hashes. Imported archive
caches are pinned dependencies, not a claim that every cached source was rebuilt.
The fixed-vector output mirror's cache-restoration incident and its resolution
are recorded in `fixed-vectors/cache-restoration.json`.

The source follows Alpöge's development and Mathlib. The compact interface is
credited to [mmmbeer's PR44](https://github.com/leanprover-community/riemann-hypothesis/pull/44)
at `c9b3e57f0fe987012d32c2523635387bfe56d5a5`. Community counts and our savings
are not additive; [the review](community/community-review.json) records overlaps,
including the subsequently merged pruning PR45.

To reproduce the static audit from the repository root:

```sh
python verification/aggressive/audit_snapshot.py \
  --base 6fc3615fcae0da5c47c04aa1ff1441b4f0e05948 \
  --out /tmp/nov21-compaction-audit.json
```

The per-family scripts record exact compiler commands and pinned dependency
paths. Native checks and replay require compatible builds of those dependencies.
Compiled objects and generated type dumps are intentionally excluded from git.
