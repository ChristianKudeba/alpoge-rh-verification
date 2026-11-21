# Isotypic representations: algebraic fixed-vector reduction

This batch replaces repeated constructions with the module-theoretic fact that
copies of a simple module both generate and separate vectors in their isotypic
sum. The new Mathlib-only module is `Lemmata.IsotypicGeneration`.

The proof first identifies the generated module with its isotypic component,
then uses Mathlib's direct-sum decomposition (`linearEquiv_finsupp`). A nonzero
vector has a nonzero coordinate, giving an intertwining projection to the simple
type. Dually, every nonzero submodule contains a copy of that type.

This has two substantive consequences for the existing arguments:

* `HasFixedVector.hasFixed` now sends a nonzero fixed vector through an
  intertwining projection. Its old finite-quotient averaging argument disappears.
  The algebraic result works for every subgroup, without smoothness or compactness.
* `fixed_ne_bot_of_mem_iSup_range` now projects from the isotypic sum containing
  the given vector. Its induction over finite sums disappears. The proof does not
  require the index type to be finite.

The original public statements retain their original hypotheses. All four
existing public theorem headers are byte-for-byte identical to the saved before
versions. `SubgroupFixed` and `IrreducibleProjectionExists` reuse the same shared
module rather than reproving module structure and separation.

## Exact accounting

| Existing source | Before | After |
| --- | ---: | ---: |
| `HasFixedVector.lean` | 113 | 23 |
| `SubgroupFixed.lean` | 111 | 88 |
| `IrreducibleProjectionExists.lean` | 76 | 67 |
| `FixedVectorsNeBotOfMemSumIntertwiningRanges.lean` | 84 | 28 |
| New `Lemmata/IsotypicGeneration.lean` | 0 | 70 |
| **Total physical source lines** | **384** | **276** |

The shared helper's full cost is included: **108 lines removed (28.125%)** in
this batch. Counting only nonempty theorem-proof body lines gives **296 → 169**,
a reduction of **127 lines**. The unchanged theorem headers make this independent
of expanded-statement shortening. These percentages concern this batch only.
The root agent's additional `GlobalTheory.IsoSep.main` consumer is not counted.

## Validation

All five source modules compiled natively with Lean 4.33.1 and the pinned Mathlib
revision `0df444a360eaa60ab8c11dca51a86af692955474`. The source SHA256,
command, elapsed time, exit code, and output are saved in the per-module JSON and
log files. `Axioms.lean` checks all four shared theorems and all four original
public declarations. Every axiom report contains exactly `propext`,
`Classical.choice`, and `Quot.sound`; see `axioms.log`.

These checks use selected pinned archive dependencies and are local module
checks, not a full-project Comparator verdict. `check.py` uses an isolated output
mirror. An initial output-path symlink mistake for the Iwasawa module was
corrected; the shared cache copy was restored from the SHA256-verified original
archive, and the final module was rechecked in the isolated output. The exact
restoration hashes are in `cache-restoration.json`.
