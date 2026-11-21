# Linear-algebra proof reductions, 21 November 2026

Four existing source modules shrink from **675 to 510 physical lines**, saving **165 lines and 7,585 bytes**. Changed proof bodies, including a deleted unused private helper, shrink from **281 to 119 nonblank lines**. Public theorem statements are byte-identical; no savings come from abbreviating statements or omitting explicit arguments there. No source modules or replacement helper declarations were added. Imports, typeclass assumptions, and toolchain pins are unchanged.

The machine-readable [manifest](manifest.json) records the source paths, exact original and final SHA-256 hashes, per-declaration counts, and verification scope. These figures compare against commit `6186b8d5c272c08c90f6f5cce1a25d22232ed78d`; they do not include earlier compaction passes or other agents’ work.

## Mathematical changes

**Projectivity replaces coordinate lifting.** In `ExistsBasisOfSurjective.lean`, a surjection onto a finite free module has a linear section because free modules are projective. Mathlib’s `LinearMap.exists_rightInverse_of_surjective` supplies that section directly. The split map from target × kernel to the original free module is then a coproduct map. A short injectivity/surjectivity argument and `LinearEquiv.ofBijective` construct the decomposition, removing an explicit inverse pair and auxiliary retraction calculations. The original product-basis and reindexing argument remains. Removing unreachable fallback branches accounts for some of this file’s proof-body reduction; the mathematical change is the projectivity and coproduct route.

**Subspace extension replaces complementary-space bookkeeping.** In `ExistsLinearEquivMapEqOfFinrankEq.lean`, equal finite dimensions first give an isomorphism between the two subspaces. `Submodule.exists_linearEquiv_restrict_eq` extends it to an automorphism of the ambient vector space. This removes separate complement choices, subtraction of dimensions, an isomorphism between the complements, and product gluing. The same abstraction shortens `trans_tuple` in both `NcSGLP.lean` and `NcXGLP.lean`: construct the isomorphism sending one independent family’s span basis to the other, extend it, and evaluate on those basis vectors.

**Duality replaces the annihilator argument.** The `pi_surj` theorem says that evaluation by a finite linearly independent family of linear functionals is surjective. Its dual map is the linear map sending the coordinate dual basis to that family. Independence makes this map injective by `Module.Basis.injective_constr_of_linearIndependent`; `LinearMap.dualMap_injective_iff` converts this to the desired surjectivity. This removes the former nonzero-annihilator contradiction and makes a private coordinate-sum lemma in `NcSGLP.lean` unused, so that lemma is deleted. The arbitrary domain remains unrestricted: the replacement adds no finite-dimensional assumption on it.

**Dual embeddings replace kernel-dimension comparisons.** For `surj_equiv`, dualize the two surjections from the same finite-dimensional source. Their duals are embeddings with isomorphic ranges. Extend the resulting range isomorphism to an automorphism of the source dual, then transpose that automorphism back through `Module.evalEquiv`. Evaluating against arbitrary functionals proves the required intertwining equation. The target’s finite-dimensional instance is derived from the existing surjection using `Module.Finite.of_surjective`; it is not a new theorem premise. This removes the previous kernel-rank and projection construction in both parallel modules.

## Exact counts

| Existing module | Physical lines before | After | Saved |
| --- | ---: | ---: | ---: |
| `ExistsBasisOfSurjective.lean` | 100 | 67 | 33 |
| `ExistsLinearEquivMapEqOfFinrankEq.lean` | 65 | 52 | 13 |
| `NcSGLP.lean` | 315 | 237 | 78 |
| `NcXGLP.lean` | 195 | 154 | 41 |
| **Total** | **675** | **510** | **165** |

Proof-body counts below exclude blank lines and declaration headers. The deleted helper contributes seven proof lines and three other physical lines to the overall total.

| Module / declaration | Proof lines before | After |
| --- | ---: | ---: |
| Basis: private `exists_linear_rightInverse_of_surjective` | 8 | 2 |
| Basis: `exists_basis_of_surjective` | 74 | 47 |
| Subspace transport: `exists_linearEquiv_map_eq_of_finrank_eq` | 25 | 12 |
| NcS: `surj_equiv` | 37 | 14 |
| NcS: `pi_surj` | 19 | 9 |
| NcS: `trans_tuple` | 41 | 6 |
| NcS: unused private `dual_apply_eq_sum_mul_single` | 7 | 0 |
| NcX: `surj_equiv` | 29 | 14 |
| NcX: `pi_surj` | 17 | 9 |
| NcX: `trans_tuple` | 24 | 6 |
| **Total** | **281** | **119** |

## Verification and evidence

All four complete replacement modules compiled natively with pinned Lean **4.33.1**, compiler commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, and Mathlib pin `0df444a360eaa60ab8c11dca51a86af692955474`. Each changed public theorem was also checked against a separately namespaced complete original copy using an equality of the two theorem constants proved by `rfl`. These checks use Lean’s proof irrelevance and verify the exact theorem type; they do not claim the different proof terms have the same syntactic construction. The private right-inverse lemma and the unchanged downstream subspace-transport theorem were checked as well.

The changed public declarations’ axiom inventories contain only `propext`, `Classical.choice`, and `Quot.sound`. No new axioms, admitted goals, imports, or module dependencies were introduced. Applied source hashes match the checked candidates. Compilation loads pinned cached dependencies; this is focused module verification, not a fresh full-project Comparator run and not independent verification of the complete claimed Riemann Hypothesis proof.

Authoritative final receipts:

- Basis decomposition: [native result](basis-surjection/final-native.json), [exact-type and axiom result](basis-surjection/equality-and-axioms.json), [diff](basis-surjection/final.diff).
- Subspace transport: [complete-module and axiom result](subspace-transport/initial.json), [exact-type result](subspace-transport/equality-and-axioms.json), [diff](subspace-transport/final.diff).
- NcS: [complete-module result](trans-tuple/passed.json), [exact-type result](trans-tuple/type-equality.json), [diff](trans-tuple/final.diff).
- NcX: [complete-module result](trans-tuple/ncx/passed.json), [exact-type result](trans-tuple/ncx/type-equality.json), [diff](trans-tuple/ncx/final.diff).

The independent final-source review is recorded in [algebra/independent-review.json](../algebra/independent-review.json). The corresponding `.log` files contain compiler output and axiom inventories. Earlier exploratory logs are retained for provenance and are superseded by the final receipts above. NcS/NcX receipts preserve the paths of the successful nested `surj-equiv` trials; their checked contents are copied unchanged into the final evidence directories. [check_native.py](check_native.py) records the native command, source digest, search path, compiler version, elapsed time, and exit code. [summarize.py](summarize.py) verifies candidate/source equality, unchanged public statement text and imports, then generates the aggregate manifest and final diffs.

## Attribution

The original statements and arguments are retained from the repository’s Alpöge/Claude claimed-proof source mirror, `CocoSgt/riemann-hypothesis-lean`, whose recorded upstream commit is `7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`. This note credits that prior work and makes no new provenance or licensing claim about it. The replacement abstractions reuse the Mathlib community’s results, including its projective-module API (the relevant source credits Kevin Buzzard and Antoine Labelle), finite-dimensional subspace extension (the relevant source credits Chris Hughes), and linear-duality API. The new application and validation work here was performed by the Codex `compact_covariant` and `algebra_candidate_search` agents; `close_bound` independently reviewed the final source changes.
