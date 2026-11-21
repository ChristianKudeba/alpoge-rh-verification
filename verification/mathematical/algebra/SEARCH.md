# Algebra search findings

Final hosted check: `682d0327f3af43f54424ffc50df4ff35`, both complete modules closed with zero sorries and only standard Lean axioms. Saved 73 lines and 3,908 bytes. Public theorem statements are byte-identical.

Pinned Mathlib source: `0df444a360eaa60ab8c11dca51a86af692955474`, extracted read-only for theorem discovery at `/workspace/principia-harness/mathlib-source`. No local Lean builds run.

The source scan found 7,547 Mathlib-only declaration candidates with at least 15 proof-body lines. This is a heuristic count (some adjacent section commands may be included); it is not a count of redundant proofs.

## Verified and applied replacements

- `BaseChangeTensorModuleCompat.lean`: identify the ring square as a tensor-product pushout using `Algebra.IsPushout.tensorProduct_tensorProduct`. Use its canonical equivalence for faithful-flatness transport, then `Algebra.IsPushout.cancelBaseChange` for the module equivalence. This removes bespoke inverse maps, balanced-relation checks and nested tensor-induction inverse proofs. Only compatibility with the given O-action remains to prove.
- `SpanEqTopIffDense.lean`, `span_eq_top_iff_dense`: replace explicit denominator multiplication and span induction with the stronger existing `multiple_mem_span_of_mem_localization_span`. The reverse implication still uses invertibility of a nonzero denominator.

## Reviewed but not edited

- `ExistsBasisOfSurjective.lean`: its private right-inverse proof can be replaced by `LinearMap.exists_rightInverse_of_surjective` using projectivity. Its subsequent explicit kernel/product splitting may admit a complementary-submodule proof with `Submodule.prodEquivOfIsCompl`; a larger shortening needs careful API/typeclass work.
- `MulTensorInjectiveOfFlatBaseChangeKerInf.lean`: manually constructs a quotient-compatible tensor inverse. A stronger quotient/base-change equivalence may help, but the given rings use arbitrary surjections and non-definitional algebra structures; no checked replacement found yet.
- `DerivationFamilyCotangentBasis.lean`: substantial bespoke derivation/cotangent duality plus Nakayama. Replacing this requires a matching universal cotangent/derivation equivalence, not merely a shorter tactic invocation.
- `IsBaseChangeLatticeOfBasisAfterExtension.lean`: substantial determinant descent plus tensor normal form; no immediate strictly stronger Mathlib theorem identified.
- `FinrankEqZeroOfDualKilledByTensor.lean`: nontrivial characteristic-zero/positive-characteristic duality and integrality argument. No safe mathematical shortcut identified.
- `ExistsUniqueCocycle.lean`: compact semidirect-product/closure argument with a bespoke topological cocycle construction. Switching representations would change public instances; left unchanged.
- `ColumnDegreeLe.lean`: invariant polynomial degree argument via generic row reduction; no immediate library replacement identified.
