# Algebra and finiteness reductions — 21 November 2026

Four existing theorems now reuse more general library arguments. Their full
types, assumptions, names, and source imports are unchanged. The net reduction
is **31 proof lines**; none of this count comes from abbreviating expanded types.

| Existing theorem | Replacement argument | Proof lines |
| --- | --- | --- |
| `GroundTheory.ProfCoh.finite_setOf_nsmul_eq_zero_QZ` | `QZ` is definitionally `AddCircle (1 : ℚ)`, so apply Mathlib's `AddCircle.finite_torsion`. This removes the separate residue enumeration, modular arithmetic, and rational reconstruction. | 27 → 1 |
| `GroundTheory.ProfCoh.inf_sup_normal_eq` | Apply Mathlib's pointwise Dedekind identity `Subgroup.inf_mul_assoc` and identify joins with products using normality. | 7 → 3 |
| `GroundTheory.ProfCoh.index_sup_ne_zero` | Inherit finite index along `U ≤ H ⊔ U` and use `FiniteIndex.index_ne_zero`. | 2 → 2 |
| `GroundTheory.ProfCoh.relIndex_sup_ne_zero` | Inherit finite index along `U ≤ K ⊔ U`, then restrict it to `H` through Mathlib's `subgroupOf` instance. | 3 → 2 |

The two modified source modules were checked in their entirety, with axiom
prints appended to exact copies of the modified source. Both checks passed
under pinned Lean 4.33.1 and the selected archive dependency cache. Each changed
theorem lists only `propext`, `Classical.choice`, and `Quot.sound`.

- `qz-finite-check.lean`, `qz-finite-module.log`, and `qz-finite-module.json`
  record the torsion-finiteness module check.
- `subgroup-index-check.lean`, `subgroup-index-module.log`, and
  `subgroup-index-module.json` record the subgroup-index module check.
- `SubgroupIndexShortcuts.lean` and `subgroup-shortcuts.log` separately check
  the three subgroup replacements using Mathlib alone.
- `algebra-reductions.json` records exact old/new source hashes, unchanged-type
  comparisons, and proof-line counts. Counts exclude the leading `by` token
  and count the remaining physical proof lines.

These are local module checks, not a full-project Comparator verdict. Imported
archive objects were reused from the pinned selected cache; no complete RH
build or new unconditional RH proof is claimed.

Further survey targets include `DefGroupLemmas`' transport of stabilizers and
finite double-coset arguments. They were inspected but not edited here: a
shared group-action transport lemma may replace repeated coordinate arguments,
whereas merely contracting their displayed matrix types would be a different
kind of saving.
