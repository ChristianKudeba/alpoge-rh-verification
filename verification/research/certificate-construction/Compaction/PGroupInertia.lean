import Mathlib

namespace Compaction.Weber

/-- In a finite p-group, a subgroup that generates normally already is the
whole group. This is the group-theoretic core of the ramification argument. -/
theorem eq_top_of_normalClosure_eq_top {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G] [Finite G] (hp : IsPGroup p G) (I : Subgroup G)
    (hgen : Subgroup.normalClosure (I : Set G) = ⊤) : I = ⊤ := by
  rcases IsCoatomic.eq_top_or_exists_le_coatom I with h | ⟨M, hM, hIM⟩
  · exact h
  have hnil : Group.IsNilpotent G := hp.isNilpotent
  haveI : M.Normal :=
    Subgroup.NormalizerCondition.normal_of_coatom M normalizerCondition_of_isNilpotent hM
  have hc : Subgroup.normalClosure (I : Set G) ≤ M :=
    Subgroup.normalClosure_le_normal hIM
  rw [hgen] at hc
  exact False.elim (hM.1 (top_unique hc))

/-- Once inertia fills the finite p-group quotient, triviality of inertia in
the relative class-field direction collapses that entire relative extension. -/
theorem relative_kernel_eq {p : ℕ} [Fact p.Prime] {G : Type*} [Group G]
    (N U I : Subgroup G) [N.Normal] [Finite (G ⧸ N)]
    (hNU : N ≤ U) (hp : IsPGroup p (G ⧸ N))
    (hgen : Subgroup.normalClosure
      ((I.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N)) = ⊤)
    (hrel : I ⊓ U ≤ N) : U = N := by
  have hI : I.map (QuotientGroup.mk' N) = ⊤ :=
    eq_top_of_normalClosure_eq_top hp _ hgen
  apply le_antisymm ?_ hNU
  intro u hu
  have hmem : (u : G ⧸ N) ∈ I.map (QuotientGroup.mk' N) := by rw [hI]; trivial
  obtain ⟨i, hi, heq⟩ := hmem
  have hdiff : i⁻¹*u ∈ N := QuotientGroup.eq.mp heq
  have hiU : i ∈ U := by
    have hh := U.mul_mem hu (U.inv_mem (hNU hdiff))
    simpa only [mul_inv_rev, inv_inv, mul_inv_cancel_left] using hh
  have hiN : i ∈ N := hrel ⟨hi, hiU⟩
  simpa only [mul_inv_cancel_left] using N.mul_mem hiN hdiff

end Compaction.Weber

#print axioms Compaction.Weber.eq_top_of_normalClosure_eq_top
#print axioms Compaction.Weber.relative_kernel_eq
