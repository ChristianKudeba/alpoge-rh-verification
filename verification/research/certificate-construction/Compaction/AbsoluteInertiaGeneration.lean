import Compaction.PGroupInertia
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.MinkAbs
import ReciprocityTheory.GaloisValuations.ArithOfA

noncomputable section
namespace Compaction.Weber

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open scoped Pointwise

/-- All finite-prime inertia normally generates the finite quotient: away from
p it is killed, and at p every inertia is conjugate to the chosen one. This is
an application of the archive's proved absolute Minkowski theorem. -/
theorem inertia_normalClosure_eq_top (Ω : Type) [Field Ω] [Algebra ℚ Ω]
    [IsAlgClosure ℚ Ω] (N : Subgroup (G ℚ Ω)) [N.Normal]
    (hN : IsOpen (N : Set (G ℚ Ω))) (p : ℕ) (A₀ : ValuationSubring Ω)
    (outside : ∀ A : ValuationSubring Ω, ¬ A.valuation (p : Ω) < 1 →
      Ine (F := ℚ) A ≤ N)
    (conjugate : ∀ A : ValuationSubring Ω, A.valuation (p : Ω) < 1 →
      ∃ g : G ℚ Ω, g • A₀ = A) :
    Subgroup.normalClosure
      (((Ine (F := ℚ) A₀).map (QuotientGroup.mk' N) : Subgroup (G ℚ Ω ⧸ N)) :
        Set (G ℚ Ω ⧸ N)) = ⊤ := by
  let C := Subgroup.normalClosure
    (((Ine (F := ℚ) A₀).map (QuotientGroup.mk' N) : Subgroup (G ℚ Ω ⧸ N)) :
      Set (G ℚ Ω ⧸ N))
  let W := C.comap (QuotientGroup.mk' N)
  have hNW : N ≤ W := by
    intro n hn
    change (n : G ℚ Ω ⧸ N) ∈ C
    rw [(QuotientGroup.eq_one_iff n).mpr hn]
    exact C.one_mem
  have hW : IsOpen (W : Set (G ℚ Ω)) := Subgroup.isOpen_mono hNW hN
  haveI : W.Normal := inferInstanceAs (C.comap (QuotientGroup.mk' N)).Normal
  have hI₀ : Ine (F := ℚ) A₀ ≤ W := by
    intro g hg
    change (g : G ℚ Ω ⧸ N) ∈ C
    exact Subgroup.subset_normalClosure ⟨g, hg, rfl⟩
  have all_inertia (A : ValuationSubring Ω) : Ine (F := ℚ) A ≤ W := by
    by_cases hp : A.valuation (p : Ω) < 1
    · obtain ⟨g, hg⟩ := conjugate A hp
      intro σ hσ
      have hback : g⁻¹*σ*g ∈ Ine (F := ℚ) A₀ := by
        have hh := conj_mem_Ine_smul (γ := g⁻¹) hσ
        simpa only [inv_inv, ← hg, inv_smul_smul] using hh
      have hh := (inferInstance : W.Normal).conj_mem _ (hI₀ hback) g
      simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel_right,
        mul_inv_cancel, mul_one] using hh
    · exact (outside A hp).trans hNW
  have htop : W = ⊤ := UpperTheory.V.CF.minkAbs Ω W hW all_inertia
  apply top_unique
  intro x _
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  have hg : g ∈ W := by rw [htop]; trivial
  exact hg

end Compaction.Weber

#print axioms Compaction.Weber.inertia_normalClosure_eq_top
