import OrbitCertificate
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.OrbFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.OrbSum

/-! Aggregate the actual PropGK integers over a fixed set of rational character
orbits. The integer is chosen before the prime, coefficient ring, realization,
and finite character family. In particular it is independent of any finite set
of primes used later in VVle. -/

noncomputable section
namespace CertificateHour.AllOrbitCertificate

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.U3

theorem of_propGK (input : PropGK) (K : Type) [Field K] [NumberField K] :
    ∃ c A : ℕ, ∀ (e N : ℕ) [NeZero N] (r s : ℕ),
      1 ≤ e → r.Prime → s.Prime → r ≠ s →
      ¬ r ∣ 30 * N * (discr K).natAbs → ¬ s ∣ 30 * N * (discr K).natAbs →
      ∃ M : ℕ, 0 < M ∧
        Real.log M ≤ 2 * c * N * ((N : ℝ) * (e + 1))^A *
          (Real.log r + Real.log s) ∧
        ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra K Ω]
          (p : ℕ) [Fact p.Prime] (coef : Coef p)
          (S : Finset (DirichletCharacter coef.O N)),
          (∀ ψ ∈ S, GD Ω K p e ψ) →
          (∀ ψ ∈ S, Vlen Ω coef e ψ ≠ ⊤) ∧
            ∑ ψ ∈ S, Vn Ω coef e ψ ≤ (M.factorization p : ℝ) := by
  classical
  obtain ⟨c, A, supply⟩ := OrbitCertificate.of_propGK input K
  refine ⟨c, A, ?_⟩
  intro e N _ r s he hr hs hrs hrd hsd
  letI : Fintype (Subgroup (ZMod N)ˣ) := Fintype.ofFinite _
  let T : Finset (Subgroup (ZMod N)ˣ) :=
    Finset.univ.filter fun H => IsCyclic ((ZMod N)ˣ ⧸ H)
  have hT (H : Subgroup (ZMod N)ˣ) : H ∈ T ↔ IsCyclic ((ZMod N)ˣ ⧸ H) := by
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
  have each := fun H : Subgroup (ZMod N)ˣ => supply e N H r s he hr hs hrs hrd hsd
  choose M hMpos hMsize hMbound using each
  let P : ℕ := ∏ H ∈ T, M H
  have hp : 0 < P := Finset.prod_pos (fun H _ => hMpos H)
  refine ⟨P, hp, ?_, ?_⟩
  · let B : ℝ := 2 * c * ((N : ℝ) * (e + 1))^A * (Real.log r + Real.log s)
    have hB : 0 ≤ B := by
      dsimp [B]
      exact mul_nonneg (by positivity)
        (add_nonneg (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _))
    have hsum : (∑ H ∈ T, (Nat.totient H.index : ℝ)) ≤ (N : ℝ) := by
      have h := orbSum (ZMod N)ˣ T (fun H hH => (hT H).mp hH)
      rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient] at h
      exact_mod_cast h.trans (Nat.totient_le N)
    calc
      Real.log P = ∑ H ∈ T, Real.log (M H) := by
        dsimp [P]
        rw [Nat.cast_prod, Real.log_prod (fun H hH => by exact_mod_cast (hMpos H).ne')]
      _ ≤ ∑ H ∈ T, B * (Nat.totient H.index : ℝ) := by
        apply Finset.sum_le_sum
        intro H hH
        simpa only [B, mul_assoc, mul_left_comm, mul_comm] using hMsize H
      _ = B * ∑ H ∈ T, (Nat.totient H.index : ℝ) := (Finset.mul_sum ..).symm
      _ ≤ B * N := mul_le_mul_of_nonneg_left hsum hB
      _ = _ := by dsimp [B]; ring
  · intro Ω _ _ _ _ p _ coef S hGD
    have hkernel (ψ : DirichletCharacter coef.O N) : ψ.toUnitHom.ker ∈ T :=
      (hT _).mpr (orbFacts coef.O N ψ).2.1
    have hpos (H : Subgroup (ZMod N)ˣ) : 0 ≤ ((M H).factorization p : ℝ) := by positivity
    have hpval : (P.factorization p : ℝ) =
        ∑ H ∈ T, ((M H).factorization p : ℝ) := by
      rw [show P = ∏ H ∈ T, M H from rfl,
        Nat.factorization_prod_apply (fun H _ => (hMpos H).ne'), Nat.cast_sum]
    refine ⟨?_, ?_⟩
    · intro ψ hψ
      exact (hMbound ψ.toUnitHom.ker Ω p coef
        ⟨ψ, (mem_orb coef).mpr rfl, hGD ψ hψ⟩).1 ψ ((mem_orb coef).mpr rfl)
    · rw [hpval]
      calc
        _ = ∑ H ∈ T, ∑ ψ ∈ S.filter (fun ψ => ψ.toUnitHom.ker = H), Vn Ω coef e ψ :=
          (Finset.sum_fiberwise_of_maps_to (s := S) (t := T)
            (g := fun ψ => ψ.toUnitHom.ker) (fun ψ _ => hkernel ψ)
            (fun ψ => Vn Ω coef e ψ)).symm
        _ ≤ ∑ H ∈ T, ((M H).factorization p : ℝ) := by
          apply Finset.sum_le_sum
          intro H hH
          by_cases hempty : S.filter (fun ψ => ψ.toUnitHom.ker = H) = ∅
          · rw [hempty, Finset.sum_empty]
            exact hpos H
          · obtain ⟨ψ₀, hψ₀⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
            obtain ⟨hψS, hψker⟩ := Finset.mem_filter.mp hψ₀
            have bound := (hMbound H Ω p coef
              ⟨ψ₀, (mem_orb coef).mpr hψker, hGD ψ₀ hψS⟩).2
            apply le_trans ?_ bound
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro ψ hψ
              exact (mem_orb coef).mpr (Finset.mem_filter.mp hψ).2
            · intro ψ _ _
              exact Vn_nonneg Ω coef e ψ

end CertificateHour.AllOrbitCertificate

#print axioms CertificateHour.AllOrbitCertificate.of_propGK
