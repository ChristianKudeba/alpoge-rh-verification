import RegularCharacterHeight

/-! An actual certificate, M=1, for the trivial-character contribution at the
exceptional primes 3 and 7. This supplies only these components, not the full
plus-height estimate. The vanishing theorem is Anton's new contribution. -/

noncomputable section
namespace CertificateHour.RegularOneCertificate

open UpperTheory.V UpperTheory.V.HV

theorem three (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]
    (h : Host) (c : Coef 3) (t : ℕ) :
    ∃ M : ℕ, 0 < M ∧ Real.log M = 0 ∧
      ∑ e ∈ Finset.Ico 1 t,
        Vlen Ω c e (1 : DirichletCharacter c.O h.N) ≤ (M.factorization 3 : ℕ∞) := by
  refine ⟨1, zero_lt_one, by simp, ?_⟩
  have hz : ∑ e ∈ Finset.Ico 1 t,
      Vlen Ω c e (1 : DirichletCharacter c.O h.N) = 0 := by
    apply Finset.sum_eq_zero
    intro e he
    exact Principia.Ordinary.RegularCharacters.three Ω h c e (Finset.mem_Ico.mp he).1
  simp only [hz, Nat.factorization_one, Finsupp.coe_zero, Pi.zero_apply, Nat.cast_zero,
    le_refl]

local instance : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩

theorem seven (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]
    (h : Host) (c : Coef 7) (t : ℕ) :
    ∃ M : ℕ, 0 < M ∧ Real.log M = 0 ∧
      ∑ e ∈ Finset.Ico 1 t,
        Vlen Ω c e (1 : DirichletCharacter c.O h.N) ≤ (M.factorization 7 : ℕ∞) := by
  refine ⟨1, zero_lt_one, by simp, ?_⟩
  have hz : ∑ e ∈ Finset.Ico 1 t,
      Vlen Ω c e (1 : DirichletCharacter c.O h.N) = 0 := by
    apply Finset.sum_eq_zero
    intro e he
    exact Principia.Ordinary.RegularCharacters.seven Ω h c e (Finset.mem_Ico.mp he).1
  simp only [hz, Nat.factorization_one, Finsupp.coe_zero, Pi.zero_apply, Nat.cast_zero,
    le_refl]

end CertificateHour.RegularOneCertificate

#print axioms CertificateHour.RegularOneCertificate.three
#print axioms CertificateHour.RegularOneCertificate.seven
