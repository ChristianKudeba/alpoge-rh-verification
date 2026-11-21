import Development.AutomorphicArithmetic.AutomorphicVarieties.LengthEqAddEigen

/-! Explicit certificates for one prime's entire interval of actual Selmer
lengths. A VVat bound constructs a prime power with the corresponding
logarithmic size bound. This does not assume a polynomial estimate. -/

noncomputable section
namespace Compaction.PrimeCertificate

open NumberField Formalism.GaloisCohomology UpperTheory.V

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
  [IsAlgClosure F Ω] {p : ℕ} [Fact p.Prime]

def exponent (D : LData F Ω p) (t : ℕ) : ℕ :=
  ∑ e ∈ Finset.Ico 1 t, (shaLen D (e : ℤ)).toNat

def certificate (D : LData F Ω p) (t : ℕ) : ℕ := p ^ exponent D t

theorem positive (D : LData F Ω p) (t : ℕ) : 0 < certificate D t :=
  pow_pos (Fact.out : p.Prime).pos _

theorem valuation (D : LData F Ω p) (t : ℕ) :
    (certificate D t).factorization p = exponent D t := by
  simp [certificate, Nat.factorization_pow, Nat.Prime.factorization_self (Fact.out : p.Prime)]

theorem other_valuation (D : LData F Ω p) (t : ℕ) {q : ℕ} (hqp : q ≠ p) :
    (certificate D t).factorization q = 0 := by
  simp [certificate, Nat.factorization_pow, (Fact.out : p.Prime).factorization, hqp]

theorem log_certificate (D : LData F Ω p) (t : ℕ) :
    Real.log (certificate D t) = (exponent D t : ℝ) * Real.log p := by
  simp only [certificate, Nat.cast_pow, Real.log_pow]

theorem extended_length (D : LData F Ω p) (t : ℕ)
    (hfinite : ∀ e : ℕ, 0 < e → e < t → shaLen D (e : ℤ) ≠ ⊤) :
    ∑ e ∈ Finset.Ico 1 t, shaLen D (e : ℤ) = (exponent D t : ℕ∞) := by
  rw [exponent, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro e he
  exact (ENat.natCast_toNat (hfinite e
    (Nat.succ_le_iff.mp (Finset.mem_Ico.mp he).1) (Finset.mem_Ico.mp he).2)).symm

/-- The integer is explicitly p raised to the sum of all actual finite lengths.
Its valuation equals that sum, while its logarithm obeys the VVat budget. -/
theorem construct {t : ℕ} {B : ℝ} (h : VVat p F t B) (Ω : Type) [Field Ω]
    [Algebra F Ω] [IsAlgClosure F Ω] (D : LData F Ω p) :
    0 < certificate D t ∧ Real.log (certificate D t) ≤ B * Real.log p ∧
      ∑ e ∈ Finset.Ico 1 t, shaLen D (e : ℤ) =
        ((certificate D t).factorization p : ℕ∞) ∧
      ∀ q : ℕ, q ≠ p → (certificate D t).factorization q = 0 := by
  obtain ⟨hf, hb⟩ := h Ω D
  refine ⟨positive D t, ?_, ?_, fun q hq => other_valuation D t hq⟩
  · rw [log_certificate]
    have hb' : (exponent D t : ℝ) ≤ B := by simpa only [exponent, Nat.cast_sum] using hb
    exact mul_le_mul_of_nonneg_right hb' (Real.log_natCast_nonneg _)
  · rw [valuation]
    exact extended_length D t hf

/-- In particular the dyadic bound exp(x^(4 eps/5)) produces a certificate
whose logarithm is at most log(2) exp(x^(4 eps/5)). -/
theorem dyadic {t : ℕ} {x eps : ℝ}
    (h : VVat 2 F t (Real.exp (x ^ (4 * eps / 5)))) (Ω : Type) [Field Ω]
    [Algebra F Ω] [IsAlgClosure F Ω] (D : LData F Ω 2) :
    0 < certificate D t ∧
      Real.log (certificate D t) ≤ Real.log 2 * Real.exp (x ^ (4 * eps / 5)) ∧
      ∑ e ∈ Finset.Ico 1 t, shaLen D (e : ℤ) =
        ((certificate D t).factorization 2 : ℕ∞) := by
  obtain ⟨hp, hb, hv, _⟩ := construct h Ω D
  exact ⟨hp, by simpa only [Nat.cast_ofNat, mul_comm] using hb, hv⟩

end Compaction.PrimeCertificate

#print axioms Compaction.PrimeCertificate.construct
#print axioms Compaction.PrimeCertificate.dyadic
