import Mathlib

/-! The two integers in Alpöge's PropGK, which each exclude one auxiliary
prime, combine into one certificate valid at every prime. -/

namespace CertificateHour.PairCertificate

def mass (a b : ℤ) : ℕ := (a.natAbs * b.natAbs)^2

theorem mass_pos {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) : 0 < mass a b :=
  pow_pos (Nat.mul_pos (Int.natAbs_pos.mpr ha) (Int.natAbs_pos.mpr hb)) _

theorem log_mass {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) :
    Real.log (mass a b) = 2 * (Real.log |(a : ℝ)| + Real.log |(b : ℝ)|) := by
  have ha' : (a.natAbs : ℝ) ≠ 0 := by exact_mod_cast Int.natAbs_ne_zero.mpr ha
  have hb' : (b.natAbs : ℝ) ≠ 0 := by exact_mod_cast Int.natAbs_ne_zero.mpr hb
  unfold mass
  rw [Nat.cast_pow, Nat.cast_mul, Real.log_pow, Real.log_mul ha' hb']
  simp only [Nat.cast_natAbs, Int.cast_abs, Nat.cast_ofNat]

theorem factorization_mass {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0)
    {p : ℕ} (hp : p.Prime) :
    (mass a b).factorization p = 2 * (padicValInt p a + padicValInt p b) := by
  simp only [mass, Nat.factorization_pow,
    Nat.factorization_mul (Int.natAbs_ne_zero.mpr ha) (Int.natAbs_ne_zero.mpr hb),
    Finsupp.smul_apply, Finsupp.add_apply, smul_eq_mul,
    Nat.factorization_def _ hp, padicValInt]

/-- The excluded primes are distinct, so the other integer always supplies
a bound. The squared product gives a single integer for all primes at once. -/
theorem dominates {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0)
    (r s : ℕ) (hrs : r ≠ s) (L : Nat.Primes → ℝ)
    (hA : ∀ p : Nat.Primes, (p : ℕ) ≠ r → L p ≤ 2 * padicValInt p a)
    (hB : ∀ p : Nat.Primes, (p : ℕ) ≠ s → L p ≤ 2 * padicValInt p b) :
    ∀ p : Nat.Primes, L p ≤ ((mass a b).factorization p : ℝ) := by
  intro p
  rw [factorization_mass ha hb p.2]
  push_cast
  by_cases hpr : (p : ℕ) = r
  · have hps : (p : ℕ) ≠ s := fun hps => hrs (hpr.symm.trans hps)
    have h := hB p hps
    have h0 := Nat.cast_nonneg (α := ℝ) (padicValInt p a)
    linarith
  · have h := hA p hpr
    have h0 := Nat.cast_nonneg (α := ℝ) (padicValInt p b)
    linarith

theorem log_mass_le {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) {A B : ℝ}
    (hA : Real.log |(a : ℝ)| ≤ A) (hB : Real.log |(b : ℝ)| ≤ B) :
    Real.log (mass a b) ≤ 2 * (A + B) := by
  rw [log_mass ha hb]
  linarith

end CertificateHour.PairCertificate

#print axioms CertificateHour.PairCertificate.dominates
#print axioms CertificateHour.PairCertificate.log_mass_le
