import PairCertificate
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.CountNormInt

namespace CertificateHour.IntegralNormCertificate

/-- Exact local size of a nonzero rational integer in the algebraic p-adic field. -/
theorem neg_log_norm_int (l : ℕ) [hl : Fact l.Prime] (n : ℤ) (hn : n ≠ 0) :
    -Real.log ‖(n : PadicAlgCl l)‖ = (padicValInt l n : ℝ) * Real.log l := by
  have hq : ((n : ℚ) : ℚ) ≠ 0 := by exact_mod_cast hn
  have hx : ‖(n : PadicAlgCl l)‖ = (l : ℝ) ^ (-(padicValInt l n : ℤ)) := by
    have hc : (((n : ℚ) : ℚ_[l]) : PadicAlgCl l) = (n : PadicAlgCl l) := by simp
    rw [← hc, PadicAlgCl.norm_extends, Padic.eq_padicNorm]
    have h := padicNorm.eq_zpow_of_nonzero (p := l) hq
    rw [padicValRat.of_int] at h
    rw [h]
    push_cast
    rfl
  rw [hx,Real.log_zpow]
  push_cast
  ring

/-- Squaring the absolute integer retains twice every prime valuation. -/
theorem factorization_square (l : ℕ) [hl : Fact l.Prime] (n : ℤ) (hn : n ≠ 0) :
    (n.natAbs^2).factorization l = 2 * padicValInt l n := by
  simpa [PairCertificate.mass,padicValInt] using
    PairCertificate.factorization_mass hn (by decide : (1:ℤ) ≠ 0) hl.out

end CertificateHour.IntegralNormCertificate

#print axioms CertificateHour.IntegralNormCertificate.neg_log_norm_int
#print axioms CertificateHour.IntegralNormCertificate.factorization_square
