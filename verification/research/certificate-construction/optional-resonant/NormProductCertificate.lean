import IntegralNormCertificate

namespace CertificateHour.NormProductCertificate

/-- An actual product lower bound from a nonzero integer yields one integral
prime-valuation bound for the entire finite family of trace differences. -/
theorem valuation_bound {α : Type*} (l : ℕ) [hl : Fact l.Prime]
    (NN : ℤ) (hne : NN ≠ 0) (X : Finset α) (f : α → PadicAlgCl l)
    (hf : ∀ x ∈ X, f x ≠ 0)
    (hprod : ‖(NN : PadicAlgCl l)‖ ≤ ∏ x ∈ X, ‖f x‖) :
    2 * ∑ x ∈ X, -Real.log ‖f x‖ ≤
      ((NN.natAbs^2).factorization l : ℝ) * Real.log l := by
  have hN0 : 0 < ‖(NN : PadicAlgCl l)‖ := norm_pos_iff.mpr (by exact_mod_cast hne)
  have hlog := Real.log_le_log hN0 hprod
  rw [Real.log_prod (fun x hx => norm_ne_zero_iff.mpr (hf x hx))] at hlog
  have hn := IntegralNormCertificate.neg_log_norm_int l NN hne
  rw [IntegralNormCertificate.factorization_square l NN hne]
  push_cast
  rw [Finset.sum_neg_distrib]
  nlinarith

/-- Divide the product valuation inequality by the positive logarithm of the
cohomology prime to bound the actual normalized Selmer length. -/
theorem normalized_bound {α : Type*} (l : ℕ) [hl : Fact l.Prime]
    (NN : ℤ) (hne : NN ≠ 0) (X : Finset α) (f : α → PadicAlgCl l)
    (hf : ∀ x ∈ X, f x ≠ 0)
    (hprod : ‖(NN : PadicAlgCl l)‖ ≤ ∏ x ∈ X, ‖f x‖)
    (a : ℝ) (ha : a * Real.log l ≤ 2 * ∑ x ∈ X, -Real.log ‖f x‖) :
    a ≤ ((NN.natAbs^2).factorization l : ℝ) := by
  have hlpos : 0 < Real.log (l:ℝ) := Real.log_pos (by exact_mod_cast hl.out.one_lt)
  have h := ha.trans (valuation_bound l NN hne X f hf hprod)
  nlinarith

end CertificateHour.NormProductCertificate

#print axioms CertificateHour.NormProductCertificate.valuation_bound
#print axioms CertificateHour.NormProductCertificate.normalized_bound
