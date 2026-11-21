import NormProductCertificate

/-! The actual archive Selmer inequality transfers to the square of a nonzero
integer norm witness, without importing the full automorphy producer. -/

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV
open UpperTheory.V.GradeZeroInterpolatingElement

namespace CertificateHour.ResonantRawBound

theorem of_norm_witness {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]
    {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (σ : G ℚ Ω)
    (NN : ℤ) (hNN : NN ≠ 0) (hne : D.AllIrr (fun r => D.aVal σ r ≠ 0))
    (control : ∀ Xi : Finset (G ℚ Ω →* M4 (PadicAlgCl l)),
      (∀ r ∈ Xi, D.EPt r ∧ Irr r) →
      (∀ r ∈ Xi, ∀ r' ∈ Xi, IsConj4 r r' → r = r') →
        ‖(NN : PadicAlgCl l)‖ ≤ ∏ r ∈ Xi, ‖D.aVal σ r‖) :
    D.Ineq σ → D.sha ≠ ⊤ ∧ Chr.nrm l c.O D.sha ≤
      ((NN.natAbs^2).factorization l : ℝ) := by
  rintro ⟨hfinite,Xi,hXi,hconj,hle⟩
  refine ⟨hfinite,?_⟩
  exact NormProductCertificate.normalized_bound l NN hNN Xi (D.aVal σ)
    (fun r hr => hne r (hXi r hr).1 (hXi r hr).2) (control Xi hXi hconj) _ hle

end CertificateHour.ResonantRawBound
#print axioms CertificateHour.ResonantRawBound.of_norm_witness
