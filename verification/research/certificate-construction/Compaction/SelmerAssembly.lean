import Compaction.CertificateAssembly
import Compaction.PrimeCertificate

/-! Construct one integer from the actual dyadic, plus, and minus certificates.
The plus/minus certificate producers are explicit hypotheses here: this lemma
does not claim to discharge the remaining character-height estimates. -/

noncomputable section
namespace Compaction.SelmerAssembly
open NumberField Formalism.GaloisCohomology UpperTheory.V

variable {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω]
  [Algebra E Ω] [IsAlgClosure E Ω]

local instance primeFact (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

def total (ld : ∀ (p : ℕ) [Fact p.Prime], LData E Ω p) (t : ℕ) (Mplus Mminus : ℕ) : ℕ :=
  PrimeCertificate.certificate (ld 2) t * (Mplus * Mminus)

/-- Exact certificate for all primes at once, including ENat finiteness. The
integer is a product of the actual component certificates, not chosen from an
already-proved bound on the total finite-prime sums. -/
theorem construct (ld : ∀ (p : ℕ) [Fact p.Prime], LData E Ω p) (t Mplus Mminus : ℕ)
    (hplus : 0 < Mplus) (hminus : 0 < Mminus)
    (hf2 : ∀ e : ℕ, 0 < e → e < t → shaLen (ld 2) (e : ℤ) ≠ ⊤)
    (hp : ∀ p : Nat.Primes, (p : ℕ) ≠ 2 →
      ∑ e ∈ Finset.Ico 1 t, plusLen (@ld p ⟨p.2⟩) e ≤ (Mplus.factorization p : ℕ∞))
    (hm : ∀ p : Nat.Primes, (p : ℕ) ≠ 2 →
      ∑ e ∈ Finset.Ico 1 t, minusLen (@ld p ⟨p.2⟩) e ≤ (Mminus.factorization p : ℕ∞)) :
    0 < total ld t Mplus Mminus ∧
      ∀ p : Nat.Primes, ∑ e ∈ Finset.Ico 1 t, shaLen (@ld p ⟨p.2⟩) (e : ℤ) ≤
        ((total ld t Mplus Mminus).factorization p : ℕ∞) := by
  have h2 := PrimeCertificate.positive (ld 2) t
  refine ⟨Nat.mul_pos h2 (Nat.mul_pos hplus hminus), fun p => ?_⟩
  unfold total
  rw [Nat.factorization_mul h2.ne' (Nat.mul_pos hplus hminus).ne', Finsupp.add_apply,
    Nat.factorization_mul hplus.ne' hminus.ne', Finsupp.add_apply, Nat.cast_add, Nat.cast_add]
  by_cases heq : (p : ℕ) = 2
  · have hsame : p = ⟨2, Nat.prime_two⟩ := Subtype.ext heq
    subst p
    have hlen := PrimeCertificate.extended_length (ld 2) t hf2
    rw [PrimeCertificate.valuation]
    exact hlen.le.trans (le_add_of_nonneg_right (zero_le : (0 : ℕ∞) ≤
      (Mplus.factorization 2 : ℕ∞) + (Mminus.factorization 2 : ℕ∞)))
  · have hsum : ∑ e ∈ Finset.Ico 1 t, shaLen (@ld p ⟨p.2⟩) (e : ℤ) =
        (∑ e ∈ Finset.Ico 1 t, plusLen (@ld p ⟨p.2⟩) e) +
          ∑ e ∈ Finset.Ico 1 t, minusLen (@ld p ⟨p.2⟩) e := by
      simp_rw [shaLen_eq_add heq]
      exact Finset.sum_add_distrib
    rw [hsum]
    exact (add_le_add (hp p heq) (hm p heq)).trans
      (le_add_of_nonneg_left (zero_le : (0 : ℕ∞) ≤
        ((PrimeCertificate.certificate (ld 2) t).factorization p : ℕ∞)))

theorem logarithm (ld : ∀ (p : ℕ) [Fact p.Prime], LData E Ω p) (t Mplus Mminus : ℕ)
    (hplus : 0 < Mplus) (hminus : 0 < Mminus) :
    Real.log (total ld t Mplus Mminus) =
      (PrimeCertificate.exponent (ld 2) t : ℝ) * Real.log 2 + Real.log Mplus + Real.log Mminus := by
  unfold total
  rw [CertificateAssembly.log_multiply (PrimeCertificate.positive (ld 2) t)
    (Nat.mul_pos hplus hminus), CertificateAssembly.log_multiply hplus hminus,
    PrimeCertificate.log_certificate]
  norm_num only [Nat.cast_ofNat]
  ring

end Compaction.SelmerAssembly

#print axioms Compaction.SelmerAssembly.construct
#print axioms Compaction.SelmerAssembly.logarithm
