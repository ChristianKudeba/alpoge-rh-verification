import Compaction.PrimeCertificate
import Compaction.FiniteLengthCard

noncomputable section
namespace Compaction.PrimeCertificate

open NumberField Formalism.GaloisCohomology UpperTheory.V

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
  [IsAlgClosure F Ω] {p : ℕ} [Fact p.Prime]

/-- The certificate is the product of the orders of the actual Selmer groups. -/
def orderCertificate (D : LData F Ω p) (t : ℕ) : ℕ :=
  ∏ e ∈ Finset.Ico 1 t, Nat.card (Sha D (e : ℤ))

theorem orderCertificate_eq (D : LData F Ω p) (t : ℕ)
    (hfinite : ∀ e : ℕ, 0 < e → e < t → shaLen D (e : ℤ) ≠ ⊤) :
    orderCertificate D t = certificate D t := by
  unfold orderCertificate certificate exponent
  calc
    ∏ e ∈ Finset.Ico 1 t, Nat.card (Sha D (e : ℤ)) =
        ∏ e ∈ Finset.Ico 1 t, p^(shaLen D (e : ℤ)).toNat := by
      apply Finset.prod_congr rfl
      intro e he
      exact FiniteLengthCard.card_eq_pow_length p (Sha D (e : ℤ))
        (hfinite e (Nat.succ_le_iff.mp (Finset.mem_Ico.mp he).1) (Finset.mem_Ico.mp he).2)
    _ = _ := Finset.prod_pow_eq_pow_sum _ _ _

theorem construct_orders {t : ℕ} {B : ℝ} (h : VVat p F t B) (Ω : Type) [Field Ω]
    [Algebra F Ω] [IsAlgClosure F Ω] (D : LData F Ω p) :
    0 < orderCertificate D t ∧ Real.log (orderCertificate D t) ≤ B * Real.log p ∧
      ∑ e ∈ Finset.Ico 1 t, shaLen D (e : ℤ) =
        ((orderCertificate D t).factorization p : ℕ∞) ∧
      ∀ q : ℕ, q ≠ p → (orderCertificate D t).factorization q = 0 := by
  rw [orderCertificate_eq D t (h Ω D).1]
  exact construct h Ω D

end Compaction.PrimeCertificate

#print axioms Compaction.PrimeCertificate.orderCertificate_eq
#print axioms Compaction.PrimeCertificate.construct_orders
