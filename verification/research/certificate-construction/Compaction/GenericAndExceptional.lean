import Mathlib

/-! Construct a single certificate from simultaneous generic certificates and
uniformly bounded exceptional lengths at finitely many small primes. -/

namespace Compaction.GenericAndExceptional

theorem construct (a : Nat.Primes → ℕ → ℕ∞) (G : Nat.Primes → ℕ → Prop)
    (M : ℕ → ℕ) (t L R : ℕ) (hL : 0 < L)
    (hM : ∀ e ∈ Finset.Ico 1 t, 0 < M e)
    (hgen : ∀ p e, e ∈ Finset.Ico 1 t → G p e →
      a p e ≤ ((M e).factorization p : ℕ∞))
    (hbad : ∀ p e, e ∈ Finset.Ico 1 t → ¬ G p e →
      (p : ℕ) ≤ L ∧ a p e ≤ (R : ℕ∞)) :
    let C := (∏ e ∈ Finset.Ico 1 t, M e) * L.factorial ^ (t * R)
    0 < C ∧ ∀ p : Nat.Primes,
      ∑ e ∈ Finset.Ico 1 t, a p e ≤ (C.factorization p : ℕ∞) := by
  classical
  let A := ∏ e ∈ Finset.Ico 1 t, M e
  let B := L.factorial ^ (t * R)
  have hA : 0 < A := Finset.prod_pos hM
  have hB : 0 < B := pow_pos (Nat.factorial_pos L) _
  refine ⟨Nat.mul_pos hA hB, fun p => ?_⟩
  change _ ≤ ((A * B).factorization p : ℕ∞)
  rw [Nat.factorization_mul hA.ne' hB.ne', Finsupp.add_apply, Nat.cast_add]
  have hval : (A.factorization p : ℕ∞) =
      ∑ e ∈ Finset.Ico 1 t, ((M e).factorization p : ℕ∞) := by
    dsimp [A]
    rw [Nat.factorization_prod_apply (fun e he => (hM e he).ne'), Nat.cast_sum]
  by_cases hp : (p : ℕ) ≤ L
  · have hv : t * R ≤ B.factorization p :=
      (p.2.pow_dvd_iff_le_factorization hB.ne').mp
        (pow_dvd_pow_of_dvd (Nat.dvd_factorial p.2.pos hp) _)
    have each (e : ℕ) (he : e ∈ Finset.Ico 1 t) :
        a p e ≤ ((M e).factorization p : ℕ∞) + (R : ℕ∞) := by
      by_cases hg : G p e
      · exact (hgen p e he hg).trans (le_add_of_nonneg_right (zero_le : (0 : ℕ∞) ≤ R))
      · exact (hbad p e he hg).2.trans
          (le_add_of_nonneg_left (zero_le : (0 : ℕ∞) ≤ (M e).factorization p))
    calc
      ∑ e ∈ Finset.Ico 1 t, a p e ≤
          ∑ e ∈ Finset.Ico 1 t, (((M e).factorization p : ℕ∞) + (R : ℕ∞)) :=
        Finset.sum_le_sum each
      _ = (A.factorization p : ℕ∞) + (((t - 1) * R : ℕ) : ℕ∞) := by
        rw [Finset.sum_add_distrib, ← hval]
        simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_mul]
      _ ≤ (A.factorization p : ℕ∞) + (B.factorization p : ℕ∞) := by
        apply add_le_add le_rfl
        exact_mod_cast (Nat.mul_le_mul_right R (Nat.sub_le t 1)).trans hv
  · rw [hval]
    apply le_trans _ (le_add_of_nonneg_right (zero_le : (0 : ℕ∞) ≤ B.factorization p))
    apply Finset.sum_le_sum
    intro e he
    exact hgen p e he (by by_contra hg; exact hp (hbad p e he hg).1)

end Compaction.GenericAndExceptional

#print axioms Compaction.GenericAndExceptional.construct
