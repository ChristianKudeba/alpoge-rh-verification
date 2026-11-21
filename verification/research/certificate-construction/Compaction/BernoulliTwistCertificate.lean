import Compaction.BernoulliLengthCertificate

/-! An actual across-twist product of conductor-only Bernoulli integer
certificates. The numerical estimate follows Anton's logarithmic factorial
estimate in Joint/PrincipalMinus, but no principal-character restriction is
used in the certificate construction.
-/

noncomputable section
namespace Compaction.BernoulliTwistCertificate

open Finset UpperTheory.V.Bern

theorem log_bnd_le (N t e : ℕ) (hN : 0 < N) (ht : 2 ≤ t) (he : e < t) :
    Real.log (bnd N (e + 1)) ≤ (2 * e + 7 : ℕ) * Real.log ((t : ℝ) * N) := by
  let u := t * N
  have hu : 2 ≤ u := ht.trans (Nat.le_mul_of_pos_right t hN)
  have hNu : N ≤ u := Nat.le_mul_of_pos_left N (by omega)
  have heu : e + 1 ≤ u := (show e + 1 ≤ t by omega).trans (Nat.le_mul_of_pos_right t hN)
  have h16 : 16 ≤ u ^ 4 := Nat.pow_le_pow_left hu 4
  have hfact := (Nat.factorial_le_pow (e + 1)).trans (Nat.pow_le_pow_left heu (e + 1))
  have hnat := Nat.mul_le_mul (Nat.mul_le_mul h16 (Nat.pow_le_pow_left hNu (e + 1 + 1))) hfact
  rw [← pow_add, ← pow_add] at hnat
  have heq : 4 + (e + 1 + 1) + (e + 1) = 2 * e + 7 := by omega
  rw [heq] at hnat
  have hreal : bnd N (e + 1) ≤ ((t : ℝ) * N) ^ (2 * e + 7) := by
    unfold bnd
    exact_mod_cast hnat
  have hpos : 0 < bnd N (e + 1) := by unfold bnd; positivity
  simpa only [Real.log_pow] using Real.log_le_log hpos hreal

theorem log_bnd_sum_le (N t : ℕ) (hN : 0 < N) (ht : 2 ≤ t) :
    ∑ e ∈ Finset.Ico 1 t, Real.log (bnd N (e + 1)) ≤
      3 * (t : ℝ) ^ 2 * Real.log ((t : ℝ) * N) := by
  let L := Real.log ((t : ℝ) * N)
  have hL : 0 ≤ L := Real.log_nonneg
    (one_le_mul_of_one_le_of_one_le (by exact_mod_cast (show 1 ≤ t by omega))
      (by exact_mod_cast hN))
  have hb : (∑ e ∈ Finset.Ico 1 t, Real.log (bnd N (e + 1))) ≤
      ((t : ℝ) - 1) * ((2 * t + 5) * L) := by
    calc
      _ ≤ ∑ e ∈ Finset.Ico 1 t, (2 * (t : ℝ) + 5) * L := by
        apply Finset.sum_le_sum
        intro e he
        have hlt := (Finset.mem_Ico.mp he).2
        apply (log_bnd_le N t e hN ht hlt).trans
        apply mul_le_mul_of_nonneg_right _ hL
        exact_mod_cast (show 2 * e + 7 ≤ 2 * t + 5 by omega)
      _ = _ := by
        rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub (by omega : 1 ≤ t)]
        simp
  have hcoef : ((t : ℝ) - 1) * (2 * t + 5) ≤ 3 * (t : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((t : ℝ) - 2)]
  exact hb.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hcoef hL)

/-- The integer is the finite product of the positive integers supplied at each
twist. Its valuation bounds the ENat sum, so infinite lengths are excluded. -/
theorem universal_across_twists {N : ℕ} [NeZero N] (t : ℕ) (ht : 2 ≤ t) :
    ∃ M : ℕ, 0 < M ∧ Real.log M ≤
      3 * (N : ℝ) * (t : ℝ) ^ 2 * Real.log ((t : ℝ) * N) ∧
      ∀ (eligible : ℕ → Prop) (length : ℕ → ℕ → ℕ∞),
      (∀ e ∈ Finset.Ico 1 t, ∀ (l : ℕ) [Fact l.Prime],
      eligible l → length l e ≠ ⊤ ∧
      ∃ T : Finset (DirichletCharacter (PadicAlgCl l) N),
        (T : Set _) ⊆ charSet (PadicAlgCl l) (parKer N (e + 1)) ∧
        ((length l e).toNat : ℝ) * Real.log l ≤
          ∑ χ ∈ T, -Real.log ‖(den N (e + 1) : PadicAlgCl l) * Bprim (e + 1) χ‖) →
      ∀ (l : ℕ) [Fact l.Prime], eligible l →
        ∑ e ∈ Finset.Ico 1 t, length l e ≤ (M.factorization l : ℕ∞) := by
  classical
  choose m hm using fun e : ℕ => BernoulliLengthCertificate.universal_at_twist (N := N) e
  refine ⟨∏ e ∈ Finset.Ico 1 t, m e, Finset.prod_pos (fun e _ => (hm e).1), ?_, ?_⟩
  · rw [Nat.cast_prod, Real.log_prod (fun e _ => Nat.cast_ne_zero.mpr (hm e).1.ne')]
    calc
      _ ≤ ∑ e ∈ Finset.Ico 1 t, (N : ℝ) * Real.log (bnd N (e + 1)) :=
        Finset.sum_le_sum (fun e _ => (hm e).2.1)
      _ = (N : ℝ) * ∑ e ∈ Finset.Ico 1 t, Real.log (bnd N (e + 1)) := (Finset.mul_sum ..).symm
      _ ≤ (N : ℝ) * (3 * (t : ℝ) ^ 2 * Real.log ((t : ℝ) * N)) :=
        mul_le_mul_of_nonneg_left (log_bnd_sum_le N t (NeZero.pos N) ht) (Nat.cast_nonneg N)
      _ = _ := by ring
  · intro eligible length comparison l _ hl
    rw [Nat.factorization_prod_apply (fun e _ => (hm e).1.ne'), Nat.cast_sum]
    exact Finset.sum_le_sum (fun e he => (hm e).2.2 eligible (fun p => length p e) (comparison e he) l hl)

end Compaction.BernoulliTwistCertificate

#print axioms Compaction.BernoulliTwistCertificate.log_bnd_sum_le
#print axioms Compaction.BernoulliTwistCertificate.universal_across_twists
