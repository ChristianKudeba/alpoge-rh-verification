import Mathlib

/-! Multiplicative assembly of actual positive-integer certificates. Bounds
are in ENat, so the arithmetic certificates force finiteness of every length.
The lemmas construct the final integer; they do not assume its existence. -/

namespace Compaction.CertificateAssembly

def Dominates (a : Nat.Primes → ℕ → ℕ∞) (t M : ℕ) : Prop :=
  ∀ p : Nat.Primes, ∑ e ∈ Finset.Ico 1 t, a p e ≤ (M.factorization p : ℕ∞)

theorem multiply {a b c : Nat.Primes → ℕ → ℕ∞} {t M N : ℕ}
    (hM : 0 < M) (hN : 0 < N) (ha : Dominates a t M) (hb : Dominates b t N)
    (hc : ∀ p e, e ∈ Finset.Ico 1 t → c p e ≤ a p e + b p e) :
    Dominates c t (M * N) := by
  intro p
  calc
    ∑ e ∈ Finset.Ico 1 t, c p e ≤ ∑ e ∈ Finset.Ico 1 t, (a p e + b p e) :=
      Finset.sum_le_sum fun e he => hc p e he
    _ = (∑ e ∈ Finset.Ico 1 t, a p e) + ∑ e ∈ Finset.Ico 1 t, b p e :=
      Finset.sum_add_distrib
    _ ≤ (M.factorization p : ℕ∞) + (N.factorization p : ℕ∞) := add_le_add (ha p) (hb p)
    _ = ((M * N).factorization p : ℕ∞) := by
      rw [Nat.factorization_mul hM.ne' hN.ne', Finsupp.add_apply, Nat.cast_add]

theorem log_multiply {M N : ℕ} (hM : 0 < M) (hN : 0 < N) :
    Real.log (M * N : ℕ) = Real.log M + Real.log N := by
  rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast hM.ne') (by exact_mod_cast hN.ne')]

theorem multiply_with_budget {a b c : Nat.Primes → ℕ → ℕ∞} {t M N : ℕ} {A B : ℝ}
    (hM : 0 < M) (hN : 0 < N) (ha : Dominates a t M) (hb : Dominates b t N)
    (hc : ∀ p e, e ∈ Finset.Ico 1 t → c p e ≤ a p e + b p e)
    (hA : Real.log M ≤ A) (hB : Real.log N ≤ B) :
    0 < M * N ∧ Real.log (M * N : ℕ) ≤ A + B ∧ Dominates c t (M * N) :=
  ⟨Nat.mul_pos hM hN, by rw [log_multiply hM hN]; exact add_le_add hA hB,
    multiply hM hN ha hb hc⟩

/-- A product over twists assembles uniform per-twist certificates. In
particular the same product works for every prime, not one prime at a time. -/
theorem across_twists (a : Nat.Primes → ℕ → ℕ∞) (t : ℕ) (M : ℕ → ℕ)
    (hM : ∀ e ∈ Finset.Ico 1 t, 0 < M e)
    (h : ∀ p e, e ∈ Finset.Ico 1 t → a p e ≤ ((M e).factorization p : ℕ∞)) :
    0 < ∏ e ∈ Finset.Ico 1 t, M e ∧
      Dominates a t (∏ e ∈ Finset.Ico 1 t, M e) := by
  classical
  refine ⟨Finset.prod_pos hM, fun p => ?_⟩
  calc
    ∑ e ∈ Finset.Ico 1 t, a p e ≤ ∑ e ∈ Finset.Ico 1 t, ((M e).factorization p : ℕ∞) :=
      Finset.sum_le_sum fun e he => h p e he
    _ = ((∏ e ∈ Finset.Ico 1 t, M e).factorization p : ℕ∞) := by
      rw [Nat.factorization_prod_apply (fun e he => (hM e he).ne'), Nat.cast_sum]

theorem log_across_twists (t : ℕ) (M : ℕ → ℕ)
    (hM : ∀ e ∈ Finset.Ico 1 t, 0 < M e) :
    Real.log (∏ e ∈ Finset.Ico 1 t, M e : ℕ) =
      ∑ e ∈ Finset.Ico 1 t, Real.log (M e) := by
  rw [Nat.cast_prod, Real.log_prod (fun e he => by exact_mod_cast (hM e he).ne')]

end Compaction.CertificateAssembly

#print axioms Compaction.CertificateAssembly.multiply_with_budget
#print axioms Compaction.CertificateAssembly.across_twists
