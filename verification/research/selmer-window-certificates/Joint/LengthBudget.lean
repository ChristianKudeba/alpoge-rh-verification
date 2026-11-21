import Mathlib

/-! The finite sums in Alpöge’s conductor-one cohomological bound have an
equivalent formulation in terms of divisibility of a single positive integer. -/

namespace Joint.LengthBudget

private def mass (L : Nat.Primes → ℕ) (S : Finset Nat.Primes) : ℕ :=
  ∏ p ∈ S, (p:ℕ)^(L p)

private theorem mass_pos (L : Nat.Primes → ℕ) (S : Finset Nat.Primes) : 0 < mass L S :=
  Finset.prod_pos (fun p _ => pow_pos p.2.pos _)

private theorem log_mass (L : Nat.Primes → ℕ) (S : Finset Nat.Primes) :
    Real.log (mass L S) = ∑ p ∈ S, Real.log (p:ℕ) * L p := by
  unfold mass
  rw [Nat.cast_prod,Real.log_prod (fun p _ => Nat.cast_ne_zero.mpr (pow_ne_zero _ p.2.ne_zero))]
  apply Finset.sum_congr rfl
  intro p _
  rw [Nat.cast_pow,Real.log_pow,mul_comm]

private theorem mass_dvd {L : Nat.Primes → ℕ} {M : ℕ}
    (h : ∀ p : Nat.Primes, (p:ℕ)^(L p) ∣ M) (S : Finset Nat.Primes) : mass L S ∣ M := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [mass]
  | @insert p S hp hS =>
    have cop : ((p:ℕ)^(L p)).Coprime (mass L S) := by
      apply Nat.Coprime.prod_right
      intro q hq
      have hpq : (p:ℕ) ≠ (q:ℕ) := fun hh => hp (Subtype.ext hh ▸ hq)
      exact (((Nat.coprime_primes p.2 q.2).2 hpq).pow_left _).pow_right _
    simpa [mass,hp] using cop.mul_dvd_of_dvd_of_dvd (h p) hS

/-- All finite subsums are bounded exactly when one integer in the prescribed
size budget contains every required prime power. The constant B is unchanged. -/
theorem bounded_iff_common_multiple (L : Nat.Primes → ℕ) (B : ℝ) :
    (∀ S : Finset Nat.Primes, ∑ p ∈ S, Real.log (p:ℕ) * L p ≤ B) ↔
      ∃ M : ℕ, 0 < M ∧ Real.log M ≤ B ∧ ∀ p : Nat.Primes, (p:ℕ)^(L p) ∣ M := by
  classical
  constructor
  · intro h
    let bound := ⌊Real.exp B⌋₊
    let attained (a : ℕ) := ∃ S : Finset Nat.Primes, mass L S = a
    let M := Nat.findGreatest attained bound
    have hb (S : Finset Nat.Primes) : mass L S ≤ bound :=
      Nat.le_floor ((Real.log_le_iff_le_exp (by exact_mod_cast mass_pos L S)).mp
        (by rw [log_mass]; exact h S))
    have h0 : attained (mass L ∅) := ⟨∅,rfl⟩
    obtain ⟨S,hS⟩ : attained M := Nat.findGreatest_spec (hb ∅) h0
    refine ⟨M,hS ▸ mass_pos L S,by rw [← hS,log_mass]; exact h S,fun p => ?_⟩
    have hle : mass L (insert p S) ≤ M :=
      Nat.le_findGreatest (hb _) (show attained (mass L (insert p S)) from ⟨_,rfl⟩)
    have hge : M ≤ mass L (insert p S) := by
      rw [← hS]
      exact Nat.le_of_dvd (mass_pos _ _) (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.subset_insert _ _))
    rw [← le_antisymm hle hge]
    exact Finset.dvd_prod_of_mem _ (Finset.mem_insert_self p S)
  · rintro ⟨M,hM,hl,hp⟩ S
    rw [← log_mass]
    exact (Real.log_le_log (by exact_mod_cast mass_pos L S)
      (by exact_mod_cast Nat.le_of_dvd hM (mass_dvd hp S))).trans hl

/-- This is the finite-subset bound in VVle for one choice of local data.
The non-infinite length condition is retained since ENat.toNat sends infinity to zero. -/
theorem local_lengths_iff (a : Nat.Primes → ℕ → ℕ∞) (t : ℕ) (B : ℝ) :
    ((∀ (p : Nat.Primes) (e : ℕ), 0 < e → e < t → a p e ≠ ⊤) ∧
      ∀ S : Finset Nat.Primes, ∑ p ∈ S, Real.log (p:ℕ) *
        ∑ e ∈ Finset.Ico 1 t, ((a p e).toNat : ℝ) ≤ B) ↔
    ((∀ (p : Nat.Primes) (e : ℕ), 0 < e → e < t → a p e ≠ ⊤) ∧
      ∃ M : ℕ, 0 < M ∧ Real.log M ≤ B ∧ ∀ p : Nat.Primes,
        (p:ℕ)^(∑ e ∈ Finset.Ico 1 t, (a p e).toNat) ∣ M) := by
  apply and_congr_right
  intro _
  simpa only [Nat.cast_sum] using
    bounded_iff_common_multiple (fun p => ∑ e ∈ Finset.Ico 1 t, (a p e).toNat) B

end Joint.LengthBudget

#print axioms Joint.LengthBudget.bounded_iff_common_multiple
#print axioms Joint.LengthBudget.local_lengths_iff


