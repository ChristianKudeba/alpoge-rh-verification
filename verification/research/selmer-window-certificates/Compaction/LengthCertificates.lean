import Joint.LengthBudget

/-! A valuation certificate includes the finiteness of the lengths, rather than
separately converting possibly infinite lengths to natural numbers. Based on
Anton's `Joint.LengthBudget.local_lengths_iff`. -/

namespace Compaction.LengthCertificates

def Budget (a : Nat.Primes → ℕ → ℕ∞) (t : ℕ) (B : ℝ) : Prop :=
  ∃ M : ℕ, 0 < M ∧ Real.log M ≤ B ∧ ∀ p : Nat.Primes,
    ∑ e ∈ Finset.Ico 1 t, a p e ≤ (M.factorization p : ℕ∞)

private theorem cast_sum {a : Nat.Primes → ℕ → ℕ∞} {t : ℕ}
    (hf : ∀ p e, 0 < e → e < t → a p e ≠ ⊤) (p : Nat.Primes) :
    ((∑ e ∈ Finset.Ico 1 t, (a p e).toNat : ℕ) : ℕ∞) =
      ∑ e ∈ Finset.Ico 1 t, a p e := by
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro e he
  exact ENat.natCast_toNat (hf p e (Nat.succ_le_iff.mp (Finset.mem_Ico.mp he).1)
    (Finset.mem_Ico.mp he).2)

/-- The finite-subset bound is equivalent to domination by the valuations of
one positive integer. Infinite lengths cannot satisfy the right-hand side. -/
theorem local_lengths_iff (a : Nat.Primes → ℕ → ℕ∞) (t : ℕ) (B : ℝ) :
    ((∀ p e, 0 < e → e < t → a p e ≠ ⊤) ∧
      ∀ S : Finset Nat.Primes, ∑ p ∈ S, Real.log (p : ℕ) *
        ∑ e ∈ Finset.Ico 1 t, ((a p e).toNat : ℝ) ≤ B) ↔ Budget a t B := by
  rw [Joint.LengthBudget.local_lengths_iff]
  constructor
  · rintro ⟨hf, M, hM, hB, hp⟩
    refine ⟨M, hM, hB, fun p => ?_⟩
    rw [← cast_sum hf p]
    exact_mod_cast (p.2.pow_dvd_iff_le_factorization hM.ne').mp (hp p)
  · rintro ⟨M, hM, hB, hp⟩
    have hf (p : Nat.Primes) (e : ℕ) (he : 0 < e) (ht : e < t) : a p e ≠ ⊤ := by
      apply ne_top_of_le_ne_top (ENat.natCast_ne_top _)
      exact (Finset.single_le_sum (fun i _ => (zero_le : (0 : ℕ∞) ≤ a p i))
        (Finset.mem_Ico.mpr ⟨Nat.succ_le_iff.mpr he, ht⟩)).trans (hp p)
    refine ⟨hf, M, hM, hB, fun p => ?_⟩
    apply (p.2.pow_dvd_iff_le_factorization hM.ne').mpr
    have h := hp p
    rw [← cast_sum hf p] at h
    exact_mod_cast h

end Compaction.LengthCertificates

#print axioms Compaction.LengthCertificates.local_lengths_iff
