import Compaction.BernoulliProductCertificate

/-! A conductor-only integer certificate for lengths admitting the archive's
pointwise Bernoulli comparison. The comparison is an explicit hypothesis,
including finiteness; it can be supplied by `Odd.atPrime` for odd primes not
dividing the field degree. No comparison for the plus eigenspace is assumed.
-/

noncomputable section
namespace Compaction.BernoulliLengthCertificate

open Finset UpperTheory.V.Bern

theorem char_count_le {N : ℕ} [NeZero N] (P : Set (Subgroup (ZMod N)ˣ)) :
    (charSet ℂ P).ncard ≤ N := by
  calc
    (charSet ℂ P).ncard ≤ Nat.card (DirichletCharacter ℂ N) := Set.ncard_le_card _
    _ = N.totient := DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ N
    _ ≤ N := Nat.totient_le N

/-- One positive integer, depending only on conductor and twist, bounds every
eligible prime length. The premise is precisely a finite-length comparison
with a parity-compatible subsum of Bernoulli valuations. -/
theorem universal_at_twist {N : ℕ} [NeZero N] (e : ℕ) :
    ∃ M : ℕ, 0 < M ∧ Real.log M ≤ N * Real.log (bnd N (e + 1)) ∧
      ∀ (eligible : ℕ → Prop) (length : ℕ → ℕ∞),
      (∀ (l : ℕ) [Fact l.Prime], eligible l → length l ≠ ⊤ ∧
      ∃ T : Finset (DirichletCharacter (PadicAlgCl l) N),
        (T : Set _) ⊆ charSet (PadicAlgCl l) (parKer N (e + 1)) ∧
        ((length l).toNat : ℝ) * Real.log l ≤
          ∑ χ ∈ T, -Real.log ‖(den N (e + 1) : PadicAlgCl l) * Bprim (e + 1) χ‖) →
      ∀ (l : ℕ) [Fact l.Prime], eligible l → length l ≤ (M.factorization l : ℕ∞) := by
  obtain ⟨M, hM, hlog, hv⟩ := BernoulliProductCertificate.exists_integer
    (e + 1) (parKer N (e + 1)) (by omega) Set.Subset.rfl
  refine ⟨M, hM, hlog.trans ?_, ?_⟩
  · exact mul_le_mul_of_nonneg_right (by exact_mod_cast char_count_le (parKer N (e + 1)))
      (Real.log_nonneg (b_denupper (e + 1) (1 : DirichletCharacter ℂ N)).2.2)
  · intro eligible length comparison l _ hl
    obtain ⟨hfinite, T, hT, hlength⟩ := comparison l hl
    have hlogp : 0 < Real.log l := Real.log_pos (by exact_mod_cast (Fact.out : l.Prime).one_lt)
    have hlen : (length l).toNat ≤ M.factorization l := by
      have hr : ((length l).toNat : ℝ) ≤ (M.factorization l : ℝ) :=
        le_of_mul_le_mul_right (hlength.trans (hv l T hT)) hlogp
      exact_mod_cast hr
    rw [← ENat.natCast_toNat hfinite]
    exact_mod_cast hlen

theorem at_twist {N : ℕ} [NeZero N] (e : ℕ) (eligible : ℕ → Prop)
    (length : ℕ → ℕ∞)
    (comparison : ∀ (l : ℕ) [Fact l.Prime], eligible l → length l ≠ ⊤ ∧
      ∃ T : Finset (DirichletCharacter (PadicAlgCl l) N),
        (T : Set _) ⊆ charSet (PadicAlgCl l) (parKer N (e + 1)) ∧
        ((length l).toNat : ℝ) * Real.log l ≤
          ∑ χ ∈ T, -Real.log ‖(den N (e + 1) : PadicAlgCl l) * Bprim (e + 1) χ‖) :
    ∃ M : ℕ, 0 < M ∧ Real.log M ≤ N * Real.log (bnd N (e + 1)) ∧
      ∀ (l : ℕ) [Fact l.Prime], eligible l → length l ≤ (M.factorization l : ℕ∞) := by
  obtain ⟨M, hM, hlog, h⟩ := universal_at_twist (N := N) e
  exact ⟨M, hM, hlog, h eligible length comparison⟩

end Compaction.BernoulliLengthCertificate

#print axioms Compaction.BernoulliLengthCertificate.char_count_le
#print axioms Compaction.BernoulliLengthCertificate.universal_at_twist
#print axioms Compaction.BernoulliLengthCertificate.at_twist
