import Compaction.OddMinusCertificate
import Compaction.FactorialSmallPrimeCertificate

/-! All odd-prime minus-eigenspace lengths are covered by the product of one
Bernoulli certificate and one factorial certificate. No field-specific list of
degree-dividing primes is needed: every such prime is at most the conductor.
The plus eigenspace and the prime two remain outside this theorem.
-/

noncomputable section
namespace Compaction.AllOddMinusCertificate

open NumberField Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Odd

def logBudget (C : ℝ) (N t : ℕ) : ℝ :=
  3 * (N : ℝ) * (t : ℝ) ^ 2 * Real.log ((t : ℝ) * N) +
    (2 * C * (N : ℝ) ^ 7 * (t : ℝ) ^ 3 + 1) * t * (N : ℝ) ^ 2

/-- The same M works for all CM subfields of the conductor-N cyclotomic field,
all algebraic closures, and every family of local data. -/
theorem universal {N : ℕ} [NeZero N] (C : ℝ) (hC : 0 ≤ C) (t : ℕ) (ht : 2 ≤ t) :
    ∃ M : ℕ, 0 < M ∧ Real.log M ≤ logBudget C N t ∧
      ∀ (hPB : PsiBound) (hSt : StickBound C)
        (E Ω : Type) [Field E] [NumberField E] [IsCMField E]
        [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω],
        Nonempty (E →ₐ[ℚ] CyclotomicField N ℚ) →
        ∀ (ld : ∀ (p : ℕ) [Fact p.Prime], LData E Ω p) (p : ℕ) [Fact p.Prime],
          p ≠ 2 → ∑ e ∈ Finset.Ico 1 t, minusLen (ld p) e ≤ (M.factorization p : ℕ∞) := by
  obtain ⟨M₀, hM₀, hlog₀, hBern⟩ := OddMinusCertificate.universal (N := N) t ht
  let A := 2 * C * (N : ℝ) ^ 7 * (t : ℝ) ^ 3
  have hA : 0 ≤ A := by dsimp [A]; positivity
  obtain ⟨M₁, hM₁, hlog₁, hsmall⟩ := FactorialSmallPrimeCertificate.universal N t (NeZero.pos N) A hA
  refine ⟨M₀ * M₁, Nat.mul_pos hM₀ hM₁, ?_, ?_⟩
  · change Real.log ((M₀ * M₁ : ℕ) : ℝ) ≤ _
    rw [Nat.cast_mul, Real.log_mul (Nat.cast_ne_zero.mpr hM₀.ne') (Nat.cast_ne_zero.mpr hM₁.ne')]
    exact add_le_add hlog₀ hlog₁
  · intro hPB hSt E Ω _ _ _ _ _ _ hemb ld p _ hp2
    have hnN := FactorialSmallPrimeCertificate.degree_le_conductor E hemb
    let length (p e : ℕ) : ℕ∞ := if hp : p.Prime then
      @minusLen E Ω _ _ _ _ _ _ p ⟨hp⟩ (@ld p ⟨hp⟩) e else 0
    have hlength (p : ℕ) [Fact p.Prime] (e : ℕ) : length p e = minusLen (ld p) e := by
      simp only [length, dif_pos (Fact.out : p.Prime)]
    rw [Nat.factorization_mul hM₀.ne' hM₁.ne', Finsupp.add_apply, Nat.cast_add]
    by_cases hpN : p ≤ N
    · have hs := hsmall (fun p => p ≠ 2) length (by
        intro l _ hlN hl2 e he
        obtain ⟨hfinite, hb⟩ := hSt E Ω N (NeZero.pos N) hemb l (ld l) (Or.inl hl2)
          e (Finset.mem_Ico.mp he).1
        have hx := FactorialSmallPrimeCertificate.length_le_ceiling C hC N t l
          (Module.finrank ℚ E) e (NeZero.pos N) (Fact.out : l.Prime).two_le hlN hnN
          (Finset.mem_Ico.mp he).1 (Finset.mem_Ico.mp he).2 (minusLen (ld l) e) hfinite hb
        simpa only [hlength, A] using hx) p hpN hp2
      have hs' : ∑ e ∈ Finset.Ico 1 t, minusLen (ld p) e ≤ (M₁.factorization p : ℕ∞) := by
        simpa only [hlength] using hs
      exact hs'.trans (le_add_left le_rfl)
    · have hpd : ¬ p ∣ Module.finrank ℚ E := by
        intro hd
        exact hpN ((Nat.le_of_dvd Module.finrank_pos hd).trans hnN)
      exact (hBern hPB E Ω hemb ld p hp2 hpd).trans (le_add_right le_rfl)

end Compaction.AllOddMinusCertificate

#print axioms Compaction.AllOddMinusCertificate.universal
