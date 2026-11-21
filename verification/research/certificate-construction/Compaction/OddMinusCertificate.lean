import Compaction.BernoulliTwistCertificate
import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.AtPrime
import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ActEx

/-! Actual odd-minus Selmer lengths admit one conductor-only integer certificate.
The arithmetic comparison is the archive's `Odd.atPrime`, using its explicit
`PsiBound` input. No comparison for plus eigenspaces or degree-dividing primes
is claimed here.
-/

noncomputable section
namespace Compaction.OddMinusCertificate

open NumberField Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Odd

/-- M is chosen before the field, algebraic closure and local-data family.
Only N and t enter its Archimedean bound. -/
theorem universal {N : ℕ} [NeZero N] (t : ℕ) (ht : 2 ≤ t) :
    ∃ M : ℕ, 0 < M ∧ Real.log M ≤
      3 * (N : ℝ) * (t : ℝ) ^ 2 * Real.log ((t : ℝ) * N) ∧
      ∀ (hPB : PsiBound) (E Ω : Type) [Field E] [NumberField E] [IsCMField E]
        [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω],
        Nonempty (E →ₐ[ℚ] CyclotomicField N ℚ) →
        ∀ (ld : ∀ (p : ℕ) [Fact p.Prime], LData E Ω p) (l : ℕ) [Fact l.Prime],
          l ≠ 2 → ¬ l ∣ Module.finrank ℚ E →
          ∑ e ∈ Finset.Ico 1 t, minusLen (ld l) e ≤ (M.factorization l : ℕ∞) := by
  obtain ⟨M, hM, hlog, hcert⟩ := BernoulliTwistCertificate.universal_across_twists
    (N := N) t ht
  refine ⟨M, hM, hlog, ?_⟩
  intro hPB E Ω _ _ _ _ _ _ hemb ld l _ hl2 hld
  obtain ⟨ρ, hρ⟩ := actEx E Ω N hemb
  let length (p e : ℕ) : ℕ∞ := if hp : p.Prime then
    @minusLen E Ω _ _ _ _ _ _ p ⟨hp⟩ (@ld p ⟨hp⟩) e else 0
  have hlength (p : ℕ) [Fact p.Prime] (e : ℕ) : length p e = minusLen (ld p) e := by
    simp only [length, dif_pos (Fact.out : p.Prime)]
  have h := hcert (fun p => p ≠ 2 ∧ ¬ p ∣ Module.finrank ℚ E) length (by
    intro e he p _ hp
    obtain ⟨hfinite, T, hT, hbound⟩ := atPrime hPB E Ω N ρ hρ p (ld p)
      hp.1 hp.2 e (Finset.mem_Ico.mp he).1
    refine ⟨?_, T, fun χ hχ => (hT hχ).2, ?_⟩
    · simpa only [hlength] using hfinite
    · simpa only [hlength, alN] using hbound) l ⟨hl2, hld⟩
  simpa only [hlength] using h

end Compaction.OddMinusCertificate

#print axioms Compaction.OddMinusCertificate.universal
