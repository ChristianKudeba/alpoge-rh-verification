import Compaction.AllOddMinusCertificate
import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ThmBcOfPsiBound
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.Iv
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PoitouTateDualityOfNormalised
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PoitouTateNineTerm.PoitouTateNormalisedHolds
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.UnramifiedOrthogonality

/-! Supply the already proved archive arithmetic inputs for the explicit
all-odd-prime minus-eigenspace certificate. This theorem contains no unproved
height, family-connection, PsiBound or StickBound premise. It does not control
the plus eigenspace or the prime two and therefore does not establish VVle/RH.
-/

noncomputable section
namespace Compaction.AllOddMinusCertificateClosed

open NumberField Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Odd

private theorem duality : GlobalTheory.Published.PoitouTateDuality :=
  GlobalTheory.PoitouTateConj.poitouTateDuality_of_normalised
    PositivityTheory.Lit1.PTN.poitouTateNormalised_holds

theorem exists_uniform_certificates :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) [NeZero N] (t : ℕ), 2 ≤ t →
      ∃ M : ℕ, 0 < M ∧ Real.log M ≤ AllOddMinusCertificate.logBudget C N t ∧
        ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E]
          [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω],
          Nonempty (E →ₐ[ℚ] CyclotomicField N ℚ) →
          ∀ (ld : ∀ (p : ℕ) [Fact p.Prime], LData E Ω p) (p : ℕ) [Fact p.Prime],
            p ≠ 2 → ∑ e ∈ Finset.Ico 1 t, minusLen (ld p) e ≤ (M.factorization p : ℕ∞) := by
  obtain ⟨C, hC, hSt⟩ := stickBound
  refine ⟨C, hC, ?_⟩
  intro N _ t ht
  obtain ⟨M, hM, hlog, hcert⟩ := AllOddMinusCertificate.universal (N := N) C hC t ht
  exact ⟨M, hM, hlog, hcert
    (ML.iv duality GlobalTheory.CompanionTheory.Hypotheses₂.unramifiedOrthogonality) hSt⟩

end Compaction.AllOddMinusCertificateClosed

#print axioms Compaction.AllOddMinusCertificateClosed.exists_uniform_certificates
