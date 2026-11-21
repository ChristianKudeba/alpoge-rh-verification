import Joint.TwistCohomologyBound
import CompanionTheory.AutomorphicTheory.PadicCyclotomicFields.GcohTop
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PoitouTateDualityOfNormalised
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PoitouTateNineTerm.PoitouTateNormalisedHolds
import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.Kmono

/-! Shared closed arithmetic inputs, without importing the general
Ferrero--Washington proof or a dyadic certificate route. -/

noncomputable section
namespace Compaction.ClosedCohomologyInputs
open Formalism.GaloisCohomology UpperTheory.V
open CompanionTheory.LocalTateOrthogonality.Gcoh

theorem duality : GlobalTheory.Published.PoitouTateDuality :=
  GlobalTheory.PoitouTateConj.poitouTateDuality_of_normalised
    PositivityTheory.Lit1.PTN.poitouTateNormalised_holds

theorem local_finiteness : LocalFinitenessK := top_locfin

theorem local_tate : LocalTateDualityK := top_tate

/-- One high-twist exponent works simultaneously for all fields and characters.
Anton's class-counting supplier avoids the older K-theory bridge. -/
theorem high_twist : ∃ CK : ℝ, 1 ≤ CK ∧ LemmaK CK := by
  obtain ⟨C, hC⟩ := Joint.TwistCohomologyBound.exists_exponent duality local_finiteness local_tate
  refine ⟨max C 1, le_max_right _ _, ?_⟩
  exact Win.kmono C (max C 1) (le_max_left _ _) hC

end Compaction.ClosedCohomologyInputs

#print axioms Compaction.ClosedCohomologyInputs.duality
#print axioms Compaction.ClosedCohomologyInputs.local_finiteness
#print axioms Compaction.ClosedCohomologyInputs.local_tate
#print axioms Compaction.ClosedCohomologyInputs.high_twist
