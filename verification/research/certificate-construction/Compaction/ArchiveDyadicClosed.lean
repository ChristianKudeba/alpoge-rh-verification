import Compaction.ArchiveDyadic
import Compaction.ClosedCohomologyInputs

/-! Close every arithmetic input of the dyadic certificate theorem using
actual archive proofs. This theorem concerns the 2-primary component only;
it does not supply the odd-prime plus-height estimate or prove RH.

The high-twist supplier is Anton's Joint/TwistCohomologyBound, using the
archive's class-counting chain rather than its older K-theory bridge.
-/

noncomputable section
namespace Compaction.ArchiveDyadicClosed
open Formalism.HC Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V

theorem duality : GlobalTheory.Published.PoitouTateDuality :=
  ClosedCohomologyInputs.duality

/-- One high-twist exponent works for all fields and characters. -/
theorem high_twist : ∃ CK : ℝ, 1 ≤ CK ∧ LemmaK CK := ClosedCohomologyInputs.high_twist

/-- Unconditional dyadic certificates for every character on the original
windows. The logarithm of the explicit integer is at most
log(2)*exp(x^(4 eps/5)); J is fixed before the moving primes q,d and one Y is
chosen before every x in its square window. -/
theorem windows (ψ : PChar) {Ct eps : ℝ} (hCt : 1 ≤ Ct)
    (heps : 0 < eps) (htiny : eps < 1/52)
    (e : ℝ → ℕ) (page : ∀ x ≥ (1:ℝ), PageN eps x (e x)) :
    ∃ J : ℝ, 1 ≤ J ∧ DyadicWindows.Window ψ J Ct eps e := by
  obtain ⟨CK, hCK, hK⟩ := high_twist
  exact ArchiveDyadic.from_archive duality ClosedCohomologyInputs.local_finiteness
    ClosedCohomologyInputs.local_tate ψ hCK hCt heps htiny hK e page

end Compaction.ArchiveDyadicClosed

#print axioms Compaction.ArchiveDyadicClosed.duality
#print axioms Compaction.ArchiveDyadicClosed.high_twist
#print axioms Compaction.ArchiveDyadicClosed.windows
