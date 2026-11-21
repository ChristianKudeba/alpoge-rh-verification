import Mathlib
import Lemmata.SubmersionNormalForm
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DensInfLoc

noncomputable section

namespace PI.VolStabSW

open MeasureTheory Topology

theorem changeVar_holds : ChangeVar := by
  intro n m μ hμ f hf x0 hx0
  exact SubmersionNormalForm.local_changeOfVariables μ hμ f hf x0 hx0

end PI.VolStabSW
