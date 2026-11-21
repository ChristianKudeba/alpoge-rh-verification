import Formalism.ZetaRealNonvanish

open Complex Set Filter Topology

noncomputable section

namespace Formalism

/-- A local holomorphic differential equation determines nonvanishing throughout a connected
domain, by the identity principle and the nonvanishing theorem for logarithmic derivatives. -/
theorem logDerivZeroFree_of_eventuallyEq (h : LogDerivZeroFree)
    {P q : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hUc : IsPreconnected U)
    (hP : Differentiable ℂ P) (hne : ∃ z, P z ≠ 0) (hq : DifferentiableOn ℂ q U)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) (heq : deriv P =ᶠ[𝓝 z₀] fun z => q z * P z) :
    ∀ s ∈ U, P s ≠ 0 := by
  have hid := (hP.deriv.differentiableOn.analyticOnNhd hU).eqOn_of_preconnected_of_eventuallyEq
    ((hq.mul hP.differentiableOn).analyticOnNhd hU) hUc hz₀ heq
  exact h P q U hU hP hne hq (fun s hs => hid hs)

end Formalism
