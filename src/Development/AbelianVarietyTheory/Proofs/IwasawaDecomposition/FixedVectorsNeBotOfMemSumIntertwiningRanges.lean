import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IrreducibleProjectionExists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed

namespace GlobalTheory.UnrLoc

theorem fixed_ne_bot_of_mem_iSup_range :
    ∀ {G V X : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup X] [Module ℂ X]
      {ι : Type} [Finite ι] {σ : Representation ℂ G V}, σ.IsIrreducible →
      ∀ {ρ : Representation ℂ G X} (T : ι → σ.IntertwiningMap ρ) (K : Subgroup G) {f : X},
      f ∈ ⨆ j, LinearMap.range (T j).toLinearMap → f ≠ 0 → (∀ k ∈ K, ρ k f = f) →
      GlobalTheory.PRep.fixed σ K ≠ ⊥ := by
  intro G V X _ _ _ _ _ ι _ σ hσ ρ T K f hf hf0 hfix
  let Y : Submodule ℂ X := ⨆ j, LinearMap.range (T j).toLinearMap
  let P := {p : V →ₗ[ℂ] X //
    (∀ (g : G) (v : V), p (σ g v) = ρ g (p v)) ∧ LinearMap.range p ≤ Y}
  have hY : Y ≤ ⨆ p : P, LinearMap.range p.1 := by
    refine iSup_le fun j => ?_
    exact le_iSup (fun p : P => LinearMap.range p.1)
      ⟨(T j).toLinearMap, (T j).isIntertwining,
        le_iSup (fun j => LinearMap.range (T j).toLinearMap) j⟩
  obtain ⟨p, hp, hp0⟩ := UpperTheory.irreducible_projection_exists σ ρ hσ Y hY hf hf0
  rw [Submodule.ne_bot_iff]
  refine ⟨p f, ?_, hp0⟩
  intro k
  simpa using (hp (k : G) f hf).symm.trans (congrArg p (hfix _ k.2))

end GlobalTheory.UnrLoc
