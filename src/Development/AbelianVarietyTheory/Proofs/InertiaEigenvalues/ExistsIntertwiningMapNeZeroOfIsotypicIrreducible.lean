import Mathlib
import Lemmata.IsotypicGeneration

namespace GlobalTheory.IsoSep

open Representation

theorem main : ∀ (H V W : Type) [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ H V) (σ : Representation ℂ H W), σ.IsIrreducible → (⨆ f : σ.IntertwiningMap ρ, LinearMap.range f.toLinearMap) = ⊤ → (∀ (W' : Type) [AddCommGroup W'] [Module ℂ W'] (σ' : Representation ℂ H W'), σ'.IsIrreducible → ∀ f' : σ'.IntertwiningMap ρ, f' ≠ 0 → Nonempty (σ.Equiv σ')) → ∀ v : V, v ≠ 0 → ∃ p : ρ.IntertwiningMap σ, p v ≠ 0 := by
  intro H V W _ _ _ _ _ ρ σ hσ hsum _ v hv
  apply Lemmata.IsotypicGeneration.intertwiner σ ρ hσ ?_ hv
  apply top_unique
  rw [← hsum]
  exact iSup_le fun f => le_iSup_of_le
    ⟨f.toLinearMap, fun g x => IntertwiningMap.isIntertwining σ ρ f g x⟩ le_rfl

end GlobalTheory.IsoSep
