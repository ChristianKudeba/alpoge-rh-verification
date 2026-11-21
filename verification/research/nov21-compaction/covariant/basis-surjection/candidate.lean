import Mathlib

noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Module

private theorem exists_linear_rightInverse_of_surjective {R : Type} [CommRing R] {m₁ m₂ : ℕ}
    (f : (Fin m₁ → R) →ₗ[R] (Fin m₂ → R)) (hf : Function.Surjective f) :
    ∃ s : (Fin m₂ → R) →ₗ[R] (Fin m₁ → R), ∀ y, f (s y) = y := by
  obtain ⟨s, hs⟩ := f.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hf)
  exact ⟨s, fun y => LinearMap.congr_fun hs y⟩

theorem exists_basis_of_surjective {R : Type} [CommRing R] [IsLocalRing R] {m₁ m₂ : ℕ}
    (f : (Fin m₁ → R) →ₗ[R] (Fin m₂ → R)) (hf : Function.Surjective f) :
    ∃ B : Module.Basis (Fin m₂ ⊕ Fin (m₁ - m₂)) R (Fin m₁ → R),
      (∀ j, f (B (Sum.inl j)) = Pi.single j 1) ∧ ∀ j, f (B (Sum.inr j)) = 0 := by
  obtain ⟨s, hs⟩ := exists_linear_rightInverse_of_surjective f hf
  have hfk : ∀ k : LinearMap.ker f, f (k : Fin m₁ → R) = 0 := fun k => LinearMap.mem_ker.mp k.2
  let g : (Fin m₂ → R) × LinearMap.ker f →ₗ[R] (Fin m₁ → R) :=
    LinearMap.coprod s (LinearMap.ker f).subtype
  have hg : Function.Bijective g := by
    constructor
    · rintro ⟨u, k⟩ ⟨v, l⟩ h
      have huv : u = v := by
        simpa only [g, LinearMap.coprod_apply, Submodule.subtype_apply, map_add, hs, hfk, add_zero] using congrArg f h
      apply Prod.ext huv
      apply Subtype.ext
      simpa [g, huv] using h
    · intro x
      refine ⟨(f x, ⟨x - s (f x), by simp only [LinearMap.mem_ker, map_sub, hs, sub_self]⟩), ?_⟩
      change s (f x) + (x - s (f x)) = x
      abel
  let e := LinearEquiv.ofBijective g hg
  have he : ∀ p, f (e p) = p.1 := fun p => by
    change f (s p.1 + (p.2 : Fin m₁ → R)) = p.1
    rw [map_add, hs, hfk, add_zero]
  let r := (LinearMap.snd R (Fin m₂ → R) (LinearMap.ker f)).comp e.symm.toLinearMap
  have hrk : ∀ k : LinearMap.ker f, r k = k := by
    intro k
    have hk : e (0, k) = (k : Fin m₁ → R) := by simp [e, g]
    change (e.symm (k : Fin m₁ → R)).2 = k
    rw [← hk, e.symm_apply_apply]
  have hproj : Module.Projective R (LinearMap.ker f) :=
    Module.Projective.of_split (LinearMap.ker f).subtype r (LinearMap.ext fun k => by
      rw [LinearMap.comp_apply, Submodule.subtype_apply, hrk, LinearMap.id_apply])
  have hfin : Module.Finite R (LinearMap.ker f) :=
    Module.Finite.of_surjective r (fun k => ⟨k, hrk k⟩)
  have hfree : Module.Free R (LinearMap.ker f) := Module.free_of_flat_of_isLocalRing
  let bk := Module.Free.chooseBasis R (LinearMap.ker f)
  let bp := (Pi.basisFun R (Fin m₂)).prod bk
  let b := bp.map e
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex R (LinearMap.ker f)) = m₁ - m₂ := by
    have h1 := Module.finrank_eq_card_basis b
    rw [Module.finrank_fin_fun, Fintype.card_sum, Fintype.card_fin] at h1
    omega
  have hb : ∀ i, f (b i) = (bp i).1 := fun i => by
    rw [Basis.map_apply, he]
  refine ⟨b.reindex (Equiv.sumCongr (Equiv.refl _) (Fintype.equivFinOfCardEq hcard)),
    fun j => ?_, fun j => ?_⟩
  · rw [Basis.reindex_apply, hb]
    simp [bp, Basis.prod_apply]
  · rw [Basis.reindex_apply, hb]
    simp [bp, Basis.prod_apply]

end Formalism.MainNotions.N.Ln03.Pf
