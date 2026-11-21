import Mathlib

open Submodule

namespace Lemmata

/-- A nondegenerate finite pairing has an integral right-dual family whenever
its integral dual lattice is contained in the original lattice. -/
theorem exists_integral_right_dual
    {O K V ι : Type*} [CommRing O] [Field K] [Algebra O K]
    [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] [Fintype ι] [DecidableEq ι]
    (b : ι → V) (hli : LinearIndependent K b) (B : V →ₗ[K] V →ₗ[K] K)
    (hb : ∀ Q ∈ span K (Set.range b), (∀ P ∈ span K (Set.range b), B P Q = 0) → Q = 0)
    (hc : ∀ Q ∈ span K (Set.range b), (∀ P ∈ span O (Set.range b),
      B P Q ∈ Set.range (algebraMap O K)) → Q ∈ span O (Set.range b)) :
    ∃ d : ι → V, (∀ j, d j ∈ span O (Set.range b)) ∧
      ∀ i j, B (b i) (d j) = if j = i then 1 else 0 := by
  classical
  let v : (ι → K) →ₗ[K] V := Fintype.linearCombination K b
  let e : (ι → K) →ₗ[K] (ι → K) := LinearMap.pi fun i => (B (b i)).comp v
  have hv (c : ι → K) : v c ∈ span K (Set.range b) := by
    change Fintype.linearCombination K b c ∈ _
    rw [Fintype.linearCombination_apply]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (subset_span ⟨i, rfl⟩)
  have he : Function.Injective e := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c h
    apply hli.fintypeLinearCombination_injective
    change v c = v 0
    rw [map_zero]
    apply hb _ (hv c)
    intro P hP
    induction hP using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact congrFun h i
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul a x _ hx => simp [hx]
  have hs := LinearMap.surjective_of_injective he
  choose c hc' using fun j => hs (Pi.single j 1)
  have hp (i j : ι) : B (b i) (v (c j)) = if j = i then 1 else 0 := by
    simpa [e, Pi.single_apply, eq_comm] using congrFun (hc' j) i
  refine ⟨fun j => v (c j), fun j => hc _ (hv _) ?_, hp⟩
  intro P hP
  induction hP using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    refine ⟨if j = i then 1 else 0, ?_⟩
    rw [hp]
    split_ifs <;> simp
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨s, hs⟩ := hx
    obtain ⟨t, ht⟩ := hy
    exact ⟨s + t, by simp [hs, ht]⟩
  | smul a x _ hx =>
    obtain ⟨s, hs⟩ := hx
    refine ⟨a * s, ?_⟩
    rw [← algebraMap_smul K a x, map_smul, LinearMap.smul_apply, smul_eq_mul, map_mul, hs]

end Lemmata
