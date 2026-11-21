import Lemmata.IntegralDualFamily

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Submodule

theorem pb_abs {O K V : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
    (w π : O) (hw : Irreducible w) (hπ : w ^ 2 = π) (N n : ℕ) (b : Fin n → V) (hli : LinearIndependent K b)
    (B0 : V →ₗ[K] V →ₗ[K] K)
    (hb : ∀ Q ∈ span K (Set.range b), (∀ P ∈ span K (Set.range b), B0 P Q = 0) → Q = 0)
    (hc : ∀ Q ∈ span K (Set.range b), (∀ P ∈ span O (Set.range b), B0 P Q ∈ Set.range (algebraMap O K)) →
      Q ∈ span O (Set.range b))
    (hd : ∀ Q ∈ span O (Set.range b), ∀ P ∈ span O (Set.range b),
      B0 P ((algebraMap O K π ^ N) • Q) ∈ Set.range (algebraMap O K)) :
    ∃ (x x' : Fin n → V) (ka : Fin n → ℕ), (∀ i, ka i ≤ N) ∧ (∀ i, x i ∈ span O (Set.range b)) ∧
      (∀ i, x' i ∈ span O (Set.range b)) ∧
      ∀ a' i, algebraMap O K π ^ N * B0 (x i) (x' a') = if a' = i then algebraMap O K π ^ ka i else 0 := by
  classical
  obtain ⟨d, hd, hpair⟩ := Lemmata.exists_integral_right_dual b hli B0 hb hc
  refine ⟨b, d, fun _ => N, fun _ => le_rfl,
    fun i => subset_span ⟨i, rfl⟩, hd, ?_⟩
  intro j i
  rw [hpair]
  split_ifs <;> simp_all

end Formalism.MainNotions.flipOneThree.Pf

end
