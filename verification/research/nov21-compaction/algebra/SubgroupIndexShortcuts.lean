import Mathlib

namespace SubgroupIndexShortcuts

variable {G : Type*} [Group G]

theorem inf_sup_normal_eq {X H U : Subgroup G} [U.Normal] (hUX : U ≤ X) :
    X ⊓ (H ⊔ U) = (X ⊓ H) ⊔ U := by
  apply SetLike.coe_injective
  simpa only [Subgroup.coe_inf, Subgroup.mul_normal] using
    (Subgroup.inf_mul_assoc X H U hUX).symm

theorem index_sup_ne_zero (H U : Subgroup G) [U.FiniteIndex] :
    (H ⊔ U).index ≠ 0 := by
  let : (H ⊔ U).FiniteIndex := Subgroup.finiteIndex_of_le le_sup_right
  exact Subgroup.FiniteIndex.index_ne_zero

theorem relIndex_sup_ne_zero (K H U : Subgroup G) [U.FiniteIndex] :
    (K ⊔ U).relIndex H ≠ 0 := by
  let : (K ⊔ U).FiniteIndex := Subgroup.finiteIndex_of_le le_sup_right
  exact Subgroup.FiniteIndex.index_ne_zero (H := (K ⊔ U).subgroupOf H)

end SubgroupIndexShortcuts

#print axioms SubgroupIndexShortcuts.inf_sup_normal_eq
#print axioms SubgroupIndexShortcuts.index_sup_ne_zero
#print axioms SubgroupIndexShortcuts.relIndex_sup_ne_zero
