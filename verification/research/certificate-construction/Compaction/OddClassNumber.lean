import Mathlib

namespace Compaction.OddClassNumber

theorem odd_card_of_square_index_one (G : Type*) [CommGroup G] [Finite G]
    (h : (powMonoidHom 2 : G →* G).range.index = 1) : Odd (Nat.card G) := by
  have hsurj : Function.Surjective (powMonoidHom 2 : G →* G) :=
    MonoidHom.range_eq_top.mp (Subgroup.index_eq_one.mp h)
  have hinj : Function.Injective (powMonoidHom 2 : G →* G) :=
    Finite.injective_iff_surjective.mpr hsurj
  have hnot : ¬ 2 ∣ Nat.card G := by
    intro hdvd
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := G) 2 hdvd
    have hpow : g ^ 2 = 1 := by rw [← hg]; exact pow_orderOf_eq_one g
    have hgone : g = 1 := hinj (by simpa using hpow)
    rw [hgone, orderOf_one] at hg
    norm_num at hg
  exact Nat.odd_iff.mpr (by omega)

open NumberField in
theorem classNumber_odd_of_square_index_one (K : Type*) [Field K] [NumberField K]
    (h : (powMonoidHom 2 : ClassGroup (𝓞 K) →* ClassGroup (𝓞 K)).range.index = 1) :
    Odd (classNumber K) := by
  simpa only [classNumber, Nat.card_eq_fintype_card] using
    odd_card_of_square_index_one (ClassGroup (𝓞 K)) h

end Compaction.OddClassNumber

#print axioms Compaction.OddClassNumber.odd_card_of_square_index_one
#print axioms Compaction.OddClassNumber.classNumber_odd_of_square_index_one
