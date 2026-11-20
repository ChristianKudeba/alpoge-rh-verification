import Mathlib

open Complex

theorem Formalism.VW.rh_of_right (hz : ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → riemannZeta s ≠ 0) : RiemannHypothesis := by
  intro s hs htriv hs1
  rcases lt_trichotomy s.re (1 / 2) with hlt | heq | hgt
  · have hs0 : s ≠ 0 := by
      rintro rfl
      norm_num [riemannZeta_zero] at hs
    have hG : Gammaℝ s ≠ 0 := by
      intro hg
      obtain ⟨n, hn⟩ := Gammaℝ_eq_zero_iff.mp hg
      cases n with
      | zero => exact hs0 (by simpa using hn)
      | succ n => exact htriv ⟨n, by rw [hn]; push_cast; ring⟩
    rw [riemannZeta_def_of_ne_zero hs0, div_eq_zero_iff] at hs
    have hc := hs.resolve_right hG
    have ht : 1 - s ≠ 1 := fun e => hs0 (by linear_combination -e)
    have hright : 1 / 2 < (1 - s).re := by
      rw [sub_re, one_re]
      linarith
    apply False.elim (hz (1 - s) hright ht ?_)
    rw [riemannZeta_def_of_ne_zero (sub_ne_zero.mpr hs1.symm),
      completedRiemannZeta_one_sub, hc, zero_div]
  · exact heq
  · exact False.elim (hz s hgt hs1 hs)
