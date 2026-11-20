import Mathlib

open Complex DirichletCharacter

theorem Formalism.VW.gammaFactor_ne_zero {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 0 < s.re) : gammaFactor χ s ≠ 0 := by
  rcases χ.even_or_odd with h | h
  · rw [h.gammaFactor_def]; exact Gammaℝ_ne_zero_of_re_pos hs
  · rw [h.gammaFactor_def]; exact Gammaℝ_ne_zero_of_re_pos (by rw [add_re, one_re]; linarith)

theorem Formalism.VW.differentiable_gammaFactor_inv {N : ℕ} (χ : DirichletCharacter ℂ N) :
    Differentiable ℂ (fun s => (DirichletCharacter.gammaFactor χ s)⁻¹) := by
  rcases χ.even_or_odd with h | h <;> simp only [h.gammaFactor_def]
  · exact Complex.differentiable_Gammaℝ_inv
  · exact Complex.differentiable_Gammaℝ_inv.comp (differentiable_id.add_const 1)

theorem Formalism.VW.rootNumber_ne_zero {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) : χ.rootNumber ≠ 0 := by
  intro h
  have h1 := hχ.completedLFunction_one_sub (-1)
  rw [h, mul_zero, zero_mul] at h1
  have h2 := χ.LFunction_eq_completed_div_gammaFactor (1 - -1) (Or.inl (by norm_num))
  rw [h1, zero_div] at h2
  exact χ.LFunction_ne_zero_of_one_le_re (Or.inr (by norm_num)) (by norm_num) h2
