import Mathlib

namespace Compaction.PolynomialAbsorption

/-- Enlarge the height exponent to absorb one fixed polynomial error term.
The new exponent is chosen before u. -/
theorem exists_exponent (K C : ℝ) (hK : 0 ≤ K) :
    ∃ D : ℝ, C ≤ D ∧ ∀ u : ℝ, 2 ≤ u → u ^ C + K * u ^ (9 : ℝ) ≤ u ^ D := by
  let n := ⌈K + 1⌉₊
  let b := |C| + 9
  let D := b + (n : ℝ)
  have hbC : C ≤ b := by dsimp [b]; linarith [le_abs_self C]
  refine ⟨D, hbC.trans (le_add_of_nonneg_right (Nat.cast_nonneg n)), ?_⟩
  intro u hu
  have hu1 : 1 ≤ u := by linarith
  have hu0 : 0 < u := by linarith
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hn : K + 1 ≤ (n : ℝ) := Nat.le_ceil _
  have hbin := one_add_mul_le_pow (show (-2 : ℝ) ≤ u - 1 by linarith) n
  rw [show (1 : ℝ) + (u - 1) = u by ring] at hbin
  have hnPow : K + 1 ≤ u ^ n := by
    have hmul : (n : ℝ) ≤ (n : ℝ) * (u - 1) := by nlinarith
    linarith
  have hfirst : u ^ C ≤ u ^ b := Real.rpow_le_rpow_of_exponent_le hu1 hbC
  have hsecond : u ^ (9 : ℝ) ≤ u ^ b :=
    Real.rpow_le_rpow_of_exponent_le hu1 (by dsimp [b]; linarith [abs_nonneg C])
  calc
    u ^ C + K * u ^ (9 : ℝ) ≤ (K + 1) * u ^ b := by
      have h := mul_le_mul_of_nonneg_left hsecond hK
      nlinarith
    _ ≤ (u ^ n) * u ^ b := mul_le_mul_of_nonneg_right hnPow (Real.rpow_nonneg hu0.le b)
    _ = u ^ b * u ^ (n : ℝ) := by rw [Real.rpow_natCast]; ring
    _ = u ^ D := (Real.rpow_add hu0 b (n : ℝ)).symm

end Compaction.PolynomialAbsorption

#print axioms Compaction.PolynomialAbsorption.exists_exponent
