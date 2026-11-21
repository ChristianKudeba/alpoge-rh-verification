import Compaction.AllOddMinusCertificate

namespace Compaction.OddMinusBudgetBound

theorem polynomial_envelope (C : ℝ) (hC : 0 ≤ C) (N t : ℕ)
    (hN : 1 ≤ N) (ht : 1 ≤ t) :
    AllOddMinusCertificate.logBudget C N t ≤
      (2 * C + 4) * ((N : ℝ) * t) ^ 9 := by
  let n : ℝ := N
  let s : ℝ := t
  let u := n * s
  have hn : 1 ≤ n := by change (1 : ℝ) ≤ (N : ℝ); exact_mod_cast hN
  have hs : 1 ≤ s := by change (1 : ℝ) ≤ (t : ℝ); exact_mod_cast ht
  have hu : 1 ≤ u := one_le_mul_of_one_le_of_one_le hn hs
  have hn0 : 0 ≤ n := by linarith
  have hs0 : 0 ≤ s := by linarith
  have hlog : Real.log u ≤ u := by
    have h := Real.log_le_sub_one_of_pos (show 0 < u by linarith)
    linarith
  have hfirst : n * s ^ 2 * Real.log u ≤ u ^ 9 := by
    calc
      _ ≤ n * s ^ 2 * u := mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = n ^ 2 * s ^ 3 := by dsimp [u]; ring
      _ ≤ n ^ 3 * s ^ 3 :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hn (by norm_num : 2 ≤ 3)) (by positivity)
      _ = u ^ 3 := by dsimp [u]; ring
      _ ≤ u ^ 9 := pow_le_pow_right₀ hu (by norm_num)
  have hsecond : n ^ 9 * s ^ 4 ≤ u ^ 9 := by
    calc
      _ ≤ n ^ 9 * s ^ 9 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hs (by norm_num : 4 ≤ 9)) (by positivity)
      _ = u ^ 9 := by dsimp [u]; ring
  have hthird : n ^ 2 * s ≤ u ^ 9 := by
    calc
      _ ≤ n ^ 2 * s ^ 2 :=
        mul_le_mul_of_nonneg_left (by simpa using pow_le_pow_right₀ hs (by norm_num : 1 ≤ 2)) (by positivity)
      _ = u ^ 2 := by dsimp [u]; ring
      _ ≤ u ^ 9 := pow_le_pow_right₀ hu (by norm_num)
  dsimp only [AllOddMinusCertificate.logBudget]
  rw [mul_comm (t : ℝ) (N : ℝ)]
  change 3 * n * s ^ 2 * Real.log u + (2 * C * n ^ 7 * s ^ 3 + 1) * s * n ^ 2 ≤
    (2 * C + 4) * u ^ 9
  calc
    _ = 3 * (n * s ^ 2 * Real.log u) + 2 * C * (n ^ 9 * s ^ 4) + n ^ 2 * s := by ring
    _ ≤ 3 * u ^ 9 + 2 * C * u ^ 9 + u ^ 9 := by gcongr
    _ = _ := by ring

end Compaction.OddMinusBudgetBound

#print axioms Compaction.OddMinusBudgetBound.polynomial_envelope
