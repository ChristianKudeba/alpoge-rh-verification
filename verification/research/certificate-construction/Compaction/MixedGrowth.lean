import Mathlib

/-! Fixed powers and subexponential arithmetic budgets fit the exact Selmer
window budget. Constants are fixed before the scale x, and the power gap is
strict. These estimates supply no arithmetic certificate by themselves. -/

noncomputable section
namespace Compaction.MixedGrowth
open Filter

theorem scaled_rpow (C θ δ eps : ℝ) (hθ : 0 < θ) (hgap : δ < eps) :
    ∀ᶠ x : ℝ in atTop, C * x ^ δ ≤ θ * x ^ eps := by
  have h := (tendsto_rpow_atTop (sub_pos.mpr hgap)).eventually
    (eventually_ge_atTop (C / θ))
  filter_upwards [h, eventually_gt_atTop (0 : ℝ)] with x hx hx0
  have hc : C ≤ θ * x ^ (eps - δ) := by
    simpa only [mul_comm] using (div_le_iff₀ hθ).mp hx
  calc
    C * x ^ δ ≤ (θ * x ^ (eps - δ)) * x ^ δ :=
      mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hx0.le _)
    _ = θ * x ^ eps := by
      rw [mul_assoc, ← Real.rpow_add hx0]
      congr 2
      ring

theorem exponential_budget (K C δ eps : ℝ) (hK : 0 < K) (heps : 0 < eps)
    (hgap : δ < eps) :
    ∀ᶠ x : ℝ in atTop,
      K * Real.exp (C * x ^ δ) ≤ Real.sqrt (Real.exp (x ^ eps)) := by
  have hC := scaled_rpow C (1 / 4) δ eps (by norm_num) hgap
  have hK' := scaled_rpow (Real.log K) (1 / 4) 0 eps (by norm_num) heps
  filter_upwards [hC, hK'] with x hx hk
  have he : Real.log K + C * x ^ δ ≤ x ^ eps / 2 := by
    simp only [Real.rpow_zero, mul_one] at hk
    linarith
  calc
    K * Real.exp (C * x ^ δ) = Real.exp (Real.log K + C * x ^ δ) := by
      rw [Real.exp_add, Real.exp_log hK]
    _ ≤ Real.exp (x ^ eps / 2) := Real.exp_le_exp.mpr he
    _ = Real.sqrt (Real.exp (x ^ eps)) := Real.exp_half _

theorem polynomial_budget (C k : ℝ) {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ x : ℝ in atTop, C * x ^ k ≤ Real.sqrt (Real.exp (x ^ eps)) := by
  have h := ((isLittleO_rpow_exp_pos_mul_atTop (k / eps)
    (by norm_num : (0 : ℝ) < 1 / 2)).const_mul_left C).bound (by norm_num : (0 : ℝ) < 1)
  have hc := (tendsto_rpow_atTop heps).eventually h
  filter_upwards [hc, eventually_gt_atTop (0 : ℝ)] with x hx hx0
  have hk : eps * (k / eps) = k := by field_simp
  have hp : (x ^ eps) ^ (k / eps) = x ^ k := by rw [← Real.rpow_mul hx0.le, hk]
  have hb : C * x ^ k ≤ Real.exp ((1 / 2) * x ^ eps) := by
    calc
      C * x ^ k ≤ ‖C * x ^ k‖ := le_abs_self _
      _ ≤ Real.exp ((1 / 2) * x ^ eps) := by
        simpa only [hp, one_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hx
  simpa only [one_div_mul_eq_div, Real.exp_half] using hb

theorem mixed_budget (A k K C δ eps : ℝ) (hK : 0 < K)
    (heps : 0 < eps) (hgap : δ < eps) :
    ∀ᶠ x : ℝ in atTop, A * x ^ k + K * Real.exp (C * x ^ δ) ≤
      Real.sqrt (Real.exp (x ^ eps)) := by
  filter_upwards [polynomial_budget (2 * A) k heps,
    exponential_budget (2 * K) C δ eps (by positivity) heps hgap] with x hx hy
  nlinarith

end Compaction.MixedGrowth

#print axioms Compaction.MixedGrowth.scaled_rpow
#print axioms Compaction.MixedGrowth.exponential_budget
#print axioms Compaction.MixedGrowth.mixed_budget
