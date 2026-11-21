import Formalism.ZetaNonvanishing.MellinDeriv

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Formalism

theorem mellinElem_part1 (a σ : ℝ) (h : a < σ) :
    IntegrableOn (fun x : ℝ => x ^ a * x ^ (-σ - 1)) (Ioi 1) := by
  have hi : IntegrableOn (fun x : ℝ => x ^ (a + (-σ - 1))) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
  refine hi.congr_fun (fun x hx => ?_) measurableSet_Ioi
  have hx0 : (0:ℝ) < x := lt_trans one_pos hx
  simp only
  rw [Real.rpow_add hx0]

theorem mellinElem_part2 (σ : ℝ) (h : 1 < σ) :
    IntegrableOn (fun x : ℝ => |x * Real.log x| * x ^ (-σ - 1)) (Ioi 1) := by
  set ε : ℝ := (σ - 1) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hi : IntegrableOn (fun x : ℝ => x ^ (ε - σ) / ε) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by rw [hε]; linarith) one_pos).div_const ε
  refine hi.mono' ?_ ?_
  · have : Measurable (fun x : ℝ => |x * Real.log x| * x ^ (-σ - 1)) := by fun_prop
    exact this.aestronglyMeasurable
  · refine ae_restrict_of_forall_mem measurableSet_Ioi (fun x hx => ?_)
    have hx0 : (0:ℝ) < x := lt_trans one_pos hx
    have hlog : 0 ≤ Real.log x := Real.log_nonneg (le_of_lt hx)
    have hl := Real.log_le_rpow_div hx0.le hε0
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    have e1 : x * Real.log x * x ^ (-σ - 1) = Real.log x * x ^ (-σ) := by
      rw [Real.rpow_sub_one hx0.ne']; field_simp
    rw [e1, Real.rpow_sub hx0, Real.rpow_neg hx0.le]
    calc Real.log x * (x ^ σ)⁻¹ ≤ x ^ ε / ε * (x ^ σ)⁻¹ :=
          mul_le_mul_of_nonneg_right hl (by positivity)
      _ = x ^ ε / x ^ σ / ε := by ring

theorem mellinElem_part3 (a : ℝ) (s : ℂ) (h : a < s.re) :
    ∫ x in Ioi (1:ℝ), ((x ^ a : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) = 1 / (s - a) := by
  have e : EqOn (fun x : ℝ => ((x ^ a : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1))
      (fun x : ℝ => (x : ℂ) ^ ((a : ℂ) - s - 1)) (Ioi 1) := by
    intro x hx
    have hx0 : (0:ℝ) < x := lt_trans one_pos hx
    simp only
    rw [ofReal_cpow hx0.le, ← cpow_add _ _ (ofReal_ne_zero.mpr hx0.ne')]
    ring_nf
  have hre : ((a : ℂ) - s - 1).re < -1 := by simp; linarith
  rw [setIntegral_congr_fun measurableSet_Ioi e, integral_Ioi_cpow_of_lt hre one_pos,
    ofReal_one, one_cpow, show (a : ℂ) - s - 1 + 1 = -(s - a) by ring, neg_div_neg_eq]

theorem mellinElem_part4 (s : ℂ) (h : 1 < s.re) :
    ∫ x in Ioi (1:ℝ), ((x * Real.log x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) = 1 / (s - 1) ^ 2 := by
  have hint : ∀ σ : ℝ, 1 < σ →
      IntegrableOn (fun x : ℝ => ‖(x : ℂ)‖ * x ^ (-σ - 1)) (Ioi 1) := by
    intro σ hσ
    refine (mellinElem_part1 1 σ hσ).congr_fun (fun x hx => ?_) measurableSet_Ioi
    simp [Real.rpow_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (lt_trans one_pos (show (1 : ℝ) < x from hx))]
  have hM := mellinDeriv (fun x : ℝ => (x : ℂ)) 1
    Complex.measurable_ofReal.aestronglyMeasurable hint s h
  have heq : (fun z : ℂ => (z - 1)⁻¹) =ᶠ[𝓝 s]
      (fun z : ℂ => ∫ x in Ioi (1:ℝ), (x : ℂ) * (x : ℂ) ^ (-z - 1)) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds h] with z hz
    simpa only [Real.rpow_one, Complex.ofReal_one, one_div] using
      (mellinElem_part3 1 z hz).symm
  have hs : s - 1 ≠ 0 := by
    intro hs
    have := congrArg Complex.re (sub_eq_zero.mp hs)
    simp only [Complex.one_re] at this
    linarith
  have hd := (hM.congr_of_eventuallyEq heq).unique
    (((hasDerivAt_id s).sub_const 1).inv hs)
  calc
    _ = -(∫ x in Ioi (1:ℝ), -(Real.log x : ℂ) * (x : ℂ) * (x : ℂ) ^ (-s - 1)) := by
      rw [← integral_neg]
      refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
      push_cast
      ring
    _ = 1 / (s - 1) ^ 2 := by simpa only [id_eq, neg_div, neg_neg] using congrArg Neg.neg hd

theorem mellinElem : MellinElem :=
  ⟨mellinElem_part1, mellinElem_part2, mellinElem_part3, mellinElem_part4⟩

end Formalism
