import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.SecondBound

noncomputable section
namespace Joint.PowerWindow
open UpperTheory.V UpperTheory.V.Win

/-- A single exceptional value costs a factor sB in logarithmic scale. -/
theorem log_window (s B : ℝ) (hs : 1 ≤ s) (hB : 1 ≤ B) (R : ℕ) (U : ℝ)
    (hU : 0 < U) (T : Finset ℝ) (hT : T.card ≤ R) :
    ∃ y : ℝ, U/(s*(s*B)^R) ≤ y ∧ s*y ≤ U ∧
      ∀ a ∈ T, ∀ u : ℝ, y ≤ u → u ≤ s*y → a ≤ u → B*a ≤ u := by
  classical
  have hs0 : 0 < s := by linarith
  have hB0 : 0 < B := by linarith
  have hsB : 1 ≤ s*B := one_le_mul_of_one_le_of_one_le hs hB
  induction R generalizing U T with
  | zero =>
    have empty : T = ∅ := Finset.card_eq_zero.mp (by omega)
    refine ⟨U/s,by simp,by field_simp <;> norm_num,by simp [empty]⟩
  | succ n ih =>
    by_cases bad : ∃ a ∈ T, U/(s*B) < a ∧ a ≤ U
    · obtain ⟨b,hb,hb₀,_⟩ := bad
      obtain ⟨y,yl,yu,good⟩ := ih (U/(s*B)) (by positivity) (T.erase b)
        (by rw [Finset.card_erase_of_mem hb]; omega)
      refine ⟨y,?_,yu.trans (div_le_self hU.le hsB),?_⟩
      · simpa only [pow_succ,div_div,mul_assoc,mul_left_comm,mul_comm] using yl
      · intro a ha u hu hu' hau
        exact good a (Finset.mem_erase.mpr ⟨fun hab => by subst a; linarith,ha⟩) u hu hu' hau
    · have small (a : ℝ) (ha : a ∈ T) (haU : a ≤ U) : a ≤ U/(s*B) :=
        le_of_not_gt (fun h => bad ⟨a,ha,h,haU⟩)
      have top : s*(U/s) = U := by field_simp
      refine ⟨U/s,?_,top.le,?_⟩
      · apply div_le_div_of_nonneg_left hU.le hs0
        exact le_mul_of_one_le_right hs0.le (one_le_pow₀ hsB)
      · intro a ha u hu hu' hau
        have h := (le_div_iff₀ (by positivity : 0<s*B)).mp (small a ha (hau.trans (hu'.trans top.le)))
        apply le_trans _ hu
        rw [le_div_iff₀ hs0]
        linarith only [h,show B*a*s = a*(s*B) by ring]

theorem power_window (s eta Ct X : ℝ) (R : ℕ) (exc : Finset ℕ)
    (hs : 1 ≤ s) (heta : 0 < eta) (hle : eta ≤ Ct) (hX : 1 < X) (hc : exc.card ≤ R) :
    ∃ Y : ℝ, X^(1/(s*(s*(Ct/eta))^R)) ≤ Y ∧ Y^s ≤ X ∧
      ∀ x : ℝ, Y ≤ x → x ≤ Y^s → Good eta Ct exc x := by
  classical
  have hCt := heta.trans_le hle
  have hX0 : 0 < X := by linarith
  obtain ⟨y,yl,yu,good⟩ := log_window s (Ct/eta) hs ((one_le_div heta).mpr hle) R (Real.log X)
    (Real.log_pos hX) (exc.image fun a : ℕ => Real.log (a:ℝ)/Ct) (Finset.card_image_le.trans hc)
  have hpow : (Real.exp y)^s = Real.exp (s*y) := by rw [←Real.exp_mul,mul_comm]
  refine ⟨Real.exp y,?_,?_,?_⟩
  · rwa [Real.rpow_def_of_pos hX0,Real.exp_le_exp,mul_one_div]
  · rwa [hpow,←Real.le_log_iff_exp_le hX0]
  · intro x hx hx' a ha hau
    have hx0 := lt_of_lt_of_le (Real.exp_pos y) hx
    rcases Nat.eq_zero_or_pos a with rfl | ha0
    · simpa using (Real.rpow_pos_of_pos hx0 eta).le
    have hap : (0:ℝ) < a := by exact_mod_cast ha0
    have h1 := (Real.le_log_iff_exp_le hx0).mpr hx
    have h2 : Real.log x ≤ s*y := by rwa [Real.log_le_iff_le_exp hx0,←hpow]
    have h3 : Real.log (a:ℝ)/Ct ≤ Real.log x := by
      rw [div_le_iff₀ hCt,mul_comm,←Real.log_rpow hx0]
      exact Real.log_le_log hap hau
    have hv := good _ (Finset.mem_image_of_mem _ ha) (Real.log x) h1 h2 h3
    rw [show Ct/eta*(Real.log (a:ℝ)/Ct) = Real.log (a:ℝ)/eta by field_simp,
      div_le_iff₀ heta] at hv
    rwa [Real.rpow_def_of_pos hx0,←Real.log_le_iff_le_exp hap]

theorem square_window (eta Ct X : ℝ) (R : ℕ) (exc : Finset ℕ)
    (heta : 0 < eta) (hle : eta ≤ Ct) (hX : 1 < X) (hc : exc.card ≤ R) :
    ∃ Y : ℝ, InRange (2^(R+1)*(Ct/eta)^R) X Y ∧
      ∀ x : ℝ, Y ≤ x → x ≤ Y^(2:ℝ) → Good eta Ct exc x := by
  obtain ⟨Y,h,Yu,H⟩ := power_window 2 eta Ct X R exc (by norm_num) heta hle hX hc
  exact ⟨Y,⟨by simpa only [mul_pow,pow_succ,mul_assoc,mul_left_comm,mul_comm] using h,Yu⟩,H⟩

end Joint.PowerWindow
#print axioms Joint.PowerWindow.log_window
#print axioms Joint.PowerWindow.power_window
#print axioms Joint.PowerWindow.square_window

