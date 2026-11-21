import Compaction.OddMinusVVle
import Compaction.PolynomialAbsorption
import Development.AutomorphicArithmetic.AutomorphicVarieties.CMFieldExponentialBounds.AdmissibleOfPageN

/-! Replace the separate ThmBc assumption by the constructed conductor-only
odd-minus certificates. The height/window input is unchanged. The extra
polynomial term is absorbed by enlarging the height exponent before X,q,d,Y.
This does not prove the remaining JointWin input or assert a completed RH proof.
-/

noncomputable section
namespace Compaction.JointWindowWithoutMinus
open NumberField Formalism.HC UpperTheory.Top UpperTheory.V

theorem vwinAt_of_joint {Ct : ℝ} (hC : 1 ≤ Ct) (hJ : JointWin Ct) (ψ : PChar) : VWinAt ψ Ct := by
  intro eps h0 h1 e he
  set t : ℝ → ℕ := fun x => ⌊x ^ Ct⌋₊ with ht
  have hadm : admitted 4 Ct e t := admissible_of_pageN h0 h1 hC he
  obtain ⟨J, C, P, XJ, hJ0, hmain⟩ := hJ ψ eps 4 h0 h1 e t hadm
  obtain ⟨Cm, hCm, hminus⟩ := OddMinusVVle.exists_polynomial_bound
  let K : ℝ := 2 * Cm + 4
  have hK : 0 ≤ K := by dsimp [K]; linarith
  obtain ⟨D, hCD, habs⟩ := PolynomialAbsorption.exists_exponent K C hK
  obtain ⟨xT, hxT⟩ := error_terms_le_sqrt_exp_rpow eps 0 D h0
  obtain ⟨xN, hxN⟩ := log_conductor_mul_height_le_of_pageN eps Ct ψ.N h0 h1
  obtain ⟨Y0, hY0⟩ := log_mul_le_rpow_of_winPair eps h0
  obtain ⟨J', hJ'1, hJJ'⟩ : ∃ J' : ℝ, 1 ≤ J' ∧ J ≤ J' := ⟨max J 1, le_max_right _ _, le_max_left _ _⟩
  have hJ'0 : 0 < J' := by linarith
  obtain ⟨P', hPP', hNP'⟩ : ∃ P' : ℝ, P ≤ P' ∧ (ψ.N : ℝ) ≤ P' := ⟨max P (ψ.N : ℝ), le_max_left _ _, le_max_right _ _⟩
  obtain ⟨XB, hXB⟩ := eventually_winPair_gt_power eps J' Ct P' h0 hJ'0
  obtain ⟨L, hxTL, hxNL, hY0L, h2L⟩ : ∃ L : ℝ, xT ≤ L ∧ xN ≤ L ∧ Y0 ≤ L ∧ 2 ≤ L :=
    ⟨max (max xT xN) (max Y0 2), le_max_of_le_left (le_max_left _ _), le_max_of_le_left (le_max_right _ _),
      le_max_of_le_right (le_max_left _ _), le_max_of_le_right (le_max_right _ _)⟩
  have hL1 : (1 : ℝ) ≤ L := by linarith
  have hL0 : (0 : ℝ) ≤ L := by linarith
  refine ⟨J', hJ'1, max (max XJ XB) (L ^ J'), ?_⟩
  intro X hX q d hw
  have hXJ : XJ ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hXB' : XB ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hXL : L ^ J' ≤ X := le_trans (le_max_right _ _) hX
  have hLX : L ≤ X ^ (1 / J') := by
    have := Real.rpow_le_rpow (Real.rpow_nonneg hL0 _) hXL (le_of_lt (one_div_pos.mpr hJ'0))
    rwa [← Real.rpow_mul hL0, mul_one_div_cancel hJ'0.ne', Real.rpow_one] at this
  have hX1 : 1 ≤ X := by
    have : 1 ≤ L ^ J' := Real.one_le_rpow hL1 hJ'0.le
    linarith
  have hX0 : (0 : ℝ) ≤ X := by linarith
  obtain ⟨hq3, hd3, hPq, hPd⟩ := hXB X hXB' q d hw
  have hlog := hY0 _ (hY0L.trans hLX) q d hw
  have hpow : (X ^ (1 / J')) ^ (eps / 4) = X ^ (eps / (4 * J')) := by
    rw [← Real.rpow_mul hX0]
    congr 1
    field_simp
  have hmono : X ^ (eps / (4 * J')) ≤ X ^ (eps / (4 * J)) :=
    Real.rpow_le_rpow_of_exponent_le hX1 (div_le_div_of_nonneg_left h0.le (by positivity) (by linarith))
  have hlogJ : Real.log (↑q * ↑d) ≤ X ^ (eps / (4 * J)) := by
    rw [hpow] at hlog
    exact hlog.trans hmono
  have hN0 : 0 < ψ.N := (AbF.ofChar ψ).pos
  have hcop : ∀ r : ℕ, Nat.Prime r → (ψ.N : ℝ) < r → Nat.Coprime r ψ.N := by
    intro r hr hlt
    have hlt' : ψ.N < r := by exact_mod_cast hlt
    exact (Nat.Prime.coprime_iff_not_dvd hr).2 (fun hdvd => absurd (Nat.le_of_dvd hN0 hdvd) (not_le.2 hlt'))
  have hpp : PrimePair ψ.N q d :=
    ⟨hw.q_prime, hw.q_mod, hw.d_prime, hw.d_mod,
      Nat.Coprime.mul (hcop q hw.q_prime (lt_of_le_of_lt hNP' hPq)) (hcop d hw.d_prime (lt_of_le_of_lt hNP' hPd))⟩
  obtain ⟨Y, ⟨hYlo, hYhi⟩, hY⟩ :=
    hmain X hXJ q d hpp hq3 hd3 (lt_of_le_of_lt hPP' hPq) (lt_of_le_of_lt hPP' hPd) hlogJ
  have hWY : X ^ (1 / J') ≤ Y :=
    le_trans (Real.rpow_le_rpow_of_exponent_le hX1 (one_div_le_one_div_of_le (by linarith) hJJ')) hYlo
  refine ⟨Y, hWY, hYhi, ?_⟩
  intro x hxY hxY2
  have hWx : X ^ (1 / J') ≤ x := hWY.trans hxY
  have hLx : L ≤ x := hLX.trans hWx
  have hx2 : 2 ≤ x := h2L.trans hLx
  have hx1 : 1 ≤ x := by linarith
  obtain ⟨hBa, hHV⟩ := hY x hxY hxY2
  intro E _ _ hE
  have hq0 : 0 < q := hw.q_prime.pos
  have hd0 : 0 < d := hw.d_prime.pos
  have hq4 : q % 4 = 3 := by
    have := hw.q_mod
    omega
  haveI : IsCMField E := isCMField_of_isChiField ψ (e x) q d hw.q_prime hq4 E hE
  have hE' : IsCompField (AbF.ofChar ψ) (e x) q d E := (isCompField_ofChar ψ (e x) q d E).2 hE
  have h2 := hBa E hE'
  have hp := hHV E hE
  obtain ⟨hc1, hc2, hc3⟩ := conductor_bounds_of_isChiField ψ (e x) q d hq0 hd0 E hE
  obtain ⟨-, -, ht2, htle⟩ := hadm x hx2
  have ht1 : 1 ≤ t x := by omega
  have hmem : condF E ∈ {n : ℕ | 0 < n ∧ Nonempty (E →ₐ[ℚ] CyclotomicField n ℚ)} := by
    apply Nat.sInf_mem
    obtain ⟨n, hn, j, _⟩ := hE'
    exact ⟨n, Nat.pos_of_ne_zero hn.out, ⟨j⟩⟩
  letI : NeZero (condF E) := ⟨hmem.1.ne'⟩
  have hm := hminus (condF E) (t x) ht2 E hmem.2
  have hWpos : (0 : ℝ) ≤ X ^ (1 / J') := Real.rpow_nonneg hX0 _
  have hqd : Real.log (↑q * ↑d) ≤ x ^ (eps / 4) := by
    have hlog0 := hY0 _ (hY0L.trans hLX) q d hw
    exact hlog0.trans (Real.rpow_le_rpow hWpos hWx (by linarith))
  have hNt := hxN x (hxNL.trans hLx) (condF E) (t x) (e x) q d hc1 hc2 (he x hx1) ht1 htle hqd
  have hv := vvle_of_parts h2 hm hp
  have hu1 : (1 : ℝ) ≤ ↑(condF E) * ↑(t x) := by
    have a : (1 : ℝ) ≤ condF E := by exact_mod_cast hc1
    have b : (1 : ℝ) ≤ t x := by exact_mod_cast ht1
    nlinarith
  have hu2 : (2 : ℝ) ≤ (condF E : ℝ) * t x := by
    have hn : (1 : ℝ) ≤ condF E := by exact_mod_cast hc1
    have ht : (2 : ℝ) ≤ t x := by exact_mod_cast ht2
    nlinarith
  have hpoly := habs ((condF E : ℝ) * t x) hu2
  rw [Real.rpow_ofNat] at hpoly
  have hcoef : C * Real.exp (x ^ (4 * eps / 5)) ≤ D * Real.exp (x ^ (4 * eps / 5)) :=
    mul_le_mul_of_nonneg_right hCD (Real.exp_pos _).le
  have htot := hxT x (hxTL.trans hLx) _ hu1 hNt
  have htot' : Real.exp (x ^ (4 * eps / 5)) * Real.log 2 +
      K * ((condF E : ℝ) * t x) ^ 9 +
      (((condF E : ℝ) * t x) ^ C + C * Real.exp (x ^ (4 * eps / 5))) ≤
      Real.sqrt (Real.exp (x ^ eps)) := by
    have hcombine : Real.exp (x ^ (4 * eps / 5)) * Real.log 2 +
        K * ((condF E : ℝ) * t x) ^ 9 +
        (((condF E : ℝ) * t x) ^ C + C * Real.exp (x ^ (4 * eps / 5))) ≤
        Real.exp (x ^ (4 * eps / 5)) * Real.log 2 +
        (((condF E : ℝ) * t x) ^ D + D * Real.exp (x ^ (4 * eps / 5))) := by
      linarith
    exact hcombine.trans (by simpa only [zero_mul, add_zero] using htot)
  exact VVle.mono hv le_rfl htot' 


theorem vwin_of_joint (hJ : JointWin 401) : VWin := by
  intro ψ
  exact vwinAt_of_joint (by norm_num) hJ ψ

end Compaction.JointWindowWithoutMinus

#print axioms Compaction.JointWindowWithoutMinus.vwinAt_of_joint
#print axioms Compaction.JointWindowWithoutMinus.vwin_of_joint
