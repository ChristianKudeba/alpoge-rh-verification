import Mathlib

/-!
Continuous densities are closed under approximation bounded by a common
integrable envelope. The error rate may be any nonnegative decreasing sequence
tending to zero. The source has no topology or group structure, and `pull` is
an arbitrary assignment of source sets to target sets.
-/

noncomputable section

namespace ContinuousDensityLimit

open MeasureTheory Topology Set Filter

variable {V X : Type*} [MeasurableSpace V]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X]
  {μ : Measure V} {pull : Set X → Set V} {ν : Measure X}

def HasDensity (μ : Measure V) (pull : Set X → Set V) (ν : Measure X) (φ : V → ℝ) (g : X → ℝ) :
    Prop :=
  Integrable φ μ ∧ Continuous g ∧ ∀ S : Set X, IsCompact S →
    ∫ v in pull S, φ v ∂μ = ∫ b in S, g b ∂ν

theorem HasDensity.sub [IsFiniteMeasureOnCompacts ν] {φ₁ φ₂ : V → ℝ} {g₁ g₂ : X → ℝ}
    (h₁ : HasDensity μ pull ν φ₁ g₁) (h₂ : HasDensity μ pull ν φ₂ g₂) :
    HasDensity μ pull ν (fun v => φ₁ v - φ₂ v) (fun b => g₁ b - g₂ b) := by
  obtain ⟨i1, c1, e1⟩ := h₁
  obtain ⟨i2, c2, e2⟩ := h₂
  refine ⟨i1.sub i2, c1.sub c2, fun S hS => ?_⟩
  rw [integral_sub i1.integrableOn i2.integrableOn,
    integral_sub (c1.continuousOn.integrableOn_compact hS) (c2.continuousOn.integrableOn_compact hS),
    e1 S hS, e2 S hS]

theorem HasDensity.const_mul (c : ℝ) {φ : V → ℝ} {g : X → ℝ} (h : HasDensity μ pull ν φ g) :
    HasDensity μ pull ν (fun v => c * φ v) (fun b => c * g b) := by
  obtain ⟨hi, hc, he⟩ := h
  refine ⟨hi.const_mul c, continuous_const.mul hc, fun S hS => ?_⟩
  rw [integral_const_mul, integral_const_mul, he S hS]

theorem nonneg_of_setIntegral [LocallyCompactSpace X] [IsFiniteMeasureOnCompacts ν]
    [ν.IsOpenPosMeasure] (D : X → ℝ) (hD : Continuous D)
    (h0 : ∀ S, IsCompact S → 0 ≤ ∫ b in S, D b ∂ν) (b0 : X) : 0 ≤ D b0 := by
  by_contra hneg
  push_neg at hneg
  have hU : {b | D b < D b0 / 2} ∈ 𝓝 b0 :=
    (isOpen_lt hD continuous_const).mem_nhds (by show D b0 < D b0 / 2; linarith)
  obtain ⟨K, hKn, hKU, hKc⟩ := local_compact_nhds hU
  have hpos : 0 < ν K := ν.measure_pos_of_mem_nhds hKn
  have hfin : ν K < ⊤ := hKc.measure_lt_top
  have h1 : ∫ b in K, D b ∂ν ≤ ∫ b in K, D b0 / 2 ∂ν :=
    setIntegral_mono_on (hD.continuousOn.integrableOn_compact hKc)
      (continuousOn_const.integrableOn_compact hKc) hKc.measurableSet
      (fun x hx => le_of_lt (hKU hx))
  rw [setIntegral_const, smul_eq_mul] at h1
  try simp only [Measure.real] at h1
  have h2 : 0 < (ν K).toReal := ENNReal.toReal_pos hpos.ne' hfin.ne
  have h3 := h0 K hKc
  nlinarith

theorem HasDensity.le [LocallyCompactSpace X] [IsFiniteMeasureOnCompacts ν] [ν.IsOpenPosMeasure]
    {φ₁ φ₂ : V → ℝ} {g₁ g₂ : X → ℝ}
    (h₁ : HasDensity μ pull ν φ₁ g₁) (h₂ : HasDensity μ pull ν φ₂ g₂) (hle : ∀ v, φ₁ v ≤ φ₂ v) (b : X) :
    g₁ b ≤ g₂ b := by
  have h := h₂.sub h₁
  have hS : ∀ S, IsCompact S → 0 ≤ ∫ x in S, g₂ x - g₁ x ∂ν := by
    intro S hS
    rw [← h.2.2 S hS]
    exact integral_nonneg fun v => sub_nonneg.mpr (hle v)
  have key : 0 ≤ g₂ b - g₁ b := nonneg_of_setIntegral (fun x => g₂ x - g₁ x) h.2.1 hS b
  linarith


/-- An order-bounded approximation of integrable functions transfers to a
continuous density. No regularity of the set assignment `pull` is needed. -/
theorem exists_of_weighted_approximation
    [LocallyCompactSpace X] [IsFiniteMeasureOnCompacts ν] [ν.IsOpenPosMeasure]
    {φ ind : V → ℝ} {g0 : X → ℝ} {φn : ℕ → V → ℝ} {g : ℕ → X → ℝ}
    (ε : ℕ → ℝ) (hε : ∀ n, 0 ≤ ε n) (hεanti : Antitone ε)
    (hεlim : Tendsto ε atTop (𝓝 0))
    (hφi : Integrable φ μ) (hg0 : HasDensity μ pull ν ind g0)
    (hg : ∀ n, HasDensity μ pull ν (φn n) (g n))
    (hbd : ∀ n x, |φn n x - φ x| ≤ ε n * ind x) :
    ∃ G : X → ℝ, Continuous G ∧ ∀ S : Set X, IsCompact S →
      ∫ v in pull S, φ v ∂μ = ∫ b in S, G b ∂ν := by
  have hgg : ∀ n m b, |g n b - g m b| ≤ (ε n + ε m) * g0 b := by
    intro n m b
    have hA := hg0.const_mul (ε n + ε m)
    have hle : ∀ n m x, φn n x - φn m x ≤ (ε n + ε m) * ind x := by
      intro n m x
      have h1 := abs_le.1 (hbd n x)
      have h2 := abs_le.1 (hbd m x)
      rw [add_mul]
      linarith [h1.1, h1.2, h2.1, h2.2]
    have u1 := ((hg n).sub (hg m)).le hA (hle n m) b
    have hA' := hg0.const_mul (ε m + ε n)
    have u2 := ((hg m).sub (hg n)).le hA' (hle m n) b
    refine abs_le.2 ⟨?_, u1⟩
    have : (ε m + ε n) = (ε n + ε m) :=
      add_comm _ _
    rw [this] at u2
    linarith
  have hcauchy : ∀ b, CauchySeq fun n => g n b := by
    intro b
    refine cauchySeq_of_le_tendsto_0 (fun N : ℕ => 2 * (ε N) * |g0 b|)
      (fun n m N hn hm => ?_) ?_
    · rw [Real.dist_eq]
      have h1 := hεanti hn
      have h2 := hεanti hm
      calc |g n b - g m b| ≤ (ε n + ε m) * g0 b := hgg n m b
        _ ≤ (ε n + ε m) * |g0 b| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) (add_nonneg (hε n) (hε m))
        _ ≤ (ε N + ε N) * |g0 b| :=
          mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
        _ = 2 * (ε N) * |g0 b| := by ring
    · have := (hεlim.const_mul (2 : ℝ)).mul_const |g0 b|
      rwa [mul_zero, zero_mul] at this
  set G : X → ℝ := fun b => limUnder atTop fun n => g n b with hG_def
  have hlim : ∀ b, Tendsto (fun n => g n b) atTop (𝓝 (G b)) := fun b =>
    (hcauchy b).tendsto_limUnder
  have hGn : ∀ n b, |G b - g n b| ≤ ε n * g0 b := by
    intro n b
    have ht : Tendsto (fun m => |g m b - g n b|) atTop (𝓝 |G b - g n b|) :=
      ((hlim b).sub_const _).abs
    have ht2 : Tendsto (fun m : ℕ => (ε n + ε m) * g0 b) atTop
        (𝓝 ((ε n + 0) * g0 b)) :=
      (tendsto_const_nhds.add hεlim).mul_const _
    have := le_of_tendsto_of_tendsto' ht ht2 fun m => by
      rw [abs_sub_comm]
      exact hgg n m b
    rwa [add_zero] at this
  have hGc : Continuous G := by
    refine TendstoLocallyUniformly.continuous (F := g) (p := atTop) ?_
      (Eventually.of_forall fun n => (hg n).2.1).frequently
    rw [Metric.tendstoLocallyUniformly_iff]
    intro δ hδ x
    refine ⟨{y | g0 y < g0 x + 1}, (isOpen_lt hg0.2.1 continuous_const).mem_nhds (by simp), ?_⟩
    have ht : Tendsto (fun n : ℕ => ε n * (|g0 x| + 1)) atTop (𝓝 0) := by
      have := hεlim.mul_const (|g0 x| + 1)
      rwa [zero_mul] at this
    filter_upwards [ht.eventually (Iio_mem_nhds hδ)] with n hn y hy
    have hy' : g0 y < g0 x + 1 := hy
    have hx' := le_abs_self (g0 x)
    rw [Real.dist_eq]
    calc |G y - g n y| ≤ ε n * g0 y := hGn n y
      _ ≤ ε n * (|g0 x| + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (hε n)
      _ < δ := hn
  refine ⟨G, hGc, fun S hS => ?_⟩
  have hC : ∀ n : ℕ, |∫ v in pull S, φ v ∂μ - ∫ b in S, G b ∂ν| ≤
      2 * (ε n) * |∫ b in S, g0 b ∂ν| := by
    intro n
    have e1 : |∫ v in pull S, φ v ∂μ - ∫ v in pull S, φn n v ∂μ| ≤
        ∫ v in pull S, ε n * ind v ∂μ := by
      rw [← integral_sub hφi.integrableOn (hg n).1.integrableOn, ← Real.norm_eq_abs]
      refine norm_integral_le_of_norm_le (g := fun v => ε n * ind v)
        (hg0.1.const_mul _).integrableOn (ae_of_all _ ?_)
      intro x
      rw [Real.norm_eq_abs, abs_sub_comm]
      exact hbd n x
    have e2 : |∫ b in S, g n b ∂ν - ∫ b in S, G b ∂ν| ≤ ∫ b in S, ε n * g0 b ∂ν := by
      rw [← integral_sub ((hg n).2.1.continuousOn.integrableOn_compact hS)
        (hGc.continuousOn.integrableOn_compact hS), ← Real.norm_eq_abs]
      refine norm_integral_le_of_norm_le (g := fun b => ε n * g0 b)
        ((continuous_const.mul hg0.2.1).continuousOn.integrableOn_compact hS) (ae_of_all _ ?_)
      intro b
      rw [Real.norm_eq_abs, abs_sub_comm]
      exact hGn n b
    rw [integral_const_mul, hg0.2.2 S hS] at e1
    rw [integral_const_mul] at e2
    rw [(hg n).2.2 S hS] at e1
    have h3 := abs_sub_le (∫ v in pull S, φ v ∂μ) (∫ b in S, g n b ∂ν) (∫ b in S, G b ∂ν)
    have h4 : ε n * ∫ b in S, g0 b ∂ν ≤ ε n * |∫ b in S, g0 b ∂ν| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) (hε n)
    linarith
  by_contra hne
  have hpos : 0 < |∫ v in pull S, φ v ∂μ - ∫ b in S, G b ∂ν| :=
    abs_pos.2 (sub_ne_zero.2 hne)
  have ht : Tendsto (fun n : ℕ => 2 * (ε n) * |∫ b in S, g0 b ∂ν|) atTop (𝓝 0) := by
    have := (hεlim.const_mul (2 : ℝ)).mul_const
      |∫ b in S, g0 b ∂ν|
    rwa [mul_zero, zero_mul] at this
  obtain ⟨n, hn⟩ := (ht.eventually (Iio_mem_nhds hpos)).exists
  exact absurd (hC n) (not_le.2 hn)

end ContinuousDensityLimit
