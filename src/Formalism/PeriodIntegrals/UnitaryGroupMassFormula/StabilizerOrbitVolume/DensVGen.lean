import Mathlib
import Lemmata.ContinuousDensityLimit
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.FibFour

noncomputable section

namespace PI.VolStabSW

open MeasureTheory Topology Set Filter
open scoped Pointwise

def IsLCcOn {V : Type} [TopologicalSpace V] (U : Set V) (φ : V → ℝ) : Prop :=
  IsLocallyConstant φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ U

def HasCOSub (V : Type) [AddGroup V] [TopologicalSpace V] : Prop :=
  ∀ N ∈ 𝓝 (0 : V), ∃ Λ : AddSubgroup V, IsOpen (Λ : Set V) ∧ IsCompact (Λ : Set V) ∧
    (Λ : Set V) ⊆ N

section Dens

variable {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X]
  {μ : Measure V} {f : V → Y} {ι : X → Y} {ν : Measure X}

def HasDens (μ : Measure V) (f : V → Y) (ι : X → Y) (ν : Measure X) (φ : V → ℝ) (g : X → ℝ) :
    Prop :=
  Integrable φ μ ∧ Continuous g ∧ ∀ S : Set X, IsCompact S →
    ∫ v in f ⁻¹' (ι '' S), φ v ∂μ = ∫ b in S, g b ∂ν

theorem HasDens.sub [IsFiniteMeasureOnCompacts ν] {φ₁ φ₂ : V → ℝ} {g₁ g₂ : X → ℝ}
    (h₁ : HasDens μ f ι ν φ₁ g₁) (h₂ : HasDens μ f ι ν φ₂ g₂) :
    HasDens μ f ι ν (fun v => φ₁ v - φ₂ v) (fun b => g₁ b - g₂ b) :=
  ContinuousDensityLimit.HasDensity.sub h₁ h₂

theorem HasDens.const_mul (c : ℝ) {φ : V → ℝ} {g : X → ℝ} (h : HasDens μ f ι ν φ g) :
    HasDens μ f ι ν (fun v => c * φ v) (fun b => c * g b) :=
  ContinuousDensityLimit.HasDensity.const_mul c h

theorem nonneg_of_setIntegral [LocallyCompactSpace X] [IsFiniteMeasureOnCompacts ν]
    [ν.IsOpenPosMeasure] (D : X → ℝ) (hD : Continuous D)
    (h0 : ∀ S, IsCompact S → 0 ≤ ∫ b in S, D b ∂ν) (b0 : X) : 0 ≤ D b0 :=
  ContinuousDensityLimit.nonneg_of_setIntegral D hD h0 b0

theorem HasDens.le [LocallyCompactSpace X] [IsFiniteMeasureOnCompacts ν] [ν.IsOpenPosMeasure]
    {φ₁ φ₂ : V → ℝ} {g₁ g₂ : X → ℝ}
    (h₁ : HasDens μ f ι ν φ₁ g₁) (h₂ : HasDens μ f ι ν φ₂ g₂) (hle : ∀ v, φ₁ v ≤ φ₂ v) (b : X) :
    g₁ b ≤ g₂ b :=
  ContinuousDensityLimit.HasDensity.le h₁ h₂ hle b

end Dens

section Approx

variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]

theorem isOpen_inf_iInf (Λ₀ : AddSubgroup V) (h₀o : IsOpen (Λ₀ : Set V)) {ι : Type}
    (t : Finset ι) (L : ι → AddSubgroup V) (hLo : ∀ i, IsOpen (L i : Set V)) :
    IsOpen ((Λ₀ ⊓ ⨅ i ∈ t, L i : AddSubgroup V) : Set V) := by
  refine AddSubgroup.isOpen_of_mem_nhds _ (g := (0 : V)) ?_
  have h1 : (Λ₀ : Set V) ∈ 𝓝 (0 : V) := h₀o.mem_nhds Λ₀.zero_mem
  have h2 : (⋂ i ∈ t, (L i : Set V)) ∈ 𝓝 (0 : V) :=
    (Filter.biInter_finset_mem t).2 fun i _ => (hLo i).mem_nhds (L i).zero_mem
  filter_upwards [h1, h2] with x hx1 hx2
  simp only [Set.mem_iInter, SetLike.mem_coe] at hx1 hx2
  simp only [SetLike.mem_coe, AddSubgroup.mem_inf, AddSubgroup.mem_iInf]
  exact ⟨hx1, fun i hi => hx2 i hi⟩

theorem exists_sub_osc (hNA : HasCOSub V) {φ : V → ℝ} (hc : Continuous φ)
    (hs : HasCompactSupport φ) {ε : ℝ} (hε : 0 < ε) (Λ₀ : AddSubgroup V)
    (h₀o : IsOpen (Λ₀ : Set V)) (h₀c : IsCompact (Λ₀ : Set V)) :
    ∃ Λ : AddSubgroup V, IsOpen (Λ : Set V) ∧ IsCompact (Λ : Set V) ∧ Λ ≤ Λ₀ ∧
      ∀ x z, z ∈ Λ → |φ (x + z) - φ x| < ε := by
  have hloc : ∀ x : V, ∃ W : AddSubgroup V, IsOpen (W : Set V) ∧
      ∀ w ∈ W, |φ (x + w) - φ x| < ε / 2 := by
    intro x
    have hcx : ContinuousAt (fun w => φ (x + w)) 0 :=
      (hc.comp (continuous_const.add continuous_id)).continuousAt
    have hN : {w | |φ (x + w) - φ x| < ε / 2} ∈ 𝓝 (0 : V) := by
      have h1 := hcx.preimage_mem_nhds (Metric.ball_mem_nhds _ (half_pos hε))
      filter_upwards [h1] with w hw
      simpa [Real.dist_eq] using hw
    obtain ⟨W, hWo, -, hWN⟩ := hNA _ hN
    exact ⟨W, hWo, fun w hw => hWN hw⟩
  choose W hWo hW using hloc
  have hUo : ∀ i, IsOpen ((fun y => -i + y) ⁻¹' (W i : Set V)) :=
    fun i => (hWo i).preimage (continuous_const.add continuous_id)
  have hcov : tsupport φ ⊆ ⋃ i, (fun y => -i + y) ⁻¹' (W i : Set V) := by
    intro y _
    refine Set.mem_iUnion.mpr ⟨y, ?_⟩
    show -y + y ∈ W y
    simp
  obtain ⟨t, ht⟩ := hs.elim_finite_subcover (fun i => (fun y => -i + y) ⁻¹' (W i : Set V)) hUo hcov
  have hΛo := isOpen_inf_iInf Λ₀ h₀o t W hWo
  refine ⟨Λ₀ ⊓ ⨅ i ∈ t, W i, hΛo,
    h₀c.of_isClosed_subset (AddSubgroup.isClosed_of_isOpen _ hΛo)
      (SetLike.coe_subset_coe.mpr inf_le_left), inf_le_left, ?_⟩
  intro x z hz
  have hz' := hz
  simp only [AddSubgroup.mem_inf, AddSubgroup.mem_iInf] at hz'
  have hzW : ∀ i ∈ t, z ∈ W i := hz'.2
  have hzero : ∀ y, y ∉ tsupport φ → φ y = 0 := fun y hy => by
    by_contra hne
    exact hy (subset_tsupport φ (Function.mem_support.mpr hne))
  by_cases hx : x ∈ ⋃ i ∈ t, (fun y => -i + y) ⁻¹' (W i : Set V)
  · simp only [Set.mem_iUnion] at hx
    obtain ⟨i, hi, hxi⟩ := hx
    have hxi' : -i + x ∈ W i := hxi
    have h1 := hW i (-i + x) hxi'
    have h2 := hW i (-i + (x + z)) (by
      have e : -i + (x + z) = (-i + x) + z := by abel
      rw [e]
      exact (W i).add_mem hxi' (hzW i hi))
    simp only [add_neg_cancel_left] at h1 h2
    rw [abs_lt] at h1 h2 ⊢
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  · have hxz : x + z ∉ ⋃ i ∈ t, (fun y => -i + y) ⁻¹' (W i : Set V) := by
      intro hc'
      apply hx
      simp only [Set.mem_iUnion] at hc' ⊢
      obtain ⟨i, hi, hxi⟩ := hc'
      refine ⟨i, hi, ?_⟩
      have hxi' : -i + (x + z) ∈ W i := hxi
      show -i + x ∈ W i
      have e : -i + x = (-i + (x + z)) + -z := by abel
      rw [e]
      exact (W i).add_mem hxi' ((W i).neg_mem (hzW i hi))
    rw [hzero x (fun h => hx (ht h)), hzero (x + z) (fun h => hxz (ht h))]
    simpa using hε

end Approx

section Main

variable {V X Y : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [MeasurableSpace V] [OpensMeasurableSpace V]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X]
  [LocallyCompactSpace X]

def cosApx (Λ : AddSubgroup V) (φ : V → ℝ) (x : V) : ℝ := φ ((x : V ⧸ Λ).out)

omit [TopologicalSpace V] [IsTopologicalAddGroup V] [MeasurableSpace V] [OpensMeasurableSpace V]
  in
theorem cosApx_sub_mem (Λ : AddSubgroup V) (x : V) : -((x : V ⧸ Λ).out) + x ∈ Λ := by
  have h : ((((x : V ⧸ Λ).out : V) : V ⧸ Λ)) = (x : V ⧸ Λ) := Quotient.out_eq _
  exact QuotientAddGroup.eq.mp h

omit [TopologicalSpace V] [IsTopologicalAddGroup V] [MeasurableSpace V] [OpensMeasurableSpace V]
  in
theorem cosApx_eq (Λ : AddSubgroup V) (φ : V → ℝ) {x y : V} (h : -x + y ∈ Λ) :
    cosApx Λ φ y = cosApx Λ φ x := by
  have e : (y : V ⧸ Λ) = (x : V ⧸ Λ) := (QuotientAddGroup.eq.mpr h).symm
  show φ ((y : V ⧸ Λ).out) = φ ((x : V ⧸ Λ).out)
  rw [e]

omit [MeasurableSpace V] [OpensMeasurableSpace V] in
theorem cosApx_lc (Λ : AddSubgroup V) (hΛ : IsOpen (Λ : Set V)) (φ : V → ℝ) :
    IsLocallyConstant (cosApx Λ φ) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hc : Continuous fun y : V => -x + y := continuous_const.add continuous_id
  have hm : (fun y : V => -x + y) ⁻¹' (Λ : Set V) ∈ 𝓝 x :=
    (hΛ.preimage hc).mem_nhds (by show -x + x ∈ Λ; simp)
  filter_upwards [hm] with y hy
  exact cosApx_eq Λ φ hy

theorem densApprox_lc (μ : Measure V) [IsFiniteMeasureOnCompacts μ] (f : V → Y) (ι : X → Y)
    (ν : Measure X) [IsFiniteMeasureOnCompacts ν] [ν.IsOpenPosMeasure] (U : Set V)
    (hU : IsOpen U) (hNA : HasCOSub V) : DensApprox (IsLCcOn U) μ f ι ν U := by
  intro hLC φ hφ
  obtain ⟨hc, hs, hsU⟩ := hφ
  obtain ⟨W, hW, hKW⟩ := compact_open_separated_add_right hs.isCompact hU hsU
  obtain ⟨Λ₀, h₀o, h₀c, h₀W⟩ := hNA W hW
  set K' : Set V := tsupport φ + (Λ₀ : Set V) with hK'
  have hcos : ∀ x y, -x + y ∈ Λ₀ → y ∈ K' → x ∈ K' := by
    intro x y h hy
    obtain ⟨k, hk, l, hl, rfl⟩ := hy
    exact ⟨k, hk, l - (-x + (k + l)), Λ₀.sub_mem hl h, by abel⟩
  have hcos' : ∀ x y, -x + y ∈ Λ₀ → (y ∈ K' ↔ x ∈ K') := by
    intro x y h
    refine ⟨hcos x y h, hcos y x ?_⟩
    have := Λ₀.neg_mem h
    rwa [neg_add_rev, neg_neg] at this
  have hnb : ∀ x : V, {y | -x + y ∈ Λ₀} ∈ 𝓝 x := by
    intro x
    refine (h₀o.preimage (continuous_const.add continuous_id)).mem_nhds ?_
    show -x + x ∈ Λ₀
    rw [neg_add_cancel]
    exact Λ₀.zero_mem
  have hK'cl : IsClosed K' := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro x hx
    exact Filter.mem_of_superset (hnb x) fun y hy hyK => hx (hcos x y hy hyK)
  have hK'c : IsCompact K' := hs.isCompact.add h₀c
  have hK'U : K' ⊆ U := (Set.add_subset_add subset_rfl h₀W).trans hKW
  have hKK' : tsupport φ ⊆ K' := fun x hx => ⟨x, hx, 0, Λ₀.zero_mem, add_zero x⟩
  have hlcc : ∀ ψ : V → ℝ, IsLocallyConstant ψ → Function.support ψ ⊆ K' → IsLCcOn U ψ :=
    fun ψ h1 h2 => ⟨h1, hK'c.of_isClosed_subset isClosed_closure (closure_minimal h2 hK'cl),
      (closure_minimal h2 hK'cl).trans hK'U⟩
  have hdens : ∀ ψ, IsLCcOn U ψ → ∃ g, HasDens μ f ι ν ψ g := fun ψ h => by
    obtain ⟨g, hg, hS⟩ := hLC ψ h
    exact ⟨g, h.1.continuous.integrable_of_hasCompactSupport h.2.1, hg, hS⟩
  set ind : V → ℝ := K'.indicator fun _ => 1 with hind_def
  have hind : IsLCcOn U ind := by
    refine hlcc ind ?_ Set.support_indicator_subset
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    refine ⟨{y | -x + y ∈ Λ₀}, h₀o.preimage (continuous_const.add continuous_id),
      mem_of_mem_nhds (hnb x), fun y hy => ?_⟩
    have := hcos' x y hy
    rw [hind_def]
    by_cases hx : x ∈ K'
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (this.2 hx)]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem fun h => hx (this.1 h)]
  obtain ⟨g0, hg0⟩ := hdens ind hind
  have hε : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  choose Λ hΛo hΛc hΛ0 hosc using fun n : ℕ => exists_sub_osc hNA hc hs (hε n) Λ₀ h₀o h₀c
  set φn : ℕ → V → ℝ := fun n => cosApx (Λ n) φ with hφn_def
  have hφn_close : ∀ n x, |φn n x - φ x| < 1 / ((n : ℝ) + 1) := by
    intro n x
    have := hosc n ((x : V ⧸ Λ n).out) _ (cosApx_sub_mem (Λ n) x)
    rw [add_neg_cancel_left] at this
    rw [abs_sub_comm]
    exact this
  have hφn_supp : ∀ n, Function.support (φn n) ⊆ K' := by
    intro n x hx
    exact ⟨_, subset_tsupport φ hx, _, hΛ0 n (cosApx_sub_mem (Λ n) x), add_neg_cancel_left _ x⟩
  have hφn : ∀ n, IsLCcOn U (φn n) := fun n => hlcc _ (cosApx_lc _ (hΛo n) φ) (hφn_supp n)
  choose g hg using fun n => hdens (φn n) (hφn n)
  have hbd : ∀ n x, |φn n x - φ x| ≤ 1 / ((n : ℝ) + 1) * ind x := by
    intro n x
    by_cases hx : x ∈ K'
    · rw [hind_def, Set.indicator_of_mem hx, mul_one]
      exact (hφn_close n x).le
    · have h1 : φn n x = 0 := by
        by_contra h
        exact hx (hφn_supp n h)
      have h2 : φ x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (hKK' h)
      rw [hind_def, Set.indicator_of_notMem hx, h1, h2]
      simp
  exact ContinuousDensityLimit.exists_of_weighted_approximation
    (pull := fun S => f ⁻¹' (ι '' S))
    (fun n : ℕ => 1 / ((n : ℝ) + 1)) (fun n => (hε n).le)
    (fun n m hnm => one_div_le_one_div_of_le (by positivity)
      (by exact_mod_cast Nat.add_le_add_right hnm 1))
    tendsto_one_div_add_atTop_nhds_zero_nat
    (hc.integrable_of_hasCompactSupport hs) hg0 hg hbd

end Main

end PI.VolStabSW
