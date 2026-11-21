import Mathlib

noncomputable section

namespace Formalism.L2.SG.Pf.NcS.LT.GLP

variable {K : Type*} [Field K]

theorem surj_equiv {C W : Type*} [AddCommGroup C] [Module K C] [FiniteDimensional K C]
    [AddCommGroup W] [Module K W] (L1 L2 : C →ₗ[K] W) (h1 : Function.Surjective L1)
    (h2 : Function.Surjective L2) : ∃ δ : C ≃ₗ[K] C, ∀ c, L1 (δ c) = L2 c := by
  letI : FiniteDimensional K W := Module.Finite.of_surjective L1 h1
  let e1 := LinearEquiv.ofInjective L1.dualMap (LinearMap.dualMap_injective_of_surjective h1)
  let e2 := LinearEquiv.ofInjective L2.dualMap (LinearMap.dualMap_injective_of_surjective h2)
  obtain ⟨A, hA⟩ := Submodule.exists_linearEquiv_restrict_eq (e1.symm.trans e2)
  let δ : C ≃ₗ[K] C := (Module.evalEquiv K C).trans
    (A.dualMap.trans (Module.evalEquiv K C).symm)
  refine ⟨δ, fun c => ?_⟩
  apply (Module.evalEquiv K W).injective
  ext φ
  have h := congrArg (fun f : Module.Dual K C => f c) (hA (e1 φ))
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] at h
  change (L1.dualMap φ) ((Module.evalEquiv K C).symm (A.dualMap ((Module.evalEquiv K C) c))) = _
  rw [Module.apply_evalEquiv_symm_apply]
  exact h.symm

theorem pi_surj {V : Type*} [AddCommGroup V] [Module K V] {a : ℕ} (ψ : Fin a → Module.Dual K V)
    (hψ : LinearIndependent K ψ) : Function.Surjective (LinearMap.pi ψ) := by
  have hdual : (LinearMap.pi ψ).dualMap =
      (Pi.basisFun K (Fin a)).dualBasis.constr K ψ := by
    apply (Pi.basisFun K (Fin a)).dualBasis.ext
    intro i
    rw [Module.Basis.constr_basis]
    ext v
    simp [Module.Basis.dualBasis_apply]
  rw [← LinearMap.dualMap_injective_iff, hdual]
  exact (Pi.basisFun K (Fin a)).dualBasis.injective_constr_of_linearIndependent hψ

theorem trans_tuple {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {a : ℕ}
    (x y : Fin a → V) (hx : LinearIndependent K x) (hy : LinearIndependent K y) :
    ∃ A : V ≃ₗ[K] V, ∀ j, A (x j) = y j := by
  obtain ⟨A, hA⟩ := Submodule.exists_linearEquiv_restrict_eq
    ((Module.Basis.span hx).equiv (Module.Basis.span hy) (Equiv.refl (Fin a)))
  refine ⟨A, fun j => ?_⟩
  have hj := hA ((Module.Basis.span hx) j)
  rw [Module.Basis.equiv_apply] at hj
  simpa only [Equiv.refl_apply, Module.Basis.span_apply] using hj.symm

private theorem eq_zero_of_mem_of_disjoint {V : Type*} [AddCommGroup V] [Module K V] {S T : Submodule K V}
    (h : Disjoint S T) {v : V} (hS : v ∈ S) (hT : v ∈ T) : v = 0 :=
  (Submodule.mem_bot K).mp (h.le_bot (Submodule.mem_inf.mpr ⟨hS, hT⟩))

private theorem exists_not_mem_of_ne_top_of_ne_top {V : Type*} [AddCommGroup V] [Module K V]
    (U W : Submodule K V) (hU : U ≠ ⊤) (hW : W ≠ ⊤) : ∃ v, v ∉ U ∧ v ∉ W := by
  obtain ⟨u, hu⟩ : ∃ u, u ∉ U := by
    by_contra hcon
    push_neg at hcon
    exact hU (Submodule.eq_top_iff'.mpr hcon)
  obtain ⟨w, hw⟩ : ∃ w, w ∉ W := by
    by_contra hcon
    push_neg at hcon
    exact hW (Submodule.eq_top_iff'.mpr hcon)
  by_cases huW : u ∈ W
  · by_cases hwU : w ∈ U
    · refine ⟨u + w, fun h => hu ?_, fun h => hw ?_⟩
      · simpa using U.sub_mem h hwU
      · simpa using W.sub_mem h huW
    · exact ⟨w, hwU, hw⟩
  · exact ⟨u, hu, huW⟩

private theorem exists_common_complement_of_finrank_eq {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (n : ℕ) : ∀ U W : Submodule K V, Module.finrank K U = Module.finrank K W →
      Module.finrank K V = Module.finrank K U + n →
      ∃ T : Submodule K V, Disjoint T U ∧ Disjoint T W ∧
        Module.finrank K V = Module.finrank K U + Module.finrank K T := by
  induction n with
  | zero =>
    intro U W _ hn
    refine ⟨⊥, disjoint_bot_left, disjoint_bot_left, ?_⟩
    rw [finrank_bot]
    omega
  | succ n ih =>
    intro U W hUW hn
    have hU : U ≠ ⊤ := by
      rintro rfl
      rw [finrank_top] at hn
      omega
    have hW : W ≠ ⊤ := by
      rintro rfl
      rw [finrank_top] at hUW
      omega
    obtain ⟨v, hvU, hvW⟩ := exists_not_mem_of_ne_top_of_ne_top U W hU hW
    have hv0 : v ≠ 0 := fun h => hvU (by rw [h]; exact U.zero_mem)
    have hback : ∀ S : Submodule K V, ∀ c : K, c ≠ 0 → c • v ∈ S → v ∈ S := by
      intro S c hc hcv
      have hm := S.smul_mem c⁻¹ hcv
      first
      | (rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at hm)
      | simpa [hc] using hm
    have hinf : ∀ S : Submodule K V, v ∉ S → S ⊓ Submodule.span K {v} = ⊥ := by
      intro S hvS
      rw [eq_bot_iff]
      intro z hz
      rw [Submodule.mem_bot]
      obtain ⟨hzS, hzv⟩ := Submodule.mem_inf.mp hz
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hzv
      by_cases hc : c = 0
      · simp [hc]
      · exact (hvS (hback S c hc hzS)).elim
    have key : ∀ S : Submodule K V, v ∉ S →
        Module.finrank K ↥(S ⊔ Submodule.span K {v}) = Module.finrank K S + 1 := by
      intro S hvS
      have h := Submodule.finrank_sup_add_finrank_inf_eq S (Submodule.span K {v})
      rw [hinf S hvS, finrank_bot, finrank_span_singleton hv0] at h
      omega
    obtain ⟨T, hTU, hTW, hT⟩ := ih (U ⊔ Submodule.span K {v}) (W ⊔ Submodule.span K {v})
      (by rw [key U hvU, key W hvW, hUW]) (by rw [key U hvU]; omega)
    have hvT : v ∉ T := fun h => hv0 (eq_zero_of_mem_of_disjoint hTU h
      (Submodule.mem_sup_right (Submodule.mem_span_singleton_self v)))
    have disj : ∀ S : Submodule K V, v ∉ S → Disjoint T (S ⊔ Submodule.span K {v}) →
        Disjoint (T ⊔ Submodule.span K {v}) S := by
      intro S hvS hTS
      rw [disjoint_iff, eq_bot_iff]
      intro z hz
      rw [Submodule.mem_bot]
      obtain ⟨hz1, hzS⟩ := Submodule.mem_inf.mp hz
      obtain ⟨t, ht, w', hw', rfl⟩ := Submodule.mem_sup.mp hz1
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw'
      have ht0 : t = 0 := by
        refine eq_zero_of_mem_of_disjoint hTS ht ?_
        have htt : t = (t + c • v) - c • v := by abel
        rw [htt]
        exact Submodule.sub_mem _ (Submodule.mem_sup_left hzS)
          (Submodule.mem_sup_right (Submodule.smul_mem _ c (Submodule.mem_span_singleton_self v)))
      subst ht0
      by_cases hc : c = 0
      · simp [hc]
      · exact (hvS (hback S c hc (by simpa using hzS))).elim
    refine ⟨T ⊔ Submodule.span K {v}, disj U hvU hTU, disj W hvW hTW, ?_⟩
    rw [key T hvT]
    rw [key U hvU] at hT
    omega

theorem fix_tuple {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {a : ℕ}
    (x : Fin a → V) (hx : LinearIndependent K x) (φ ψ : Fin a → Module.Dual K V)
    (hφ : LinearIndependent K φ) (hψ : LinearIndependent K ψ) (h : ∀ i j, φ i (x j) = ψ i (x j)) :
    ∃ B : V ≃ₗ[K] V, (∀ j, B (x j) = x j) ∧ ∀ i v, ψ i (B v) = φ i v := by
  let Φ : V →ₗ[K] (Fin a → K) := LinearMap.pi φ
  let Ψ : V →ₗ[K] (Fin a → K) := LinearMap.pi ψ
  have hΦ : Function.Surjective Φ := pi_surj φ hφ
  have hΨ : Function.Surjective Ψ := pi_surj ψ hψ
  have eΦ := LinearMap.finrank_range_add_finrank_ker Φ
  have eΨ := LinearMap.finrank_range_add_finrank_ker Ψ
  rw [LinearMap.range_eq_top.mpr hΦ, finrank_top] at eΦ
  rw [LinearMap.range_eq_top.mpr hΨ, finrank_top] at eΨ
  obtain ⟨T, hTΦ, hTΨ, hT⟩ := exists_common_complement_of_finrank_eq
    (Module.finrank K V - Module.finrank K (LinearMap.ker Φ)) (LinearMap.ker Φ) (LinearMap.ker Ψ)
    (by omega) (by omega)
  have hTdim : Module.finrank K T = Module.finrank K (Fin a → K) := by omega
  let f : T →ₗ[K] (Fin a → K) := Ψ.domRestrict T
  have hfinj : Function.Injective f := by
    refine (injective_iff_map_eq_zero f).mpr fun t ht => ?_
    have h0 : (t : V) = 0 := eq_zero_of_mem_of_disjoint hTΨ t.2 (LinearMap.mem_ker.mpr ht)
    first
    | exact Subtype.ext h0
    | simpa using h0
  have hfsurj : Function.Surjective f := by
    first
    | exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hTdim).mp hfinj
    | exact LinearMap.range_eq_top.mp
        ((LinearMap.ker_eq_bot_iff_range_eq_top_of_finrank_eq_finrank hTdim).mp
          (LinearMap.ker_eq_bot.mpr hfinj))
  let eT : T ≃ₗ[K] (Fin a → K) := LinearEquiv.ofBijective f ⟨hfinj, hfsurj⟩
  let s : (Fin a → K) →ₗ[K] V := T.subtype ∘ₗ eT.symm.toLinearMap
  have hs : ∀ t, Ψ (s t) = t := by
    intro t
    have h1 : Ψ (s t) = eT (eT.symm t) := by
      first
      | rfl
      | exact (LinearEquiv.ofBijective_apply f _ (eT.symm t)).symm
    rw [h1, LinearEquiv.apply_symm_apply]
  have hsT : ∀ t, s t ∈ T := fun t => (eT.symm t).2
  let B : V →ₗ[K] V := LinearMap.id + s ∘ₗ (Φ - Ψ)
  have hBv : ∀ v, B v = v + s (Φ v - Ψ v) := by
    intro v
    first
    | rfl
    | simp [B]
  have hΨB : ∀ v, Ψ (B v) = Φ v := by
    intro v
    rw [hBv, map_add, hs]
    abel
  have hBx : ∀ j, B (x j) = x j := by
    intro j
    have hM : Φ (x j) = Ψ (x j) := funext fun i => h i j
    rw [hBv, hM, sub_self, map_zero, add_zero]
  have hinj : Function.Injective B := by
    refine (injective_iff_map_eq_zero B).mpr fun v hv => ?_
    have hΦv : Φ v = 0 := by rw [← hΨB v, hv, map_zero]
    have hvT : v ∈ T := by
      rw [hBv] at hv
      rw [eq_neg_of_add_eq_zero_left hv]
      exact T.neg_mem (hsT _)
    exact eq_zero_of_mem_of_disjoint hTΦ hvT (LinearMap.mem_ker.mpr hΦv)
  refine ⟨LinearEquiv.ofInjectiveEndo B hinj, fun j => ?_, fun i v => ?_⟩
  · first
    | exact hBx j
    | simpa using hBx j
  · first
    | exact congrFun (hΨB v) i
    | simpa using congrFun (hΨB v) i

theorem glPair {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {a : ℕ}
    (x y : Fin a → V) (ξ η : Fin a → Module.Dual K V) (hx : LinearIndependent K x)
    (hy : LinearIndependent K y) (hξ : LinearIndependent K ξ) (hη : LinearIndependent K η)
    (h : ∀ i j, ξ i (x j) = η i (y j)) :
    ∃ A : V ≃ₗ[K] V, (∀ j, A (x j) = y j) ∧ ∀ i v, η i (A v) = ξ i v := by
  obtain ⟨A0, hA0⟩ := trans_tuple x y hx hy
  have hψ' : LinearIndependent K (fun i => (η i).comp A0.toLinearMap) := by
    rw [Fintype.linearIndependent_iff] at hη ⊢
    intro g hg
    apply hη g
    refine LinearMap.ext fun v => ?_
    have hgv := LinearMap.congr_fun hg (A0.symm v)
    first
    | simpa using hgv
    | simpa [LinearMap.sum_apply] using hgv
  obtain ⟨B, hB1, hB2⟩ := fix_tuple x hx ξ
    (fun i => (η i).comp A0.toLinearMap) hξ hψ' (fun i j => by
      show ξ i (x j) = η i (A0 (x j))
      rw [hA0 j, h i j])
  refine ⟨B.trans A0, fun j => ?_, fun i v => ?_⟩
  · rw [LinearEquiv.trans_apply, hB1 j, hA0 j]
  · rw [LinearEquiv.trans_apply]
    exact hB2 i v

end Formalism.L2.SG.Pf.NcS.LT.GLP

#print axioms Formalism.L2.SG.Pf.NcS.LT.GLP.surj_equiv

#print axioms Formalism.L2.SG.Pf.NcS.LT.GLP.pi_surj

#print axioms Formalism.L2.SG.Pf.NcS.LT.GLP.trans_tuple
