import Mathlib

namespace UpperTheory.Reformulated.B.CovariantDegrees

noncomputable def jE {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω]
    [Algebra E Ω] (j : Ω →+* PadicAlgCl l) : E →+* PadicAlgCl l :=
  j.comp (algebraMap E Ω)

theorem aux2 {E : Type} [Field E] [NumberField E] : Module.Free ℚ E := inferInstance

noncomputable def KwF {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [NumberField E]
    [Field Ω] [Algebra E Ω] (j : Ω →+* PadicAlgCl l) : IntermediateField ℚ_[l] (PadicAlgCl l) :=
  IntermediateField.adjoin ℚ_[l] (Set.range fun i => jE j (Module.finBasis ℚ E i))

@[reducible] noncomputable def G.{u_1, u_2} (F : Type u_1) (Ω : Type u_2)
    [Field F] [Field Ω] [Algebra F Ω] : Type u_2 := Ω ≃ₐ[F] Ω

noncomputable def Dec.{u_1, u_2} {F : Type u_1} {Ω : Type u_2}
    [Field F] [Field Ω] [Algebra F Ω] (A : ValuationSubring Ω) : Subgroup (G F Ω) :=
  A.decompositionSubgroup F

theorem aux6 {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] :
    Module.IsTorsionFree E Ω := inferInstance

theorem aux7 {Ω : Type} [Field Ω] [CharZero Ω] : Module.IsTorsionFree ℚ Ω := inferInstance

@[reducible] noncomputable def Om (l : ℕ) [Fact l.Prime] : Type := PadicAlgCl l

@[reducible] noncomputable def GQ (l : ℕ) [Fact l.Prime] : Type := Om l ≃ₐ[ℚ_[l]] Om l

theorem laurent_T_neg_one_mul_T_one {l : ℕ} [Fact l.Prime] :
    IsScalarTower ℚ ℚ_[l] (Om l) := inferInstance

theorem aux11 {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [CharZero Ω]
    (j : Ω →+* PadicAlgCl l) :
    letI : Algebra Ω (PadicAlgCl l) := j.toAlgebra
    IsScalarTower ℚ Ω (PadicAlgCl l) := by
  letI : Algebra Ω (PadicAlgCl l) := j.toAlgebra
  exact IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)

theorem aux12 {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] : Normal ℚ Ω :=
  inferInstance

noncomputable def resQ {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [CharZero Ω]
    [IsAlgClosure ℚ Ω] (j : Ω →+* PadicAlgCl l) (σ : GQ l) : Ω ≃ₐ[ℚ] Ω :=
  letI : Algebra Ω (PadicAlgCl l) := j.toAlgebra
  haveI : IsScalarTower ℚ Ω (PadicAlgCl l) := aux11 j
  haveI : IsScalarTower ℚ ℚ_[l] (PadicAlgCl l) := laurent_T_neg_one_mul_T_one
  haveI : Normal ℚ Ω := aux12
  (σ.restrictScalars ℚ).toAlgHom.restrictNormal' Ω

private theorem j_resQ {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [CharZero Ω]
    [IsAlgClosure ℚ Ω] (j : Ω →+* PadicAlgCl l) (σ : GQ l) (x : Ω) :
    j (resQ j σ x) = σ (j x) := by
  letI : Algebra Ω (PadicAlgCl l) := j.toAlgebra
  haveI := aux11 j
  haveI : Normal ℚ Ω := aux12
  exact AlgHom.restrictNormal_commutes (σ.restrictScalars ℚ).toAlgHom Ω x

private theorem jE_mem {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [NumberField E]
    [Field Ω] [Algebra E Ω] (j : Ω →+* PadicAlgCl l) (x : E) :
    jE j x ∈ KwF (E := E) j := by
  rw [← (Module.finBasis ℚ E).sum_repr x, map_sum]
  refine sum_mem fun i _ => ?_
  rw [Rat.smul_def, map_mul, map_ratCast]
  exact mul_mem (SubfieldClass.ratCast_mem _ _) (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)

theorem zero_contDiffOn_supported :
    ∀ {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [NumberField E]
      [Field Ω] [Algebra E Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]
      (j : Ω →+* PadicAlgCl l), ∀ σ ∈ (KwF (E := E) j).fixingSubgroup,
      ∀ x : E, (resQ j σ).toRingEquiv ((algebraMap E Ω) x) = (algebraMap E Ω) x := by
  intro l hl E Ω _ _ _ _ _ _ j σ hσ x
  apply j.injective
  refine (j_resQ j σ _).trans ?_
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ _ (jE_mem j x)

noncomputable def resE {l : ℕ} [Fact l.Prime] {E Ω : Type}
    [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]
    (j : Ω →+* PadicAlgCl l) (σ : GQ l)
    (hσ : σ ∈ (KwF (E := E) j).fixingSubgroup) : G E Ω :=
  AlgEquiv.ofRingEquiv (zero_contDiffOn_supported j σ hσ)

private theorem j_resE {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [NumberField E]
    [Field Ω] [Algebra E Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (j : Ω →+* PadicAlgCl l)
    (σ : GQ l) (hσ : σ ∈ (KwF (E := E) j).fixingSubgroup) (x : Ω) :
    j (resE j σ hσ x) = σ (j x) :=
  j_resQ j σ x

open Pointwise in
private theorem resE_mem {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [NumberField E]
    [Field Ω] [Algebra E Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {j : Ω →+* PadicAlgCl l}
    {A : ValuationSubring Ω} (hj : ∀ x : Ω, x ∈ A ↔ ‖j x‖ ≤ 1)
    (σ : GQ l) (hσ : σ ∈ (KwF (E := E) j).fixingSubgroup) :
    resE j σ hσ ∈ Dec A := by
  have hn : ∀ x, ‖j (resE j σ hσ x)‖ = ‖j x‖ := fun x => by
    rw [j_resE]
    exact (spectralNorm_eq_of_equiv σ (j x)).symm
  refine MulAction.mem_stabilizer_iff.2 (SetLike.ext fun x => ?_)
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, hj, hj, ← hn]
  simp


theorem column_matrix_mul_inverse :
    ∀ {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [NumberField E]
      [Field Ω] [Algebra E Ω] {j : Ω →+* PadicAlgCl l}
      (σ : (KwF (E := E) j).fixingSubgroup), ↑σ ∈ (KwF (E := E) j).fixingSubgroup := by
  intro l hl E Ω _ _ _ _ j σ
  exact σ.2

theorem complex_normed_instance_compat :
    ∀ {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [NumberField E]
      [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]
      {j : Ω →+* PadicAlgCl l} {A : ValuationSubring Ω},
      (∀ x : Ω, x ∈ A ↔ ‖j x‖ ≤ 1) →
      ∀ σ : (KwF (E := E) j).fixingSubgroup, resE j σ.1 σ.2 ∈ Dec A := by
  intro l hl E Ω _ _ _ _ _ _ _ j A hj σ
  exact resE_mem hj _ _

theorem padic_embedding_algebra_compat :
    ∀ {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [NumberField E]
      [Field Ω] [Algebra E Ω] {j : Ω →+* PadicAlgCl l},
      ↑(1 : (KwF (E := E) j).fixingSubgroup) ∈ (KwF (E := E) j).fixingSubgroup := by
  intro l hl E Ω _ _ _ _ j
  exact Subgroup.one_mem _

theorem blockM_one_partner_eq_one :
    ∀ {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [NumberField E]
      [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]
      {j : Ω →+* PadicAlgCl l} {A : ValuationSubring Ω},
      (∀ x : Ω, x ∈ A ↔ ‖j x‖ ≤ 1) →
      resE (E := E) j (↑(1 : (KwF (E := E) j).fixingSubgroup)) (Subgroup.one_mem _) ∈ Dec A := by
  intro l hl E Ω _ _ _ _ _ _ _ j A hj
  exact resE_mem hj _ _

theorem blockM_mul_alt :
    ∀ {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [NumberField E]
      [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]
      {j : Ω →+* PadicAlgCl l} {A : ValuationSubring Ω}
      (hj : ∀ x : Ω, x ∈ A ↔ ‖j x‖ ≤ 1),
      (⟨resE (E := E) j (↑(1 : (KwF (E := E) j).fixingSubgroup))
        (padic_embedding_algebra_compat), blockM_one_partner_eq_one hj⟩ : Dec (F := E) A) = 1 := by
  intro l hl E Ω _ _ _ _ _ _ _ j A hj
  refine Subtype.ext (AlgEquiv.ext fun x => j.injective ?_)
  exact j_resE (E := E) j 1 (Subgroup.one_mem _) x

theorem conj_invariant_character_mem :
    ∀ {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [NumberField E]
      [Field Ω] [Algebra E Ω] {j : Ω →+* PadicAlgCl l}
      (σ τ : (KwF (E := E) j).fixingSubgroup), ↑(σ * τ) ∈ (KwF (E := E) j).fixingSubgroup := by
  intro l hl E Ω _ _ _ _ j σ τ
  exact (σ * τ).2

theorem rootGL_mem_unitary :
    ∀ {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [NumberField E]
      [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]
      {j : Ω →+* PadicAlgCl l} {A : ValuationSubring Ω},
      (∀ x : Ω, x ∈ A ↔ ‖j x‖ ≤ 1) →
      ∀ σ τ : (KwF (E := E) j).fixingSubgroup, resE j (σ * τ).1 (σ * τ).2 ∈ Dec A := by
  intro l hl E Ω _ _ _ _ _ _ _ j A hj σ τ
  exact resE_mem hj _ _

theorem conj_invariant_character_transport :
    ∀ {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [NumberField E]
      [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]
      {j : Ω →+* PadicAlgCl l} {A : ValuationSubring Ω}
      (hj : ∀ x : Ω, x ∈ A ↔ ‖j x‖ ≤ 1) (σ τ : (KwF (E := E) j).fixingSubgroup),
      (⟨resE j (σ * τ).1 (σ * τ).2, rootGL_mem_unitary hj σ τ⟩ : Dec A) =
      ⟨resE j σ.1 σ.2, complex_normed_instance_compat hj σ⟩ *
      ⟨resE j τ.1 τ.2, complex_normed_instance_compat hj τ⟩ := by
  intro l hl E Ω _ _ _ _ _ _ _ j A hj σ τ
  refine Subtype.ext (AlgEquiv.ext fun x => j.injective ?_)
  refine (j_resE j (σ * τ).1 (σ * τ).2 x).trans ?_
  refine Eq.symm ((j_resE j σ.1 σ.2 (resE j τ.1 τ.2 x)).trans ?_)
  rw [j_resE]
  rfl

noncomputable def rHom {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [NumberField E]
    [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]
    {j : Ω →+* PadicAlgCl l} {A : ValuationSubring Ω} (hj : ∀ x : Ω, x ∈ A ↔ ‖j x‖ ≤ 1) :
    (KwF (E := E) j).fixingSubgroup →* Dec (F := E) A where
  toFun σ := ⟨resE j σ.1 σ.2, complex_normed_instance_compat hj σ⟩
  map_one' := blockM_mul_alt hj
  map_mul' := conj_invariant_character_transport hj

theorem continuous_rHom :
    ∀ {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [NumberField E]
      [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]
      {j : Ω →+* PadicAlgCl l} {A : ValuationSubring Ω} (hj : ∀ x : Ω, x ∈ A ↔ ‖j x‖ ≤ 1),
      Continuous (rHom (E := E) hj) := by
  intro l hl E Ω _ _ _ _ _ _ _ j A hj
  have h : Continuous ((Dec A).subtype.comp (rHom (E := E) hj)) := by
    apply continuous_of_continuousAt_one
    rw [ContinuousAt, map_one]
    intro s hs
    obtain ⟨L, hL, hLs⟩ := (krullTopology_mem_nhds_one_iff E Ω s).1 hs
    let b := Module.finBasis E L
    have hU : ∀ᶠ σ : (KwF (E := E) j).fixingSubgroup in nhds 1,
        ∀ i, σ.1 (j (b i)) = j (b i) := by
      refine Filter.eventually_all.2 fun i => ?_
      have ho := (stabilizer_isOpen_of_isIntegral (K := ℚ_[l]) (j (b i))).preimage
        (continuous_subtype_val (p := fun σ => σ ∈ (KwF (E := E) j).fixingSubgroup))
      exact ho.mem_nhds (Subgroup.one_mem (MulAction.stabilizer _ _))
    refine hU.mono fun σ hσ => hLs ?_
    refine (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx => ?_
    have key : (resE j σ.1 σ.2).toLinearMap ∘ₗ L.val.toLinearMap = L.val.toLinearMap :=
      b.ext fun i => j.injective ((j_resE j σ.1 σ.2 (b i)).trans (hσ i))
    exact LinearMap.congr_fun key ⟨x, hx⟩
  exact continuous_induced_rng.2 h

end UpperTheory.Reformulated.B.CovariantDegrees
