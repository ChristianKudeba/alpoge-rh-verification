import Mathlib

@[reducible] noncomputable def UpperTheory.Reformulated.B.Uc13.Af
    (F : Type) [Field F] [NumberField F] : Type :=
  IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F

@[reducible] noncomputable def UpperTheory.Reformulated.B.Uc13.Fv
    (F : Type) [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) : Type :=
  IsDedekindDomain.HeightOneSpectrum.adicCompletion F v

theorem UpperTheory.Reformulated.B.Uc13.aux3
    (F : Type) [Field F] [NumberField F]
    (i : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    SubringClass (ValuationSubring (IsDedekindDomain.HeightOneSpectrum.adicCompletion F i))
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion F i) := inferInstance

theorem UpperTheory.Reformulated.B.Uc13.aux4
    (F : Type) [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (x : F) :
    RestrictedProduct.evalRingHom (fun w => IsDedekindDomain.HeightOneSpectrum.adicCompletion F w) v
        (algebraMap F (UpperTheory.Reformulated.B.Uc13.Af F) x) =
      RestrictedProduct.evalRingHom (fun w => IsDedekindDomain.HeightOneSpectrum.adicCompletion F w) v
        (algebraMap F (UpperTheory.Reformulated.B.Uc13.Af F) x) := rfl


noncomputable def UpperTheory.Reformulated.B.Uc13.evalV
    (F : Type) [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    UpperTheory.Reformulated.B.Uc13.Af F →ₐ[F] UpperTheory.Reformulated.B.Uc13.Fv F v where
  toRingHom := RestrictedProduct.evalRingHom
    (fun w => IsDedekindDomain.HeightOneSpectrum.adicCompletion F w) v
  commutes' := UpperTheory.Reformulated.B.Uc13.aux4 F v

noncomputable def UpperTheory.Reformulated.B.Uc13.intAf
    (F : Type) [Field F] [NumberField F] : Set (UpperTheory.Reformulated.B.Uc13.Af F) :=
  {a | ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F),
    UpperTheory.Reformulated.B.Uc13.evalV F v a ∈
      IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers F v}

open scoped TensorProduct

noncomputable def UpperTheory.Reformulated.B.Uc13.intA
    (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] :
    AddSubgroup (TensorProduct F (UpperTheory.Reformulated.B.Uc13.Af F) E) :=
  AddSubgroup.closure {y | ∃ a ∈ UpperTheory.Reformulated.B.Uc13.intAf F,
    ∃ x : NumberField.RingOfIntegers E, y = a ⊗ₜ[F] (x : E)}

private theorem UpperTheory.Reformulated.B.Uc13.intAf_mul (F : Type) [Field F] [NumberField F]
    {a b : UpperTheory.Reformulated.B.Uc13.Af F} (ha : a ∈ UpperTheory.Reformulated.B.Uc13.intAf F)
    (hb : b ∈ UpperTheory.Reformulated.B.Uc13.intAf F) : a * b ∈ UpperTheory.Reformulated.B.Uc13.intAf F := by
  intro v
  rw [map_mul]
  exact mul_mem (ha v) (hb v)


theorem UpperTheory.Reformulated.B.Uc13.mul_mem_intA :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
      {x y : TensorProduct F (UpperTheory.Reformulated.B.Uc13.Af F) E},
      x ∈ UpperTheory.Reformulated.B.Uc13.intA F E →
      y ∈ UpperTheory.Reformulated.B.Uc13.intA F E →
      x * y ∈ UpperTheory.Reformulated.B.Uc13.intA F E := by
  intro F E _ _ _ _ _ x y hx hy
  unfold UpperTheory.Reformulated.B.Uc13.intA at *
  induction hx, hy using AddSubgroup.closure_induction₂ with
  | mem x y hx hy =>
    obtain ⟨a, ha, s, rfl⟩ := hx
    obtain ⟨b, hb, t, rfl⟩ := hy
    refine AddSubgroup.subset_closure
      ⟨a * b, UpperTheory.Reformulated.B.Uc13.intAf_mul F ha hb, s * t, ?_⟩
    rw [Algebra.TensorProduct.tmul_mul_tmul]
    rfl
  | zero_left x hx => rw [zero_mul]; exact zero_mem _
  | zero_right x hx => rw [mul_zero]; exact zero_mem _
  | add_left x y z hx hy hz h1 h2 => rw [add_mul]; exact add_mem h1 h2
  | add_right y z x hy hz hx h1 h2 => rw [mul_add]; exact add_mem h1 h2
  | neg_left x y hx hy h => rw [neg_mul]; exact neg_mem h
  | neg_right x y hx hy h => rw [mul_neg]; exact neg_mem h
