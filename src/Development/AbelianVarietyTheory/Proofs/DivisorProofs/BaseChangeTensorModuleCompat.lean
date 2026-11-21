import Mathlib
open TensorProduct

namespace GlobalTheory

set_option maxHeartbeats 1000000 in

theorem baseChange_tensor_int_field_equiv :
    ∀ (K L O : Type) [Field K] [Field L] [Algebra K L] [CommRing O] (M : Type) [AddCommGroup M]
    [Module K M] [Module O M] [SMulCommClass K O M] (N : Type) [AddCommGroup N] [Module L N] [Module O N]
    [SMulCommClass L O N] (e : L ⊗[K] M ≃ₗ[L] N), (∀ (a : O) (m : M), e (1 ⊗ₜ (a • m)) = a • e (1 ⊗ₜ m)) →
    letI : Module (K ⊗[ℤ] O) M := TensorProduct.Algebra.module
    letI : Module (L ⊗[ℤ] O) N := TensorProduct.Algebra.module
    ∃ _ : Algebra (K ⊗[ℤ] O) (L ⊗[ℤ] O), Module.FaithfullyFlat (K ⊗[ℤ] O) (L ⊗[ℤ] O) ∧
      Nonempty ((L ⊗[ℤ] O) ⊗[K ⊗[ℤ] O] M ≃ₗ[L ⊗[ℤ] O] N) := by
  intro R R' O _ _ _ _ M _ _ _ _ N _ _ _ _ e he
  letI : Module (R ⊗[ℤ] O) M := TensorProduct.Algebra.module
  letI : Module (R' ⊗[ℤ] O) N := TensorProduct.Algebra.module
  let f : R ⊗[ℤ] O →ₐ[ℤ] R' ⊗[ℤ] O :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom ℤ R R') (AlgHom.id ℤ O)
  letI : Algebra (R ⊗[ℤ] O) (R' ⊗[ℤ] O) := f.toRingHom.toAlgebra
  letI : Module (R ⊗[ℤ] O) N := Module.compHom N f.toRingHom
  haveI : IsScalarTower (R ⊗[ℤ] O) (R' ⊗[ℤ] O) N := ⟨fun a x n => mul_smul (f a) x n⟩
  have hf : ∀ (r : R) (o : O), f (r ⊗ₜ o) = algebraMap R R' r ⊗ₜ o := fun r o => rfl

  haveI : Module.FaithfullyFlat R R' := inferInstance
  haveI : IsScalarTower R (R ⊗[ℤ] O) (R' ⊗[ℤ] O) :=
    IsScalarTower.of_algebraMap_smul (R := R) (A := R ⊗[ℤ] O) (M := R' ⊗[ℤ] O) fun r x => by
      change algebraMap R (R' ⊗[ℤ] O) r * x = r • x
      exact (Algebra.smul_def r x).symm
  haveI : Algebra.IsPushout R R' (R ⊗[ℤ] O) (R' ⊗[ℤ] O) :=
    Algebra.IsPushout.tensorProduct_tensorProduct ℤ O R R' (by
      ext o
      change f ((1 : R) ⊗ₜ[ℤ] o) = (1 : R') ⊗ₜ[ℤ] o
      rw [hf, map_one])
  haveI : Algebra.IsPushout R (R ⊗[ℤ] O) R' (R' ⊗[ℤ] O) :=
    Algebra.IsPushout.symm inferInstance
  have hFF : Module.FaithfullyFlat (R ⊗[ℤ] O) (R' ⊗[ℤ] O) :=
    Module.FaithfullyFlat.of_linearEquiv (R ⊗[ℤ] O) ((R ⊗[ℤ] O) ⊗[R] R')
      (Algebra.IsPushout.equiv R (R ⊗[ℤ] O) R' (R' ⊗[ℤ] O)).toLinearEquiv.symm

  have hj : ∀ (a : R ⊗[ℤ] O) (m : M), e (1 ⊗ₜ (a • m)) = f a • e (1 ⊗ₜ m) := by
    intro a m
    induction a using TensorProduct.induction_on with
    | zero => simp only [Module.zero_smul, _root_.zero_smul, tmul_zero, map_zero]
    | tmul r o =>
      rw [hf, TensorProduct.Algebra.smul_def, TensorProduct.Algebra.smul_def, ← he,
        TensorProduct.tmul_smul, ← algebraMap_smul R', map_smul]
    | add a b ha hb => rw [add_smul, tmul_add, map_add, ha, hb, map_add, add_smul]
  let j : M →ₗ[R ⊗[ℤ] O] N :=
    { toFun := fun m => e (1 ⊗ₜ m)
      map_add' := fun x y => by simp [tmul_add]
      map_smul' := fun a m => hj a m }
  let Φ : (R' ⊗[ℤ] O) ⊗[R ⊗[ℤ] O] M →ₗ[R' ⊗[ℤ] O] N := LinearMap.liftBaseChange _ j
  haveI : IsScalarTower R (R ⊗[ℤ] O) M :=
    IsScalarTower.of_algebraMap_smul (R := R) (A := R ⊗[ℤ] O) (M := M) fun r m => by
      change r • ((1 : O) • m) = r • m
      rw [one_smul]
  haveI : IsScalarTower R' (R' ⊗[ℤ] O) N :=
    IsScalarTower.of_algebraMap_smul (R := R') (A := R' ⊗[ℤ] O) (M := N) fun r n => by
      change r • ((1 : O) • n) = r • n
      rw [one_smul]
  let c := Algebra.IsPushout.cancelBaseChange R R' (R ⊗[ℤ] O) (R' ⊗[ℤ] O) M
  have hΦ : (Φ.restrictScalars R').comp c.symm.toLinearMap = e.toLinearMap := by
    apply LinearMap.ext
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add y z hy hz => simp only [map_add, hy, hz]
    | tmul r m =>
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, c,
        Algebra.IsPushout.cancelBaseChange_symm_tmul, Φ, LinearMap.liftBaseChange_tmul]
      change (r ⊗ₜ[ℤ] (1 : O)) • e (1 ⊗ₜ m) = e (r ⊗ₜ m)
      rw [TensorProduct.Algebra.smul_def, one_smul, ← map_smul, TensorProduct.smul_tmul',
        smul_eq_mul, _root_.mul_one]
  have hbij : Function.Bijective Φ := by
    have hcomp : Function.Bijective ((Φ.restrictScalars R').comp c.symm.toLinearMap) := by
      rw [hΦ]
      exact e.bijective
    exact (Function.Bijective.of_comp_iff Φ c.symm.bijective).mp hcomp
  exact ⟨f.toRingHom.toAlgebra, hFF, ⟨LinearEquiv.ofBijective Φ hbij⟩⟩

end GlobalTheory
