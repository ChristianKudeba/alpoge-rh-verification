import Joint.WeberBase
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.IsAlgClosureRat

noncomputable section
namespace Joint.WeberRank
open NumberField Formalism.HC Formalism.ConjugateSelfDual ReciprocityTheory.Gal
  Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two

private theorem fn_cyclotomic (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
    [IsAlgClosure K Ω] (n : ℕ) : IsCyclotomicExtension {2^n} K (Fn K Ω 2 n) :=
  (fnCyc K Ω 2 n).1

theorem gaussian (web : Joint.WeberBase.Weber) (Ω : Type) [Field Ω]
    [Algebra (CyclotomicField 4 ℚ) Ω] [IsAlgClosure (CyclotomicField 4 ℚ) Ω] :
    XRk 2 1 (cycU 2 (⊤ : Subgroup (G (CyclotomicField 4 ℚ) Ω))) 0 := by
  let K := CyclotomicField 4 ℚ
  letI : IsCyclotomicExtension {4} ℚ K := CyclotomicField.isCyclotomicExtension 4 ℚ
  apply infRk K Ω 2 1 0 ⊤ one_ne_zero isClosed_univ
  intro n hn
  let F := Fn K Ω 2 n
  letI : IsCyclotomicExtension {2^n} K F := fn_cyclotomic K Ω n
  letI : IsScalarTower ℚ K F := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  exact levelRk K Ω 2 n 0 hn (by simpa only [pow_zero] using
    (Joint.WeberBase.class_quotient web n hn K F).le)

theorem base_zero (web : Joint.WeberBase.Weber) (Ω : Type) [Field Ω]
    [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] :
    XRk 2 1 (cycU 2 (abU Ω (withI (AbF.ofChar PChar.one)))) 0 := by
  let K := CyclotomicField 4 ℚ
  letI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  letI : Algebra K Ω := (IsAlgClosed.lift : K →ₐ[ℚ] Ω).toRingHom.toAlgebra
  letI : IsScalarTower ℚ K Ω := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  letI : IsAlgClosure K Ω := ⟨inferInstance,Algebra.IsAlgebraic.tower_top (K:=ℚ) K⟩
  rw [←abField Ω _ K Joint.WeberBase.realized]
  exact (rkTransport ℚ Ω K 2 1 0).mp (gaussian web Ω)

/-- Adding the two ramified quadratic characters costs at most 24 generators. -/
theorem moving_rank (web : Joint.WeberBase.Weber) (Ω : Type) [Field Ω]
    [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (q d : ℕ) (hp : PrimePair 1 q d) :
    XRk 2 1 (cycU 2 (abU Ω (base2 (AbF.ofChar PChar.one) q d))) 24 := by
  have hdeg : (AbF.ofChar PChar.one).deg = 1 := by
    change (1 : DirichletCharacter ℂ 1).toUnitHom.ker.index = 1
    exact Subgroup.index_eq_one.mpr (Subsingleton.elim _ _)
  simpa only [hdeg,zero_add,Nat.mul_one] using
    baseRk Ω (AbF.ofChar PChar.one) q d 0 hp (base_zero web Ω)

end Joint.WeberRank
#print axioms Joint.WeberRank.moving_rank

