import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes

noncomputable section
namespace Joint.WeberBase
open NumberField Formalism.HC UpperTheory.Top UpperTheory.V UpperTheory.V.Two

/-- Weber's odd-class-number theorem for cyclotomic fields of 2-power conductor. -/
def Weber : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ (F : Type) [Field F] [NumberField F]
    [IsCyclotomicExtension {2^n} ℚ F], Odd (classNumber F)

theorem with_i : withI (AbF.ofChar PChar.one) = AbF.cyc 4 := by
  change (⟨4,by decide, _⟩ : AbF) = ⟨4,by decide,⊥⟩
  congr 1
  have hm (x : (ZMod 4)ˣ) : ZMod.unitsMap (dvd_refl 4) x = x := by
    apply Units.ext
    simp <;> rfl
  apply Subgroup.ext
  intro x
  change ((ZMod.unitsMap (by decide : 1 ∣ 4) x ∈ (AbF.ofChar PChar.one).H) ∧
    ZMod.unitsMap (dvd_refl 4) x = 1) ↔ x = 1
  refine ⟨fun h => (hm x).symm.trans h.2,?_⟩
  rintro rfl
  exact ⟨(ZMod.unitsMap (by decide : 1 ∣ 4)).map_one ▸ (AbF.ofChar PChar.one).H.one_mem,
    (ZMod.unitsMap (dvd_refl 4)).map_one⟩

theorem realized : IsAbField (withI (AbF.ofChar PChar.one)) (CyclotomicField 4 ℚ) := by
  rw [with_i]
  let K := CyclotomicField 4 ℚ
  letI : IsCyclotomicExtension {4} ℚ K := CyclotomicField.isCyclotomicExtension 4 ℚ
  let z := IsCyclotomicExtension.zeta 4 ℚ K
  have hz : IsPrimitiveRoot z 4 := IsCyclotomicExtension.zeta_spec 4 ℚ K
  refine ⟨4,inferInstance,AlgHom.id ℚ K,z,by decide,hz,fun σ a hσ => ?_⟩
  have ker : (AbF.cyc 4).ker a ↔ a ≡ 1 [MOD 4] := by
    change (∃ u : (ZMod 4)ˣ, u ∈ (⊥ : Subgroup _) ∧ (u : ZMod 4) = a) ↔ _
    rw [← ZMod.natCast_eq_natCast_iff]
    simp [eq_comm]
  rw [ker]
  have hh : σ z = z ↔ a ≡ 1 [MOD 4] := by
    rw [hσ]
    have ho : IsOfFinOrder z := isOfFinOrder_iff_pow_eq_one.mpr ⟨4,by decide,hz.pow_eq_one⟩
    simpa only [pow_one,←hz.eq_orderOf] using ho.pow_eq_pow_iff_modEq (n:=a) (m:=1)
  rw [←hh]
  refine ⟨fun h => h z,fun h => ?_⟩
  have hσ' : σ = (AlgEquiv.refl : K ≃ₐ[ℚ] K) :=
    IsCyclotomicExtension.algEquiv_eq_of_apply_eq {4} ℚ K fun m hm _ => by
      obtain rfl := Set.mem_singleton_iff.mp hm
      exact ⟨z,hz,h⟩
  simp [hσ']

theorem squares_surjective (G : Type*) [CommGroup G] [Finite G] (h : Odd (Nat.card G)) :
    Function.Surjective (powMonoidHom 2 : G →* G) := by
  obtain ⟨k,hk⟩ := h
  intro a
  refine ⟨a^(k+1),?_⟩
  change (a^(k+1))^2 = a
  rw [←pow_mul,show (k+1)*2 = Nat.card G+1 by omega,pow_succ,pow_card_eq_one',one_mul]

theorem class_quotient (web : Weber) (n : ℕ) (hn : 2 ≤ n)
    (K F : Type) [Field K] [NumberField K] [IsCyclotomicExtension {4} ℚ K]
    [Field F] [NumberField F] [Algebra K F] [IsScalarTower ℚ K F]
    [IsCyclotomicExtension {2^n} K F] :
    Nat.card (ClassGroup (𝓞 F) ⧸ (powMonoidHom 2 : ClassGroup (𝓞 F) →* _).range) = 1 := by
  have hu := IsCyclotomicExtension.trans ({4}:Set ℕ) {2^n} ℚ K F (algebraMap K F).injective
  have hd : 4 ∣ 2^n := (by norm_num : (4:ℕ) ∣ 2^2).trans (pow_dvd_pow 2 hn)
  letI : IsCyclotomicExtension {2^n} ℚ F :=
    (IsCyclotomicExtension.iff_union_of_dvd ℚ F (S:=({2^n}:Set ℕ)) (n:=4)
      ⟨2^n,rfl,by positivity,hd⟩).mpr (by simpa only [Set.union_comm] using hu)
  have odd : Odd (Nat.card (ClassGroup (𝓞 F))) := by
    simpa only [classNumber,Nat.card_eq_fintype_card] using web n hn F
  change (powMonoidHom 2 : ClassGroup (𝓞 F) →* _).range.index = 1
  exact Subgroup.index_eq_one.mpr (MonoidHom.range_eq_top.mpr (squares_surjective _ odd))

end Joint.WeberBase
#print axioms Joint.WeberBase.realized
#print axioms Joint.WeberBase.class_quotient

