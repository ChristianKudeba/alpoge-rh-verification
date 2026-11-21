import Compaction.HilbertPowerKernel
import Compaction.CyclotomicPowerKernel
import Compaction.PrincipalCyclotomicPrime
import Compaction.CyclotomicPlaceConjugacy
import Compaction.OddClassNumber
import Compaction.AbsoluteInertiaGeneration

/-! Weber's odd-class-number theorem by principal ramification, Minkowski and
the normal-generation property of finite 2-groups. No Ferrero--Washington or
Iwasawa bound is an assumption. Candidate pending full-import compilation. -/

noncomputable section
namespace Compaction.Weber

open NumberField IsDedekindDomain IsCyclotomicExtension.Rat Formalism.ConjugateSelfDual
  ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum
open scoped Pointwise

theorem odd_classNumber (n : ℕ) (hn : 2 ≤ n) (K : Type) [Field K] [NumberField K]
    [IsCyclotomicExtension {2^n} ℚ K] : Odd (classNumber K) := by
  let k := n-1
  have hkn : k+1=n := by dsimp [k]; omega
  letI : NeZero (2^(k+1) : ℕ) := ⟨by positivity⟩
  haveI : IsCyclotomicExtension {2^(k+1)} ℚ K := by rw [hkn]; infer_instance
  haveI : IsGalois ℚ K := IsCyclotomicExtension.isGalois {2^n} ℚ K
  let Ω := AlgebraicClosure K
  letI : IsAlgClosure ℚ Ω :=
    ⟨IsAlgClosure.isAlgClosed K, Algebra.IsAlgebraic.trans ℚ K Ω⟩
  let ζ := IsCyclotomicExtension.zeta (2^(k+1)) ℚ K
  have hζ : IsPrimitiveRoot ζ (2^(k+1)) := IsCyclotomicExtension.zeta_spec _ ℚ K
  let v : HeightOneSpectrum (𝓞 K) := ⟨Ideal.span {hζ.toInteger-1},
    isPrime_span_zeta_sub_one 2 k hζ, span_zeta_sub_one_ne_bot 2 k hζ⟩
  have hv : (2 : 𝓞 K) ∈ v.asIdeal := p_mem_span_zeta_sub_one 2 k hζ
  let A₀ := placeOf Ω v
  have hA₀ : IsPlaceOver A₀ v := isPlaceOver_placeOf Ω v
  let N := HilbertPowerKernel.kernel K Ω 2
  let U := galOf ℚ K Ω
  haveI : N.Normal := HilbertPowerKernel.normal K Ω 2
  have hopen : IsOpen (N : Set (G ℚ Ω)) := HilbertPowerKernel.isOpen K Ω 2
  haveI : Finite (G ℚ Ω ⧸ N) := N.quotient_finite_of_isOpen hopen
  have hp : IsPGroup 2 (G ℚ Ω ⧸ N) :=
    CyclotomicPowerKernel.quotient_is_two_group K Ω k
  have hgen := inertia_normalClosure_eq_top Ω N hopen 2 A₀
    (fun A hA => CyclotomicPowerKernel.contains_outside_prime (p:=2) (k:=k+1) K Ω 2 A hA)
    (fun A hA => CyclotomicPlaceConjugacy.conjugate (p:=2) (k:=k) K Ω v hv A₀ hA₀ A hA)
  have hNU : N ≤ U := by
    rintro g ⟨u, _, rfl⟩
    exact u.2
  have hrel : Ine (F:=ℚ) A₀ ⊓ U ≤ N := by
    intro g hg
    let u : U := ⟨g, hg.2⟩
    exact HilbertPowerKernel.contains_relative_inertia K Ω 2 A₀ u hg.1
  have hUN : U=N := relative_kernel_eq N U (Ine (F:=ℚ) A₀) hNU hp hgen hrel
  have hidx := HilbertPowerKernel.index K Ω 2
  change N.index = (powMonoidHom 2 : ClassGroup (𝓞 K) →* ClassGroup (𝓞 K)).range.index *
    Module.finrank ℚ K at hidx
  have hUidx : U.index = Module.finrank ℚ K := (galEmbTop ℚ K Ω).2.2
  rw [← hUN, hUidx] at hidx
  have hdegree : 0 < Module.finrank ℚ K := Module.finrank_pos
  have hone : (powMonoidHom 2 : ClassGroup (𝓞 K) →* ClassGroup (𝓞 K)).range.index = 1 := by
    nlinarith
  exact OddClassNumber.classNumber_odd_of_square_index_one K hone

theorem weber :
    ∀ (n : ℕ), 2 ≤ n → ∀ (K : Type) [Field K] [NumberField K]
      [IsCyclotomicExtension {2^n} ℚ K], Odd (classNumber K) :=
  odd_classNumber

end Compaction.Weber

#print axioms Compaction.Weber.odd_classNumber
#print axioms Compaction.Weber.weber
