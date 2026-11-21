import Compaction.PrincipalCyclotomicPrime
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.PlaceDict

/-! All absolute places above the ramified prime of a prime-power cyclotomic
field are conjugate by an automorphism fixing that number field. -/

noncomputable section
namespace Compaction.CyclotomicPlaceConjugacy

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
  Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum
open scoped Pointwise

variable {p k : ℕ} [Fact p.Prime] (K Ω : Type) [Field K] [NumberField K] [Field Ω]
  [alg : Algebra ℚ K] [Algebra ℚ Ω] [Algebra K Ω] [IsScalarTower ℚ K Ω]
  [IsAlgClosure ℚ Ω] [IsAlgClosure K Ω]
  [IsCyclotomicExtension {p^(k+1)} ℚ K]

include k

theorem conjugate (v₀ : HeightOneSpectrum (𝓞 K))
    (hv₀ : (p : 𝓞 K) ∈ v₀.asIdeal) (A₀ : ValuationSubring Ω) (hA₀ : IsPlaceOver A₀ v₀)
    (A : ValuationSubring Ω) (hA : A.valuation (p : Ω) < 1) :
    ∃ σ : G ℚ Ω, σ • A₀ = A := by
  obtain rfl : alg = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  have hp : p.Prime := Fact.out
  obtain ⟨v, hv⟩ := (placeDict K Ω).2.1 A ((placeDict K Ω).2.2.1 A p hp.ne_zero hA)
  have hpv : (p : 𝓞 K) ∈ v.asIdeal := by
    simpa only [Above, Set.mem_setOf_eq] using ((placeDict K Ω).2.2.2 A v p hv).mp hA
  have heq : v = v₀ := PrincipalCyclotomicPrime.unique (k:=k) K v v₀ hpv hv₀
  have hplace : IsPlaceOver A v₀ := heq ▸ hv
  obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver (F := K) hA₀ hplace
  refine ⟨σ.restrictScalars ℚ, ?_⟩
  change σ • A₀ = A
  exact hσ

end Compaction.CyclotomicPlaceConjugacy

#print axioms Compaction.CyclotomicPlaceConjugacy.conjugate
