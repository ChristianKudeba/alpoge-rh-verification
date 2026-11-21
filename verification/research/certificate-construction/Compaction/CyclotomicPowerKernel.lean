import Compaction.HilbertPowerKernel
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.IneCyc

/-! Two arithmetic consequences for the elementary Hilbert-class kernel over
a prime-power cyclotomic field. Candidate pending full-import compilation. -/

noncomputable section
namespace Compaction.CyclotomicPowerKernel

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
  Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum

variable (K Ω : Type) [Field K] [NumberField K] [Field Ω]
  [Algebra ℚ K] [Algebra ℚ Ω] [Algebra K Ω] [IsScalarTower ℚ K Ω]
  [IsAlgClosure ℚ Ω] [IsAlgClosure K Ω] [Normal ℚ K]

theorem contains_outside_prime {p k : ℕ} [Fact p.Prime]
    [IsCyclotomicExtension {p^k} ℚ K] (n : ℕ) (A : ValuationSubring Ω)
    (hA : ¬ A.valuation (p : Ω) < 1) :
    Ine (F := ℚ) A ≤ HilbertPowerKernel.kernel K Ω n := by
  intro g hg
  let u : galOf ℚ K Ω := ⟨g, UpperTheory.V.FW.ineCyc ℚ Ω K p k A hA hg⟩
  exact HilbertPowerKernel.contains_relative_inertia K Ω n A u hg

theorem quotient_is_two_group (k : ℕ) [IsCyclotomicExtension {2^(k+1)} ℚ K] :
    letI := HilbertPowerKernel.normal K Ω 2
    IsPGroup 2 (G ℚ Ω ⧸ HilbertPowerKernel.kernel K Ω 2) := by
  letI := HilbertPowerKernel.normal K Ω 2
  letI : NeZero (2^(k+1) : ℕ) := ⟨by positivity⟩
  haveI : Finite (G ℚ Ω ⧸ HilbertPowerKernel.kernel K Ω 2) :=
    (HilbertPowerKernel.kernel K Ω 2).quotient_finite_of_isOpen
      (HilbertPowerKernel.isOpen K Ω 2)
  let C := ClassGroup (𝓞 K)
  let S := (powMonoidHom 2 : C →* C).range
  have hC : IsPGroup 2 (C ⧸ S) := by
    intro x
    refine ⟨1, ?_⟩
    obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective x
    simp only [pow_one]
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact ⟨c, rfl⟩
  obtain ⟨r, hr⟩ := IsPGroup.iff_card.mp hC
  have hidx : S.index = 2^r := by simpa only [Subgroup.index_eq_card] using hr
  have hdegree : Module.finrank ℚ K = 2^k := by
    calc Module.finrank ℚ K = (2^(k+1)).totient :=
          IsCyclotomicExtension.finrank K
            (Polynomial.cyclotomic.irreducible_rat (by positivity))
      _ = 2^k := by rw [Nat.totient_prime_pow_succ Nat.prime_two]; simp
  apply IsPGroup.of_card (n := r+k)
  rw [← Subgroup.index_eq_card, HilbertPowerKernel.index K Ω 2, hidx, hdegree,
    pow_add]

end Compaction.CyclotomicPowerKernel

#print axioms Compaction.CyclotomicPowerKernel.contains_outside_prime
#print axioms Compaction.CyclotomicPowerKernel.quotient_is_two_group
