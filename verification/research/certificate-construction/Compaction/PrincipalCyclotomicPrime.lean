import Mathlib

/-! The only finite ramified prime in a prime-power cyclotomic field is
principal. Its class and hence its Artin Frobenius in every unramified abelian
extension are trivial. This is an arithmetic bridge for the Weber argument. -/

noncomputable section
namespace Compaction.PrincipalCyclotomicPrime

open NumberField IsDedekindDomain IsCyclotomicExtension.Rat

variable {p k : ℕ} [Fact p.Prime] (K : Type) [Field K] [NumberField K]
  [IsCyclotomicExtension {p^(k+1)} ℚ K]

include k

theorem principal (v : HeightOneSpectrum (𝓞 K)) (hv : (p : 𝓞 K) ∈ v.asIdeal) :
    v.asIdeal.IsPrincipal := by
  have hp : p.Prime := Fact.out
  letI : NeZero (p^(k+1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let ζ := IsCyclotomicExtension.zeta (p^(k+1)) ℚ K
  have hζ : IsPrimitiveRoot ζ (p^(k+1)) := IsCyclotomicExtension.zeta_spec _ ℚ K
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    Int.ideal_span_isMaximal_of_prime p
  letI : v.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := by
    refine ⟨hmax.eq_of_le (Ideal.comap_isPrime _ _).ne_top ?_⟩
    rw [Ideal.span_singleton_le_iff_mem, Ideal.under, Ideal.mem_comap]
    simpa using hv
  rw [eq_span_zeta_sub_one_of_liesOver p k K hζ v.asIdeal]
  infer_instance

theorem class_eq_one (v : HeightOneSpectrum (𝓞 K)) (hv : (p : 𝓞 K) ∈ v.asIdeal) :
    ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩ = 1 :=
  (ClassGroup.mk0_eq_one_iff _).mpr (principal (k:=k) K v hv)

theorem unique (v w : HeightOneSpectrum (𝓞 K))
    (hv : (p : 𝓞 K) ∈ v.asIdeal) (hw : (p : 𝓞 K) ∈ w.asIdeal) : v = w := by
  have hp : p.Prime := Fact.out
  letI : NeZero (p^(k+1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let ζ := IsCyclotomicExtension.zeta (p^(k+1)) ℚ K
  have hζ : IsPrimitiveRoot ζ (p^(k+1)) := IsCyclotomicExtension.zeta_spec _ ℚ K
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    Int.ideal_span_isMaximal_of_prime p
  letI : v.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := by
    refine ⟨hmax.eq_of_le (Ideal.comap_isPrime _ _).ne_top ?_⟩
    rw [Ideal.span_singleton_le_iff_mem, Ideal.under, Ideal.mem_comap]
    simpa using hv
  letI : w.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := by
    refine ⟨hmax.eq_of_le (Ideal.comap_isPrime _ _).ne_top ?_⟩
    rw [Ideal.span_singleton_le_iff_mem, Ideal.under, Ideal.mem_comap]
    simpa using hw
  apply HeightOneSpectrum.ext
  rw [eq_span_zeta_sub_one_of_liesOver p k K hζ v.asIdeal,
    eq_span_zeta_sub_one_of_liesOver p k K hζ w.asIdeal]

end Compaction.PrincipalCyclotomicPrime

#print axioms Compaction.PrincipalCyclotomicPrime.principal
#print axioms Compaction.PrincipalCyclotomicPrime.class_eq_one
#print axioms Compaction.PrincipalCyclotomicPrime.unique
