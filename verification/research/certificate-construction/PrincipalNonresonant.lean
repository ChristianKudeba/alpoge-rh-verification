import ConductorOneCases
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.GdOfHost

/-! Use Q(sqrt(-3)) instead of the original Q(sqrt(-7)) auxiliary field for
principal hosts. This makes every odd nonresonant prime generic, including 7.
Only resonant primes remain; they satisfy p <= 2*t on the required twist range.
-/

noncomputable section
namespace CertificateHour.PrincipalNonresonant

open NumberField NumberField.InfinitePlace IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC
open ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

theorem class_number_three : classNumber (Kstar 3) = 1 := by
  obtain ⟨hd,htc,hfr,_⟩ := kstar 3 Nat.prime_three (by decide)
  letI : IsTotallyComplex (Kstar 3) := htc
  have hc : nrComplexPlaces (Kstar 3) = 1 := by
    have hh := IsTotallyComplex.finrank (Kstar 3)
    omega
  apply classNumber_eq_one_iff.mpr
  apply RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt
  rw [hd,hfr,hc]
  norm_num [Nat.factorial]
  nlinarith [Real.pi_gt_three]

private theorem not_small_other_prime {Ω : Type} [Field Ω] (A : ValuationSubring Ω)
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (hA : A.valuation (p : Ω) < 1) : ¬ A.valuation (q : Ω) < 1 := by
  intro hB
  obtain ⟨a,b,hab⟩ := (Nat.isCoprime_iff_coprime).mpr ((Nat.coprime_primes hp hq).mpr hne)
  have h1 : (a : Ω) * (p : Ω) + (b : Ω) * (q : Ω) = 1 := by
    have hh := congrArg (fun z : ℤ => (z : Ω)) hab
    push_cast at hh
    exact hh
  have ha : A.valuation (a : Ω) ≤ 1 := (A.valuation_le_one_iff _).mpr (intCast_mem A a)
  have hb : A.valuation (b : Ω) ≤ 1 := (A.valuation_le_one_iff _).mpr (intCast_mem A b)
  have hx : A.valuation ((a : Ω) * (p : Ω)) < 1 := by
    rw [map_mul]
    exact (mul_le_mul_of_nonneg_right ha (zero_le : 0 ≤ A.valuation (p : Ω))).trans_lt
      (by simpa using hA)
  have hy : A.valuation ((b : Ω) * (q : Ω)) < 1 := by
    rw [map_mul]
    exact (mul_le_mul_of_nonneg_right hb (zero_le : 0 ≤ A.valuation (q : Ω))).trans_lt
      (by simpa using hB)
  have bad := Valuation.map_add_lt A.valuation hx hy
  rw [h1,map_one] at bad
  exact lt_irrefl _ bad

/-- At a principal host all odd nonresonant primes admit the same auxiliary
field Q(sqrt(-3)). In particular 7 is no longer exceptional away from 3|e. -/
theorem gd (h : Host) (one : h.chi = PChar.one) (t : ℕ) (big : h.Big t)
    (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra (Kstar 3) Ω]
    (p e : ℕ) [Fact p.Prime] (odd : p ≠ 2) (he : 0 < e) (ht : e < t)
    (nonresonant : ¬ p - 1 ∣ 2*e) (O : Type) [CommRing O] [IsDomain O]
    (ψ : DirichletCharacter O h.N) (host : h.IsChar ψ) (parity : PsiEven e ψ) :
    GD Ω (Kstar 3) p e ψ := by
  have prime : p.Prime := Fact.out
  have pn3 : p ≠ 3 := by
    rintro rfl
    exact nonresonant (by simpa using dvd_mul_right 2 e)
  have hn3 : ¬ 3 ∣ h.N := by
    intro hdv
    rcases ((hostIndex h).2.2.2.2.2.1 3 Nat.prime_three).mp hdv with h2|hq|hq|hd
    · norm_num at h2
    · change 3 ∣ h.chi.N at hq
      rw [one] at hq
      exact Nat.prime_three.not_dvd_one hq
    · have := big.1
      omega
    · have := big.2.1
      omega
  have hord : ¬ p ∣ orderOf ψ := by
    intro hdv
    have hdv' := hdv.trans (Principia.Ordinary.CharacterCases.order_dvd_two_power one host)
    exact odd ((Nat.prime_dvd_prime_iff_eq prime Nat.prime_two).mp (prime.dvd_of_dvd_pow hdv'))
  have hcomp : comp p ψ ^ 2 = 1 :=
    ((hostComp h O ψ host).2.2 p prime odd).2.2.1 (by
      change ¬ p ∣ h.chi.N
      rw [one]
      exact prime.not_dvd_one)
  obtain ⟨hd,htc,hdegree,_⟩ := kstar 3 Nat.prime_three (by decide)
  refine ⟨odd,he,?_,hord,hcomp,parity,hdegree,htc,?_,?_,?_,nonresonant⟩
  · rw [even_iff_two_dvd]
    exact (dvd_pow_self 2 (by omega : h.ex+2 ≠ 0)).trans h.two_pow_dvd
  · rw [hd,class_number_three]
    norm_num only [Int.natAbs_neg,Int.natAbs_natCast,mul_one]
    exact fun hdv => pn3 ((Nat.prime_dvd_prime_iff_eq prime Nat.prime_three).mp hdv)
  · rw [hd]
    norm_num only [Int.natAbs_neg,Int.natAbs_natCast]
    exact Nat.prime_three.coprime_iff_not_dvd.mpr hn3
  · intro inclusion
    obtain ⟨A,hA⟩ := (Chr.placesQ Ω).1 3 Nat.prime_three
    apply kstarRam 3 Nat.prime_three (by decide) Ω A hA
    intro g hg
    apply inclusion
    rw [Subgroup.mem_inf]
    constructor
    · have hAp := not_small_other_prime A 3 p Nat.prime_three prime pn3.symm hA
      have hc := ((places ℚ Ω p A).2.2.2 hAp) hg
      rw [MonoidHom.mem_ker] at hc ⊢
      simp [cycMod,hc]
    · have hAN : ¬ A.valuation (h.N : Ω) < 1 := by
        rw [(Chr.placesQ Ω).2.1 A h.N (NeZero.ne _)]
        rintro ⟨q,hqN,hq⟩
        have hqp := Nat.prime_of_mem_primeFactors hqN
        have hnq : 3 ≠ q := by
          rintro rfl
          exact hn3 (Nat.dvd_of_mem_primeFactors hqN)
        exact not_small_other_prime A 3 q Nat.prime_three hqp hnq hA hq
      have hc := ((Chr.clsFacts ℚ Ω h.N).2.2.2.2 A hAN) hg
      rw [MonoidHom.mem_ker] at hc ⊢
      simp [Chr.dirG,hc]

end CertificateHour.PrincipalNonresonant

#print axioms CertificateHour.PrincipalNonresonant.class_number_three
#print axioms CertificateHour.PrincipalNonresonant.gd
