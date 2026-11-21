import PrincipalNonresonant
import PlusCertificate
import RootAuxiliaryPrimes
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.HostLevel

/-! The actual PropGK integers give a uniform polynomial-size certificate for
all nonresonant odd primes of a principal host. The certificate is selected
before any field realization or local cohomology data; auxiliary primes are
constructed with an explicit logarithmic bound instead of assumed. -/

noncomputable section
namespace CertificateHour.PrincipalCertificate

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.HC
open Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.U3

theorem nonresonant_at (input : PropGK) :
    ∃ c A : ℕ, ∀ (h : Host), h.chi = PChar.one → ∀ t : ℕ, h.Big t →
      ∀ e : ℕ, 0 < e → e < t →
      ∃ M : ℕ, 0 < M ∧
        Real.log M ≤ 48606 * c * (h.N : ℝ)^3 * ((h.N : ℝ) * (e + 1))^A ∧
        ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
          IsChiField PChar.one h.ex h.q1 h.d E →
          ∀ (Ω' : Type) [Field Ω'] [Algebra E Ω'] [IsAlgClosure E Ω']
            (p : ℕ) [Fact p.Prime] (D : LData E Ω' p), p ≠ 2 → ¬ p-1 ∣ 2*e →
            plusLen D e ≠ ⊤ ∧ plusLen D e ≤ (M.factorization p : ℕ∞) := by
  obtain ⟨c,A,supply⟩ := AllOrbitCertificate.of_propGK input (Kstar 3)
  refine ⟨c,A,?_⟩
  intro h one t big e he ht
  obtain ⟨r,s,hr,hs,hrs,hrd,hsd,hlog⟩ := Compaction.AuxiliaryPrimes.exists_pair
    (90*h.N) (Nat.mul_pos (by decide) h.N_pos)
  have hd := (kstar 3 Nat.prime_three (by decide)).1
  have hm : 30*h.N*(discr (Kstar 3)).natAbs = 90*h.N := by
    rw [hd]
    norm_num only [Int.natAbs_neg,Int.natAbs_natCast]
    ring
  obtain ⟨M,hM,hsize,control⟩ := supply e h.N r s he hr hs hrs
    (by rw [hm]; exact hrd) (by rw [hm]; exact hsd)
  refine ⟨M,hM,?_,?_⟩
  · have hN1 : (1 : ℝ) ≤ h.N := by exact_mod_cast h.N_pos
    have hN2 : (1 : ℝ) ≤ (h.N : ℝ)^2 := one_le_pow₀ hN1
    have hsmall : Real.log r + Real.log s ≤ 24303*(h.N : ℝ)^2 := by
      apply hlog.trans
      push_cast
      nlinarith
    have hbound := mul_le_mul_of_nonneg_left hsmall
      (by positivity : 0 ≤ 2*(c : ℝ)*h.N*((h.N : ℝ)*(e+1))^A)
    apply hsize.trans
    convert hbound using 1 <;> ring
  · intro E _ _ _ field Ω' _ _ _ p _ D odd nonresonant
    let Ω := AlgebraicClosure ℚ
    letI : Algebra (Kstar 3) Ω :=
      (IsAlgClosed.lift (R:=ℚ) (S:=Kstar 3) (M:=Ω)).toRingHom.toAlgebra
    haveI : NeZero h.N.totient := ⟨(Nat.totient_pos.mpr h.N_pos).ne'⟩
    obtain ⟨coef,roots⟩ := exists_coef p h.N.totient
    haveI := roots
    have ho : h.o = 1 := by change ordC h.chi = 1; rw [one]; exact orderOf_one
    have idx : ¬ p ∣ h.H.index := by
      intro hp
      have hp' := hp.trans (hostIndex h).1
      rw [ho,mul_one] at hp'
      exact odd ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp
        ((Fact.out : p.Prime).dvd_of_dvd_pow hp'))
    have chars : (h.X coef e : Set (DirichletCharacter coef.O h.N)) =
        Chr.evenSet coef.O h.H e := by
      ext ψ
      simp [Host.mem_X,Chr.evenSet,Host.IsChar,PsiEven]
    have field' : IsChiField h.chi h.ex h.q1 h.d E := by simpa only [one] using field
    apply PlusCertificate.of_character_certificate (Kstar 3) h.N h.H e M control
      E (hostLevel h E field') Ω' Ω p odd idx coef D he (h.X coef e) chars
    intro ψ hψ
    obtain ⟨hchar,hpar⟩ := (Host.mem_X h).mp hψ
    exact PrincipalNonresonant.gd h one t big Ω p e odd he ht nonresonant coef.O ψ hchar hpar

end CertificateHour.PrincipalCertificate
#print axioms CertificateHour.PrincipalCertificate.nonresonant_at
