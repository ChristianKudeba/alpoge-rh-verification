import PlusCertificate
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.GdOfHost
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.HostLevel

/-! A real arithmetic certificate for all generic odd primes at one twist.
The integer is independent of the host-field realization and of local data.
The only substantial producer still assumed is the archive's PropGK theorem;
its actual NN witnesses, rather than a VVle bound, construct the integer here.
-/

noncomputable section
namespace CertificateHour.GenericHostCertificate

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.HC
open Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.U3

theorem generic_at (input : PropGK) (χ : PChar) :
    ∃ c A : ℕ, ∀ (h : Host), h.chi = χ → ∀ t : ℕ, h.Big t →
      ∀ (e r s : ℕ), 0 < e → e < t → r.Prime → s.Prime → r ≠ s →
      ¬ r ∣ 30 * h.N * (discr (Kstar (pK χ))).natAbs →
      ¬ s ∣ 30 * h.N * (discr (Kstar (pK χ))).natAbs →
      ∃ M : ℕ, 0 < M ∧
        Real.log M ≤ 2 * c * h.N * ((h.N : ℝ) * (e + 1))^A *
          (Real.log r + Real.log s) ∧
        ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
          IsChiField χ h.ex h.q1 h.d E →
          ∀ (Ω' : Type) [Field Ω'] [Algebra E Ω'] [IsAlgClosure E Ω']
            (p : ℕ) [Fact p.Prime] (D : LData E Ω' p), p ≠ 2 → h.CaseI p e →
            plusLen D e ≠ ⊤ ∧ plusLen D e ≤ (M.factorization p : ℕ∞) := by
  obtain ⟨c,A,supply⟩ := AllOrbitCertificate.of_propGK input (Kstar (pK χ))
  refine ⟨c,A,?_⟩
  intro h one t big e r s he ht hr hs hrs hrd hsd
  subst χ
  obtain ⟨M,hM,hsize,control⟩ := supply e h.N r s he hr hs hrs hrd hsd
  refine ⟨M,hM,hsize,?_⟩
  intro E _ _ _ field Ω' _ _ _ p _ D odd generic
  let Ω := AlgebraicClosure ℚ
  letI : Algebra (Kstar (pK h.chi)) Ω :=
    (IsAlgClosed.lift (R:=ℚ) (S:=Kstar (pK h.chi)) (M:=Ω)).toRingHom.toAlgebra
  haveI : NeZero h.N.totient := ⟨(Nat.totient_pos.mpr h.N_pos).ne'⟩
  obtain ⟨coef,roots⟩ := exists_coef p h.N.totient
  haveI := roots
  have idx : ¬ p ∣ h.H.index :=
    ((bchiFacts h t big).2.2.2.2 p (Fact.out : p.Prime) odd generic.1).2.2.2.2.2.2.1
  have chars : (h.X coef e : Set (DirichletCharacter coef.O h.N)) =
      Chr.evenSet coef.O h.H e := by
    ext ψ
    simp [Host.mem_X, Chr.evenSet, Host.IsChar, PsiEven]
  apply PlusCertificate.of_character_certificate (Kstar (pK h.chi)) h.N h.H e M control
    E (hostLevel h E field) Ω' Ω p odd idx coef D he (h.X coef e) chars
  intro ψ hψ
  obtain ⟨hchar,hpar⟩ := (Host.mem_X h).mp hψ
  exact gdOfHost h t big Ω p e odd he ht generic coef.O ψ hchar hpar

end CertificateHour.GenericHostCertificate

#print axioms CertificateHour.GenericHostCertificate.generic_at
