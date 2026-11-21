import HeightResonantCertificate

/-! Combine the constructed nonresonant certificate with a single factorial
for the remaining resonant primes. The pointwise resonant bound is the explicit
remaining arithmetic input; in particular it includes nontrivial p=3,e=1. -/

noncomputable section
namespace CertificateHour.FullPlusCertificate

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.HC
open Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.U3

open Classical in
def length {E Ω : Type} [Field E] [NumberField E] [IsCMField E]
    [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {p : ℕ} [Fact p.Prime]
    (D : LData E Ω p) (e : ℕ) : ℕ∞ := if p ≠ 2 then plusLen D e else 0

theorem with_resonant_bound (input : PropGK) :
    ∃ c A : ℕ, ∀ (h : Host), h.chi = PChar.one → ∀ t : ℕ, 0 < t → h.Big t →
      ∀ R : ℕ,
        (∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
          IsChiField PChar.one h.ex h.q1 h.d E →
          ∀ (Ω : Type) [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
            (p : ℕ) [Fact p.Prime] (D : LData E Ω p), p ≠ 2 →
            ∀ e ∈ Finset.Ico 1 t, p-1 ∣ 2*e → plusLen D e ≤ (R : ℕ∞)) →
        ∃ M : ℕ, 0 < M ∧
          Real.log M ≤ 48606*c*(h.N : ℝ)^3*t*((h.N : ℝ)*t)^A + 4*(t : ℝ)^3*R ∧
          ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
            IsChiField PChar.one h.ex h.q1 h.d E →
            ∀ (Ω : Type) [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
              (ld : ∀ (p : ℕ) [Fact p.Prime], LData E Ω p),
              Compaction.CertificateAssembly.Dominates (fun p e => length (ld p) e) t M := by
  classical
  obtain ⟨c,A,supply⟩ := PrincipalTwistCertificate.nonresonant_budget input
  refine ⟨c,A,?_⟩
  intro h one t ht big R resonant
  obtain ⟨P,hP,hlog,control⟩ := supply h one t big
  obtain ⟨hF,hFlog,hFcontrol⟩ := ResonantCertificate.certificate t R ht
  refine ⟨P*ResonantCertificate.mass t R,Nat.mul_pos hP hF,?_,?_⟩
  · rw [Compaction.CertificateAssembly.log_multiply hP hF]
    exact add_le_add hlog hFlog
  · intro E _ _ _ field Ω _ _ _ ld
    let a : Nat.Primes → ℕ → ℕ∞ := fun p e => plusLen (ld p) e
    have hr := hFcontrol a (by
      intro p e he odd res
      exact resonant E field Ω p (ld p) odd e he res)
    apply Compaction.CertificateAssembly.multiply hP hF (control E field Ω ld) hr
    intro p e he
    by_cases hp : (p : ℕ) = 2
    · simp [length,PrincipalTwistCertificate.length,ResonantCertificate.part,hp]
    · by_cases hres : (p : ℕ)-1 ∣ 2*e
      · simp [length,PrincipalTwistCertificate.length,ResonantCertificate.part,hp,hres,a]
      · simp [length,PrincipalTwistCertificate.length,ResonantCertificate.part,hp,hres,a]

end CertificateHour.FullPlusCertificate
#print axioms CertificateHour.FullPlusCertificate.with_resonant_bound
