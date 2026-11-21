import PrincipalCertificate
import RootCertificateAssembly

/-! One integer for all positive twists below t and all nonresonant odd primes.
It controls actual extended-natural cohomology lengths simultaneously for every
host-field realization and all local data. The remaining odd part is confined
to resonant primes p-1 | 2e, hence p <= 2t on this twist interval. -/

noncomputable section
namespace CertificateHour.PrincipalTwistCertificate

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.HC
open Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.U3

open Classical in
def length {E Ω : Type} [Field E] [NumberField E] [IsCMField E]
    [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {p : ℕ} [Fact p.Prime]
    (D : LData E Ω p) (e : ℕ) : ℕ∞ :=
  if p ≠ 2 ∧ ¬ p-1 ∣ 2*e then plusLen D e else 0

/-- The complement of the new certificate is a uniformly finite prime set. -/
theorem resonant_prime_lt {p e t : ℕ} (prime : p.Prime) (he : 0 < e)
    (ht : e < t) (resonant : p-1 ∣ 2*e) : p < 2*t := by
  have hp := prime.two_le
  have hdiv : p-1 ≤ 2*e := Nat.le_of_dvd (by omega) resonant
  omega

theorem nonresonant_budget (input : PropGK) :
    ∃ c A : ℕ, ∀ (h : Host), h.chi = PChar.one → ∀ t : ℕ, h.Big t →
      ∃ M : ℕ, 0 < M ∧
        Real.log M ≤ 48606 * c * (h.N : ℝ)^3 * t * ((h.N : ℝ) * t)^A ∧
        ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
          IsChiField PChar.one h.ex h.q1 h.d E →
          ∀ (Ω : Type) [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
            (ld : ∀ (p : ℕ) [Fact p.Prime], LData E Ω p),
            Compaction.CertificateAssembly.Dominates (fun p e => length (ld p) e) t M := by
  classical
  obtain ⟨c,A,supply⟩ := PrincipalCertificate.nonresonant_at input
  refine ⟨c,A,?_⟩
  intro h one t big
  have each (e : ℕ) : ∃ M : ℕ, 0 < M ∧
      (e ∈ Finset.Ico 1 t →
        Real.log M ≤ 48606*c*(h.N : ℝ)^3*((h.N : ℝ)*(e+1))^A ∧
        ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
          IsChiField PChar.one h.ex h.q1 h.d E →
          ∀ (Ω : Type) [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
            (p : ℕ) [Fact p.Prime] (D : LData E Ω p), p ≠ 2 → ¬ p-1 ∣ 2*e →
            plusLen D e ≠ ⊤ ∧ plusLen D e ≤ (M.factorization p : ℕ∞)) := by
    by_cases he : e ∈ Finset.Ico 1 t
    · obtain ⟨M,hM,hm,hc⟩ := supply h one t big e
        (Nat.succ_le_iff.mp (Finset.mem_Ico.mp he).1) (Finset.mem_Ico.mp he).2
      exact ⟨M,hM,fun _ => ⟨hm,hc⟩⟩
    · exact ⟨1,zero_lt_one,fun he' => False.elim (he he')⟩
  choose M hM hrest using each
  let P := ∏ e ∈ Finset.Ico 1 t, M e
  have hp : 0 < P := Finset.prod_pos (fun e _ => hM e)
  refine ⟨P,hp,?_,?_⟩
  · let B : ℝ := 48606*c*(h.N : ℝ)^3*((h.N : ℝ)*t)^A
    have hB : 0 ≤ B := by dsimp [B]; positivity
    have per (e : ℕ) (he : e ∈ Finset.Ico 1 t) : Real.log (M e) ≤ B := by
      apply ((hrest e he).1).trans
      have hbase : (h.N : ℝ)*(e+1) ≤ (h.N : ℝ)*t := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        exact_mod_cast Nat.succ_le_of_lt (Finset.mem_Ico.mp he).2
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hbase A)
        (by positivity : 0 ≤ 48606*(c : ℝ)*(h.N : ℝ)^3)
    calc
      Real.log P = ∑ e ∈ Finset.Ico 1 t, Real.log (M e) :=
        Compaction.CertificateAssembly.log_across_twists t M (fun e _ => hM e)
      _ ≤ ∑ e ∈ Finset.Ico 1 t, B := Finset.sum_le_sum per
      _ = ((t-1 : ℕ) : ℝ)*B := by rw [Finset.sum_const,Nat.card_Ico,nsmul_eq_mul]
      _ ≤ (t : ℝ)*B := mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le t 1) hB
      _ = _ := by dsimp [B]; ring
  · intro E _ _ _ field Ω _ _ _ ld
    exact (Compaction.CertificateAssembly.across_twists (fun p e => length (ld p) e) t M
      (fun e _ => hM e) (by
        intro p e he
        by_cases hp : (p : ℕ) ≠ 2 ∧ ¬ (p : ℕ)-1 ∣ 2*e
        · simp only [length,if_pos hp]
          exact ((hrest e he).2 E field Ω p (ld p) hp.1 hp.2).2
        · simp only [length,if_neg hp]
          exact zero_le)).2

end CertificateHour.PrincipalTwistCertificate
#print axioms CertificateHour.PrincipalTwistCertificate.nonresonant_budget
#print axioms CertificateHour.PrincipalTwistCertificate.resonant_prime_lt
