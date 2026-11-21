import PrincipalTwistCertificate
import RootGenericAndExceptional
import RootFactorialSmallPrime

/-! A single explicit factorial handles the remaining finitely many resonant
primes once a uniform pointwise natural-number bound is provided. -/

noncomputable section
namespace CertificateHour.ResonantCertificate

open Classical in
def part (a : Nat.Primes → ℕ → ℕ∞) (p : Nat.Primes) (e : ℕ) : ℕ∞ :=
  if (p : ℕ) ≠ 2 ∧ (p : ℕ)-1 ∣ 2*e then a p e else 0

def mass (t R : ℕ) : ℕ := (2*t).factorial^(t*R)

theorem certificate (t R : ℕ) (ht : 0 < t) :
    0 < mass t R ∧ Real.log (mass t R) ≤ 4*(t : ℝ)^3*R ∧
      ∀ a : Nat.Primes → ℕ → ℕ∞,
        (∀ (p : Nat.Primes) (e : ℕ), e ∈ Finset.Ico 1 t → (p : ℕ) ≠ 2 → (p : ℕ)-1 ∣ 2*e → a p e ≤ (R : ℕ∞)) →
        Compaction.CertificateAssembly.Dominates (part a) t (mass t R) := by
  classical
  have hpos : 0 < mass t R := pow_pos (Nat.factorial_pos _) _
  refine ⟨hpos,?_,?_⟩
  · unfold mass
    rw [Nat.cast_pow,Real.log_pow,Nat.cast_mul]
    have hf := Compaction.FactorialSmallPrimeCertificate.log_factorial_le (2*t) (by omega)
    have hmul := mul_le_mul_of_nonneg_left hf (by positivity : (0 : ℝ) ≤ (t : ℝ)*R)
    calc
      _ ≤ (t : ℝ)*R*((2*t : ℕ) : ℝ)^2 := hmul
      _ = _ := by push_cast; ring
  · intro a bound
    have h := Compaction.GenericAndExceptional.construct (part a)
      (fun p e => (p : ℕ) = 2 ∨ ¬ (p : ℕ)-1 ∣ 2*e) (fun _ => 1) t (2*t) R (by omega)
      (by intro e _; exact zero_lt_one) (by
        intro p e he hg
        rcases hg with htwo | hnot
        · simp [part,htwo]
        · simp [part,hnot]) (by
        intro p e he hbad
        have hp : (p : ℕ) ≠ 2 ∧ (p : ℕ)-1 ∣ 2*e := by push_neg at hbad; exact hbad
        refine ⟨(PrincipalTwistCertificate.resonant_prime_lt p.2
          (Nat.succ_le_iff.mp (Finset.mem_Ico.mp he).1) (Finset.mem_Ico.mp he).2 hp.2).le,?_⟩
        simpa only [part,if_pos hp] using bound p e he hp.1 hp.2)
    simpa only [Finset.prod_const_one,one_mul,mass,Compaction.CertificateAssembly.Dominates] using h.2

end CertificateHour.ResonantCertificate
#print axioms CertificateHour.ResonantCertificate.certificate
