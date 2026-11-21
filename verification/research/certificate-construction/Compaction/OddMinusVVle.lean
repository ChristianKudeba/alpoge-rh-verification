import Compaction.AllOddMinusCertificateClosed
import Compaction.OddMinusBudgetBound
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Sumval

/-! Supply the archive's actual VVminusLe interface from the constructed
integer certificate, with one conductor-only polynomial bound. -/

noncomputable section
namespace Compaction.OddMinusVVle

open NumberField Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Bern

local instance primeFact (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

theorem of_certificate {E Ω : Type} [Field E] [NumberField E] [IsCMField E]
    [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (ld : ∀ (p : ℕ) [Fact p.Prime], LData E Ω p) (t M : ℕ) (hM : 0 < M)
    (hcert : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 →
      ∑ e ∈ Finset.Ico 1 t, minusLen (ld p) e ≤ (M.factorization p : ℕ∞)) :
    (∀ (p : ℕ) [Fact p.Prime] (e : ℕ), p ≠ 2 → 0 < e → e < t → minusLen (ld p) e ≠ ⊤) ∧
      ∀ S : Finset Nat.Primes, (∀ p ∈ S, (p : ℕ) ≠ 2) →
        ∑ p ∈ S, Real.log (p : ℕ) *
          ∑ e ∈ Finset.Ico 1 t, ((minusLen (ld p) e).toNat : ℝ) ≤ Real.log M := by
  have hf (p : ℕ) [Fact p.Prime] (e : ℕ) (hp : p ≠ 2) (he : e ∈ Finset.Ico 1 t) :
      minusLen (ld p) e ≠ ⊤ := by
    have hs : (∑ e ∈ Finset.Ico 1 t, minusLen (ld p) e) ≠ ⊤ :=
      ne_top_of_le_ne_top (ENat.natCast_ne_top _) (hcert p hp)
    exact ENat.sum_ne_top.mp hs e he
  refine ⟨fun p _ e hp he ht => hf p e hp (Finset.mem_Ico.mpr ⟨Nat.succ_le_iff.mpr he, ht⟩), ?_⟩
  intro S hS
  have hsum (p : Nat.Primes) (hp : p ∈ S) :
      ∑ e ∈ Finset.Ico 1 t, ((minusLen (ld p) e).toNat : ℝ) ≤ (M.factorization p : ℝ) := by
    have h := ENat.toNat_le_of_le_natCast (hcert p (hS p hp))
    rw [ENat.toNat_sum (fun e he => hf p e (hS p hp) he)] at h
    exact_mod_cast h
  calc
    _ ≤ ∑ p ∈ S, Real.log (p : ℕ) * (M.factorization p : ℝ) :=
      Finset.sum_le_sum (fun p hp => mul_le_mul_of_nonneg_left (hsum p hp) (Real.log_natCast_nonneg _))
    _ = ∑ p ∈ S, (padicValInt p (M : ℤ) : ℝ) * Real.log (p : ℕ) := by
      apply Finset.sum_congr rfl
      intro p _
      rw [mul_comm, Nat.factorization_def M p.2]
      rfl
    _ = ∑ p ∈ S.image (fun p : Nat.Primes => (p : ℕ)),
        (padicValInt p (M : ℤ) : ℝ) * Real.log p := by
      exact (Finset.sum_image
        (f := fun p : ℕ => (padicValInt p (M : ℤ) : ℝ) * Real.log p)
        (s := S) (g := fun p : Nat.Primes => (p : ℕ))
        (fun a _ b _ h => Nat.Primes.coe_nat_injective h)).symm
    _ ≤ Real.log |((M : ℤ) : ℝ)| := b_sumval (M : ℤ) (by exact_mod_cast hM.ne')
      (S.image fun p : Nat.Primes => (p : ℕ)) (by
        intro p hp
        obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hp
        exact q.2)
    _ = Real.log M := by rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg M)]

theorem exists_polynomial_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) [NeZero N] (t : ℕ), 2 ≤ t →
      ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
        Nonempty (E →ₐ[ℚ] CyclotomicField N ℚ) →
        VVminusLe E t ((2 * C + 4) * ((N : ℝ) * t) ^ 9) := by
  obtain ⟨C, hC, hall⟩ := AllOddMinusCertificateClosed.exists_uniform_certificates
  refine ⟨C, hC, ?_⟩
  intro N _ t ht E _ _ _ hemb Ω _ _ _ ld
  obtain ⟨M, hM, hlog, hcert⟩ := hall N t ht
  obtain ⟨hf, hs⟩ := of_certificate ld t M hM (hcert E Ω hemb ld)
  refine ⟨hf, fun S hS => (hs S hS).trans (hlog.trans ?_)⟩
  exact OddMinusBudgetBound.polynomial_envelope C hC N t (NeZero.pos N) (by omega)

end Compaction.OddMinusVVle

#print axioms Compaction.OddMinusVVle.of_certificate
#print axioms Compaction.OddMinusVVle.exists_polynomial_bound
