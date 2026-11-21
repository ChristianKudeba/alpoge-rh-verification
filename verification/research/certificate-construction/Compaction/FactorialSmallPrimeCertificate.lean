import Mathlib

/-! An explicit factorial certificate for every prime at most the conductor.
This handles degree-dividing exceptional primes without listing their factors.
-/

noncomputable section
namespace Compaction.FactorialSmallPrimeCertificate

theorem degree_le_conductor {N : ℕ} [NeZero N] (E : Type) [Field E] [NumberField E]
    (hemb : Nonempty (E →ₐ[ℚ] CyclotomicField N ℚ)) : Module.finrank ℚ E ≤ N := by
  obtain ⟨j⟩ := hemb
  letI : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) :=
    CyclotomicField.isCyclotomicExtension N ℚ
  calc
    Module.finrank ℚ E ≤ Module.finrank ℚ (CyclotomicField N ℚ) :=
      LinearMap.finrank_le_finrank_of_injective (f := j.toLinearMap) j.injective
    _ = N.totient := IsCyclotomicExtension.Rat.finrank N (CyclotomicField N ℚ)
    _ ≤ N := Nat.totient_le N

theorem log_factorial_le (N : ℕ) (hN : 0 < N) :
    Real.log (N.factorial : ℝ) ≤ (N : ℝ) ^ 2 := by
  have hpow : (N.factorial : ℝ) ≤ (N : ℝ) ^ N := by exact_mod_cast Nat.factorial_le_pow N
  have hlog : Real.log (N : ℝ) ≤ N := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < N by exact_mod_cast hN)
    linarith
  calc
    Real.log (N.factorial : ℝ) ≤ Real.log ((N : ℝ) ^ N) :=
      Real.log_le_log (by exact_mod_cast Nat.factorial_pos N) hpow
    _ = (N : ℝ) * Real.log N := Real.log_pow _ _
    _ ≤ (N : ℝ) * N := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg N)
    _ = _ := by ring

/-- The certificate `(N!)^(t*ceil A)` is selected before the length family.
Valuation domination is stated in ENat, so it cannot hide infinite lengths. -/
theorem universal (N t : ℕ) (hN : 0 < N) (A : ℝ) (hA : 0 ≤ A) :
    ∃ M : ℕ, 0 < M ∧
      Real.log M ≤ (A + 1) * t * (N : ℝ) ^ 2 ∧
      ∀ (eligible : ℕ → Prop) (length : ℕ → ℕ → ℕ∞),
        (∀ (p : ℕ) [Fact p.Prime], p ≤ N → eligible p → ∀ e ∈ Finset.Ico 1 t,
          length p e ≤ (⌈A⌉₊ : ℕ∞)) →
        ∀ (p : ℕ) [Fact p.Prime], p ≤ N → eligible p →
          ∑ e ∈ Finset.Ico 1 t, length p e ≤
            (M.factorization p : ℕ∞) := by
  let R := ⌈A⌉₊
  let M := N.factorial ^ (t * R)
  have hM : 0 < M := pow_pos (Nat.factorial_pos N) _
  refine ⟨M, hM, ?_, ?_⟩
  · change Real.log ((N.factorial ^ (t * R) : ℕ) : ℝ) ≤ _
    rw [Nat.cast_pow, Real.log_pow, Nat.cast_mul]
    calc
      (t : ℝ) * R * Real.log (N.factorial : ℝ)
          ≤ (t : ℝ) * R * (N : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left (log_factorial_le N hN) (by positivity)
      _ ≤ (t : ℝ) * (A + 1) * (N : ℝ) ^ 2 := by
        gcongr
        exact (Nat.ceil_lt_add_one hA).le
      _ = _ := by ring
  · intro eligible length hb p _ hp hel
    have hd : p ^ (t * R) ∣ M := pow_dvd_pow_of_dvd
      (Nat.dvd_factorial (Fact.out : p.Prime).pos hp) _
    have hv : t * R ≤ M.factorization p :=
      ((Fact.out : p.Prime).pow_dvd_iff_le_factorization hM.ne').mp hd
    calc
      ∑ e ∈ Finset.Ico 1 t, length p e ≤ ∑ _e ∈ Finset.Ico 1 t, (R : ℕ∞) :=
        Finset.sum_le_sum (fun e he => hb p hp hel e he)
      _ = (((t - 1) * R : ℕ) : ℕ∞) := by
        simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_mul]
      _ ≤ (M.factorization p : ℕ∞) := by
        exact_mod_cast (Nat.mul_le_mul_right R (Nat.sub_le t 1)).trans hv

/-- Coarse pointwise Stickelberger bound, uniform for p,n≤N and e<t.
The intentionally coarse polynomial will still be absorbed by the window
budget because the conductor grows subexponentially in x^eps. -/
theorem length_le_ceiling (C : ℝ) (hC : 0 ≤ C) (N t p n e : ℕ)
    (hN : 0 < N) (hp : 2 ≤ p) (hpN : p ≤ N) (hnN : n ≤ N)
    (he : 1 ≤ e) (het : e < t) (a : ℕ∞) (hfinite : a ≠ ⊤)
    (hbound : (a.toNat : ℝ) * Real.log p ≤
      C * p * (n : ℝ) ^ 2 * (e + 1) * Real.log ((e : ℝ) * p * N) ^ 2) :
    a ≤ (⌈2 * C * (N : ℝ) ^ 7 * (t : ℝ) ^ 3⌉₊ : ℕ∞) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hpN' : (p : ℝ) ≤ N := by exact_mod_cast hpN
  have hnN' : (n : ℝ) ≤ N := by exact_mod_cast hnN
  have he' : (1 : ℝ) ≤ e := by exact_mod_cast he
  have het' : (e : ℝ) + 1 ≤ t := by exact_mod_cast het
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlogp : (1 / 2 : ℝ) ≤ Real.log p := by
    have hi : (p : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hp2
    linarith [Real.one_sub_inv_le_log_of_pos hp0]
  have harg : (1 : ℝ) ≤ (e : ℝ) * p * N := by
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le he' (by linarith)) hN'
  have hargle : (e : ℝ) * p * N ≤ (t : ℝ) * (N : ℝ) ^ 2 := by
    calc
      (e : ℝ) * p * N ≤ (t : ℝ) * N * N := by gcongr <;> linarith
      _ = _ := by ring
  have hlg0 : 0 ≤ Real.log ((e : ℝ) * p * N) := Real.log_nonneg harg
  have hlg : Real.log ((e : ℝ) * p * N) ≤ (t : ℝ) * (N : ℝ) ^ 2 :=
    (Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < (e : ℝ) * p * N)).trans
      (by linarith)
  have hsq := pow_le_pow_left₀ hlg0 hlg 2
  have hcoarse : C * p * (n : ℝ) ^ 2 * (e + 1) * Real.log ((e : ℝ) * p * N) ^ 2 ≤
      C * (N : ℝ) ^ 7 * (t : ℝ) ^ 3 := by
    calc
      _ ≤ C * N * (N : ℝ) ^ 2 * t * ((t : ℝ) * (N : ℝ) ^ 2) ^ 2 := by gcongr
      _ = _ := by ring
  have hr : (a.toNat : ℝ) ≤ 2 * C * (N : ℝ) ^ 7 * (t : ℝ) ^ 3 := by
    have hn : (0 : ℝ) ≤ a.toNat := Nat.cast_nonneg _
    have hm := mul_le_mul_of_nonneg_left hlogp hn
    nlinarith [hbound.trans hcoarse]
  have hnat : a.toNat ≤ ⌈2 * C * (N : ℝ) ^ 7 * (t : ℝ) ^ 3⌉₊ := by
    exact_mod_cast hr.trans (Nat.le_ceil _)
  rw [← ENat.natCast_toNat hfinite]
  exact_mod_cast hnat

end Compaction.FactorialSmallPrimeCertificate

#print axioms Compaction.FactorialSmallPrimeCertificate.universal
#print axioms Compaction.FactorialSmallPrimeCertificate.length_le_ceiling
#print axioms Compaction.FactorialSmallPrimeCertificate.degree_le_conductor
