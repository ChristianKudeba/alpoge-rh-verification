import Mathlib

/-! Two auxiliary primes avoiding an arbitrary integer, with polynomial bounds
for the sum of their logarithms. The second Euclid number uses the same
factorial, avoiding the exponentially worse factorial of the first prime. -/

noncomputable section
namespace Compaction.AuxiliaryPrimes

theorem exists_pair (m : ℕ) (hm : 0 < m) :
    ∃ r s : ℕ, r.Prime ∧ s.Prime ∧ r ≠ s ∧ ¬ r ∣ m ∧ ¬ s ∣ m ∧
      Real.log r + Real.log s ≤ 3 * (1 + (m : ℝ)^2) := by
  let A := m.factorial
  let u := A + 1
  let v := A * (A + 1) + 1
  let r := u.minFac
  let s := v.minFac
  have hA : 0 < A := Nat.factorial_pos m
  have hu : u ≠ 1 := by dsimp [u]; omega
  have hv : v ≠ 1 := by dsimp [v]; nlinarith
  have hr : r.Prime := Nat.minFac_prime hu
  have hs : s.Prime := Nat.minFac_prime hv
  have hrU : r ∣ u := Nat.minFac_dvd u
  have hsV : s ∣ v := Nat.minFac_dvd v
  have hmA : m ∣ A := Nat.dvd_factorial hm le_rfl
  have hnotr : ¬ r ∣ m := by
    intro h
    have hA' : r ∣ A := h.trans hmA
    have h1 : r ∣ 1 := by
      have hu' : r ∣ A + 1 := hrU
      exact (Nat.dvd_add_iff_right hA').mpr hu'
    exact hr.not_dvd_one h1
  have hnots : ¬ s ∣ m := by
    intro h
    have hA' : s ∣ A := h.trans hmA
    have hp : s ∣ A * (A + 1) := dvd_mul_of_dvd_left hA' _
    have h1 : s ∣ 1 := by
      have hv' : s ∣ A * (A + 1) + 1 := hsV
      exact (Nat.dvd_add_iff_right hp).mpr hv'
    exact hs.not_dvd_one h1
  have hrs : r ≠ s := by
    intro h
    have hp : s ∣ A * (A + 1) := by
      rw [← h]
      exact dvd_mul_of_dvd_right hrU A
    have h1 : s ∣ 1 := by
      have hv' : s ∣ A * (A + 1) + 1 := hsV
      exact (Nat.dvd_add_iff_right hp).mpr hv'
    exact hs.not_dvd_one h1
  refine ⟨r, s, hr, hs, hrs, hnotr, hnots, ?_⟩
  have hrle : r ≤ A + 1 := Nat.minFac_le (by dsimp [u]; omega)
  have hsle : s ≤ (A + 1)^2 :=
    (Nat.minFac_le (by dsimp [v]; positivity)).trans (by dsimp [v]; nlinarith)
  have hAreal : (0 : ℝ) < A := by exact_mod_cast hA
  have hlogA : Real.log (A : ℝ) ≤ (m : ℝ)^2 := by
    have hpow : (A : ℝ) ≤ (m : ℝ)^m := by exact_mod_cast Nat.factorial_le_pow m
    have hlogm : Real.log (m : ℝ) ≤ m := by
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < m by exact_mod_cast hm)
      linarith
    calc
      Real.log (A : ℝ) ≤ Real.log ((m : ℝ)^m) := Real.log_le_log hAreal hpow
      _ = (m : ℝ) * Real.log m := Real.log_pow _ _
      _ ≤ (m : ℝ) * m := mul_le_mul_of_nonneg_left hlogm (Nat.cast_nonneg _)
      _ = _ := by ring
  have hlogU : Real.log ((A : ℝ) + 1) ≤ 1 + (m : ℝ)^2 := by
    have hAle : (1 : ℝ) ≤ A := by exact_mod_cast hA
    calc
      Real.log ((A : ℝ) + 1) ≤ Real.log (2 * (A : ℝ)) :=
        Real.log_le_log (by positivity) (by linarith)
      _ = Real.log 2 + Real.log (A : ℝ) := Real.log_mul (by norm_num) hAreal.ne'
      _ ≤ 1 + (m : ℝ)^2 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hlogr : Real.log (r : ℝ) ≤ Real.log ((A : ℝ) + 1) :=
    Real.log_le_log (by exact_mod_cast hr.pos) (by exact_mod_cast hrle)
  have hlogs : Real.log (s : ℝ) ≤ 2 * Real.log ((A : ℝ) + 1) := by
    calc
      Real.log (s : ℝ) ≤ Real.log (((A : ℝ) + 1)^2) :=
        Real.log_le_log (by exact_mod_cast hs.pos) (by exact_mod_cast hsle)
      _ = _ := by rw [Real.log_pow]; norm_num
  linarith

end Compaction.AuxiliaryPrimes

#print axioms Compaction.AuxiliaryPrimes.exists_pair
