import Mathlib

/-! The zero-loss, one-twist form of Alpöge's sumBack_one. -/
namespace CertificateHour.NormalizedLength

theorem bound {ι : Type} (S : Finset ι) (f : ι → ℕ∞) (a : ℕ∞) (E : ℕ)
    (hE : E ≠ 0) (hf : ∀ i ∈ S, f i ≠ ⊤)
    (h : a * (E : ℕ∞) ≤ ∑ i ∈ S, f i) :
    a ≠ ⊤ ∧ (a.toNat : ℝ) ≤ ∑ i ∈ S, ((f i).toNat : ℝ) / E := by
  have hsum : ∑ i ∈ S, f i = ((∑ i ∈ S, (f i).toNat : ℕ) : ℕ∞) := by
    rw [Nat.cast_sum]
    exact Finset.sum_congr rfl fun i hi => (ENat.natCast_toNat (hf i hi)).symm
  rw [hsum] at h
  have ha : a ≠ ⊤ := by
    rintro rfl
    rw [ENat.top_mul (by exact_mod_cast hE)] at h
    exact absurd h (not_le.mpr (ENat.natCast_lt_top _))
  refine ⟨ha, ?_⟩
  have hn : a.toNat * E ≤ ∑ i ∈ S, (f i).toNat := by
    rw [← ENat.natCast_toNat ha] at h
    exact_mod_cast h
  have hEpos : (0 : ℝ) < E := by exact_mod_cast Nat.pos_of_ne_zero hE
  rw [← Finset.sum_div, le_div_iff₀ hEpos]
  exact_mod_cast hn

end CertificateHour.NormalizedLength
#print axioms CertificateHour.NormalizedLength.bound
