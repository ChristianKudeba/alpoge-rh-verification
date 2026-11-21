import Mathlib

namespace CertificateHour.RootTripleCertificate

/-- Replace a bounded integer depending on three roots of unity by one integer
for every root triple at once. The logarithmic cost is at most k cubed. -/
theorem collect (k : ℕ) (hk : 0 < k) (B : ℝ) (hB : 0 ≤ B)
    (P : ℕ → ℂ → ℂ → ℂ → Prop)
    (mono : ∀ a b : ℕ, 0 < a → 0 < b → a ∣ b →
      ∀ z₁ z₂ z₃, P a z₁ z₂ z₃ → P b z₁ z₂ z₃)
    (each : ∀ z₁ z₂ z₃ : ℂ, z₁^k = 1 → z₂^k = 1 → z₃^k = 1 →
      ∃ M : ℕ, 0 < M ∧ Real.log M ≤ B ∧ P M z₁ z₂ z₃) :
    ∃ M : ℕ, 0 < M ∧ Real.log M ≤ (k:ℝ)^3*B ∧
      ∀ z₁ z₂ z₃ : ℂ, z₁^k = 1 → z₂^k = 1 → z₃^k = 1 → P M z₁ z₂ z₃ := by
  classical
  let roots := Polynomial.nthRootsFinset k (1:ℂ)
  let Z := ↥roots
  let T := Z × Z × Z
  have exists_each (z : T) := each z.1.1 z.2.1.1 z.2.2.1
    ((Polynomial.mem_nthRootsFinset hk (1:ℂ)).mp z.1.2)
    ((Polynomial.mem_nthRootsFinset hk (1:ℂ)).mp z.2.1.2)
    ((Polynomial.mem_nthRootsFinset hk (1:ℂ)).mp z.2.2.2)
  choose m hm hs hc using exists_each
  let M := ∏ z : T, m z
  have hM : 0 < M := Finset.prod_pos (fun z _ => hm z)
  refine ⟨M,hM,?_,?_⟩
  · have hcard : Fintype.card T ≤ k^3 := by
      have hr : roots.card ≤ k :=
        (Multiset.toFinset_card_le (Polynomial.nthRoots k (1:ℂ))).trans
          (Polynomial.card_nthRoots k (1:ℂ))
      have hcZ : Fintype.card Z = roots.card := Fintype.card_coe _
      dsimp [T]
      rw [Fintype.card_prod,Fintype.card_prod,hcZ]
      calc roots.card * (roots.card * roots.card) = roots.card^3 := by ring
           _ ≤ k^3 := Nat.pow_le_pow_left hr 3
    calc
      Real.log M = ∑ z : T, Real.log (m z) := by
        dsimp [M]
        rw [Nat.cast_prod,Real.log_prod (fun z _ => by exact_mod_cast (hm z).ne')]
      _ ≤ ∑ z : T, B := Finset.sum_le_sum (fun z _ => hs z)
      _ = (Fintype.card T : ℝ)*B := by simp
      _ ≤ (k:ℝ)^3*B := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hB
  intro z₁ z₂ z₃ hz₁ hz₂ hz₃
  let z : T := (⟨z₁,(Polynomial.mem_nthRootsFinset hk (1:ℂ)).mpr hz₁⟩,
    ⟨z₂,(Polynomial.mem_nthRootsFinset hk (1:ℂ)).mpr hz₂⟩,
    ⟨z₃,(Polynomial.mem_nthRootsFinset hk (1:ℂ)).mpr hz₃⟩)
  exact mono (m z) M (hm z) hM
    (Finset.dvd_prod_of_mem m (Finset.mem_univ z)) z₁ z₂ z₃ (hc z)

end CertificateHour.RootTripleCertificate
#print axioms CertificateHour.RootTripleCertificate.collect
