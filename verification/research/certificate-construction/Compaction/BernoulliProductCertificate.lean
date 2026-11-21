import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Prodint
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.BUltraUnit

/-! Preserve the actual integer produced by `b_prodint`. The archive's `prodVal`
forgets it after defining its prime valuations. Here the integer is retained as
a certificate simultaneously valid at every prime. This does not assume a
Selmer/Bernoulli comparison: that comparison remains a separate arithmetic input.
-/

noncomputable section
namespace Compaction.BernoulliProductCertificate

open Finset UpperTheory.V.Bern

/-- A single positive integer certifies the p-adic size of every eligible
character subsum, at every prime, with the original Archimedean size bound. -/
theorem exists_integer {N : ℕ} [NeZero N] (k : ℕ)
    (P : Set (Subgroup (ZMod N)ˣ)) (hk : 1 ≤ k) (hP : P ⊆ parKer N k) :
    ∃ M : ℕ, 0 < M ∧
      Real.log M ≤ (charSet ℂ P).ncard * Real.log (bnd N k) ∧
      ∀ (l : ℕ) [Fact l.Prime]
        (T : Finset (DirichletCharacter (PadicAlgCl l) N)),
        (T : Set _) ⊆ charSet (PadicAlgCl l) P →
        ∑ χ ∈ T, -Real.log ‖(den N k : PadicAlgCl l) * Bprim k χ‖ ≤
          (M.factorization l : ℝ) * Real.log l := by
  obtain ⟨M, hM, hlog, hprod⟩ := b_prodint k P hk hP
  have habs : (M.natAbs : ℝ) = |(M : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
  refine ⟨M.natAbs, Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr hM), ?_, ?_⟩
  · simpa only [habs] using hlog
  · intro l _ T hT
    have hnorm : ‖(l : PadicAlgCl l)‖ = (l : ℝ)⁻¹ := by
      rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), PadicAlgCl.norm_extends, Padic.norm_p]
    have hS : (charSet (PadicAlgCl l) P).Finite := Set.toFinite _
    have hint : ∀ χ ∈ charSet (PadicAlgCl l) P,
        IsIntegral ℤ (((1 : ℕ) : PadicAlgCl l) * ((den N k : PadicAlgCl l) * Bprim k χ)) := by
      intro χ _
      rw [Nat.cast_one, one_mul]
      exact (b_primmem k χ).2.2.1
    have hpr : ∏ᶠ χ ∈ charSet (PadicAlgCl l) P,
        ((1 : ℕ) : PadicAlgCl l) * ((den N k : PadicAlgCl l) * Bprim k χ) = (M : PadicAlgCl l) := by
      simpa only [Nat.cast_one, one_mul] using hprod (PadicAlgCl l)
    have hu := b_ultra l hnorm (charSet (PadicAlgCl l) P)
      (fun χ => (den N k : PadicAlgCl l) * Bprim k χ) 1 M hS hM hint hpr
    rw [finsum_mem_eq_finite_toFinset_sum _ hS] at hu
    have hv : M.natAbs.factorization l = padicValInt l M := by
      rw [Nat.factorization_def _ (Fact.out : l.Prime)]
      rfl
    rw [hv]
    calc
      ∑ χ ∈ T, -Real.log ‖(den N k : PadicAlgCl l) * Bprim k χ‖
          ≤ ∑ χ ∈ T, max 0 (-Real.log ‖(den N k : PadicAlgCl l) * Bprim k χ‖) :=
        Finset.sum_le_sum fun χ _ => le_max_right _ _
      _ ≤ ∑ χ ∈ hS.toFinset, max 0 (-Real.log ‖(den N k : PadicAlgCl l) * Bprim k χ‖) :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun χ hχ => hS.mem_toFinset.mpr (hT (Finset.mem_coe.mpr hχ)))
          (fun _ _ _ => le_max_left _ _)
      _ ≤ _ := hu

end Compaction.BernoulliProductCertificate

#print axioms Compaction.BernoulliProductCertificate.exists_integer
