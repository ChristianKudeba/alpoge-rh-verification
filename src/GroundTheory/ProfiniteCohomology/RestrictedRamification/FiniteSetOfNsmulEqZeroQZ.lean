import Mathlib
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BrauerSplit
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.ExistsUnitsToIdelesEqOfIdelesSumInvEqZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IsDedekindDomain IntermediateField GroundTheory.Global DirectSum

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

theorem finite_setOf_nsmul_eq_zero_QZ {m : ℕ} (hm : m ≠ 0) : {q : QZ | m • q = 0}.Finite :=
  AddCircle.finite_torsion (1 : ℚ) (Nat.pos_of_ne_zero hm)

variable (K : FiniteSubfield)

theorem exists_place_above (ℓ : ℕ) (hℓ : ℓ.Prime) :
    ∃ w : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ w.asIdeal := by
  have hprime : (Ideal.span {(ℓ : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hℓ.ne_zero)).2 (Nat.prime_iff_prime_int.1 hℓ)
  have hne : Ideal.span {(ℓ : ℤ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hℓ.ne_zero
  have hmax : (Ideal.span {(ℓ : ℤ)}).IsMaximal := hprime.isMaximal hne
  obtain ⟨Q, hQ, hQc⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 K.1)
    (Ideal.span {(ℓ : ℤ)})
  have hmem : ((ℓ : ℕ) : 𝓞 K.1) ∈ Q := by
    have h1 : (ℓ : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 K.1)) := by
      rw [← Ideal.under_def, ← hQc.over]
      exact Ideal.subset_span rfl
    simpa using h1
  refine ⟨⟨Q, hQ.isPrime, fun h => ?_⟩, hmem⟩
  rw [h] at hmem
  have h2 : ((ℓ : ℕ) : 𝓞 K.1) = 0 := (Ideal.mem_bot).1 hmem
  exact hℓ.ne_zero (by exact_mod_cast h2)

variable (S : Set (HeightOneSpectrum (𝓞 K.1))) (ℓ : ℕ) (hℓ : ℓ.Prime)
  (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S) (ιs : LocalEmbeddings K)

open Classical in
include hℓ hS in

theorem exists_gsLocalRes_eq_single (v : HeightOneSpectrum (𝓞 K.1)) (hv : v ∉ S)
    (t : localGaloisCohomology K 2 (.inr v)) (k : ℕ) (ht : ℓ ^ k • t = 0) :
    ∃ x : cohomology (uliftIntToIntRep (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S))) 2,
      ℓ ^ k • x = 0 ∧ (gsLocalRes S (ιs.fin v) 2).hom x = t ∧
      ∀ v' : HeightOneSpectrum (𝓞 K.1), v' ∉ S → v' ≠ v → (gsLocalRes S (ιs.fin v') 2).hom x = 0 := by
  refine (exists_place_above K ℓ hℓ).elim fun w hw => ?_
  have hwS : w ∈ S := hS w hw
  have hwv : w ≠ v := fun h => hv (h ▸ hwS)
  refine ((placeInv_bijective_inr (K := K) w).2 (-(placeInv (.inr v) t))).elim fun t' ht' => ?_
  refine (⟨_, rfl⟩ : ∃ T : ⨁ u : Place K.1, localGaloisCohomology K 2 u,
      T = DirectSum.of (fun u : Place K.1 => localGaloisCohomology K 2 u) (.inr v) t +
        DirectSum.of (fun u : Place K.1 => localGaloisCohomology K 2 u) (.inr w) t').elim fun T hTdef => ?_
  have hT : sumPlaceInv K T = 0 := by
    rw [hTdef, map_add, sumPlaceInv_of, sumPlaceInv_of, ht', add_neg_cancel]
  refine ((sumPlaceInv_eq_zero_iff ιs T).1 hT).elim fun y hy => ?_
  have ht'k : ℓ ^ k • t' = 0 := by
    apply (placeInv_bijective_inr (K := K) w).1
    rw [map_nsmul, ht', smul_neg, ← map_nsmul, ht, map_zero, neg_zero, map_zero]
  have hTk : ℓ ^ k • T = 0 := by
    rw [hTdef, smul_add, ← map_nsmul, ← map_nsmul, ht, ht'k, map_zero, map_zero, add_zero]
  have hyk : ℓ ^ k • y = 0 :=
    brauerLocal_injective ιs (by rw [map_nsmul, hy, hTk, map_zero])
  refine (exists_gsBrauerInfl_eq K S ℓ hℓ hS y k hyk).elim fun x hx => ?_
  have hxk : ℓ ^ k • x = 0 := by
    apply gsBrauerInfl_injective K S
    rw [map_nsmul, hx, hyk, map_zero]
  refine ⟨x, hxk, ?_, fun v' hv' hv'v => ?_⟩
  · rw [← brauerLocal_gsBrauerInfl_inr, hx, hy]
    rw [hTdef]
    simp only [DirectSum.add_apply, DirectSum.of_eq_same]
    rw [DirectSum.of_eq_of_ne _ _ _ (by simpa using hwv.symm), add_zero]
  · have hv'w : v' ≠ w := fun h => hv' (h ▸ hwS)
    have h0 : brauerLocal ιs ((gsBrauerInfl K S 2).hom x) (.inr v') = 0 := by
      rw [hx, hy, hTdef]
      simp only [DirectSum.add_apply]
      rw [DirectSum.of_eq_of_ne _ _ _ (by simpa using hv'v),
        DirectSum.of_eq_of_ne _ _ _ (by simpa using hv'w), add_zero]
    exact (brauerLocal_gsBrauerInfl_inr K S ιs v' x).symm.trans h0

end

end GroundTheory.ProfCoh
