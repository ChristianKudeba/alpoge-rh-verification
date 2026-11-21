import PairCertificate
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.KatoUse

/-! Turn the actual NN integers supplied by PropGK into one simultaneous
certificate, independent of the prime, coefficient ring and Galois realization.
The geometric producer PropGK remains an explicit input; this theorem does not
replace its automorphy proof. -/

noncomputable section
namespace CertificateHour.OrbitCertificate

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.U3

/-- For a fixed character orbit, two good auxiliary primes supply one integer
whose valuation controls every permitted realization of the whole orbit. -/
theorem of_propGK (input : PropGK) (K : Type) [Field K] [NumberField K] :
    ∃ c A : ℕ, ∀ (e N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ) (r s : ℕ),
      1 ≤ e → r.Prime → s.Prime → r ≠ s →
      ¬ r ∣ 30 * N * (discr K).natAbs → ¬ s ∣ 30 * N * (discr K).natAbs →
      ∃ M : ℕ, 0 < M ∧
        Real.log M ≤ 2 * c * Nat.totient H.index * ((N : ℝ) * (e + 1))^A *
          (Real.log r + Real.log s) ∧
        ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra K Ω]
          (p : ℕ) [Fact p.Prime] (coef : Coef p),
          (∃ ψ ∈ orb coef H, GD Ω K p e ψ) →
          (∀ ψ ∈ orb coef H, Vlen Ω coef e ψ ≠ ⊤) ∧
            ∑ ψ ∈ orb coef H, Vn Ω coef e ψ ≤ (M.factorization p : ℝ) := by
  obtain ⟨c, A, supply⟩ := input K
  refine ⟨c, A, ?_⟩
  intro e N _ H r s he hr hs hrs hrd hsd
  obtain ⟨n, hn, hsize, control⟩ := supply e N H r he hr hrd
  obtain ⟨n', hn', hsize', control'⟩ := supply e N H s he hs hsd
  refine ⟨PairCertificate.mass n n', PairCertificate.mass_pos hn hn', ?_, ?_⟩
  · calc
      _ ≤ 2 * (c * Nat.totient H.index * ((N : ℝ) * (e + 1))^A * Real.log r +
        c * Nat.totient H.index * ((N : ℝ) * (e + 1))^A * Real.log s) :=
          PairCertificate.log_mass_le hn hn' hsize hsize'
      _ = _ := by ring
  · intro Ω _ _ _ _ p _ coef existsGD
    rw [PairCertificate.factorization_mass hn hn' (Fact.out : p.Prime)]
    push_cast
    by_cases hpr : p = r
    · have hps : p ≠ s := fun hps => hrs (hpr.symm.trans hps)
      obtain ⟨finite, bound⟩ := control' Ω p hps coef existsGD
      exact ⟨finite, by linarith [Nat.cast_nonneg (α := ℝ) (padicValInt p n)]⟩
    · obtain ⟨finite, bound⟩ := control Ω p hpr coef existsGD
      exact ⟨finite, by linarith [Nat.cast_nonneg (α := ℝ) (padicValInt p n')]⟩

end CertificateHour.OrbitCertificate

#print axioms CertificateHour.OrbitCertificate.of_propGK
