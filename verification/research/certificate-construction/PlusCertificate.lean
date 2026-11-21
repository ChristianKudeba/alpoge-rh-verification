import AllOrbitCertificate
import NormalizedLength
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.RedPrime
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.DvrFacts

/-! A certificate from PropGK for the actual plus-length at one twist, whenever
the host characters have GD. No finite set of primes is part of the certificate
construction. The arithmetic GD hypothesis is satisfied on generic Case I. -/

noncomputable section
namespace CertificateHour.PlusCertificate

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.U3

theorem of_character_certificate
    (K : Type) [Field K] [NumberField K] (N : ℕ) [NeZero N]
    (H : Subgroup (ZMod N)ˣ) (e M : ℕ)
    (hM : ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra K Ω]
      (p : ℕ) [Fact p.Prime] (coef : Coef p)
      (S : Finset (DirichletCharacter coef.O N)), (∀ ψ ∈ S, GD Ω K p e ψ) →
      (∀ ψ ∈ S, Vlen Ω coef e ψ ≠ ⊤) ∧
        ∑ ψ ∈ S, Vn Ω coef e ψ ≤ (M.factorization p : ℝ))
    (E : Type) [Field E] [NumberField E] [IsCMField E] (hlevel : Chr.HasLevel E N H)
    (Ω' : Type) [Field Ω'] [Algebra E Ω'] [IsAlgClosure E Ω']
    (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra K Ω]
    (p : ℕ) [Fact p.Prime] (odd : p ≠ 2) (idx : ¬ p ∣ H.index)
    (coef : Coef p) [HasEnoughRootsOfUnity coef.O (Nat.totient N)]
    (D : LData E Ω' p) (positive : 0 < e)
    (S : Finset (DirichletCharacter coef.O N))
    (hS : (S : Set _) = Chr.evenSet coef.O H e) (gd : ∀ ψ ∈ S, GD Ω K p e ψ) :
    plusLen D e ≠ ⊤ ∧ plusLen D e ≤ (M.factorization p : ℕ∞) := by
  obtain ⟨hf, hsize⟩ := hM Ω p coef S gd
  have hred := redPrime E N H hlevel p odd idx coef Ω' D Ω e positive.ne' S hS
  have hdvr := dvrFacts p coef.O
  have hEfin : eO p coef.O ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top _) hdvr.2.2.2.2.2.2.1
  have hEeq : eO p coef.O = (((eO p coef.O).toNat : ℕ) : ℕ∞) :=
    (ENat.natCast_toNat hEfin).symm
  have hEpos : (eO p coef.O).toNat ≠ 0 := by
    intro hz
    exact hdvr.2.2.2.2.2.1 (by rw [hEeq, hz]; rfl)
  rw [hEeq] at hred
  have back := NormalizedLength.bound S (fun ψ => Vlen Ω coef e ψ) (plusLen D e)
    (eO p coef.O).toNat hEpos hf hred
  refine ⟨back.1, ?_⟩
  have hnat : (plusLen D e).toNat ≤ M.factorization p := by
    exact_mod_cast back.2.trans hsize
  rw [← ENat.natCast_toNat back.1]
  exact_mod_cast hnat

end CertificateHour.PlusCertificate
#print axioms CertificateHour.PlusCertificate.of_character_certificate
