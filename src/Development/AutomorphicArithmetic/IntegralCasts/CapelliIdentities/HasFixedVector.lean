import Mathlib
import Lemmata.IsotypicGeneration
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BlochKatoSelmerVanishes
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIdempotentElemCharIdem
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL


theorem UpperTheory.Reformulated.B.HasFixedVector.hasFixed :
    ∀ {F : Type} [inst : Field F] [inst_1 : NumberField F] {n : ℕ} {V : Type} [inst_2 : AddCommGroup V]
      [inst_3 : _root_.Module ℂ V] {ρ : Representation ℂ (GL (Fin n) (GlobalTheory.CuspRep.Af F)) V}
      {w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)}
      {σ : GlobalTheory.CuspRep.SmIrr (GL (Fin n) (IsDedekindDomain.HeightOneSpectrum.adicCompletion F w))},
      UpperTheory.V.Af.LocIsotypic ρ w σ →
        ∀ {U : Subgroup (GL (Fin n) (IsDedekindDomain.HeightOneSpectrum.adicCompletion F w))},
          IsCompact (↑U : Set (GL (Fin n) (IsDedekindDomain.HeightOneSpectrum.adicCompletion F w))) →
            UpperTheory.V.Af.HasFixed (MonoidHom.comp ρ (GlobalTheory.CuspRep.locGL F n w)) U → UpperTheory.V.Af.HasFixed σ.ρ U := by
  intro F _ _ n V _ _ ρ w σ hiso U _ hfix
  obtain ⟨v, hv, hvfix⟩ := hfix
  obtain ⟨f, hf⟩ := Lemmata.IsotypicGeneration.intertwiner σ.ρ
    (MonoidHom.comp ρ (GlobalTheory.CuspRep.locGL F n w)) σ.irred
    (by simpa using hiso.2) hv
  exact ⟨f v, hf, fun u hu => by rw [← f.isIntertwining, hvfix u hu]⟩
