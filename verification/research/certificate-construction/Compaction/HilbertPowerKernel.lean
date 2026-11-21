import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ArtConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ArtSurj
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ArtIne
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ArtDec
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ToGalDict
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalQuot

/-! The kernel defining the elementary Hilbert p-class field is open and
normal over Q whenever the original number field is normal over Q. This is the
normality bridge for the proposed Weber proof. This file is a candidate pending
compilation against the complete archive imports. -/

noncomputable section
namespace Compaction.HilbertPowerKernel

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
  Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum

variable (K Ω : Type) [Field K] [NumberField K] [Field Ω]
  [Algebra ℚ K] [Algebra ℚ Ω] [Algebra K Ω] [IsScalarTower ℚ K Ω]
  [IsAlgClosure ℚ Ω] [IsAlgClosure K Ω] [Normal ℚ K]

def kernel (n : ℕ) : Subgroup (G ℚ Ω) :=
  (((powMonoidHom n : ClassGroup (𝓞 K) →* ClassGroup (𝓞 K)).range).comap
    ((artCl K Ω).comp (toGal K (le_refl (galOf ℚ K Ω))))).map
      (galOf ℚ K Ω).subtype

theorem normal (n : ℕ) : (kernel K Ω n).Normal := by
  haveI : (galOf ℚ K Ω).Normal := by
    rw [← (galQuot ℚ K Ω).2.1]
    infer_instance
  constructor
  rintro a ⟨u, hu, rfl⟩ g
  let v : galOf ℚ K Ω := ⟨g * (u : G ℚ Ω) * g⁻¹,
    (inferInstance : (galOf ℚ K Ω).Normal).conj_mem _ u.2 g⟩
  refine ⟨v, ?_, rfl⟩
  let τ : K ≃+* K := (AlgEquiv.restrictNormalHom K g : Gal(K/ℚ)).toRingEquiv
  have hlift : IsLift τ g.toRingEquiv := (galQuot ℚ K Ω).2.2 g
  have hconj : conjGal hlift (toGal K (le_refl (galOf ℚ K Ω)) v) =
      toGal K (le_refl (galOf ℚ K Ω)) u := by
    apply AlgEquiv.ext
    intro x
    change g.symm ((g * (u : G ℚ Ω) * g⁻¹) (g x)) = (u : G ℚ Ω) x
    simp
  have hart := artConj K Ω τ g.toRingEquiv hlift
    (toGal K (le_refl (galOf ℚ K Ω)) v)
  rw [hconj] at hart
  change ∃ c : ClassGroup (𝓞 K), c ^ n =
    artCl K Ω (toGal K (le_refl (galOf ℚ K Ω)) u) at hu
  obtain ⟨c, hc⟩ := hu
  change ∃ c : ClassGroup (𝓞 K), c ^ n =
    artCl K Ω (toGal K (le_refl (galOf ℚ K Ω)) v)
  refine ⟨clMap τ c, ?_⟩
  rw [hart, ← hc, map_pow]

theorem isOpen (n : ℕ) : IsOpen (kernel K Ω n : Set (G ℚ Ω)) := by
  let U := galOf ℚ K Ω
  let f : U →* ClassGroup (𝓞 K) := (artCl K Ω).comp (toGal K (le_refl U))
  let S := (powMonoidHom n : ClassGroup (𝓞 K) →* ClassGroup (𝓞 K)).range
  have hf : IsLocallyConstant f :=
    (artSurj K Ω).2.comp_continuous (toGalDict ℚ Ω K U (le_refl U)).2.2.1
  have ho : IsOpen (S.comap f : Set U) := hf (S : Set (ClassGroup (𝓞 K)))
  have hU : IsOpen (U : Set (G ℚ Ω)) := (galEmbTop ℚ K Ω).2.1
  change IsOpen (Subtype.val '' (S.comap f : Set U))
  exact hU.isOpenMap_subtype_val _ ho

/-- The index factors as the class-group quotient size times the original
field degree. For n=p and a p-extension K/Q, it is a p-power. -/
theorem index (n : ℕ) : (kernel K Ω n).index =
    (powMonoidHom n : ClassGroup (𝓞 K) →* ClassGroup (𝓞 K)).range.index *
      Module.finrank ℚ K := by
  let U := galOf ℚ K Ω
  have hf : Function.Surjective ((artCl K Ω).comp (toGal K (le_refl U))) :=
    (artSurj K Ω).1.comp
      (((toGalDict ℚ Ω K U (le_refl U)).2.2.2 (le_refl U)).1.surjective)
  rw [kernel, Subgroup.index_map_subtype,
    ((powMonoidHom n : ClassGroup (𝓞 K) →* ClassGroup (𝓞 K)).range).index_comap_of_surjective hf,
    (galEmbTop ℚ K Ω).2.2]

/-- All inertia relative to K lies in the elementary Hilbert-class kernel. -/
theorem contains_relative_inertia (n : ℕ) (A : ValuationSubring Ω)
    (u : galOf ℚ K Ω) (hu : (u : G ℚ Ω) ∈ Ine (F := ℚ) A) :
    (u : G ℚ Ω) ∈ kernel K Ω n := by
  have hmem : toGal K (le_refl (galOf ℚ K Ω)) u ∈ Ine (F := K) A :=
    ((toGalDict ℚ Ω K (galOf ℚ K Ω) (le_refl _)).2.1 A u).mpr hu
  have hart := (artIne K Ω).1 A _ hmem
  refine ⟨u, ?_, rfl⟩
  change ∃ c : ClassGroup (𝓞 K), c ^ n =
    artCl K Ω (toGal K (le_refl (galOf ℚ K Ω)) u)
  exact ⟨1, by rw [one_pow, hart]⟩

/-- A principal prime's entire decomposition group is killed. This is the
splitting input at the prime (zeta-1) above 2 in Weber's theorem. -/
theorem contains_principal_decomposition (n : ℕ) (A : ValuationSubring Ω)
    (v : HeightOneSpectrum (𝓞 K)) (hA : IsPlaceOver A v) (hv : primeCl v = 1)
    (u : galOf ℚ K Ω) (hu : (u : G ℚ Ω) ∈ Dec (F := ℚ) A) :
    (u : G ℚ Ω) ∈ kernel K Ω n := by
  have hmem : toGal K (le_refl (galOf ℚ K Ω)) u ∈ Dec (F := K) A :=
    ((toGalDict ℚ Ω K (galOf ℚ K Ω) (le_refl _)).1 A u).mpr hu
  have hart : artCl K Ω (toGal K (le_refl (galOf ℚ K Ω)) u) = 1 := by
    have hm : artCl K Ω (toGal K (le_refl (galOf ℚ K Ω)) u) ∈
        (Dec (F := K) A).map (artCl K Ω) := ⟨_, hmem, rfl⟩
    rw [artDec K Ω A v hA, hv] at hm
    simpa using hm
  refine ⟨u, ?_, rfl⟩
  change ∃ c : ClassGroup (𝓞 K), c ^ n =
    artCl K Ω (toGal K (le_refl (galOf ℚ K Ω)) u)
  exact ⟨1, by rw [one_pow, hart]⟩

end Compaction.HilbertPowerKernel

#print axioms Compaction.HilbertPowerKernel.normal
#print axioms Compaction.HilbertPowerKernel.isOpen
#print axioms Compaction.HilbertPowerKernel.index
#print axioms Compaction.HilbertPowerKernel.contains_principal_decomposition
