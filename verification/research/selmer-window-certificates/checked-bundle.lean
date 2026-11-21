import Mathlib
set_option linter.all false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 4000000

section
-- Source: ReciprocityTheory/GaloisValuations/SeparatedDvrSecondCohomologyMem.lean

namespace ReciprocityTheory.Gal

set_option linter.unusedVariables false

noncomputable section

open Representation

variable {R : Type*} [CommRing R]
variable {G : Type*} [Group G] [TopologicalSpace G]
variable {M : Type*} [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul R M]

section ContMaps

variable (R M)

def contMaps (X : Type*) [TopologicalSpace X] : Submodule R (X → M) where
  carrier := {f | Continuous f}
  zero_mem' := continuous_const
  add_mem' hf hg := hf.add hg
  smul_mem' c _ hf := hf.const_smul c

variable {R M}

theorem mem_contMaps {X : Type*} [TopologicalSpace X] (f : X → M) :
    f ∈ contMaps R M X ↔ Continuous f := Iff.rfl

end ContMaps

def ContAction (rho : Representation R G M) : Prop :=
  Continuous (fun p : G × M => rho p.1 p.2)

variable (rho : Representation R G M)

def H0 : Submodule R M := rho.invariants

theorem mem_riemannRochSpace_iff_regularAt_everywhere (m : M) : m ∈ H0 rho ↔ ∀ g, rho g m = m := Iff.rfl

def Z1 : Submodule R (G → M) where
  carrier := {f | Continuous f ∧ ∀ g h, f (g * h) = f g + rho g (f h)}
  zero_mem' := ⟨continuous_const, fun g h => by simp⟩
  add_mem' := fun {f f'} hf hf' => ⟨hf.1.add hf'.1, fun g h => by
    simp only [Pi.add_apply, hf.2, hf'.2, map_add]; abel⟩
  smul_mem' c f hf := ⟨hf.1.const_smul c, fun g h => by
    simp only [Pi.smul_apply, hf.2, map_smul, smul_add]⟩

theorem mem_Z1_iff_cocycle (f : G → M) :
    f ∈ Z1 rho ↔ Continuous f ∧ ∀ g h, f (g * h) = f g + rho g (f h) := Iff.rfl

def d0 : M →ₗ[R] (G → M) := LinearMap.pi fun g => rho g - LinearMap.id

@[simp] theorem amitsur_d0_apply (m : M) (g : G) : d0 rho m g = rho g m - m := rfl

def B1 : Submodule R (G → M) := LinearMap.range (d0 rho)

theorem mem_coboundaries1 (f : G → M) : f ∈ B1 rho ↔ ∃ m, ∀ g, f g = rho g m - m := by
  constructor
  · rintro ⟨m, rfl⟩
    exact ⟨m, fun g => rfl⟩
  · rintro ⟨m, hm⟩
    exact ⟨m, funext fun g => (hm g).symm⟩

abbrev H1 := Z1 rho ⧸ (B1 rho).comap (Z1 rho).subtype

def Z2 : Submodule R (G × G → M) where
  carrier := {f | Continuous f ∧
    ∀ g h k, rho g (f (h, k)) - f (g * h, k) + f (g, h * k) - f (g, h) = 0}
  zero_mem' := ⟨continuous_const, fun g h k => by simp⟩
  add_mem' := fun {f f'} hf hf' => ⟨hf.1.add hf'.1, fun g h k => by
    have e1 := hf.2 g h k; have e2 := hf'.2 g h k
    simp only [Pi.add_apply, map_add]
    calc _ = (rho g (f (h, k)) - f (g * h, k) + f (g, h * k) - f (g, h)) +
          (rho g (f' (h, k)) - f' (g * h, k) + f' (g, h * k) - f' (g, h)) := by abel
      _ = 0 := by rw [e1, e2, add_zero]⟩
  smul_mem' c f hf := ⟨hf.1.const_smul c, fun g h k => by
    have e := hf.2 g h k
    simp only [Pi.smul_apply, map_smul]
    rw [← smul_sub, ← smul_add, ← smul_sub, e, smul_zero]⟩

theorem mem_cocycles2 (f : G × G → M) :
    f ∈ Z2 rho ↔ Continuous f ∧
      ∀ g h k, rho g (f (h, k)) - f (g * h, k) + f (g, h * k) - f (g, h) = 0 := Iff.rfl

def d1 : (G → M) →ₗ[R] (G × G → M) where
  toFun c p := rho p.1 (c p.2) - c (p.1 * p.2) + c p.1
  map_add' c c' := by
    funext p; simp only [Pi.add_apply, map_add]; abel
  map_smul' r c := by
    funext p; simp only [Pi.smul_apply, map_smul, RingHom.id_apply, smul_sub, smul_add]

@[simp] theorem d1_apply (c : G → M) (g h : G) :
    d1 rho c (g, h) = rho g (c h) - c (g * h) + c g := rfl

def B2 : Submodule R (G × G → M) := (contMaps R M G).map (d1 rho)

theorem separated_dvr_second_cohomology_mem (f : G × G → M) :
    f ∈ B2 rho ↔ ∃ c : G → M, Continuous c ∧ d1 rho c = f := Iff.rfl

abbrev H2 := Z2 rho ⧸ (B2 rho).comap (Z2 rho).subtype

def Cn (rho : Representation R G M) (n : ℕ) : Submodule R ((Fin n → G) → M) := contMaps R M (Fin n → G)

def dn (n : ℕ) : ((Fin n → G) → M) →ₗ[R] ((Fin (n + 1) → G) → M) where
  toFun f g := rho (g 0) (f fun i => g i.succ) + Finset.univ.sum fun j : Fin (n + 1) =>
    (-1 : R) ^ ((j : ℕ) + 1) • f (Fin.contractNth j (· * ·) g)
  map_add' f f' := by
    funext g
    simp [Finset.sum_add_distrib, add_add_add_comm]
  map_smul' r f := by
    funext g
    simp [Finset.smul_sum, ← smul_assoc, mul_comm r]

theorem dn_apply (n : ℕ) (f : (Fin n → G) → M) (g : Fin (n + 1) → G) :
    dn rho n f g = rho (g 0) (f fun i => g i.succ) + Finset.univ.sum fun j : Fin (n + 1) =>
      (-1 : R) ^ ((j : ℕ) + 1) • f (Fin.contractNth j (· * ·) g) := rfl

def Zn (n : ℕ) : Submodule R ((Fin n → G) → M) := Cn rho n ⊓ LinearMap.ker (dn rho n)

def Bn : (n : ℕ) → Submodule R ((Fin n → G) → M)
  | 0 => ⊥
  | n + 1 => (Cn rho n).map (dn rho n)

abbrev Hn (n : ℕ) := Zn rho n ⧸ (Bn rho n).comap (Zn rho n).subtype

section Restriction

variable {H : Type*} [Group H] [TopologicalSpace H] (phi : H →* G)

def resH0 : H0 rho →ₗ[R] H0 (rho.comp phi) :=
  Submodule.inclusion fun _ hm h => hm (phi h)

variable (hphi : Continuous phi)
include hphi

def restrictCocycles1 : Z1 rho →ₗ[R] Z1 (rho.comp phi) where
  toFun f := ⟨f.1 ∘ phi, f.2.1.comp hphi, fun g h => by
    simp only [Function.comp_apply, map_mul, MonoidHom.coe_comp]
    exact f.2.2 _ _⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem restrictCocycles1_apply (f : Z1 rho) (h : H) : (restrictCocycles1 rho phi hphi f).1 h = f.1 (phi h) := rfl

def resH1 : H1 rho →ₗ[R] H1 (rho.comp phi) :=
  Submodule.mapQ _ _ (restrictCocycles1 rho phi hphi) fun f hf => by
    obtain ⟨m, hm⟩ := (mem_coboundaries1 rho _).1 hf
    exact (mem_coboundaries1 _ _).2 ⟨m, fun h => hm (phi h)⟩

def restrictCocycles2 : Z2 rho →ₗ[R] Z2 (rho.comp phi) where
  toFun f := ⟨fun p => f.1 (phi p.1, phi p.2), f.2.1.comp (hphi.prodMap hphi), fun g h k => by
    simp only [map_mul, MonoidHom.coe_comp, Function.comp_apply]
    exact f.2.2 _ _ _⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem restrictCocycles2_apply (f : Z2 rho) (g h : H) :
    (restrictCocycles2 rho phi hphi f).1 (g, h) = f.1 (phi g, phi h) := rfl

def resH2 : H2 rho →ₗ[R] H2 (rho.comp phi) :=
  Submodule.mapQ _ _ (restrictCocycles2 rho phi hphi) fun f hf => by
    obtain ⟨c, hc, hcf⟩ := (separated_dvr_second_cohomology_mem rho _).1 hf
    refine (separated_dvr_second_cohomology_mem _ _).2 ⟨c ∘ phi, hc.comp hphi, ?_⟩
    funext p
    have e := congrFun hcf (phi p.1, phi p.2)
    simp only [Submodule.coe_subtype] at e
    change _ = f.1 (phi p.1, phi p.2)
    rw [← e]
    simp [d1]

end Restriction

section Map

variable {M' : Type*} [AddCommGroup M'] [Module R M'] [TopologicalSpace M']
  [IsTopologicalAddGroup M'] [ContinuousConstSMul R M']
  (rho' : Representation R G M') (u : M →ₗ[R] M') (hu : Continuous u)
  (hequiv : ∀ g m, u (rho g m) = rho' g (u m))
include hu hequiv

def cocycles1MapOfEquivariant : Z1 rho →ₗ[R] Z1 rho' where
  toFun f := ⟨u ∘ f.1, hu.comp f.2.1, fun g h => by
    simp only [Function.comp_apply, f.2.2 g h, map_add, hequiv]⟩
  map_add' f f' := Subtype.ext (funext fun g => map_add u _ _)
  map_smul' r f := Subtype.ext (funext fun g => map_smul u _ _)

def mapH1 : H1 rho →ₗ[R] H1 rho' :=
  Submodule.mapQ _ _ (cocycles1MapOfEquivariant rho rho' u hu hequiv) fun f hf => by
    obtain ⟨m, hm⟩ := (mem_coboundaries1 rho _).1 hf
    refine (mem_coboundaries1 _ _).2 ⟨u m, fun g => ?_⟩
    have e := hm g
    simp only [Submodule.coe_subtype] at e
    change u (f.1 g) = _
    rw [e, map_sub, hequiv]

def cocycles2Map : Z2 rho →ₗ[R] Z2 rho' where
  toFun f := ⟨u ∘ f.1, hu.comp f.2.1, fun g h k => by
    simp only [Function.comp_apply, ← hequiv, ← map_sub, ← map_add, f.2.2 g h k, map_zero]⟩
  map_add' f f' := Subtype.ext (funext fun g => map_add u _ _)
  map_smul' r f := Subtype.ext (funext fun g => map_smul u _ _)

def mapH2 : H2 rho →ₗ[R] H2 rho' :=
  Submodule.mapQ _ _ (cocycles2Map rho rho' u hu hequiv) fun f hf => by
    obtain ⟨c, hc, hcf⟩ := (separated_dvr_second_cohomology_mem rho _).1 hf
    refine (separated_dvr_second_cohomology_mem _ _).2 ⟨u ∘ c, hu.comp hc, ?_⟩
    funext p
    have e := congrFun hcf p
    simp only [Submodule.coe_subtype] at e
    change _ = u (f.1 p)
    rw [← e]
    simp [d1, hequiv]

end Map

section Pair

variable {G' : Type*} [Group G'] [TopologicalSpace G']
  {M' : Type*} [AddCommGroup M'] [Module R M'] [TopologicalSpace M']
  [IsTopologicalAddGroup M'] [ContinuousConstSMul R M']
  (rho' : Representation R G' M') (phi : G' →* G) (hphi : Continuous phi)
  (u : M →ₗ[R] M') (hu : Continuous u) (hcompat : ∀ g m, u (rho (phi g) m) = rho' g (u m))
include hphi hu hcompat

def compatiblePairCocycles1 : Z1 rho →ₗ[R] Z1 rho' where
  toFun f := ⟨fun g => u (f.1 (phi g)), hu.comp (f.2.1.comp hphi), fun g h => by
    simp only [map_mul, f.2.2, map_add, hcompat]⟩
  map_add' f f' := Subtype.ext (funext fun g => map_add u _ _)
  map_smul' r f := Subtype.ext (funext fun g => map_smul u _ _)

@[simp] theorem compatiblePairCocycles1_apply (f : Z1 rho) (g : G') :
    (compatiblePairCocycles1 rho rho' phi hphi u hu hcompat f).1 g = u (f.1 (phi g)) := rfl

def pairH1DecompositionMap : H1 rho →ₗ[R] H1 rho' :=
  Submodule.mapQ _ _ (compatiblePairCocycles1 rho rho' phi hphi u hu hcompat) fun f hf => by
    obtain ⟨m, hm⟩ := (mem_coboundaries1 rho _).1 hf
    refine (mem_coboundaries1 _ _).2 ⟨u m, fun g => ?_⟩
    have e := hm (phi g)
    simp only [Submodule.coe_subtype] at e
    change u (f.1 (phi g)) = _
    rw [e, map_sub, hcompat]

def compatiblePairCocycles2 : Z2 rho →ₗ[R] Z2 rho' where
  toFun f := ⟨fun p => u (f.1 (phi p.1, phi p.2)), hu.comp (f.2.1.comp (hphi.prodMap hphi)),
    fun g h k => by
      have e := congrArg u (f.2.2 (phi g) (phi h) (phi k))
      simp only [map_sub, map_add, map_zero, hcompat] at e
      simpa only [map_mul] using e⟩
  map_add' f f' := Subtype.ext (funext fun g => map_add u _ _)
  map_smul' r f := Subtype.ext (funext fun g => map_smul u _ _)

@[simp] theorem compatiblePairCocycles2_apply (f : Z2 rho) (g h : G') :
    (compatiblePairCocycles2 rho rho' phi hphi u hu hcompat f).1 (g, h) = u (f.1 (phi g, phi h)) := rfl

def compatiblePairH2 : H2 rho →ₗ[R] H2 rho' :=
  Submodule.mapQ _ _ (compatiblePairCocycles2 rho rho' phi hphi u hu hcompat) fun f hf => by
    obtain ⟨c, hc, hcf⟩ := (separated_dvr_second_cohomology_mem rho _).1 hf
    refine (separated_dvr_second_cohomology_mem _ _).2 ⟨fun g => u (c (phi g)), hu.comp (hc.comp hphi), ?_⟩
    funext p
    have e := congrFun hcf (phi p.1, phi p.2)
    simp only [Submodule.coe_subtype] at e
    change _ = u (f.1 (phi p.1, phi p.2))
    rw [← e]
    simp [d1, hcompat]

end Pair

section MapPair

variable {M' : Type*} [AddCommGroup M'] [Module R M'] [TopologicalSpace M']
  [IsTopologicalAddGroup M'] [ContinuousConstSMul R M']
  (rho' : Representation R G M') (u : M →ₗ[R] M') (hu : Continuous u)
  (hequiv : ∀ g m, u (rho g m) = rho' g (u m))

end MapPair

theorem coboundaries_le_cocycles (h : ContAction rho) : B1 rho ≤ Z1 rho := by
  intro f hf
  obtain ⟨m, hm⟩ := (mem_coboundaries1 rho f).1 hf
  obtain rfl : f = fun g => rho g m - m := funext hm
  refine ⟨(h.comp (continuous_id.prodMk continuous_const)).sub continuous_const, fun g k => ?_⟩
  simp only [map_mul, Module.End.mul_apply, map_sub]
  abel

theorem coboundaries2_le_cocycles2 [ContinuousMul G] (h : ContAction rho) : B2 rho ≤ Z2 rho := by
  intro f hf
  obtain ⟨c, hc, rfl⟩ := (separated_dvr_second_cohomology_mem rho f).1 hf
  refine ⟨?_, fun g k l => ?_⟩
  · have h1 : Continuous fun p : G × G => rho p.1 (c p.2) :=
      h.comp (continuous_fst.prodMk (hc.comp continuous_snd))
    have h2 : Continuous fun p : G × G => c (p.1 * p.2) := hc.comp continuous_mul
    have h3 : Continuous fun p : G × G => c p.1 := hc.comp continuous_fst
    exact (h1.sub h2).add h3
  · simp only [d1_apply, map_mul, Module.End.mul_apply, map_sub, map_add, mul_assoc]
    abel

end

end ReciprocityTheory.Gal
end


section
-- Source: ReciprocityTheory/GaloisValuations/ContinuousConstSMulQuotient.lean

namespace ReciprocityTheory.Gal

noncomputable section

open Representation

variable {R : Type*} [CommRing R]
variable {G : Type*} [Group G] [TopologicalSpace G]
variable {M : Type*} [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul R M]

variable (rho : Representation R G M)

section Cup

variable {M' : Type*} [AddCommGroup M'] [Module R M'] [TopologicalSpace M']
  [IsTopologicalAddGroup M'] [ContinuousConstSMul R M']
  {P : Type*} [AddCommGroup P] [Module R P] [TopologicalSpace P]
  [IsTopologicalAddGroup P] [ContinuousConstSMul R P]
  (rho' : Representation R G M') (rhoP : Representation R G P)
  (b : M →ₗ[R] M' →ₗ[R] P) (hb : Continuous fun p : M × M' => b p.1 p.2)
  (hbe : ∀ g x y, b (rho g x) (rho' g y) = rhoP g (b x y))

section CupZ11

include hb hbe

def cupCocycleZ1Z1 (hrho' : ContAction rho') : Z1 rho →ₗ[R] Z1 rho' →ₗ[R] Z2 rhoP :=
  LinearMap.mk₂ R
    (fun x y => ⟨fun p => b (x.1 p.1) (rho' p.1 (y.1 p.2)),
      hb.comp ((x.2.1.comp continuous_fst).prodMk
        (hrho'.comp (continuous_fst.prodMk (y.2.1.comp continuous_snd)))),
      fun g h k => by
        have hx := x.2.2 g h
        have hy := y.2.2 h k
        dsimp only
        rw [← hbe, hx, hy, map_mul, Module.End.mul_apply]
        simp only [map_add, LinearMap.add_apply]
        abel⟩)
    (fun x x' y => Subtype.ext (funext fun p => by simp))
    (fun r x y => Subtype.ext (funext fun p => by simp))
    (fun x y y' => Subtype.ext (funext fun p => by simp))
    (fun r x y => Subtype.ext (funext fun p => by simp))

@[simp] theorem cupCocycleZ1Z1_apply (hrho' : ContAction rho') (x : Z1 rho) (y : Z1 rho') (g h : G) :
    (cupCocycleZ1Z1 rho rho' rhoP b hb hbe hrho' x y).1 (g, h) = b (x.1 g) (rho' g (y.1 h)) := rfl

def cupProductH1H1 (hrho' : ContAction rho') : H1 rho →ₗ[R] H1 rho' →ₗ[R] H2 rhoP :=
  LinearMap.liftQ₂ _ _ ((cupCocycleZ1Z1 rho rho' rhoP b hb hbe hrho').compr₂ (Submodule.mkQ _))
    (fun x hx => by
      obtain ⟨m, hm⟩ := (mem_coboundaries1 rho _).1 hx
      rw [LinearMap.mem_ker]
      refine LinearMap.ext fun y => ?_
      rw [LinearMap.compr₂_apply, Submodule.mkQ_apply, LinearMap.zero_apply,
        Submodule.Quotient.mk_eq_zero]
      refine (separated_dvr_second_cohomology_mem _ _).2 ⟨fun h => b m (y.1 h), hb.comp (continuous_const.prodMk y.2.1), ?_⟩
      funext p
      obtain ⟨g, h⟩ := p
      have e := hm g
      simp only [Submodule.coe_subtype] at e
      simp only [d1_apply, Submodule.coe_subtype, cupCocycleZ1Z1_apply, e, ← hbe, y.2.2 g h, map_add,
        map_sub, LinearMap.sub_apply]
      abel)
    (fun y hy => by
      obtain ⟨m, hm⟩ := (mem_coboundaries1 rho' _).1 hy
      rw [LinearMap.mem_ker]
      refine LinearMap.ext fun x => ?_
      rw [LinearMap.flip_apply, LinearMap.compr₂_apply, Submodule.mkQ_apply, LinearMap.zero_apply,
        Submodule.Quotient.mk_eq_zero]
      refine (separated_dvr_second_cohomology_mem _ _).2 ⟨fun g => -b (x.1 g) (rho' g m),
        (hb.comp (x.2.1.prodMk (hrho'.comp (continuous_id.prodMk continuous_const)))).neg, ?_⟩
      funext p
      obtain ⟨g, h⟩ := p
      have e := hm h
      simp only [Submodule.coe_subtype] at e
      simp only [d1_apply, Submodule.coe_subtype, cupCocycleZ1Z1_apply, e, map_neg, ← hbe, x.2.2 g h,
        map_mul, Module.End.mul_apply, map_add, map_sub, LinearMap.add_apply]
      abel)

end CupZ11

include hb hbe

def cupCocycleH0Z2 : H0 rho →ₗ[R] Z2 rho' →ₗ[R] Z2 rhoP :=
  LinearMap.mk₂ R
    (fun m f => ⟨fun p => b m.1 (f.1 p), hb.comp (continuous_const.prodMk f.2.1),
      fun g h k => by
        have e := congrArg (b m.1) (f.2.2 g h k)
        simp only [map_sub, map_add, map_zero] at e
        rw [← hbe, (mem_riemannRochSpace_iff_regularAt_everywhere rho m.1).1 m.2 g]
        exact e⟩)
    (fun m m' f => Subtype.ext (funext fun p => by simp))
    (fun r m f => Subtype.ext (funext fun p => by simp))
    (fun m f f' => Subtype.ext (funext fun p => by simp))
    (fun r m f => Subtype.ext (funext fun p => by simp))

@[simp] theorem cupCocycleH0Z2_apply (m : H0 rho) (f : Z2 rho') (p : G × G) :
    (cupCocycleH0Z2 rho rho' rhoP b hb hbe m f).1 p = b m.1 (f.1 p) := rfl

def cupProductH0H2 : H0 rho →ₗ[R] H2 rho' →ₗ[R] H2 rhoP :=
  (Submodule.liftQ _ ((cupCocycleH0Z2 rho rho' rhoP b hb hbe).compr₂ (Submodule.mkQ _)).flip
    (fun f hf => by
      obtain ⟨c, hc, hcf⟩ := (separated_dvr_second_cohomology_mem rho' _).1 hf
      rw [LinearMap.mem_ker]
      refine LinearMap.ext fun m => ?_
      rw [LinearMap.flip_apply, LinearMap.compr₂_apply, Submodule.mkQ_apply, LinearMap.zero_apply,
        Submodule.Quotient.mk_eq_zero]
      refine (separated_dvr_second_cohomology_mem _ _).2 ⟨fun g => b m.1 (c g), hb.comp (continuous_const.prodMk hc), ?_⟩
      funext p
      obtain ⟨g, h⟩ := p
      have e := congrFun hcf (g, h)
      simp only [Submodule.coe_subtype] at e
      simp only [d1_apply, Submodule.coe_subtype, cupCocycleH0Z2_apply, ← e, ← hbe,
        (mem_riemannRochSpace_iff_regularAt_everywhere rho m.1).1 m.2 g, map_add, map_sub])).flip

def cupCocycleZ2H0 : Z2 rho →ₗ[R] H0 rho' →ₗ[R] Z2 rhoP :=
  LinearMap.mk₂ R
    (fun f m => ⟨fun p => b (f.1 p) m.1, hb.comp (f.2.1.prodMk continuous_const),
      fun g h k => by
        have e := congrArg (b.flip m.1) (f.2.2 g h k)
        simp only [map_sub, map_add, map_zero, LinearMap.flip_apply] at e
        rw [← (mem_riemannRochSpace_iff_regularAt_everywhere rho' m.1).1 m.2 g, hbe, (mem_riemannRochSpace_iff_regularAt_everywhere rho' m.1).1 m.2 g] at e
        exact e⟩)
    (fun f f' m => Subtype.ext (funext fun p => by simp))
    (fun r f m => Subtype.ext (funext fun p => by simp))
    (fun f m m' => Subtype.ext (funext fun p => by simp))
    (fun r f m => Subtype.ext (funext fun p => by simp))

@[simp] theorem cupCocycleZ2H0_apply (f : Z2 rho) (m : H0 rho') (p : G × G) :
    (cupCocycleZ2H0 rho rho' rhoP b hb hbe f m).1 p = b (f.1 p) m.1 := rfl

def cupProductH2H0 : H2 rho →ₗ[R] H0 rho' →ₗ[R] H2 rhoP :=
  Submodule.liftQ _ ((cupCocycleZ2H0 rho rho' rhoP b hb hbe).compr₂ (Submodule.mkQ _))
    (fun f hf => by
      obtain ⟨c, hc, hcf⟩ := (separated_dvr_second_cohomology_mem rho _).1 hf
      rw [LinearMap.mem_ker]
      refine LinearMap.ext fun m => ?_
      rw [LinearMap.compr₂_apply, Submodule.mkQ_apply, LinearMap.zero_apply,
        Submodule.Quotient.mk_eq_zero]
      refine (separated_dvr_second_cohomology_mem _ _).2 ⟨fun g => b (c g) m.1, hb.comp (hc.prodMk continuous_const), ?_⟩
      funext p
      obtain ⟨g, h⟩ := p
      have e := congrFun hcf (g, h)
      simp only [Submodule.coe_subtype] at e
      have hm := (mem_riemannRochSpace_iff_regularAt_everywhere rho' m.1).1 m.2 g
      simp only [d1_apply, Submodule.coe_subtype, cupCocycleZ2H0_apply, ← e, map_add, map_sub,
        LinearMap.add_apply, LinearMap.sub_apply]
      rw [← hbe, hm])

end Cup

section Local

variable {I : Type*} {D : I → Type*} [∀ i, Group (D i)] [∀ i, TopologicalSpace (D i)]
  (phi : ∀ i, D i →* G) (hphi : ∀ i, Continuous (phi i))

abbrev LocCond := ∀ i, Submodule R (H1 (rho.comp (phi i)))

def Sel (L : LocCond rho phi) : Submodule R (H1 rho) :=
  ⨅ i, (L i).comap (resH1 rho (phi i) (hphi i))

theorem mem_Sel (L : LocCond rho phi) (x : H1 rho) :
    x ∈ Sel rho phi hphi L ↔ ∀ i, resH1 rho (phi i) (hphi i) x ∈ L i := by
  simp only [Sel, Submodule.mem_iInf, Submodule.mem_comap]

def Sha1 : Submodule R (H1 rho) := ⨅ i, LinearMap.ker (resH1 rho (phi i) (hphi i))

def Sha2 : Submodule R (H2 rho) := ⨅ i, LinearMap.ker (resH2 rho (phi i) (hphi i))

end Local

section Inertia

variable {D : Type*} [Group D] [TopologicalSpace D] (rhoD : Representation R D M)
  (J : Subgroup D)

def H1ur : Submodule R (H1 rhoD) :=
  LinearMap.ker (resH1 rhoD J.subtype continuous_subtype_val)

variable (Mplus : Submodule R M) (hMplus : ∀ g, Mplus ≤ Mplus.comap (rhoD g))

theorem continuous_mkQ : Continuous (Mplus.mkQ) := by
  first
  | exact continuous_quot_mk
  | exact continuous_coinduced_rng

instance continuousConstSMul_quotient (N : Submodule R M) : ContinuousConstSMul R (M ⧸ N) :=
  ⟨fun c => by
    rw [(Submodule.isQuotientMap_mkQ N).continuous_iff]
    exact (Submodule.isQuotientMap_mkQ N).continuous.comp (continuous_const_smul c)⟩

def toQuotientH1 : H1 rhoD →ₗ[R] H1 (rhoD.quotient Mplus hMplus) :=
  mapH1 rhoD (rhoD.quotient Mplus hMplus) Mplus.mkQ (continuous_mkQ Mplus) (fun _ _ => rfl)

def greenbergSelmer : Submodule R (H1 rhoD) :=
  LinearMap.ker ((resH1 (rhoD.quotient Mplus hMplus) J.subtype continuous_subtype_val).comp
    (toQuotientH1 rhoD Mplus hMplus))

def strictGreenbergSelmer : Submodule R (H1 rhoD) := LinearMap.ker (toQuotientH1 rhoD Mplus hMplus)

end Inertia

end

end ReciprocityTheory.Gal
end


section
-- Source: Formalism/ConjugateSelfDual/Statement.lean
noncomputable section
open NumberField IsDedekindDomain Polynomial Filter
open scoped ModularForm MatrixGroups
namespace Formalism.ConjugateSelfDual
abbrev G (F Ω : Type*) [Field F] [Field Ω] [Algebra F Ω] := Ω ≃ₐ[F] Ω

abbrev Qbar (l : ℕ) [Fact l.Prime] := PadicAlgCl l

def cyc (F Ω : Type*) [Field F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact l.Prime] :
    G F Ω →* (Qbar l)ˣ :=
  (Units.map ((algebraMap ℚ_[l] (PadicAlgCl l)).comp PadicInt.Coe.ringHom).toMonoidHom).comp
    ((cyclotomicCharacter (Ω) l).comp
      (MulSemiringAction.toRingAut (G F Ω) (Ω)))

section places

variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

def IsPlaceOver (A : ValuationSubring (Ω)) (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  ∀ x : 𝓞 F, A.valuation (algebraMap F (Ω) (x : F)) < 1 ↔ x ∈ v.asIdeal

def normV (v : HeightOneSpectrum (𝓞 F)) : ℕ := Nat.card (𝓞 F ⧸ v.asIdeal)

def Inertia (A : ValuationSubring (Ω)) : Set (G F Ω) :=
  {σ | σ ∈ A.decompositionSubgroup F ∧ ∀ x, A.valuation x ≤ 1 → A.valuation (σ x - x) < 1}

def IsFrob (A : ValuationSubring (Ω)) (q : ℕ) (σ : G F Ω) : Prop :=
  σ ∈ A.decompositionSubgroup F ∧ ∀ x, A.valuation x ≤ 1 → A.valuation (σ x - x ^ q) < 1

end places
end Formalism.ConjugateSelfDual
end
end


section
-- Source: ReciprocityTheory/GaloisValuations/GlobalA.lean

noncomputable section

open NumberField IsDedekindDomain Pointwise

namespace ReciprocityTheory.Gal

section krull

variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] [Algebra.IsIntegral F Ω]

theorem isOpen_setOf_apply (x : Ω) (P : Ω → Prop) : IsOpen {τ : Ω ≃ₐ[F] Ω | P (τ x)} := by
  have hx : IsIntegral F x := Algebra.IsIntegral.isIntegral x
  haveI : FiniteDimensional F (IntermediateField.adjoin F {x}) :=
    IntermediateField.adjoin.finiteDimensional hx
  have hH : IsOpen ((IntermediateField.adjoin F {x}).fixingSubgroup : Set (Ω ≃ₐ[F] Ω)) :=
    IntermediateField.fixingSubgroup_isOpen _
  rw [isOpen_iff_forall_mem_open]
  intro τ hτ
  refine ⟨(fun σ => τ⁻¹ * σ) ⁻¹' ((IntermediateField.adjoin F {x}).fixingSubgroup : Set (Ω ≃ₐ[F] Ω)),
    ?_, ?_, ?_⟩
  · intro σ hσ
    have hσ' : τ⁻¹ * σ ∈ (IntermediateField.adjoin F {x}).fixingSubgroup := hσ
    rw [IntermediateField.mem_fixingSubgroup_iff] at hσ'
    have h1 := hσ' x (IntermediateField.mem_adjoin_simple_self F x)
    have h2 : σ x = τ x := by
      calc σ x = (τ * (τ⁻¹ * σ)) x := by rw [mul_inv_cancel_left]
        _ = τ ((τ⁻¹ * σ) x) := by rw [AlgEquiv.mul_apply]
        _ = τ x := by rw [h1]
    show P (σ x)
    rw [h2]
    exact hτ
  · exact hH.preimage (continuous_const.mul continuous_id)
  · show τ⁻¹ * τ ∈ (IntermediateField.adjoin F {x}).fixingSubgroup
    rw [inv_mul_cancel]
    exact one_mem _

theorem isClosed_setOf_apply (x : Ω) (P : Ω → Prop) : IsClosed {τ : Ω ≃ₐ[F] Ω | P (τ x)} := by
  rw [← isOpen_compl_iff]
  exact isOpen_setOf_apply x (fun y => ¬ P y)

end krull

section roots

variable {Ω : Type*} [Field Ω]

theorem eq_one_of_pow_eq_one (A : ValuationSubring Ω) {N : ℕ} (hN : ¬ A.valuation (N : Ω) < 1)
    {ξ : Ω} (hξ : ξ ^ N = 1) (h : A.valuation (ξ - 1) < 1) : ξ = 1 := by
  have hξ1 : A.valuation ξ ≤ 1 := by
    have h2 := Valuation.map_add A.valuation (ξ - 1) 1
    rw [sub_add_cancel, Valuation.map_one] at h2
    exact h2.trans (max_le h.le le_rfl)
  have hpow : ∀ j : ℕ, A.valuation (ξ ^ j) ≤ 1 := fun j => by
    rw [Valuation.map_pow]
    exact pow_le_one' hξ1 j
  have hgeom : ∀ i : ℕ, A.valuation (ξ ^ i - 1) < 1 := by
    intro i
    rw [← geom_sum_mul, Valuation.map_mul]
    refine lt_of_le_of_lt (mul_le_of_le_one_left' ?_) h
    exact Valuation.map_sum_le _ (fun j _ => hpow j)
  by_contra hne
  have h3 := geom_sum_mul ξ N
  rw [hξ, sub_self] at h3
  have hS := (mul_eq_zero.1 h3).resolve_right (fun h4 => hne (sub_eq_zero.1 h4))
  have h5 := Valuation.map_sum_lt A.valuation (s := Finset.range N) (f := fun i => ξ ^ i - 1)
    one_ne_zero (fun i _ => hgeom i)
  rw [Finset.sum_sub_distrib, hS] at h5
  apply hN
  simpa using h5

theorem valuation_eq_one_of_pow_eq_one (A : ValuationSubring Ω) {N : ℕ} (hN0 : N ≠ 0) {b : Ω}
    (hb : b ^ N = 1) : A.valuation b = 1 := by
  have h1 : A.valuation b ^ N = 1 := by rw [← Valuation.map_pow, hb, Valuation.map_one]
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := Nat.exists_eq_succ_of_ne_zero hN0
  rw [pow_succ] at h1
  rcases lt_trichotomy (A.valuation b) 1 with hlt | heq | hgt
  · exfalso
    have h2 : A.valuation b ^ M * A.valuation b ≤ A.valuation b :=
      mul_le_of_le_one_left' (pow_le_one' hlt.le M)
    rw [h1] at h2
    exact absurd hlt (not_lt.2 h2)
  · exact heq
  · exfalso
    have h2 : A.valuation b ≤ A.valuation b ^ M * A.valuation b :=
      le_mul_of_one_le_left' (one_le_pow_of_one_le' hgt.le M)
    rw [h1] at h2
    exact absurd hgt (not_lt.2 h2)

theorem eq_of_pow_eq_one (A : ValuationSubring Ω) {N : ℕ} (hN : ¬ A.valuation (N : Ω) < 1)
    {a b : Ω} (ha : a ^ N = 1) (hb : b ^ N = 1) (h : A.valuation (a - b) < 1) : a = b := by
  have hN0 : N ≠ 0 := by
    rintro rfl
    apply hN
    simp
  have hb0 : b ≠ 0 := by
    rintro rfl
    simp [hN0] at hb
  have hvb := valuation_eq_one_of_pow_eq_one A hN0 hb
  have hξ : (a / b) ^ N = 1 := by rw [div_pow, ha, hb, div_one]
  have hξ1 : A.valuation (a / b - 1) < 1 := by
    rw [div_sub_one hb0, Valuation.map_div, hvb, div_one]
    exact h
  have h2 := eq_one_of_pow_eq_one A hN hξ hξ1
  rwa [div_eq_one_iff_eq hb0] at h2

end roots

section exists_place

variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

theorem exists_valuationSubring_over (v : HeightOneSpectrum (𝓞 F)) :
    ∃ A : ValuationSubring Ω, ∀ x : 𝓞 F,
      A.valuation (algebraMap F Ω (x : F)) < 1 ↔ x ∈ v.asIdeal := by
  classical
  let φ : 𝓞 F →+* Ω := (algebraMap F Ω).comp (algebraMap (𝓞 F) F)
  have hφ : Function.Injective φ :=
    (algebraMap F Ω).injective.comp (IsFractionRing.injective (𝓞 F) F)
  have hu : ∀ y : v.asIdeal.primeCompl, IsUnit (φ y) := by
    intro y
    refine isUnit_iff_ne_zero.2 ?_
    intro h0
    apply y.2
    have h1 : (y : 𝓞 F) = 0 := hφ (h0.trans (map_zero φ).symm)
    rw [h1]
    exact v.asIdeal.zero_mem
  let f : (Localization.AtPrime v.asIdeal) →+* Ω := IsLocalization.lift (M := v.asIdeal.primeCompl) hu
  have hf : ∀ z : 𝓞 F, f (algebraMap (𝓞 F) (Localization.AtPrime v.asIdeal) z) = φ z := fun z => IsLocalization.lift_eq hu z
  have hfi : Function.Injective f := by
    rw [IsLocalization.lift_injective_iff]
    intro a b
    constructor
    · intro hab
      rw [IsLocalization.injective (M := v.asIdeal.primeCompl) (S := (Localization.AtPrime v.asIdeal))
        (Ideal.primeCompl_le_nonZeroDivisors _) hab]
    · intro hab
      rw [hφ hab]
  obtain ⟨B, hB⟩ := LocalSubring.exists_le_valuationSubring (LocalSubring.range f)
  rw [LocalSubring.le_def] at hB
  obtain ⟨hle, hloc⟩ := hB
  haveI := hloc
  refine ⟨B, fun x => ?_⟩
  have hmem : φ x ∈ B := hle ⟨algebraMap (𝓞 F) (Localization.AtPrime v.asIdeal) x, hf x⟩
  let bx : B := ⟨φ x, hmem⟩
  have hv : B.valuation (algebraMap F Ω (x : F)) = B.valuation (bx : Ω) := rfl
  rw [hv, ← ValuationSubring.valuation_lt_one_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · intro hnu
    by_contra hx
    apply hnu
    have h1 : IsUnit (algebraMap (𝓞 F) (Localization.AtPrime v.asIdeal) x) :=
      IsLocalization.map_units (Localization.AtPrime v.asIdeal) (⟨x, hx⟩ : v.asIdeal.primeCompl)
    have h3 := (h1.map f.rangeRestrict).map (Subring.inclusion hle)
    rw [show f.rangeRestrict (algebraMap (𝓞 F) (Localization.AtPrime v.asIdeal) x) =
      (⟨φ x, ⟨_, hf x⟩⟩ : f.range) from Subtype.ext (hf x)] at h3
    exact h3
  · intro hx hu'
    have h1 := isUnit_of_map_unit (Subring.inclusion hle) ⟨φ x, ⟨_, hf x⟩⟩ hu'
    obtain ⟨w, hw⟩ := h1.exists_right_inv
    obtain ⟨r, hr⟩ := w.2
    have h4 : f (algebraMap (𝓞 F) (Localization.AtPrime v.asIdeal) x * r) = f 1 := by
      rw [map_mul, hf, hr, map_one]
      exact congrArg Subtype.val hw
    have h5 : IsUnit (algebraMap (𝓞 F) (Localization.AtPrime v.asIdeal) x) := ⟨⟨_, r, hfi h4, (mul_comm _ _).trans (hfi h4)⟩, rfl⟩
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime v.asIdeal) v.asIdeal x).1 h5 hx

end exists_place

end ReciprocityTheory.Gal
end
end


section
-- Source: ReciprocityTheory/GaloisValuations/GlobalB.lean

set_option linter.style.haveILetI false

noncomputable section

open NumberField IsDedekindDomain Pointwise
open scoped nonZeroDivisors

namespace ReciprocityTheory.Gal

section den

variable {Ω : Type*} [Field Ω]

theorem isIntegral_int_of_isIntegral {F : Type*} [Field F] [NumberField F] [Algebra F Ω] {b : Ω} (hb : IsIntegral (𝓞 F) b) : IsIntegral ℤ b :=
  isIntegral_trans b hb

theorem mem_of_isIntegral_int (A : ValuationSubring Ω) {b : Ω} (hb : IsIntegral ℤ b) : b ∈ A := by
  have h1 : IsIntegral A b := hb.tower_top
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := Ω)).mp h1
  rw [← hy]
  exact y.2

theorem exists_den (F : Type*) [Field F] [NumberField F] [Algebra F Ω] [IsAlgClosure F Ω]
    (A : ValuationSubring Ω) {x : Ω} (hx : A.valuation x ≤ 1) :
    ∃ s t : Ω, IsIntegral ℤ s ∧ IsIntegral ℤ t ∧ A.valuation s = 1 ∧ s * x = t := by
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have hxF : IsIntegral F x := Algebra.IsIntegral.isIntegral x
  have hxQ : IsIntegral ℚ x := isIntegral_trans x hxF
  let E := IntermediateField.adjoin ℚ ({x} : Set Ω)
  have : FiniteDimensional ℚ E := IntermediateField.adjoin.finiteDimensional hxQ
  have : NumberField E := ⟨⟩
  let x' : E := ⟨x, IntermediateField.mem_adjoin_simple_self ℚ x⟩
  let M : FractionalIdeal (𝓞 E)⁰ E := 1 + FractionalIdeal.spanSingleton _ x'
  have h1M : (1 : E) ∈ M := by
    have hle1 : (1 : FractionalIdeal (𝓞 E)⁰ E) ≤ M := by
      simp only [M, ← FractionalIdeal.sup_eq_add]; exact le_sup_left
    exact hle1 (FractionalIdeal.one_mem_one _)
  have hxM : x' ∈ M := by
    have hle1 : FractionalIdeal.spanSingleton (𝓞 E)⁰ x' ≤ M := by
      simp only [M, ← FractionalIdeal.sup_eq_add]; exact le_sup_right
    exact hle1 (FractionalIdeal.mem_spanSingleton_self _ _)
  have hM : M ≠ 0 := by
    intro h
    rw [h] at h1M
    exact one_ne_zero ((FractionalIdeal.mem_zero_iff _).mp h1M)
  have hMM : M * M⁻¹ = 1 := mul_inv_cancel₀ hM
  obtain ⟨α, hα, β, hβ, e⟩ : ∃ α ∈ M⁻¹, ∃ β ∈ M⁻¹, α + x' * β = 1 := by
    have h1 : (1 : E) ∈ M * M⁻¹ := by rw [hMM]; exact FractionalIdeal.one_mem_one _
    have e2 : M * M⁻¹ = M⁻¹ ⊔ FractionalIdeal.spanSingleton _ x' * M⁻¹ := by
      simp only [M, add_mul, one_mul, FractionalIdeal.sup_eq_add]
    rw [e2, ← FractionalIdeal.mem_coe, FractionalIdeal.coe_sup, Submodule.mem_sup] at h1
    obtain ⟨α, hα, z, hz, e⟩ := h1
    obtain ⟨β, hβ, rfl⟩ := FractionalIdeal.mem_singleton_mul.mp hz
    exact ⟨α, hα, β, hβ, e⟩
  have hint : ∀ γ ∈ M⁻¹, IsIntegral ℤ (γ : Ω) ∧ IsIntegral ℤ ((γ * x' : E) : Ω) := by
    intro γ hγ
    rw [FractionalIdeal.mem_inv_iff hM] at hγ
    have key : ∀ z : E, z ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) → IsIntegral ℤ (z : Ω) := by
      intro z hz
      obtain ⟨z', rfl⟩ := (FractionalIdeal.mem_one_iff _).mp hz
      have : IsIntegral ℤ (algebraMap (𝓞 E) E z') := z'.2
      exact this.map (IsScalarTower.toAlgHom ℤ E Ω)
    exact ⟨by simpa using key _ (hγ 1 h1M), key _ (hγ x' hxM)⟩
  have hle : ∀ γ ∈ M⁻¹, A.valuation (γ : Ω) ≤ 1 := fun γ hγ =>
    (A.valuation_le_one_iff _).mpr (mem_of_isIntegral_int A (hint γ hγ).1)
  by_cases ha : A.valuation (α : Ω) = 1
  · exact ⟨α, _, (hint α hα).1, (hint α hα).2, ha, by simp [x']⟩
  by_cases hb : A.valuation (β : Ω) = 1
  · exact ⟨β, _, (hint β hβ).1, (hint β hβ).2, hb, by simp [x', mul_comm]⟩
  exfalso
  have ha' : A.valuation (α : Ω) < 1 := lt_of_le_of_ne (hle α hα) ha
  have hb' : A.valuation (β : Ω) < 1 := lt_of_le_of_ne (hle β hβ) hb
  have e' : (α : Ω) + x * (β : Ω) = 1 := by
    have := congrArg (fun z : E => (z : Ω)) e
    simpa [x'] using this
  have : A.valuation ((α : Ω) + x * (β : Ω)) < 1 := by
    refine Valuation.map_add_lt _ ha' ?_
    rw [Valuation.map_mul]
    calc A.valuation x * A.valuation (β : Ω) ≤ 1 * A.valuation (β : Ω) := mul_le_mul_left hx _
      _ < 1 := by rw [one_mul]; exact hb'
  rw [e', Valuation.map_one] at this
  exact lt_irrefl _ this

theorem le_of_valuation_lt_one_iff (F : Type*) [Field F] [NumberField F] [Algebra F Ω]
    [IsAlgClosure F Ω] {A A' : ValuationSubring Ω}
    (h : ∀ b : Ω, IsIntegral ℤ b → (A.valuation b < 1 ↔ A'.valuation b < 1)) : A ≤ A' := by
  intro x hx
  have hx' : A.valuation x ≤ 1 := (A.valuation_le_one_iff x).mpr hx
  obtain ⟨s, t, hs, ht, hs1, e⟩ := exists_den F A hx'
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs1
  have hs1' : A'.valuation s = 1 := by
    refine le_antisymm ((A'.valuation_le_one_iff s).mpr (mem_of_isIntegral_int A' hs)) ?_
    rw [← not_lt, ← h s hs, hs1]
    exact lt_irrefl 1
  have hxt : x = t * s⁻¹ := by rw [← e]; field_simp
  rw [← A'.valuation_le_one_iff, hxt, Valuation.map_mul, map_inv₀, hs1', inv_one, mul_one,
    A'.valuation_le_one_iff]
  exact mem_of_isIntegral_int A' ht

theorem eq_of_valuation_lt_one_iff (F : Type*) [Field F] [NumberField F] [Algebra F Ω]
    [IsAlgClosure F Ω] {A A' : ValuationSubring Ω}
    (h : ∀ b : Ω, IsIntegral ℤ b → (A.valuation b < 1 ↔ A'.valuation b < 1)) : A = A' :=
  le_antisymm (le_of_valuation_lt_one_iff F h)
    (le_of_valuation_lt_one_iff F fun b hb => (h b hb).symm)

end den

section places

variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]

theorem smul_valuation_lt_one_iff (g : Ω ≃ₐ[F] Ω) (A : ValuationSubring Ω) (y : Ω) :
    (g • A).valuation y < 1 ↔ A.valuation ((g⁻¹ : Ω ≃ₐ[F] Ω) y) < 1 := by
  rw [← ValuationSubring.mem_nonunits_iff, ← ValuationSubring.mem_nonunits_iff,
    ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, map_inv₀,
    map_eq_zero_iff _ (g⁻¹ : Ω ≃ₐ[F] Ω).injective]

omit [NumberField F] [IsAlgClosure F Ω] in
theorem smul_le_one_of_isIntegral (g : Ω ≃ₐ[F] Ω) {A : ValuationSubring Ω}
    (hA : ∀ b : Ω, IsIntegral ℤ b → b ∈ A) {b : Ω} (hb : IsIntegral ℤ b) : b ∈ g • A := by
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]
  exact hA _ (hb.map ((g⁻¹ : Ω ≃ₐ[F] Ω).toAlgHom.restrictScalars ℤ))

variable (F Ω) in

abbrev IntCl := integralClosure (𝓞 F) Ω

theorem valuation_le_one_intCl (A : ValuationSubring Ω) (b : IntCl F Ω) :
    A.valuation (b : Ω) ≤ 1 :=
  (A.valuation_le_one_iff _).mpr (mem_of_isIntegral_int A (isIntegral_int_of_isIntegral b.2))

def primeBelow (A : ValuationSubring Ω) : Ideal (IntCl F Ω) where
  carrier := {b | A.valuation (b : Ω) < 1}
  add_mem' {a b} ha hb := by
    show A.valuation ((a : Ω) + b) < 1
    exact Valuation.map_add_lt _ ha hb
  zero_mem' := by show A.valuation ((0 : IntCl F Ω) : Ω) < 1; simp
  smul_mem' c b hb := by
    show A.valuation ((c : Ω) * b) < 1
    rw [Valuation.map_mul]
    calc A.valuation (c : Ω) * A.valuation (b : Ω) ≤ 1 * A.valuation (b : Ω) :=
          mul_le_mul_left (valuation_le_one_intCl A c) _
      _ < 1 := by rw [one_mul]; exact hb

theorem mem_primeBelow {A : ValuationSubring Ω} {b : IntCl F Ω} :
    b ∈ primeBelow A ↔ A.valuation (b : Ω) < 1 := Iff.rfl

instance isPrime_primeBelow (A : ValuationSubring Ω) : (primeBelow (F := F) A).IsPrime where
  ne_top' h := by
    have : (1 : IntCl F Ω) ∈ primeBelow A := h ▸ Submodule.mem_top
    rw [mem_primeBelow] at this
    simp at this
  mem_or_mem' {a b} hab := by
    rw [mem_primeBelow, mem_primeBelow]
    rw [mem_primeBelow] at hab
    by_contra hn
    simp only [not_or, not_lt] at hn
    have ha : A.valuation (a : Ω) = 1 := le_antisymm (valuation_le_one_intCl A a) hn.1
    have hb : A.valuation (b : Ω) = 1 := le_antisymm (valuation_le_one_intCl A b) hn.2
    have : A.valuation ((a * b : IntCl F Ω) : Ω) = 1 := by
      rw [MulMemClass.coe_mul, Valuation.map_mul, ha, hb, one_mul]
    rw [this] at hab
    exact lt_irrefl _ hab

theorem under_primeBelow {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)}
    (hA : ∀ x : 𝓞 F, A.valuation (algebraMap F Ω (x : F)) < 1 ↔ x ∈ v.asIdeal) :
    (primeBelow (F := F) A).under (𝓞 F) = v.asIdeal := by
  ext x
  rw [Ideal.under, Ideal.mem_comap, mem_primeBelow, ← hA x]
  rfl

theorem primeBelow_smul (g : Ω ≃ₐ[F] Ω) (A : ValuationSubring Ω) :
    primeBelow (F := F) (g • A) = g • primeBelow (F := F) A := by
  ext b
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, mem_primeBelow, mem_primeBelow,
    smul_valuation_lt_one_iff]
  rfl

end places

section profinite

variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]

variable (F Ω) in

theorem continuousSMul_intCl :
    @ContinuousSMul (Ω ≃ₐ[F] Ω) (IntCl F Ω) _ _ ⊥ := by
  letI : TopologicalSpace (IntCl F Ω) := ⊥
  haveI : DiscreteTopology (IntCl F Ω) := ⟨rfl⟩
  refine ⟨continuous_discrete_rng.mpr fun c => ?_⟩
  rw [isOpen_iff_forall_mem_open]
  rintro ⟨g₀, b₀⟩ h
  refine ⟨{g : Ω ≃ₐ[F] Ω | g (b₀ : Ω) = g₀ (b₀ : Ω)} ×ˢ {b₀}, ?_,
    (isOpen_setOf_apply (F := F) (b₀ : Ω) (· = g₀ (b₀ : Ω))).prod (isOpen_discrete _), ⟨rfl, rfl⟩⟩
  rintro ⟨g, b⟩ ⟨hg, hb⟩
  simp only [Set.mem_singleton_iff] at hb
  subst hb
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at h ⊢
  rw [← h]
  exact Subtype.ext hg

variable (F Ω) in

theorem isInvariant_intCl : Algebra.IsInvariant (𝓞 F) (IntCl F Ω) (Ω ≃ₐ[F] Ω) := by
  refine ⟨fun b hb => ?_⟩
  have hfix : ∀ σ : Ω ≃ₐ[F] Ω, σ (b : Ω) = b := fun σ => congrArg Subtype.val (hb σ)
  have hbot := (InfiniteGalois.mem_bot_iff_fixed (b : Ω)).mpr hfix
  obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp hbot
  have hcint : IsIntegral (𝓞 F) c := by
    have : IsIntegral (𝓞 F) (algebraMap F Ω c) := hc ▸ b.2
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom (𝓞 F) F Ω)
      (algebraMap F Ω).injective).mp this
  obtain ⟨a, ha⟩ := (IsIntegrallyClosed.isIntegral_iff (R := 𝓞 F) (K := F)).mp hcint
  refine ⟨a, Subtype.ext ?_⟩
  rw [← hc, ← ha]
  rfl

theorem exists_smul_eq_of_over {A A' : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)}
    (hA : ∀ x : 𝓞 F, A.valuation (algebraMap F Ω (x : F)) < 1 ↔ x ∈ v.asIdeal)
    (hA' : ∀ x : 𝓞 F, A'.valuation (algebraMap F Ω (x : F)) < 1 ↔ x ∈ v.asIdeal) :
    ∃ g : Ω ≃ₐ[F] Ω, g • A = A' := by
  letI : TopologicalSpace (IntCl F Ω) := ⊥
  haveI : DiscreteTopology (IntCl F Ω) := ⟨rfl⟩
  haveI := continuousSMul_intCl F Ω
  haveI := isInvariant_intCl F Ω
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite (A := 𝓞 F)
    (G := Ω ≃ₐ[F] Ω) (primeBelow (F := F) A) (primeBelow (F := F) A')
    (by rw [under_primeBelow hA, under_primeBelow hA'])
  refine ⟨g, eq_of_valuation_lt_one_iff F fun b hb => ?_⟩
  let b' : IntCl F Ω := ⟨b, hb.tower_top⟩
  change b' ∈ primeBelow (F := F) (g • A) ↔ b' ∈ primeBelow (F := F) A'
  rw [primeBelow_smul, hg]

theorem exists_frob_over {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)}
    (hA : ∀ x : 𝓞 F, A.valuation (algebraMap F Ω (x : F)) < 1 ↔ x ∈ v.asIdeal) :
    ∃ σ : Ω ≃ₐ[F] Ω, σ • A = A ∧ ∀ x, A.valuation x ≤ 1 →
      A.valuation (σ x - x ^ Nat.card (𝓞 F ⧸ v.asIdeal)) < 1 := by
  letI : TopologicalSpace (IntCl F Ω) := ⊥
  haveI : DiscreteTopology (IntCl F Ω) := ⟨rfl⟩
  haveI := continuousSMul_intCl F Ω
  haveI := isInvariant_intCl F Ω
  set Q := primeBelow (F := F) A with hQ
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  haveI : Q.LiesOver v.asIdeal := ⟨(under_primeBelow hA).symm⟩
  haveI : Q.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := 𝓞 F) Q
    (by rw [show Ideal.comap (algebraMap (𝓞 F) (IntCl F Ω)) Q = v.asIdeal from
      under_primeBelow hA]; exact v.isMaximal)
  letI : Field (IntCl F Ω ⧸ Q) := Ideal.Quotient.field Q
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  letI : Fintype (𝓞 F ⧸ v.asIdeal) := Fintype.ofFinite _
  haveI hBi : Algebra.IsIntegral (𝓞 F) (IntCl F Ω) := inferInstance
  haveI : Algebra.IsIntegral (𝓞 F ⧸ v.asIdeal) (IntCl F Ω ⧸ Q) :=
    Ideal.Quotient.algebra_isIntegral_of_liesOver Q v.asIdeal
  haveI : Algebra.IsAlgebraic (𝓞 F ⧸ v.asIdeal) (IntCl F Ω ⧸ Q) := Algebra.IsIntegral.isAlgebraic
  let φ : (IntCl F Ω ⧸ Q) ≃ₐ[𝓞 F ⧸ v.asIdeal] (IntCl F Ω ⧸ Q) :=
    FiniteField.frobeniusAlgEquivOfAlgebraic (𝓞 F ⧸ v.asIdeal) (IntCl F Ω ⧸ Q)
  obtain ⟨⟨σ, hσQ⟩, hσ⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite
    (G := Ω ≃ₐ[F] Ω) v.asIdeal Q φ
  have hσQ' : σ • Q = Q := hσQ
  set q := Nat.card (𝓞 F ⧸ v.asIdeal) with hq
  have hqc : Fintype.card (𝓞 F ⧸ v.asIdeal) = q := Fintype.card_eq_nat_card
  have hcong : ∀ b : IntCl F Ω, A.valuation (σ (b : Ω) - (b : Ω) ^ q) < 1 := by
    intro b
    have h1 : Ideal.Quotient.mk Q (σ • b) =
        Ideal.Quotient.mk Q b ^ Fintype.card (𝓞 F ⧸ v.asIdeal) :=
      DFunLike.congr_fun hσ (Ideal.Quotient.mk Q b)
    have h2 : σ • b - b ^ q ∈ Q := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, h1, hqc, sub_self]
    exact h2
  have hdec : σ • A = A := by
    refine eq_of_valuation_lt_one_iff F fun b hb => ?_
    let b' : IntCl F Ω := ⟨b, hb.tower_top⟩
    change b' ∈ primeBelow (F := F) (σ • A) ↔ b' ∈ Q
    rw [primeBelow_smul, hσQ']
  refine ⟨σ, hdec, fun x hx => ?_⟩
  obtain ⟨s, t, hs, ht, hs1, e⟩ := exists_den F A hx
  have hcs := hcong ⟨s, hs.tower_top⟩
  have hct := hcong ⟨t, ht.tower_top⟩
  have hvt : A.valuation t ≤ 1 := (A.valuation_le_one_iff _).mpr (mem_of_isIntegral_int A ht)
  have hσs : A.valuation (σ s) = 1 := by
    refine le_antisymm ((A.valuation_le_one_iff _).mpr (mem_of_isIntegral_int A
      (hs.map ((σ : Ω ≃ₐ[F] Ω).toAlgHom.restrictScalars ℤ)))) ?_
    have h3 : ¬ (σ • A).valuation (σ s) < 1 := by
      rw [smul_valuation_lt_one_iff]
      have : (σ⁻¹ : Ω ≃ₐ[F] Ω) (σ s) = s := by
        show (σ⁻¹ * σ) s = s
        simp
      rw [this, hs1]
      exact lt_irrefl 1
    rw [hdec] at h3
    exact not_lt.mp h3
  have he' : σ s * σ x = σ t := by rw [← map_mul, e]
  have key : s ^ q * σ s * (σ x - x ^ q) = s ^ q * (σ t - t ^ q) + t ^ q * (s ^ q - σ s) := by
    rw [← he', ← e]; ring
  have hv : A.valuation (s ^ q * σ s * (σ x - x ^ q)) < 1 := by
    rw [key]
    apply Valuation.map_add_lt
    · rw [Valuation.map_mul, Valuation.map_pow, hs1, one_pow, one_mul]
      exact hct
    · rw [Valuation.map_mul, Valuation.map_sub_swap]
      calc A.valuation (t ^ q) * A.valuation (σ s - s ^ q) ≤ 1 * A.valuation (σ s - s ^ q) :=
            mul_le_mul_left (by rw [Valuation.map_pow]; exact pow_le_one' hvt q) _
        _ < 1 := by rw [one_mul]; exact hcs
  rw [Valuation.map_mul, Valuation.map_mul, Valuation.map_pow, hs1, hσs, one_pow, one_mul,
    one_mul] at hv
  exact hv

end profinite

end ReciprocityTheory.Gal
end
end


section
-- Source: ReciprocityTheory/GaloisValuations/Global.lean

noncomputable section

open NumberField IsDedekindDomain Pointwise

namespace ReciprocityTheory.Gal

open Formalism.ConjugateSelfDual

variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

def Dec (A : ValuationSubring (Ω)) : Subgroup (G F Ω) := A.decompositionSubgroup F

theorem mem_Dec {A : ValuationSubring (Ω)} {σ : G F Ω} :
    σ ∈ Dec (F := F) A ↔ σ • A = A := Iff.rfl

theorem apply_mem_iff_of_mem_Dec {A : ValuationSubring (Ω)} {σ : G F Ω}
    (hσ : σ ∈ Dec (F := F) A) (x : Ω) : σ x ∈ A ↔ x ∈ A := by
  have h := mem_Dec.mp hσ
  have key : σ • x ∈ σ • A ↔ x ∈ A := ValuationSubring.smul_mem_pointwise_smul_iff
  rw [h] at key
  exact key

theorem valuation_lt_one_iff' (A : ValuationSubring (Ω)) (y : Ω) :
    A.valuation y < 1 ↔ y ∈ A ∧ (y = 0 ∨ y⁻¹ ∉ A) := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  · rw [← A.valuation_le_one_iff, ← A.valuation_le_one_iff, not_le,
      Valuation.one_lt_val_iff _ (inv_ne_zero hy), inv_inv]
    simp only [hy, false_or]
    exact ⟨fun h => ⟨h.le, h⟩, fun h => h.2⟩

theorem valuation_apply_lt_one_iff {A : ValuationSubring (Ω)} {σ : G F Ω}
    (hσ : σ ∈ Dec (F := F) A) (y : Ω) :
    A.valuation (σ y) < 1 ↔ A.valuation y < 1 := by
  rw [valuation_lt_one_iff', valuation_lt_one_iff', (map_inv₀ σ y).symm, apply_mem_iff_of_mem_Dec hσ,
    apply_mem_iff_of_mem_Dec hσ, EmbeddingLike.map_eq_zero_iff]

theorem mul_inv_apply {σ : G F Ω} (x : Ω) : σ ((σ⁻¹ : G F Ω) x) = x := by
  rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]

def Ine (A : ValuationSubring (Ω)) : Subgroup (G F Ω) where
  carrier := Inertia (F := F) A
  one_mem' := ⟨(Dec (F := F) A).one_mem, fun x _ => by simp⟩
  mul_mem' := by
    rintro σ τ ⟨hσ, hσ'⟩ ⟨hτ, hτ'⟩
    refine ⟨(Dec (F := F) A).mul_mem hσ hτ, fun x hx => ?_⟩
    have e : (σ * τ) x - x = σ (τ x - x) + (σ x - x) := by
      simp [AlgEquiv.mul_apply, map_sub]
    rw [e]
    exact Valuation.map_add_lt _ ((valuation_apply_lt_one_iff hσ _).mpr (hτ' x hx)) (hσ' x hx)
  inv_mem' := by
    rintro σ ⟨hσ, hσ'⟩
    refine ⟨(Dec (F := F) A).inv_mem hσ, fun x hx => ?_⟩
    have hy : A.valuation ((σ⁻¹ : G F Ω) x) ≤ 1 := by
      rw [A.valuation_le_one_iff, ← apply_mem_iff_of_mem_Dec hσ, mul_inv_apply]
      exact (A.valuation_le_one_iff x).mp hx
    have e : (σ⁻¹ : G F Ω) x - x = -(σ ((σ⁻¹ : G F Ω) x) - (σ⁻¹ : G F Ω) x) := by
      rw [mul_inv_apply]; ring
    rw [e, Valuation.map_neg]
    exact hσ' _ hy

theorem mem_Ine {A : ValuationSubring (Ω)} {σ : G F Ω} :
    σ ∈ Ine (F := F) A ↔ σ ∈ Inertia (F := F) A := Iff.rfl

theorem Ine_le_Dec (A : ValuationSubring (Ω)) : Ine (F := F) A ≤ Dec (F := F) A := fun _ h => (mem_Ine.mp h).1

theorem conj_mem_Ine {A : ValuationSubring (Ω)} {g σ : G F Ω} (hg : g ∈ Dec (F := F) A)
    (hσ : σ ∈ Ine (F := F) A) : g * σ * g⁻¹ ∈ Ine (F := F) A := by
  refine ⟨(Dec (F := F) A).mul_mem ((Dec (F := F) A).mul_mem hg hσ.1) ((Dec (F := F) A).inv_mem hg), fun x hx => ?_⟩
  have hy : A.valuation ((g⁻¹ : G F Ω) x) ≤ 1 := by
    rw [A.valuation_le_one_iff, ← apply_mem_iff_of_mem_Dec hg, mul_inv_apply]
    exact (A.valuation_le_one_iff x).mp hx
  have e : (g * σ * g⁻¹) x - x = g (σ ((g⁻¹ : G F Ω) x) - (g⁻¹ : G F Ω) x) := by
    rw [map_sub, mul_inv_apply]; rfl
  rw [e, valuation_apply_lt_one_iff hg]
  exact hσ.2 _ hy

instance normal_Ine_subgroupOf (A : ValuationSubring (Ω)) :
    ((Ine (F := F) A).subgroupOf (Dec (F := F) A)).Normal where
  conj_mem n hn g := by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using conj_mem_Ine g.2 hn

variable (F Ω) in

def cycZ (l : ℕ) [Fact l.Prime] : G F Ω →* ℤ_[l]ˣ :=
  (cyclotomicCharacter (Ω) l).comp
    (MulSemiringAction.toRingAut (G F Ω) (Ω))

variable (F Ω) in
theorem cyc_eq_map_cycZ (l : ℕ) [Fact l.Prime] (σ : G F Ω) :
    cyc F Ω l σ = Units.map ((algebraMap ℚ_[l] (PadicAlgCl l)).comp PadicInt.Coe.ringHom).toMonoidHom
      (cycZ F Ω l σ) := rfl

variable (F Ω) in

theorem continuous_cycZ (l : ℕ) [Fact l.Prime] : Continuous (cycZ F Ω l) :=
  cyclotomicCharacter.continuous l F Ω

variable (F Ω) in

def cycMod (l : ℕ) [Fact l.Prime] (r : ℕ) : G F Ω →* (ZMod (l ^ r))ˣ :=
  (Units.map (PadicInt.toZModPow r : ℤ_[l] →+* ZMod (l ^ r)).toMonoidHom).comp (cycZ F Ω l)

def IsCC (c : G F Ω) : Prop :=
  ∃ j : Ω →+* ℂ, ∀ x, j (c x) = starRingEnd ℂ (j x)

variable (Ω) in

def placeOf (v : HeightOneSpectrum (𝓞 F)) : ValuationSubring (Ω) :=
  @Classical.epsilon _ ⟨⊤⟩ (fun A => IsPlaceOver A v)

variable (Ω) in

def frobOf (v : HeightOneSpectrum (𝓞 F)) : G F Ω :=
  @Classical.epsilon _ ⟨1⟩ (fun σ : G F Ω => IsFrob (placeOf Ω v) (normV v) σ)

section unram

variable (S : Set (HeightOneSpectrum (𝓞 F)))

variable (Ω) in

def NS : Subgroup (G F Ω) :=
  (Subgroup.normalClosure
    (⋃ v ∈ Sᶜ, ⋃ A ∈ {A : ValuationSubring (Ω) | IsPlaceOver A v}, Inertia (F := F) A)
    ).topologicalClosure

instance normal_NS : (NS Ω S).Normal := by
  unfold NS; exact Subgroup.is_normal_topologicalClosure _

variable (Ω) in
theorem isClosed_NS : IsClosed (NS Ω S : Set (G F Ω)) := Subgroup.isClosed_topologicalClosure _

variable (Ω) in

abbrev GS := G F Ω ⧸ NS Ω S

variable (Ω) in

def toGS : G F Ω →* GS Ω S := QuotientGroup.mk' (NS Ω S)

variable (Ω) in
theorem continuous_toGS : Continuous (toGS Ω S) := by
  unfold toGS
  exact continuous_quot_mk

def locHom (A : ValuationSubring (Ω)) : Dec (F := F) A →* GS Ω S :=
  (toGS Ω S).comp (Dec (F := F) A).subtype

theorem continuous_locHom (A : ValuationSubring (Ω)) :
    Continuous (locHom S A) := (continuous_toGS Ω S).comp continuous_subtype_val

def UnramOutside {H : Type*} [Group H] (ρ : G F Ω →* H) : Prop := ∀ σ ∈ NS Ω S, ρ σ = 1

theorem unramOutside_iff {H : Type*} [Group H] [TopologicalSpace H] [T2Space H]
    (ρ : G F Ω →* H) (hρ : Continuous ρ) :
    UnramOutside S ρ ↔ ∀ v ∉ S, ∀ A, IsPlaceOver A v → ∀ σ ∈ Inertia (F := F) A, ρ σ = 1 := by
  constructor
  · intro h v hv A hA σ hσ
    apply h
    apply Subgroup.le_topologicalClosure
    apply Subgroup.subset_normalClosure
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_compl_iff, exists_prop]
    exact ⟨v, hv, A, hA, hσ⟩
  · intro h σ hσ
    have hker : NS Ω S ≤ ρ.ker := by
      apply Subgroup.topologicalClosure_minimal
      · apply Subgroup.normalClosure_le_normal
        intro τ hτ
        simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_compl_iff, exists_prop] at hτ
        obtain ⟨v, hv, A, hA, hτ⟩ := hτ
        exact MonoidHom.mem_ker.mpr (h v hv A hA τ hτ)
      · rw [MonoidHom.coe_ker]
        exact isClosed_singleton.preimage hρ
    exact MonoidHom.mem_ker.mp (hker hσ)

end unram

section Basic₃

theorem valuation_natCast_le_one (A : ValuationSubring (Ω)) (n : ℕ) :
    A.valuation (n : Ω) ≤ 1 := (A.valuation_le_one_iff _).mpr (natCast_mem A n)

theorem not_valuation_lt_one_of_isPlaceOver {l : ℕ} {A : ValuationSubring (Ω)}
    {v : HeightOneSpectrum (𝓞 F)} (hl : ((l : ℕ) : 𝓞 F) ∉ v.asIdeal) (h : IsPlaceOver A v)
    (n : ℕ) : ¬ A.valuation (((l ^ n : ℕ) : Ω)) < 1 := by
  unfold Formalism.ConjugateSelfDual.IsPlaceOver at h
  intro hlt
  have hc : algebraMap F Ω (((l ^ n : ℕ) : 𝓞 F) : F) = ((l ^ n : ℕ) : Ω) := by
    simp
  rw [← hc, h] at hlt
  exact hl (v.isPrime.mem_of_pow_mem n (by simpa using hlt))

theorem cycZ_toZModPow_eq [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring (Ω)}
    {v : HeightOneSpectrum (𝓞 F)} (hl : ((l : ℕ) : 𝓞 F) ∉ v.asIdeal) (h : IsPlaceOver A v)
    {σ : G F Ω} {q : ℕ}
    (hσ : ∀ x : Ω, A.valuation x ≤ 1 → A.valuation (σ x - x ^ q) < 1) (n : ℕ) :
    PadicInt.toZModPow n ((cycZ F Ω l σ : ℤ_[l]ˣ) : ℤ_[l]) = PadicInt.toZModPow n (q : ℤ_[l]) := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ n)
  have hN0 : l ^ n ≠ 0 := pow_ne_zero _ (Fact.out : l.Prime).ne_zero
  have hspec := cyclotomicCharacter.spec (L := Ω) l
    (MulSemiringAction.toRingAut (G F Ω) (Ω) σ) ζ hζ.pow_eq_one
  set m := (((cyclotomicCharacter (Ω) l)
    (MulSemiringAction.toRingAut (G F Ω) (Ω) σ)) : ℤ_[l]).toZModPow n |>.val with hm
  have hσζ : σ ζ = ζ ^ m := hspec
  have hζA : A.valuation ζ ≤ 1 := (valuation_eq_one_of_pow_eq_one A hN0 hζ.pow_eq_one).le
  have hlt := hσ ζ hζA
  rw [hσζ] at hlt
  have heq : ζ ^ m = ζ ^ q := by
    refine eq_of_pow_eq_one A (not_valuation_lt_one_of_isPlaceOver hl h n) ?_ ?_ hlt
    · rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    · rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have heq' : (hζ.isUnit hN0).unit ^ m = (hζ.isUnit hN0).unit ^ q := Units.ext (by simpa using heq)
  have hu : IsPrimitiveRoot (hζ.isUnit hN0).unit (l ^ n) := IsPrimitiveRoot.coe_units_iff.mp (by simpa using hζ)
  rw [pow_eq_pow_iff_modEq, ← hu.eq_orderOf] at heq'
  rw [map_natCast]
  show ((cyclotomicCharacter (Ω) l)
    (MulSemiringAction.toRingAut (G F Ω) (Ω) σ) : ℤ_[l]).toZModPow n = _
  rw [← ZMod.natCast_zmod_val (((cyclotomicCharacter (Ω) l)
    (MulSemiringAction.toRingAut (G F Ω) (Ω) σ) : ℤ_[l]).toZModPow n), ← hm]
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr heq'

theorem eq_of_isPlaceOver {A : ValuationSubring (Ω)} {v v' : HeightOneSpectrum (𝓞 F)}
    (h : IsPlaceOver A v) (h' : IsPlaceOver A v') : v = v' := by
  unfold Formalism.ConjugateSelfDual.IsPlaceOver at h h'
  have e : v.asIdeal = v'.asIdeal := by
    ext x
    rw [← h x, ← h' x]
  exact IsDedekindDomain.HeightOneSpectrum.ext e

theorem inv_mul_mem_Ine_of_isFrob {A : ValuationSubring (Ω)} {q : ℕ} {σ τ : G F Ω}
    (hσ : IsFrob A q σ) (hτ : IsFrob A q τ) : σ⁻¹ * τ ∈ Ine (F := F) A := by
  obtain ⟨hσD, hσF⟩ := hσ
  obtain ⟨hτD, hτF⟩ := hτ
  have hσD' : σ ∈ Dec (F := F) A := mem_Dec.mpr hσD
  have hτD' : τ ∈ Dec (F := F) A := mem_Dec.mpr hτD
  refine mem_Ine.mpr ⟨(Dec (F := F) A).mul_mem ((Dec (F := F) A).inv_mem hσD') hτD', fun x hx => ?_⟩
  rw [← valuation_apply_lt_one_iff hσD']
  have e : σ ((σ⁻¹ * τ) x - x) = (τ x - x ^ q) - (σ x - x ^ q) := by
    rw [map_sub, AlgEquiv.mul_apply, mul_inv_apply]; ring
  rw [e]
  exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt (hτF x hx) (hσF x hx))

theorem isFrob_mul_of_mem_Ine {A : ValuationSubring (Ω)} {q : ℕ} {σ ι : G F Ω}
    (hσ : IsFrob A q σ) (hι : ι ∈ Ine (F := F) A) : IsFrob A q (σ * ι) := by
  obtain ⟨hσD, hσF⟩ := hσ
  obtain ⟨hιD, hιI⟩ := mem_Ine.mp hι
  have hσD' : σ ∈ Dec (F := F) A := mem_Dec.mpr hσD
  refine ⟨mem_Dec.mp ((Dec (F := F) A).mul_mem hσD' hιD), fun x hx => ?_⟩
  have e : (σ * ι) x - x ^ q = σ (ι x - x) + (σ x - x ^ q) := by
    rw [AlgEquiv.mul_apply, map_sub]; ring
  rw [e]
  exact Valuation.map_add_lt _ ((valuation_apply_lt_one_iff hσD' _).mpr (hιI x hx)) (hσF x hx)

variable (Ω) in

theorem exists_isPlaceOver (v : HeightOneSpectrum (𝓞 F)) :
    ∃ A : ValuationSubring (Ω), IsPlaceOver A v := by
  classical
  have hinj : Function.Injective (algebraMap F Ω) := (algebraMap F Ω).injective
  haveI hV : IsLocalRing (v.valuation F).valuationSubring.toSubring :=
    inferInstanceAs (IsLocalRing (v.valuation F).valuationSubring)
  haveI hS : IsLocalRing ((v.valuation F).valuationSubring.toSubring.map (algebraMap F Ω)) :=
    IsLocalRing.of_surjective'
      ((v.valuation F).valuationSubring.toSubring.equivMapOfInjective (algebraMap F Ω) hinj).toRingHom
      ((v.valuation F).valuationSubring.toSubring.equivMapOfInjective (algebraMap F Ω) hinj).surjective
  obtain ⟨B, hB⟩ := LocalSubring.exists_le_valuationSubring
    (LocalSubring.mk ((v.valuation F).valuationSubring.toSubring.map (algebraMap F Ω)) : LocalSubring Ω)
  obtain ⟨hsub, hloc⟩ := hB
  have hfx : ∀ z : F, v.valuation F z ≤ 1 → algebraMap F Ω z ∈ B := fun z hz =>
    hsub (Subring.mem_map.mpr ⟨z, hz, rfl⟩)
  have hle : ∀ r : 𝓞 F, v.valuation F (r : F) ≤ 1 := fun r => v.valuation_le_one r
  have hlt : ∀ r : 𝓞 F, v.valuation F (r : F) < 1 ↔ r ∈ v.asIdeal := fun r =>
    v.valuation_lt_one_iff_mem r
  refine ⟨B, ?_⟩
  unfold Formalism.ConjugateSelfDual.IsPlaceOver
  intro x
  constructor
  · intro h
    by_contra hx
    have hx1 : v.valuation F (x : F) = 1 := le_antisymm (hle x) (not_lt.mp (mt (hlt x).mp hx))
    have hx0 : (x : F) ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hx1
      exact zero_ne_one hx1
    have hne : algebraMap F Ω (x : F) ≠ 0 := (map_ne_zero _).mpr hx0
    have hinv : v.valuation F ((x : F)⁻¹) ≤ 1 := by rw [map_inv₀, hx1, inv_one]
    have hmem : algebraMap F Ω ((x : F)⁻¹) ∈ B := hfx _ hinv
    rw [map_inv₀] at hmem
    have h1 : B.valuation (algebraMap F Ω (x : F))⁻¹ ≤ 1 := (B.valuation_le_one_iff _).mpr hmem
    have h2 := (Valuation.one_lt_val_iff B.valuation (inv_ne_zero hne)).mpr (by rwa [inv_inv])
    exact absurd h1 (not_le.mpr h2)
  · intro hx
    by_contra hnot
    have hxlt := (hlt x).mpr hx
    by_cases hx0 : (x : F) = 0
    · apply hnot
      rw [hx0, map_zero, map_zero]
      exact zero_lt_one
    have hne : algebraMap F Ω (x : F) ≠ 0 := (map_ne_zero _).mpr hx0
    have hyB : algebraMap F Ω (x : F) ∈ B := hfx _ (hle x)
    have hyv : B.valuation (algebraMap F Ω (x : F)) = 1 :=
      le_antisymm ((B.valuation_le_one_iff _).mpr hyB) (not_lt.mp hnot)
    have hyinvB : (algebraMap F Ω (x : F))⁻¹ ∈ B := by
      rw [← B.valuation_le_one_iff, map_inv₀, hyv, inv_one]
    have hyS : algebraMap F Ω (x : F) ∈ (v.valuation F).valuationSubring.toSubring.map (algebraMap F Ω) :=
      Subring.mem_map.mpr ⟨_, hle x, rfl⟩
    have hunit : IsUnit (Subring.inclusion hsub ⟨_, hyS⟩) :=
      isUnit_iff_exists_inv.mpr ⟨⟨_, hyinvB⟩, Subtype.ext (mul_inv_cancel₀ hne)⟩
    obtain ⟨u, hu⟩ := hloc.map_nonunit _ hunit
    have ht := ((u⁻¹ : ((v.valuation F).valuationSubring.toSubring.map (algebraMap F Ω))ˣ) :
      ((v.valuation F).valuationSubring.toSubring.map (algebraMap F Ω))).2
    have hmul : algebraMap F Ω (x : F) *
        ((u⁻¹ : ((v.valuation F).valuationSubring.toSubring.map (algebraMap F Ω))ˣ) :
          ((v.valuation F).valuationSubring.toSubring.map (algebraMap F Ω))).1 = 1 := by
      have h3 := congrArg Subtype.val u.mul_inv
      rw [hu] at h3
      exact h3
    obtain ⟨z, hz, hzt⟩ := Subring.mem_map.mp ht
    have hzx : z = (x : F)⁻¹ := by
      apply hinj
      rw [hzt, map_inv₀]
      exact eq_inv_of_mul_eq_one_right hmul
    have hzle : v.valuation F z ≤ 1 := hz
    rw [hzx] at hzle
    have h4 := (Valuation.one_lt_val_iff (v.valuation F) (inv_ne_zero hx0)).mpr (by rwa [inv_inv])
    exact absurd hzle (not_le.mpr h4)

variable (Ω) in
theorem isPlaceOver_placeOf (v : HeightOneSpectrum (𝓞 F)) : IsPlaceOver (placeOf Ω v) v := Classical.epsilon_spec (exists_isPlaceOver Ω v)

theorem exists_smul_eq_of_isPlaceOver [IsAlgClosure F Ω] {A A' : ValuationSubring (Ω)}
    {v : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver A v) (h' : IsPlaceOver A' v) :
    ∃ σ : G F Ω, σ • A = A' := by
  exact exists_smul_eq_of_over h h'

theorem exists_isFrob [IsAlgClosure F Ω] {A : ValuationSubring (Ω)} {v : HeightOneSpectrum (𝓞 F)}
    (h : IsPlaceOver A v) : ∃ σ : G F Ω, IsFrob A (normV v) σ := by
  exact exists_frob_over h

variable (Ω) in
theorem isFrob_frobOf [IsAlgClosure F Ω] (v : HeightOneSpectrum (𝓞 F)) :
    IsFrob (placeOf Ω v) (normV v) (frobOf Ω v) := Classical.epsilon_spec (exists_isFrob (isPlaceOver_placeOf Ω v))

theorem cyc_eq_one_of_mem_Ine [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring (Ω)}
    {v : HeightOneSpectrum (𝓞 F)} (hl : ((l : ℕ) : 𝓞 F) ∉ v.asIdeal) (h : IsPlaceOver A v)
    {σ : G F Ω} (hσ : σ ∈ Ine (F := F) A) : cyc F Ω l σ = 1 := by
  obtain ⟨-, hI⟩ := mem_Ine.mp hσ
  have key : ∀ n, PadicInt.toZModPow n ((cycZ F Ω l σ : ℤ_[l]ˣ) : ℤ_[l]) =
      PadicInt.toZModPow n ((1 : ℕ) : ℤ_[l]) :=
    cycZ_toZModPow_eq hl h (fun x hx => by simpa using hI x hx)
  have hz : ((cycZ F Ω l σ : ℤ_[l]ˣ) : ℤ_[l]) = 1 := by
    simpa using PadicInt.ext_of_toZModPow.mp key
  rw [cyc_eq_map_cycZ, show cycZ F Ω l σ = 1 from Units.ext hz, map_one]

theorem cycZ_of_isFrob [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring (Ω)}
    {v : HeightOneSpectrum (𝓞 F)} (hl : ((l : ℕ) : 𝓞 F) ∉ v.asIdeal) (h : IsPlaceOver A v)
    {σ : G F Ω} (hσ : IsFrob A (normV v) σ) : ((cycZ F Ω l σ : ℤ_[l]ˣ) : ℤ_[l]) = (normV v : ℤ_[l]) := by
  obtain ⟨-, hF⟩ := hσ
  exact PadicInt.ext_of_toZModPow.mp (cycZ_toZModPow_eq hl h hF)

private theorem isClosed_setOf_apply_lemma [IsAlgClosure F Ω] (x : Ω) (P : Ω → Prop) :
    IsClosed {τ : G F Ω | P (τ x)} := by
  have hal : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  have hfd : FiniteDimensional F (IntermediateField.adjoin F {x}) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  have hH : IsOpen ((IntermediateField.adjoin F {x}).fixingSubgroup : Set (G F Ω)) :=
    IntermediateField.fixingSubgroup_isOpen _
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro σ hσ
  refine ⟨(fun τ : G F Ω => σ⁻¹ * τ) ⁻¹' ((IntermediateField.adjoin F {x}).fixingSubgroup : Set (G F Ω)),
    ?_, hH.preimage (continuous_const.mul continuous_id), ?_⟩
  · intro τ hτ hPτ
    have h1 : (σ⁻¹ * τ) x = x :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).mp hτ x (IntermediateField.mem_adjoin_simple_self F x)
    have h2 : τ x = σ x := by
      have h3 := congrArg σ h1
      rwa [AlgEquiv.mul_apply, mul_inv_apply] at h3
    exact hσ (by simpa only [Set.mem_setOf_eq, h2] using hPτ)
  · show σ⁻¹ * σ ∈ (IntermediateField.adjoin F {x}).fixingSubgroup
    rw [inv_mul_cancel]
    exact one_mem _

theorem isClosed_Dec [IsAlgClosure F Ω] (A : ValuationSubring (Ω)) : IsClosed (Dec (F := F) A : Set (G F Ω)) := by
  have e : (Dec (F := F) A : Set (G F Ω)) = ⋂ x : Ω, {τ : G F Ω | τ x ∈ A ↔ x ∈ A} := by
    ext τ
    simp only [SetLike.mem_coe, Set.mem_iInter, Set.mem_setOf_eq]
    refine ⟨fun h x => apply_mem_iff_of_mem_Dec h x, fun h => mem_Dec.mpr ?_⟩
    ext y
    have k : τ • ((τ⁻¹ : G F Ω) y) ∈ τ • A ↔ (τ⁻¹ : G F Ω) y ∈ A :=
      ValuationSubring.smul_mem_pointwise_smul_iff
    rw [AlgEquiv.smul_def, mul_inv_apply] at k
    rw [k, ← h ((τ⁻¹ : G F Ω) y), mul_inv_apply]
  rw [e]
  exact isClosed_iInter fun x => isClosed_setOf_apply_lemma x (fun y => y ∈ A ↔ x ∈ A)

theorem isClosed_Ine [IsAlgClosure F Ω] (A : ValuationSubring (Ω)) : IsClosed (Ine (F := F) A : Set (G F Ω)) := by
  have e : (Ine (F := F) A : Set (G F Ω)) = (Dec (F := F) A : Set (G F Ω)) ∩
      ⋂ x : Ω, {τ : G F Ω | A.valuation x ≤ 1 → A.valuation (τ x - x) < 1} := by
    ext τ
    simp only [SetLike.mem_coe, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
    exact Iff.rfl
  rw [e]
  exact (isClosed_Dec A).inter (isClosed_iInter fun x =>
    isClosed_setOf_apply_lemma x (fun y => A.valuation x ≤ 1 → A.valuation (y - x) < 1))

end Basic₃

end ReciprocityTheory.Gal
end
end


section
-- Source: ReciprocityTheory/Hypotheses/GalCohDefs.lean

noncomputable section

open NumberField IsDedekindDomain Representation

namespace ReciprocityTheory.Gal

open Formalism.ConjugateSelfDual

instance (priority := 100) continuousConstSMul_of_discrete {R M : Type*} [SMul R M]
    [TopologicalSpace M] [DiscreteTopology M] : ContinuousConstSMul R M :=
  ⟨fun _ => continuous_of_discreteTopology⟩

section Coeff

variable {R : Type*} [CommRing R] {Γ : Type*} [Group Γ]
  {M : Type*} [AddCommGroup M] [Module R M]

def charRep (χ : Γ →* Rˣ) : Representation R Γ R where
  toFun g := ((χ g : Rˣ) : R) • LinearMap.id
  map_one' := by ext; simp
  map_mul' g h := by ext; simp [mul_comm]

@[simp] theorem charRep_apply (χ : Γ →* Rˣ) (g : Γ) (x : R) :
    charRep χ g x = ((χ g : Rˣ) : R) * x := rfl

variable (R M) in

def TDual := Module.Dual R M

instance : AddCommGroup (TDual R M) := inferInstanceAs (AddCommGroup (Module.Dual R M))
instance : Module R (TDual R M) := inferInstanceAs (Module R (Module.Dual R M))
instance : TopologicalSpace (TDual R M) := ⊥
instance : DiscreteTopology (TDual R M) := ⟨rfl⟩
instance : FunLike (TDual R M) M R := inferInstanceAs (FunLike (M →ₗ[R] R) M R)

def TDual.mk (φ : M →ₗ[R] R) : TDual R M := φ

@[simp] theorem TDual.mk_apply (φ : M →ₗ[R] R) (m : M) : TDual.mk φ m = φ m := rfl

@[simp] theorem TDual.add_apply (φ ψ : TDual R M) (m : M) : (φ + ψ) m = φ m + ψ m := rfl

@[simp] theorem TDual.smul_apply (c : R) (φ : TDual R M) (m : M) : (c • φ) m = c * φ m := rfl

@[ext] theorem TDual.ext {φ ψ : TDual R M} (h : ∀ m, φ m = ψ m) : φ = ψ := LinearMap.ext h

def twDual (χ : Γ →* Rˣ) (rho : Representation R Γ M) : Representation R Γ (TDual R M) where
  toFun g :=
    { toFun := fun φ => TDual.mk (((χ g : Rˣ) : R) • ((φ : M →ₗ[R] R) ∘ₗ rho g⁻¹))
      map_add' := fun φ ψ => by
        ext m
        show ((χ g : Rˣ) : R) * (φ (rho g⁻¹ m) + ψ (rho g⁻¹ m)) =
          ((χ g : Rˣ) : R) * φ (rho g⁻¹ m) + ((χ g : Rˣ) : R) * ψ (rho g⁻¹ m)
        ring
      map_smul' := fun c φ => by
        ext m
        show ((χ g : Rˣ) : R) * (c * φ (rho g⁻¹ m)) = c * (((χ g : Rˣ) : R) * φ (rho g⁻¹ m))
        ring }
  map_one' := by ext φ m; simp; rfl
  map_mul' g h := by
    ext φ m
    show _ * φ (rho (g * h)⁻¹ m) = _ * (_ * φ (rho h⁻¹ (rho g⁻¹ m)))
    rw [mul_inv_rev, map_mul rho, Module.End.mul_apply, map_mul χ, Units.val_mul, mul_assoc]

@[simp] theorem twDual_apply (χ : Γ →* Rˣ) (rho : Representation R Γ M) (g : Γ) (φ : TDual R M)
    (m : M) : twDual χ rho g φ m = ((χ g : Rˣ) : R) * φ (rho g⁻¹ m) := rfl

def evalPair : M →ₗ[R] TDual R M →ₗ[R] R := LinearMap.applyₗ

@[simp] theorem evalPair_apply (m : M) (φ : TDual R M) : evalPair m φ = φ m := rfl

theorem evalPair_equiv (χ : Γ →* Rˣ) (rho : Representation R Γ M) (g : Γ) (m : M)
    (φ : TDual R M) : evalPair (rho g m) (twDual χ rho g φ) = charRep χ g (evalPair m φ) := by
  have e : rho g⁻¹ (rho g m) = m := by
    first
      | exact Representation.inv_self_apply rho g m
      | rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
      | rw [← LinearMap.mul_apply, ← map_mul, inv_mul_cancel, map_one, LinearMap.one_apply]
  rw [evalPair_apply, twDual_apply, charRep_apply, evalPair_apply, e]

end Coeff

section Cup

variable {R : Type*} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  {Γ : Type*} [Group Γ] {M : Type*} [AddCommGroup M] [Module R M]
  [TopologicalSpace M] [DiscreteTopology M]

theorem ContAction.comp' [TopologicalSpace Γ] {D : Type*} [Group D] [TopologicalSpace D]
    {rho : Representation R Γ M} (h : ContAction rho) {φ : D →* Γ} (hφ : Continuous φ) :
    ContAction (rho.comp φ) := by
  exact Continuous.comp (show Continuous (fun p : Γ × M => rho p.1 p.2) from h)
    ((hφ.comp continuous_fst).prodMk continuous_snd)

variable {D : Type*} [Group D] [TopologicalSpace D]
  (χ : Γ →* Rˣ) (rho : Representation R Γ M) (φ : D →* Γ)

def cupH0H2TwistedDual : H0 (rho.comp φ) →ₗ[R] H2 ((twDual χ rho).comp φ) →ₗ[R] H2 ((charRep χ).comp φ) :=
  cupProductH0H2 (rho.comp φ) ((twDual χ rho).comp φ) ((charRep χ).comp φ) evalPair
    continuous_of_discreteTopology (fun g x y => evalPair_equiv χ rho (φ g) x y)

def cup20 : H2 (rho.comp φ) →ₗ[R] H0 ((twDual χ rho).comp φ) →ₗ[R] H2 ((charRep χ).comp φ) :=
  cupProductH2H0 (rho.comp φ) ((twDual χ rho).comp φ) ((charRep χ).comp φ) evalPair
    continuous_of_discreteTopology (fun g x y => evalPair_equiv χ rho (φ g) x y)

def cupH1H1TwistedDual (hrho : ContAction (rho.comp φ)) :
    H1 ((twDual χ rho).comp φ) →ₗ[R] H1 (rho.comp φ) →ₗ[R] H2 ((charRep χ).comp φ) :=
  cupProductH1H1 ((twDual χ rho).comp φ) (rho.comp φ) ((charRep χ).comp φ) evalPair.flip
    continuous_of_discreteTopology (fun g y x => evalPair_equiv χ rho (φ g) x y) hrho

def perpCond {I : Type*} {D : I → Type*} [∀ i, Group (D i)] [∀ i, TopologicalSpace (D i)]
    (phi : ∀ i, D i →* Γ) (hrho : ∀ i, ContAction (rho.comp (phi i)))
    (L : ∀ i, Submodule R (H1 (rho.comp (phi i)))) :
    ∀ i, Submodule R (H1 ((twDual χ rho).comp (phi i))) :=
  fun i => ⨅ x ∈ L i, LinearMap.ker ((cupH1H1TwistedDual χ rho (phi i) (hrho i)).flip x)

theorem mem_perpCond {I : Type*} {D : I → Type*} [∀ i, Group (D i)] [∀ i, TopologicalSpace (D i)]
    (phi : ∀ i, D i →* Γ) (hrho : ∀ i, ContAction (rho.comp (phi i)))
    (L : ∀ i, Submodule R (H1 (rho.comp (phi i)))) (i : I) (y : H1 ((twDual χ rho).comp (phi i))) :
    y ∈ perpCond χ rho phi hrho L i ↔ ∀ x ∈ L i, cupH1H1TwistedDual χ rho (phi i) (hrho i) y x = 0 := by
  show y ∈ ⨅ x ∈ L i, LinearMap.ker ((cupH1H1TwistedDual χ rho (phi i) (hrho i)).flip x) ↔ _
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.flip_apply]

end Cup

section Field

variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

def locDeg (v : HeightOneSpectrum (𝓞 F)) : ℕ :=
  v.asIdeal.ramificationIdx ℤ * v.asIdeal.inertiaDeg ℤ

def IsCCAt (w : InfinitePlace F) (c : G F Ω) : Prop :=
  ∃ j : Ω →+* ℂ, (∀ x, j (c x) = starRingEnd ℂ (j x)) ∧
    InfinitePlace.mk (j.comp (algebraMap F Ω)) = w

variable (F Ω) (l : ℕ) [Fact l.Prime] (r : ℕ)

abbrev muRep : Representation (ZMod (l ^ r)) (G F Ω) (ZMod (l ^ r)) := charRep (cycMod F Ω l r)

variable {F Ω l r} in

abbrev tateDual {M : Type*} [AddCommGroup M] [Module (ZMod (l ^ r)) M]
    (rho : Representation (ZMod (l ^ r)) (G F Ω) M) :
    Representation (ZMod (l ^ r)) (G F Ω) (TDual (ZMod (l ^ r)) M) :=
  twDual (cycMod F Ω l r) rho

end Field

end ReciprocityTheory.Gal
end
end


section
-- Source: ReciprocityTheory/Hypotheses/GalCoh.lean

noncomputable section

open NumberField IsDedekindDomain Representation

namespace ReciprocityTheory.Gal

open Formalism.ConjugateSelfDual

section Local

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {r : ℕ}
  {M : Type} [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M]
  [TopologicalSpace M] [DiscreteTopology M]

def LocalFinitenessAt (A : ValuationSubring Ω)
    (rho : Representation (ZMod (l ^ r)) (Dec (F := F) A) M) (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  0 < r → IsPlaceOver A v → ContAction rho →
    Finite (H0 rho) ∧ Finite (H1 rho) ∧ Finite (H2 rho) ∧ ∀ n, 3 ≤ n → Subsingleton (Hn rho n)

def LocalTateDualityAt (A : ValuationSubring Ω)
    (rho : Representation (ZMod (l ^ r)) (Dec (F := F) A) M) (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  0 < r → IsPlaceOver A v → ∀ hrho : ContAction rho,
    Nonempty (H2 (charRep ((cycMod F Ω l r).comp (Dec (F := F) A).subtype)) ≃ₗ[ZMod (l ^ r)]
      ZMod (l ^ r)) ∧
    Function.Bijective
      (cupH0H2TwistedDual ((cycMod F Ω l r).comp (Dec (F := F) A).subtype) rho (MonoidHom.id _)) ∧
    Function.Bijective (cupH1H1TwistedDual ((cycMod F Ω l r).comp (Dec (F := F) A).subtype) rho
      (MonoidHom.id _) (hrho.comp' continuous_id)) ∧
    Function.Bijective (cupH1H1TwistedDual ((cycMod F Ω l r).comp (Dec (F := F) A).subtype) rho
      (MonoidHom.id _) (hrho.comp' continuous_id)).flip ∧
    Function.Bijective
      (cup20 ((cycMod F Ω l r).comp (Dec (F := F) A).subtype) rho (MonoidHom.id _))

def UnramifiedOrthogonalityAt (A : ValuationSubring Ω)
    (rho : Representation (ZMod (l ^ r)) (Dec (F := F) A) M) (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  0 < r → IsPlaceOver A v → ((l : ℕ) : 𝓞 F) ∉ v.asIdeal →
    (∀ σ : Dec (F := F) A, (σ : G F Ω) ∈ Ine (F := F) A → rho σ = 1) →
    ∀ hrho : ContAction rho,
    (∀ x : H1 rho,
      x ∈ H1ur rho ((Ine (F := F) A).subgroupOf (Dec (F := F) A)) ↔
        ∀ y ∈ H1ur (twDual ((cycMod F Ω l r).comp (Dec (F := F) A).subtype) rho)
            ((Ine (F := F) A).subgroupOf (Dec (F := F) A)),
          cupH1H1TwistedDual ((cycMod F Ω l r).comp (Dec (F := F) A).subtype) rho (MonoidHom.id _)
            (hrho.comp' continuous_id) y x = 0) ∧
    (∀ y : H1 (twDual ((cycMod F Ω l r).comp (Dec (F := F) A).subtype) rho),
      y ∈ H1ur (twDual ((cycMod F Ω l r).comp (Dec (F := F) A).subtype) rho)
          ((Ine (F := F) A).subgroupOf (Dec (F := F) A)) ↔
        ∀ x ∈ H1ur rho ((Ine (F := F) A).subgroupOf (Dec (F := F) A)),
          cupH1H1TwistedDual ((cycMod F Ω l r).comp (Dec (F := F) A).subtype) rho (MonoidHom.id _)
            (hrho.comp' continuous_id) y x = 0)

def LocalEulerCharAt (A : ValuationSubring Ω)
    (rho : Representation (ZMod (l ^ r)) (Dec (F := F) A) M) (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  0 < r → IsPlaceOver A v → ContAction rho →
    (((l : ℕ) : 𝓞 F) ∈ v.asIdeal →
      Nat.card (H1 rho) = Nat.card (H0 rho) * Nat.card (H2 rho) * Nat.card M ^ locDeg v) ∧
    (((l : ℕ) : 𝓞 F) ∉ v.asIdeal → Nat.card (H1 rho) = Nat.card (H0 rho) * Nat.card (H2 rho))

def LocalFinitenessResAt (rho : Representation (ZMod (l ^ r)) (G F Ω) M)
    (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  0 < r → IsPlaceOver A v → ContAction rho →
    Finite (H0 (rho.comp (Dec (F := F) A).subtype)) ∧ Finite (H1 (rho.comp (Dec (F := F) A).subtype)) ∧
    Finite (H2 (rho.comp (Dec (F := F) A).subtype)) ∧
    ∀ n, 3 ≤ n → Subsingleton (Hn (rho.comp (Dec (F := F) A).subtype) n)

def LocalTateDualityResAt (rho : Representation (ZMod (l ^ r)) (G F Ω) M)
    (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  0 < r → IsPlaceOver A v → ∀ hrho : ContAction rho,
    Nonempty (H2 ((muRep F Ω l r).comp (Dec (F := F) A).subtype) ≃ₗ[ZMod (l ^ r)] ZMod (l ^ r)) ∧
    Function.Bijective (cupH0H2TwistedDual (cycMod F Ω l r) rho (Dec (F := F) A).subtype) ∧
    Function.Bijective (cupH1H1TwistedDual (cycMod F Ω l r) rho (Dec (F := F) A).subtype
      (hrho.comp' continuous_subtype_val)) ∧
    Function.Bijective (cupH1H1TwistedDual (cycMod F Ω l r) rho (Dec (F := F) A).subtype
      (hrho.comp' continuous_subtype_val)).flip ∧
    Function.Bijective (cup20 (cycMod F Ω l r) rho (Dec (F := F) A).subtype)

def UnramifiedOrthogonalityResAt (rho : Representation (ZMod (l ^ r)) (G F Ω) M)
    (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  0 < r → IsPlaceOver A v → ((l : ℕ) : 𝓞 F) ∉ v.asIdeal → (∀ σ ∈ Ine A, rho σ = 1) →
    ∀ hrho : ContAction rho,
    (∀ x : H1 (rho.comp (Dec (F := F) A).subtype),
      x ∈ H1ur (rho.comp (Dec (F := F) A).subtype) ((Ine (F := F) A).subgroupOf (Dec (F := F) A)) ↔
        ∀ y ∈ H1ur ((tateDual rho).comp (Dec (F := F) A).subtype) ((Ine (F := F) A).subgroupOf (Dec (F := F) A)),
          cupH1H1TwistedDual (cycMod F Ω l r) rho (Dec (F := F) A).subtype (hrho.comp' continuous_subtype_val) y x = 0) ∧
    (∀ y : H1 ((tateDual rho).comp (Dec (F := F) A).subtype),
      y ∈ H1ur ((tateDual rho).comp (Dec (F := F) A).subtype) ((Ine (F := F) A).subgroupOf (Dec (F := F) A)) ↔
        ∀ x ∈ H1ur (rho.comp (Dec (F := F) A).subtype) ((Ine (F := F) A).subgroupOf (Dec (F := F) A)),
          cupH1H1TwistedDual (cycMod F Ω l r) rho (Dec (F := F) A).subtype (hrho.comp' continuous_subtype_val) y x = 0)

def LocalEulerCharResAt (rho : Representation (ZMod (l ^ r)) (G F Ω) M)
    (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  0 < r → IsPlaceOver A v → ContAction rho →
    (((l : ℕ) : 𝓞 F) ∈ v.asIdeal →
      Nat.card (H1 (rho.comp (Dec (F := F) A).subtype)) = Nat.card (H0 (rho.comp (Dec (F := F) A).subtype)) *
        Nat.card (H2 (rho.comp (Dec (F := F) A).subtype)) * Nat.card M ^ locDeg v) ∧
    (((l : ℕ) : 𝓞 F) ∉ v.asIdeal →
      Nat.card (H1 (rho.comp (Dec (F := F) A).subtype)) = Nat.card (H0 (rho.comp (Dec (F := F) A).subtype)) *
        Nat.card (H2 (rho.comp (Dec (F := F) A).subtype)))

theorem LocalFinitenessAt.restrict {rho : Representation (ZMod (l ^ r)) (G F Ω) M}
    {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)}
    (h : LocalFinitenessAt A (rho.comp (Dec (F := F) A).subtype) v) : LocalFinitenessResAt rho A v :=
  fun hr hA hc => h hr hA (hc.comp' continuous_subtype_val)

theorem LocalTateDualityAt.restrict {rho : Representation (ZMod (l ^ r)) (G F Ω) M}
    {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)}
    (h : LocalTateDualityAt A (rho.comp (Dec (F := F) A).subtype) v) :
    LocalTateDualityResAt rho A v :=
  fun hr hA hc => h hr hA (hc.comp' continuous_subtype_val)

theorem UnramifiedOrthogonalityAt.restrict {rho : Representation (ZMod (l ^ r)) (G F Ω) M}
    {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)}
    (h : UnramifiedOrthogonalityAt A (rho.comp (Dec (F := F) A).subtype) v) :
    UnramifiedOrthogonalityResAt rho A v :=
  fun hr hA hl hI hc => h hr hA hl (fun σ hσ => hI σ hσ) (hc.comp' continuous_subtype_val)

theorem LocalEulerCharAt.restrict {rho : Representation (ZMod (l ^ r)) (G F Ω) M}
    {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)}
    (h : LocalEulerCharAt A (rho.comp (Dec (F := F) A).subtype) v) : LocalEulerCharResAt rho A v :=
  fun hr hA hc => h hr hA (hc.comp' continuous_subtype_val)

end Local

section Global

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {r : ℕ}
  {M : Type} [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M]
  [TopologicalSpace M] [DiscreteTopology M]

def locFam (S : Finset (HeightOneSpectrum (𝓞 F)))
    (Av : S → ValuationSubring Ω) :
    ∀ v : S, Dec (F := F) (Av v) →* GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) :=
  fun v => locHom _ (Av v)

theorem continuous_locFam (S : Finset (HeightOneSpectrum (𝓞 F)))
    (Av : S → ValuationSubring Ω) (v : S) : Continuous (locFam S Av v) :=
  continuous_locHom _ _

def ContainsAbove (S : Finset (HeightOneSpectrum (𝓞 F))) (l : ℕ) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∈ v.asIdeal → v ∈ S

def archH0Card (S : Finset (HeightOneSpectrum (𝓞 F)))
    (rhoS : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M)
    (c : InfinitePlace F → G F Ω) : ℕ :=
  open scoped Classical in
  (∏ w ∈ Finset.univ.filter (fun w : InfinitePlace F => w.IsReal),
    Nat.card {m : M // rhoS (toGS Ω _ (c w)) m = m}) * Nat.card M ^ InfinitePlace.nrComplexPlaces F

def GlobalFinitenessAt (S : Finset (HeightOneSpectrum (𝓞 F)))
    (rhoS : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M) : Prop :=
  0 < r → ContainsAbove S l → ContAction rhoS →
    Finite (H0 rhoS) ∧ Finite (H1 rhoS) ∧ Finite (H2 rhoS) ∧
    (l ≠ 2 → ∀ n, 3 ≤ n → Subsingleton (Hn rhoS n))

def GlobalEulerCharAt (S : Finset (HeightOneSpectrum (𝓞 F)))
    (rhoS : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M) : Prop :=
  0 < r → ContainsAbove S l → ContAction rhoS →
    ∀ c : InfinitePlace F → G F Ω, (∀ w, w.IsReal → IsCCAt w (c w)) →
      Nat.card (H0 rhoS) * Nat.card (H2 rhoS) * Nat.card M ^ Module.finrank ℚ F =
        Nat.card (H1 rhoS) * archH0Card S rhoS c

def ShaDualityAt (S : Finset (HeightOneSpectrum (𝓞 F)))
    (rhoS : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M) : Prop :=
  0 < r → l ≠ 2 → ContainsAbove S l → ContAction rhoS →
    ∀ muS : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ,
      muS.comp (toGS Ω _) = cycMod F Ω l r →
    ∀ Av : S → ValuationSubring Ω, (∀ v, IsPlaceOver (Av v) v.1) →
      Finite (Sha1 rhoS (locFam S Av) (continuous_locFam S Av)) ∧
      Finite (Sha2 (twDual muS rhoS) (locFam S Av) (continuous_locFam S Av)) ∧
      Nat.card (Sha1 rhoS (locFam S Av) (continuous_locFam S Av)) =
        Nat.card (Sha2 (twDual muS rhoS) (locFam S Av) (continuous_locFam S Av))

def GreenbergWilesAt (S : Finset (HeightOneSpectrum (𝓞 F)))
    (rhoS : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M) : Prop :=
  0 < r → l ≠ 2 → ContainsAbove S l → ∀ hrho : ContAction rhoS,
    ∀ muS : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ,
      muS.comp (toGS Ω _) = cycMod F Ω l r →
    ∀ Av : S → ValuationSubring Ω, (∀ v, IsPlaceOver (Av v) v.1) →
    ∀ c : InfinitePlace F → G F Ω, (∀ w, w.IsReal → IsCCAt w (c w)) →
    ∀ L : LocCond rhoS (locFam S Av),
      Nat.card (Sel rhoS (locFam S Av) (continuous_locFam S Av) L) *
          Nat.card (H0 (twDual muS rhoS)) *
          (∏ v : S, Nat.card (H0 (rhoS.comp (locFam S Av v)))) * archH0Card S rhoS c =
        Nat.card (Sel (twDual muS rhoS) (locFam S Av) (continuous_locFam S Av)
            (perpCond muS rhoS (locFam S Av)
              (fun v => hrho.comp' (continuous_locFam S Av v)) L)) *
          Nat.card (H0 rhoS) * ∏ v : S, Nat.card (L v)

end Global

section Universal

def LocalFiniteness : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M]
    [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
    (A : ValuationSubring Ω) (rho : Representation (ZMod (l ^ r)) (Dec (F := F) A) M)
    (v : HeightOneSpectrum (𝓞 F)), LocalFinitenessAt A rho v

def LocalTateDuality : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M]
    [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
    (A : ValuationSubring Ω) (rho : Representation (ZMod (l ^ r)) (Dec (F := F) A) M)
    (v : HeightOneSpectrum (𝓞 F)), LocalTateDualityAt A rho v

def UnramifiedOrthogonality : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M]
    [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
    (A : ValuationSubring Ω) (rho : Representation (ZMod (l ^ r)) (Dec (F := F) A) M)
    (v : HeightOneSpectrum (𝓞 F)), UnramifiedOrthogonalityAt A rho v

def LocalEulerChar : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M]
    [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
    (A : ValuationSubring Ω) (rho : Representation (ZMod (l ^ r)) (Dec (F := F) A) M)
    (v : HeightOneSpectrum (𝓞 F)), LocalEulerCharAt A rho v

def GlobalFiniteness : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M]
    [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (rhoS : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M),
    GlobalFinitenessAt S rhoS

def GlobalEulerChar : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M]
    [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (rhoS : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M),
    GlobalEulerCharAt S rhoS

def ShaDuality : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M]
    [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (rhoS : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M),
    ShaDualityAt S rhoS

def GreenbergWiles : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M]
    [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (rhoS : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M),
    GreenbergWilesAt S rhoS

end Universal

section Restrict

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {r : ℕ}
  {M : Type} [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M]
  [TopologicalSpace M] [DiscreteTopology M]

theorem LocalFiniteness.restrict (h : LocalFiniteness) (rho : Representation (ZMod (l ^ r)) (G F Ω) M)
    (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)) : LocalFinitenessResAt rho A v :=
  (h F Ω l r M A _ v).restrict

theorem LocalTateDuality.restrict (h : LocalTateDuality) (rho : Representation (ZMod (l ^ r)) (G F Ω) M)
    (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)) : LocalTateDualityResAt rho A v :=
  (h F Ω l r M A _ v).restrict

theorem UnramifiedOrthogonality.restrict (h : UnramifiedOrthogonality) (rho : Representation (ZMod (l ^ r)) (G F Ω) M)
    (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)) : UnramifiedOrthogonalityResAt rho A v :=
  (h F Ω l r M A _ v).restrict

theorem LocalEulerChar.restrict (h : LocalEulerChar) (rho : Representation (ZMod (l ^ r)) (G F Ω) M)
    (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)) : LocalEulerCharResAt rho A v :=
  (h F Ω l r M A _ v).restrict

end Restrict

end ReciprocityTheory.Gal
end
end


section
-- Source: Formalism/GaloisCohomology/Statement.lean

noncomputable section

open NumberField IsDedekindDomain Representation ReciprocityTheory.Gal Formalism.ConjugateSelfDual

namespace Formalism.GaloisCohomology

section Coeff

variable (l : ℕ) [Fact l.Prime]

abbrev ZlSub : Submodule ℤ_[l] ℚ_[l] := LinearMap.range (Algebra.linearMap ℤ_[l] ℚ_[l])

def QZ : Type := ℚ_[l] ⧸ ZlSub l

instance : AddCommGroup (QZ l) := inferInstanceAs (AddCommGroup (ℚ_[l] ⧸ ZlSub l))
instance : Module ℤ_[l] (QZ l) := inferInstanceAs (Module ℤ_[l] (ℚ_[l] ⧸ ZlSub l))
instance : TopologicalSpace (QZ l) := ⊥
instance : DiscreteTopology (QZ l) := ⟨rfl⟩
instance : IsTopologicalAddGroup (QZ l) where
  continuous_add := continuous_of_discreteTopology
  continuous_neg := continuous_of_discreteTopology

def QZ.mk (x : ℚ_[l]) : QZ l := Submodule.Quotient.mk (p := ZlSub l) x

end Coeff

def scalRep {R : Type*} [CommRing R] {Γ : Type*} [Group Γ] (M : Type*) [AddCommGroup M]
    [Module R M] (ψ : Γ →* Rˣ) : Representation R Γ M where
  toFun g := ((ψ g : Rˣ) : R) • LinearMap.id
  map_one' := by ext; simp
  map_mul' g h := by
    ext x
    simp only [map_mul, Units.val_mul, mul_smul, LinearMap.smul_apply, LinearMap.id_apply,
      Module.End.mul_apply, map_smul]
    first | rfl | exact smul_comm _ _ _

@[simp] theorem scalRep_apply {R : Type*} [CommRing R] {Γ : Type*} [Group Γ] (M : Type*)
    [AddCommGroup M] [Module R M] (ψ : Γ →* Rˣ) (g : Γ) (m : M) :
    scalRep M ψ g m = ((ψ g : Rˣ) : R) • m := rfl

section Field

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  (l : ℕ) [Fact l.Prime]

variable (F) in

def Above : Set (HeightOneSpectrum (𝓞 F)) := {v | ((l : ℕ) : 𝓞 F) ∈ v.asIdeal}

variable (F Ω) in

structure LData where

  S : Finset (HeightOneSpectrum (𝓞 F))
  hS : (S : Set (HeightOneSpectrum (𝓞 F))) = Above F l

  A : S → ValuationSubring Ω
  hA : ∀ v, IsPlaceOver (A v) v.1

  chi : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* ℤ_[l]ˣ
  hchi : chi.comp (toGS Ω _) = cycZ F Ω l

variable {l}

def qzTw (D : LData F Ω l) (e : ℤ) :
    Representation ℤ_[l] (GS Ω (D.S : Set (HeightOneSpectrum (𝓞 F)))) (QZ l) :=
  scalRep (QZ l) (D.chi ^ (-e))

def zlTw (D : LData F Ω l) (n : ℤ) :
    Representation ℤ_[l] (GS Ω (D.S : Set (HeightOneSpectrum (𝓞 F)))) ℤ_[l] :=
  scalRep ℤ_[l] (D.chi ^ n)

def Sha (D : LData F Ω l) (e : ℤ) : Submodule ℤ_[l] (H1 (qzTw D e)) :=
  Sha1 (qzTw D e) (locFam D.S D.A) (continuous_locFam D.S D.A)

def shaLen (D : LData F Ω l) (e : ℤ) : ℕ∞ := Module.length ℤ_[l] (Sha D e)

def VLen (D : LData F Ω l) (e : ℤ) : ℕ∞ := Module.length ℤ_[l] (H2 (zlTw D (e + 1)))

def Sha2Zl (D : LData F Ω l) (e : ℤ) : Submodule ℤ_[l] (H2 (zlTw D (e + 1))) :=
  Sha2 (zlTw D (e + 1)) (locFam D.S D.A) (continuous_locFam D.S D.A)

def localH2 (D : LData F Ω l) (e : ℤ) :
    H2 (zlTw D (e + 1)) →ₗ[ℤ_[l]] ∀ v : D.S, H2 ((zlTw D (e + 1)).comp (locFam D.S D.A v)) :=
  LinearMap.pi fun v => resH2 (zlTw D (e + 1)) (locFam D.S D.A v) (continuous_locFam D.S D.A v)

def sumLocalH0TwistLength (D : LData F Ω l) (e : ℤ) : ℕ∞ :=
  ∑ v : D.S, Module.length ℤ_[l] (H0 ((qzTw D e).comp (locFam D.S D.A v)))

def PTCase (F : Type) [Field F] [NumberField F] (l : ℕ) : Prop :=
  l ≠ 2 ∨ InfinitePlace.nrRealPlaces F = 0

def PTCokerAt (D : LData F Ω l) (e : ℤ) : Prop :=
  PTCase F l →
    Module.length ℤ_[l] ((∀ v : D.S, H2 ((zlTw D (e + 1)).comp (locFam D.S D.A v))) ⧸
        LinearMap.range (localH2 D e)) =
      Module.length ℤ_[l] (H0 (qzTw D e))

def PTShaAt (D : LData F Ω l) (e : ℤ) : Prop :=
  PTCase F l → Module.length ℤ_[l] (Sha2Zl D e) = shaLen D e

def TateLocalDualityH2AtPlaces (D : LData F Ω l) (e : ℤ) : Prop :=
  ∀ v : D.S, Module.length ℤ_[l] (H2 ((zlTw D (e + 1)).comp (locFam D.S D.A v))) =
    Module.length ℤ_[l] (H0 ((qzTw D e).comp (locFam D.S D.A v)))

def PTCoker : Prop := ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
  [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (D : LData F Ω l) (e : ℤ), PTCokerAt D e

def PTSha : Prop := ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
  [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (D : LData F Ω l) (e : ℤ), PTShaAt D e

def TateLocalDualityH2Hypothesis : Prop := ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
  [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (D : LData F Ω l) (e : ℤ), TateLocalDualityH2AtPlaces D e

end Field

def LDataExists : Prop := ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
  [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime], Nonempty (LData F Ω l)

def Indep : Prop := ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
  [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (D D' : LData F Ω l) (e : ℤ),
  shaLen D e = shaLen D' e ∧ VLen D e = VLen D' e ∧ sumLocalH0TwistLength D e = sumLocalH0TwistLength D' e

def ContTw : Prop := ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
  [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (D : LData F Ω l) (e : ℤ),
  ContAction (qzTw D e) ∧ ContAction (zlTw D e)

def GlobalH0TwistFiniteLength : Prop := ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
  [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (D : LData F Ω l) (e : ℤ), e ≠ 0 →
  Module.length ℤ_[l] (H0 (qzTw D e)) < ⊤

def LocalH0TwistFiniteLength : Prop := ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
  [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (D : LData F Ω l) (e : ℤ), e ≠ 0 → ∀ v : D.S,
  Module.length ℤ_[l] (H0 ((qzTw D e).comp (locFam D.S D.A v))) < ⊤

def VFormula : Prop := ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
  [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (D : LData F Ω l) (e : ℤ), PTCase F l →
  PTCokerAt D e → PTShaAt D e → TateLocalDualityH2AtPlaces D e →
    VLen D e + Module.length ℤ_[l] (H0 (qzTw D e)) = shaLen D e + sumLocalH0TwistLength D e

section Sel

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
  {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul R M]

variable (F Ω) in

abbrev Places : Type :=
  {A : HeightOneSpectrum (𝓞 F) → ValuationSubring Ω // ∀ v, IsPlaceOver (A v) v}

def unrAt (rho : Representation R (G F Ω) M) (A : ValuationSubring Ω) :
    Submodule R (H1 (rho.comp (Dec (F := F) A).subtype)) :=
  H1ur (rho.comp (Dec (F := F) A).subtype) ((Ine (F := F) A).subgroupOf (Dec (F := F) A))

def SelAll (rho : Representation R (G F Ω) M) (A : Places F Ω)
    (L : ∀ v, Submodule R (H1 (rho.comp (Dec (F := F) (A.1 v)).subtype))) : Submodule R (H1 rho) :=
  Sel rho (fun v => (Dec (F := F) (A.1 v)).subtype) (fun _ => continuous_subtype_val) L

def bkCond (rho : Representation R (G F Ω) M) (A : Places F Ω)
    (l : ℕ) (Sig : Set (HeightOneSpectrum (𝓞 F)))
    (Ll : ∀ v, Submodule R (H1 (rho.comp (Dec (F := F) (A.1 v)).subtype))) :
    ∀ v, Submodule R (H1 (rho.comp (Dec (F := F) (A.1 v)).subtype)) :=
  open Classical in
  fun v => if ((l : ℕ) : 𝓞 F) ∈ v.asIdeal then Ll v else if v ∈ Sig then ⊤ else unrAt rho (A.1 v)

def selLen (rho : Representation R (G F Ω) M) (A : Places F Ω)
    (l : ℕ) (Sig : Set (HeightOneSpectrum (𝓞 F)))
    (Ll : ∀ v, Submodule R (H1 (rho.comp (Dec (F := F) (A.1 v)).subtype))) : ℕ∞ :=
  Module.length R (SelAll rho A (bkCond rho A l Sig Ll))

end Sel

def InfUnram : Prop := ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
  (S : Set (HeightOneSpectrum (𝓞 F))) (R : Type) [CommRing R] (M : Type) [AddCommGroup M]
  [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [T2Space M]
  (rhoS : Representation R (GS Ω S) M), ContAction rhoS →
    Function.Injective (resH1 rhoS (toGS Ω S) (continuous_toGS Ω S)) ∧
    ∀ x : H1 (rhoS.comp (toGS Ω S)),
      x ∈ LinearMap.range (resH1 rhoS (toGS Ω S) (continuous_toGS Ω S)) ↔
        ∀ v ∉ S, ∀ A : ValuationSubring Ω, IsPlaceOver A v →
          resH1 (rhoS.comp (toGS Ω S)) (Ine (F := F) A).subtype continuous_subtype_val x = 0

end Formalism.GaloisCohomology
end
end


section
-- Source: Formalism/TameInertiaTowers/StatementGroup.lean

open Subgroup
open scoped commutatorElement

namespace Formalism.TwoAdicCyclotomicDecomposition

abbrev GalL (n : ℕ) : Type := (ZMod (2 ^ n))ˣ × ℤˣ × ℤˣ

def JJ (n : ℕ) : GalL n := (-1, -1, -1)

def D2 (n : ℕ) : Subgroup (GalL n) :=
  ((MonoidHom.snd ℤˣ ℤˣ).comp (MonoidHom.snd (ZMod (2 ^ n))ˣ (ℤˣ × ℤˣ))).ker

def I2 (n : ℕ) : Subgroup (GalL n) := (MonoidHom.snd (ZMod (2 ^ n))ˣ (ℤˣ × ℤˣ)).ker

def Iq (n : ℕ) : Subgroup (GalL n) := Subgroup.zpowers ((1, -1, 1) : GalL n)

def Id (n : ℕ) : Subgroup (GalL n) := Subgroup.zpowers ((1, 1, -1) : GalL n)

def u5 (n : ℕ) : (ZMod (2 ^ n))ˣ := ZMod.unitOfCoprime 5 (Nat.Coprime.pow_right n (by norm_num))

def u3 (n : ℕ) : (ZMod (2 ^ n))ˣ := ZMod.unitOfCoprime 3 (Nat.Coprime.pow_right n (by norm_num))

def resMap {s m : ℕ} (h : s ≤ m) : GalL (m + 2) →* GalL (s + 2) :=
  MonoidHom.prodMap (ZMod.unitsMap (pow_dvd_pow 2 (by omega))) (MonoidHom.id (ℤˣ × ℤˣ))

abbrev GamE (s : ℕ) : Type := GalL (s + 2) ⧸ Subgroup.zpowers ((-1, 1, 1) : GalL (s + 2))

def GG {s m : ℕ} (h : s ≤ m) : Subgroup (GalL (m + 2)) :=
  ((QuotientGroup.mk' (Subgroup.zpowers ((-1, 1, 1) : GalL (s + 2)))).comp (resMap h)).ker

def UnitsTwoPow : Prop :=
  ∀ n : ℕ,
    Nat.card (ZMod (2 ^ (n + 3)))ˣ = 2 ^ (n + 2) ∧
    orderOf (u5 (n + 3)) = 2 ^ (n + 1) ∧ orderOf (u3 (n + 3)) = 2 ^ (n + 1) ∧
    (-1 : (ZMod (2 ^ (n + 3)))ˣ) ∉ Subgroup.zpowers (u5 (n + 3)) ∧
    (-1 : (ZMod (2 ^ (n + 3)))ˣ) ∉ Subgroup.zpowers (u3 (n + 3)) ∧
    ∀ u : (ZMod (2 ^ (n + 3)))ˣ, ∃! p : Bool × Fin (2 ^ (n + 1)),
      u = (if p.1 then -1 else 1) * u5 (n + 3) ^ (p.2 : ℕ)

def QuotCyclic : Prop :=
  ∀ n : ℕ,
    IsCyclic ((ZMod (2 ^ (n + 2)))ˣ ⧸ Subgroup.zpowers (-1 : (ZMod (2 ^ (n + 2)))ˣ)) ∧
    Nat.card ((ZMod (2 ^ (n + 2)))ˣ ⧸ Subgroup.zpowers (-1 : (ZMod (2 ^ (n + 2)))ˣ)) = 2 ^ n ∧
    orderOf (QuotientGroup.mk (s := Subgroup.zpowers (-1 : (ZMod (2 ^ (n + 2)))ˣ))
      (u5 (n + 2))) = 2 ^ n ∧
    orderOf (QuotientGroup.mk (s := Subgroup.zpowers (-1 : (ZMod (2 ^ (n + 2)))ˣ))
      (u3 (n + 2))) = 2 ^ n

def TwoAdicOrder : Prop :=
  ∀ (N : ℕ) (a : ℤ), Odd a → a ^ 2 ≠ 1 →
    orderOf (a : ZMod (2 ^ N)) =
      if (a : ZMod (2 ^ N)) = 1 then 1 else 2 ^ max 1 (N + 1 - padicValInt 2 (a ^ 2 - 1))

def TwoAdicVal : Prop :=
  ∀ (a : ℤ), Odd a → a ^ 2 ≠ 1 → ∀ e : ℕ, 0 < e →
    padicValInt 2 (a ^ e - 1) =
      (if Even e then padicValInt 2 (a ^ 2 - 1) + padicValNat 2 e - 1
        else padicValInt 2 (a - 1)) ∧
    padicValInt 2 (a ^ e - 1) ≤ padicValInt 2 (a ^ 2 - 1) + Nat.log 2 e

def DecompModel : Prop :=
  ∀ n : ℕ, JJ n ∉ D2 n ∧ (D2 n).index = 2 ∧
    Function.Bijective (fun x : D2 n =>
      (QuotientGroup.mk (x : GalL n) : GalL n ⧸ Subgroup.zpowers (JJ n)))

def GmRank : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    Nat.card (GalL n ⧸ Subgroup.zpowers (JJ n)) = 2 ^ n ∧
    Nat.card ((GalL n ⧸ Subgroup.zpowers (JJ n)) ⧸
      (powMonoidHom 2 : (GalL n ⧸ Subgroup.zpowers (JJ n)) →* _).range) ≤ 8 ∧
    (3 ≤ n → Nat.card ((GalL n ⧸ Subgroup.zpowers (JJ n)) ⧸
      (powMonoidHom 2 : (GalL n ⧸ Subgroup.zpowers (JJ n)) →* _).range) = 8)

def GensModel : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    I2 n ⊔ Iq n ⊔ Id n = ⊤ ∧
    I2 n = Subgroup.closure {((-1, 1, 1) : GalL n), ((u5 n, 1, 1) : GalL n)} ∧
    Nat.card (Iq n) = 2 ∧ Nat.card (Id n) = 2 ∧
    Subgroup.closure {((-1, 1, 1) : GalL n), ((u5 n, 1, 1) : GalL n),
      ((1, -1, 1) : GalL n), ((1, 1, -1) : GalL n)} = ⊤

def GamEModel : Prop :=
  ∀ s : ℕ,
    Nat.card (GamE s) = 2 ^ (s + 2) ∧
    Nonempty (GamE s ≃* Multiplicative (ZMod (2 ^ s)) × ℤˣ × ℤˣ) ∧
    (QuotientGroup.mk (JJ (s + 2)) : GamE s) = QuotientGroup.mk ((1, -1, -1) : GalL (s + 2)) ∧
    orderOf (QuotientGroup.mk (JJ (s + 2)) : GamE s) = 2

def GGModel : Prop :=
  ∀ (s m : ℕ) (h : s ≤ m),
    Nat.card (GG h) = 2 ^ (m - s + 1) ∧
    Nonempty (GG h ≃* ℤˣ × Multiplicative (ZMod (2 ^ (m - s)))) ∧
    GG h = Subgroup.closure {((-1, 1, 1) : GalL (m + 2)), ((u5 (m + 2) ^ (2 ^ s), 1, 1) : GalL (m + 2))}

def CentralExtAbelian : Prop :=
  ∀ (H G : Type) [Group H] [CommGroup G] (π : H →* G), Function.Surjective π →
    π.ker ≤ Subgroup.center H → ∀ D : Subgroup H, D.map π = ⊤ →
    (D ⊓ π.ker = ⊥ ∨ (D = ⊤ ∧ ∀ x ∈ D, ∀ y ∈ D, x * y = y * x)) →
    ∀ x y : H, x * y = y * x

def CommGen : Prop :=
  ∀ (H : Type) [Group H] (g : Fin 4 → H),
    Subgroup.closure (Set.range g) = ⊤ → commutator H ≤ Subgroup.center H →
    g 0 * g 1 = g 1 * g 0 →
    commutator H = Subgroup.closure
      {⁅g 0, g 2⁆, ⁅g 0, g 3⁆, ⁅g 1, g 2⁆, ⁅g 1, g 3⁆, ⁅g 2, g 3⁆} ∧
    ((∀ x ∈ commutator H, x ^ 2 = 1) → Nat.card (commutator H) ≤ 2 ^ 5)

def RankBound : Prop :=
  ∀ r : ℕ, 1 ≤ r → (r * (r - 1) / 2 ≤ 3 + (r - 1) ↔ r ≤ 4)

def NormalOrderTwoCentral : Prop :=
  ∀ (H : Type) [Group H] (N : Subgroup H), N.Normal → Nat.card N = 2 → N ≤ Subgroup.center H

def TwistVal : Prop :=
  ∀ s e : ℕ, 0 < e → padicValInt 2 ((5 : ℤ) ^ (2 ^ s * e) - 1) = s + 2 + padicValNat 2 e

def CoinvLength : Prop :=
  ∀ (N : ℕ) (u : ℤ), Odd u → u ≠ 1 →
    Nat.card (ZMod (2 ^ N) ⧸ AddSubgroup.zmultiples (((u - 1 : ℤ)) : ZMod (2 ^ N))) =
      2 ^ min N (padicValInt 2 (u - 1))

def PGroupGen : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (H : Type) [Group H] [Finite H], IsPGroup p H →
    ∀ S : Set H, Subgroup.normalClosure S = ⊤ → Subgroup.closure S = ⊤

def GenusModel : Prop :=
  ∀ n : ℕ, JJ n = ((-1, 1, 1) : GalL n) * ((1, -1, 1) : GalL n) * ((1, 1, -1) : GalL n) ∧
    ((-1, 1, 1) : GalL n) ∈ I2 n ∧ ((1, -1, 1) : GalL n) ∈ Iq n ∧
    ((1, 1, -1) : GalL n) ∈ Id n ∧ ((1, -1, 1) : GalL n) ≠ 1

def GenusAbelian : Prop :=
  ∀ (G : Type) [CommGroup G] [Finite G] (A B C : Subgroup G), A ⊔ B ⊔ C = ⊤ →
    Nat.card G = Nat.card A * Nat.card B * Nat.card C →
    ∀ a ∈ A, ∀ b ∈ B, ∀ c ∈ C, a * b * c = 1 → a = 1 ∧ b = 1 ∧ c = 1

end Formalism.TwoAdicCyclotomicDecomposition
end


section
-- Source: Formalism/TameInertiaTowers/StatementField.lean

open NumberField Ideal
open scoped Pointwise

noncomputable section

namespace Formalism.TwoAdicCyclotomicDecomposition

def IsLayer (n q d : ℕ) {L : Type*} [Field L] [Algebra ℚ L] (ζ a b : L) : Prop :=
  IsPrimitiveRoot ζ (2 ^ n) ∧ a ^ 2 = -(q : L) ∧ b ^ 2 = -(d : L) ∧
    IntermediateField.adjoin ℚ {ζ, a, b} = ⊤

open Classical in

def sgn {L : Type*} [Field L] [Algebra ℚ L] (σ : Gal(L/ℚ)) (x : L) : ℤˣ :=
  if σ x = x then 1 else -1

def galMap {n : ℕ} {L : Type*} [Field L] [Algebra ℚ L] {ζ : L} (hζ : IsPrimitiveRoot ζ (2 ^ n))
    (a b : L) (σ : Gal(L/ℚ)) : GalL n :=
  (hζ.autToPow ℚ σ, sgn σ a, sgn σ b)

def HypOdd (q d : ℕ) : Prop := q.Prime ∧ d.Prime ∧ q ≠ d ∧ q ≠ 2 ∧ d ≠ 2

def HypQD (q d : ℕ) : Prop := q.Prime ∧ d.Prime ∧ q % 8 = 3 ∧ d % 8 = 7

theorem HypQD.toHypOdd {q d : ℕ} (h : HypQD q d) : HypOdd q d := by
  obtain ⟨hq, hd, h3, h7⟩ := h
  refine ⟨hq, hd, ?_, ?_, ?_⟩ <;> omega

def LayerExists : Prop :=
  ∀ n q d : ℕ, ∃ (L : Type) (_ : Field L) (_ : NumberField L) (ζ a b : L), IsLayer n q d ζ a b

def LayerGalois : Prop :=
  ∀ (n q d : ℕ), 1 ≤ n → HypOdd q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L) (h : IsLayer n q d ζ a b),
    IsGalois ℚ L ∧ Module.finrank ℚ L = 2 ^ (n + 1) ∧
    (∀ σ τ : Gal(L/ℚ), galMap h.1 a b (σ * τ) = galMap h.1 a b σ * galMap h.1 a b τ) ∧
    Function.Bijective (galMap h.1 a b)

def LayerConj : Prop :=
  ∀ (n q d : ℕ), 1 ≤ n → HypOdd q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L) (h : IsLayer n q d ζ a b)
    (φ : L →+* ℂ) (σ : Gal(L/ℚ)),
    (∀ x : L, φ (σ x) = starRingEnd ℂ (φ x)) ↔ galMap h.1 a b σ = JJ n

def LayerReal : Prop :=
  ∀ (n q d : ℕ), 1 ≤ n → HypOdd q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L) (h : IsLayer n q d ζ a b),
    IsCMField L ∧
    (∀ x : L, x ∈ maximalRealSubfield L ↔
      ∀ σ : Gal(L/ℚ), galMap h.1 a b σ = JJ n → σ x = x) ∧
    Module.finrank ℚ (maximalRealSubfield L) = 2 ^ n

def LayerDecompTwo : Prop :=
  ∀ (n q d : ℕ), 1 ≤ n → HypQD q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L) (h : IsLayer n q d ζ a b)
    (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (span {(2 : ℤ)})] (σ : Gal(L/ℚ)),
    σ ∈ MulAction.stabilizer Gal(L/ℚ) P ↔ galMap h.1 a b σ ∈ D2 n

def LayerInertiaTwo : Prop :=
  ∀ (n q d : ℕ), 1 ≤ n → HypQD q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L) (h : IsLayer n q d ζ a b)
    (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (span {(2 : ℤ)})] (σ : Gal(L/ℚ)),
    (∀ x : 𝓞 L, σ • x - x ∈ P) ↔ galMap h.1 a b σ ∈ I2 n

def LayerInertiaTame : Prop :=
  ∀ (n q d : ℕ), 1 ≤ n → HypOdd q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L) (h : IsLayer n q d ζ a b),
    (∀ (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (span {(q : ℤ)})] (σ : Gal(L/ℚ)),
      (∀ x : 𝓞 L, σ • x - x ∈ P) ↔ galMap h.1 a b σ ∈ Iq n) ∧
    (∀ (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (span {(d : ℤ)})] (σ : Gal(L/ℚ)),
      (∀ x : 𝓞 L, σ • x - x ∈ P) ↔ galMap h.1 a b σ ∈ Id n)

def LayerFrob : Prop :=
  ∀ (n q d : ℕ), 1 ≤ n → HypOdd q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L) (h : IsLayer n q d ζ a b)
    (p : ℕ) [Fact p.Prime], p ≠ 2 → p ≠ q → p ≠ d →
    ∀ (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})],
      (∃ σ : Gal(L/ℚ), IsArithFrobAt ℤ σ P) ∧
      ∀ σ : Gal(L/ℚ), IsArithFrobAt ℤ σ P ↔
        (((galMap h.1 a b σ).1 : ZMod (2 ^ n)) = (p : ZMod (2 ^ n)) ∧
          (((galMap h.1 a b σ).2.1 : ℤˣ) : ℤ) = jacobiSym (-(q : ℤ)) p ∧
          (((galMap h.1 a b σ).2.2 : ℤˣ) : ℤ) = jacobiSym (-(d : ℤ)) p)

def LayerEFGTwo : Prop :=
  ∀ (n q d : ℕ), 1 ≤ n → HypQD q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L), IsLayer n q d ζ a b →
    (span {(2 : ℤ)}).ramificationIdxIn (𝓞 L) = 2 ^ (n - 1) ∧
    (span {(2 : ℤ)}).inertiaDegIn (𝓞 L) = 2 ∧
    (primesOver (span {(2 : ℤ)}) (𝓞 L)).ncard = 2 ∧
    (primesOver (span {(2 : ℤ)}) (𝓞 (maximalRealSubfield L))).ncard = 1 ∧
    (span {(2 : ℤ)}).ramificationIdxIn (𝓞 (maximalRealSubfield L)) = 2 ^ (n - 1) ∧
    (span {(2 : ℤ)}).inertiaDegIn (𝓞 (maximalRealSubfield L)) = 2

end Formalism.TwoAdicCyclotomicDecomposition
end
end


section
-- Source: Formalism/FrobeniusOrbits/Statement.lean

open NumberField IntermediateField Ideal
open scoped Pointwise

noncomputable section

namespace Formalism.FrobeniusOrbits

open Formalism.TwoAdicCyclotomicDecomposition

def HostHyp (q d : ℕ) : Prop :=
  q.Prime ∧ d.Prime ∧ q % 8 = 3 ∧ d % 16 = 7 ∧ jacobiSym (-(d : ℤ)) q = 1

theorem HostHyp.toHypQD {q d : ℕ} (h : HostHyp q d) : HypQD q d := by
  obtain ⟨h1, h2, h3, h4, -⟩ := h
  exact ⟨h1, h2, h3, by omega⟩

theorem HostHyp.toHypOdd {q d : ℕ} (h : HostHyp q d) : HypOdd q d := by
  obtain ⟨h1, h2, h3, h4, -⟩ := h
  exact ⟨h1, h2, by omega, by omega, by omega⟩

abbrev HGrp (e : ℕ) : Type :=
  (ZMod (2 ^ (e + 2)))ˣ ⧸ Subgroup.zpowers (-1 : (ZMod (2 ^ (e + 2)))ˣ)

abbrev G0 : Type := ℤˣ × ℤˣ

abbrev GG (e : ℕ) : Type := G0 × HGrp e

def hcl (e : ℕ) (u : (ZMod (2 ^ (e + 2)))ˣ) : HGrp e := QuotientGroup.mk u

def sg (e : ℕ) : GG e := ((-1, 1), 1)

def c0 : G0 := (-1, -1)

def cc (e : ℕ) : GG e := (c0, 1)

def chD (e : ℕ) : GG e →* ℤˣ := (MonoidHom.snd ℤˣ ℤˣ).comp (MonoidHom.fst G0 (HGrp e))

def chQ (e : ℕ) : GG e →* ℤˣ := (MonoidHom.fst ℤˣ ℤˣ).comp (MonoidHom.fst G0 (HGrp e))

def Psi (e : ℕ) : Subgroup (GG e) := (chD e).ker

theorem mem_Psi_iff {e : ℕ} (g : GG e) : g ∈ Psi e ↔ g.1.2 = 1 := by
  rw [Psi, MonoidHom.mem_ker]
  rfl

section Fields

variable {L : Type*} [Field L] [Algebra ℚ L]

def F1 (ζ : L) : IntermediateField ℚ L := ℚ⟮ζ + ζ⁻¹⟯

def Kd (b : L) : IntermediateField ℚ L := ℚ⟮b⟯

def E0 (a b : L) : IntermediateField ℚ L := ℚ⟮a, b⟯

def hostE (ζ a b : L) : IntermediateField ℚ L := E0 a b ⊔ F1 ζ

theorem theta_mem (ζ a b : L) : ζ + ζ⁻¹ ∈ hostE ζ a b := (le_sup_right : F1 ζ ≤ E0 a b ⊔ F1 ζ) (mem_adjoin_simple_self ℚ _)

theorem a_mem (ζ a b : L) : a ∈ hostE ζ a b := (le_sup_left : E0 a b ≤ E0 a b ⊔ F1 ζ) (subset_adjoin ℚ _ (by simp))

theorem b_mem (ζ a b : L) : b ∈ hostE ζ a b := (le_sup_left : E0 a b ≤ E0 a b ⊔ F1 ζ) (subset_adjoin ℚ _ (by simp))

def thE (ζ a b : L) : hostE ζ a b := ⟨ζ + ζ⁻¹, theta_mem ζ a b⟩

def aE (ζ a b : L) : hostE ζ a b := ⟨a, a_mem ζ a b⟩

def bE (ζ a b : L) : hostE ζ a b := ⟨b, b_mem ζ a b⟩

abbrev hostF (ζ a b : L) : Subfield (hostE ζ a b) := maximalRealSubfield (hostE ζ a b)

open Classical in

def hPart (e : ℕ) (ζ a b : L) (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) : HGrp e :=
  if h : ∃ u : (ZMod (2 ^ (e + 2)))ˣ,
      ((σ (thE ζ a b) : hostE ζ a b) : L) =
        ζ ^ (u : ZMod (2 ^ (e + 2))).val + ζ⁻¹ ^ (u : ZMod (2 ^ (e + 2))).val
  then hcl e (Classical.choose h) else 1

def galE (e : ℕ) (ζ a b : L) (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) : GG e :=
  ((sgn σ (aE ζ a b), sgn σ (bE ζ a b)), hPart e ζ a b σ)

def cmType (ζ a b : L) (d : ℕ) : Set (hostE ζ a b →+* ℂ) :=
  {φ | φ (bE ζ a b) = Complex.I * (Real.sqrt d : ℂ)}

end Fields

def HostExample : Prop :=
  HostHyp 11 7 ∧ ∀ e : ℕ, ∃ (L : Type) (_ : Field L) (_ : NumberField L) (ζ a b : L),
    IsLayer (e + 2) 11 7 ζ a b

def HostGroup : Prop :=
  ∀ e : ℕ,
    Nat.card (GG e) = 2 ^ (e + 2) ∧ (Psi e).index = 2 ∧ cc e ∉ Psi e ∧ sg e ∈ Psi e ∧
    orderOf (cc e) = 2 ∧
    IsCyclic (HGrp e) ∧ Nat.card (HGrp e) = 2 ^ e ∧ orderOf (hcl e (u5 (e + 2))) = 2 ^ e ∧
    ∃ ι : Multiplicative (ZMod (2 ^ e)) ≃* HGrp e,
      ι (Multiplicative.ofAdd 1) = hcl e (u5 (e + 2))

def HostOrders : Prop :=
  ∀ e : ℕ,
    (∀ (j : ℕ) (l : ℤ) (u : (ZMod (2 ^ (e + 2)))ˣ), ((u : ZMod (2 ^ (e + 2))) = (l : ZMod _)) →
      (orderOf (hcl e u) ≤ 2 ^ j ↔
        ((l : ZMod (2 ^ (e + 2 - j))) = 1 ∨ (l : ZMod (2 ^ (e + 2 - j))) = -1))) ∧
    ∀ g : GG e, cc e ∈ Subgroup.zpowers g ↔ g = cc e

def HostRecip : Prop := ∀ q d : ℕ, HostHyp q d → jacobiSym (-(q : ℤ)) d = -1

def HostFixed : Prop :=
  ∀ (e q d : ℕ), HypOdd q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L) (h : IsLayer (e + 2) q d ζ a b),
    hostE ζ a b = ℚ⟮ζ + ζ⁻¹, a, b⟯ ∧
    ∀ x : L, x ∈ hostE ζ a b ↔
      ∀ τ : L ≃ₐ[ℚ] L, galMap h.1 a b τ = ((-1, 1, 1) : GalL (e + 2)) → τ x = x

def HostGalois : Prop :=
  ∀ (e q d : ℕ), HypOdd q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L), IsLayer (e + 2) q d ζ a b →
    IsGalois ℚ (hostE ζ a b) ∧ Module.finrank ℚ (hostE ζ a b) = 2 ^ (e + 2) ∧
    (∀ σ τ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b,
      galE e ζ a b (σ * τ) = galE e ζ a b σ * galE e ζ a b τ) ∧
    Function.Bijective (galE e ζ a b)

def HostGalSpec : Prop :=
  ∀ (e q d : ℕ), HypOdd q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L) (h : IsLayer (e + 2) q d ζ a b)
    (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b),
    ((σ (aE ζ a b) : L) = ((((galE e ζ a b σ).1.1 : ℤˣ) : ℤ) : L) * a) ∧
    ((σ (bE ζ a b) : L) = ((((galE e ζ a b σ).1.2 : ℤˣ) : ℤ) : L) * b) ∧
    (∀ u : (ZMod (2 ^ (e + 2)))ˣ, (galE e ζ a b σ).2 = hcl e u ↔
      ((σ (thE ζ a b) : hostE ζ a b) : L) =
        ζ ^ (u : ZMod (2 ^ (e + 2))).val + ζ⁻¹ ^ (u : ZMod (2 ^ (e + 2))).val) ∧
    ∀ τ : L ≃ₐ[ℚ] L, (∀ x : hostE ζ a b, ((σ x : hostE ζ a b) : L) = τ x) →
      galE e ζ a b σ =
        (((galMap h.1 a b τ).2.1, (galMap h.1 a b τ).2.2), hcl e (galMap h.1 a b τ).1)

def HostConj : Prop :=
  ∀ (e q d : ℕ), HypOdd q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L), IsLayer (e + 2) q d ζ a b →
    IsCMField (hostE ζ a b) ∧
    ∀ (φ : hostE ζ a b →+* ℂ) (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b),
      (∀ x, φ (σ x) = starRingEnd ℂ (φ x)) ↔ galE e ζ a b σ = cc e

def HostReal : Prop :=
  ∀ (e q d : ℕ), HypOdd q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L), IsLayer (e + 2) q d ζ a b →
    Module.finrank ℚ (hostF ζ a b) = 2 ^ (e + 1) ∧
    ∀ x : hostE ζ a b,
      (x ∈ hostF ζ a b ↔
        ∀ σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b, galE e ζ a b σ = cc e → σ x = x) ∧
      (x ∈ hostF ζ a b ↔ (x : L) ∈ ℚ⟮a * b, ζ + ζ⁻¹⟯)

def TwoPowerCyclotomicLayerRealSubfieldCharacterization : Prop :=
  ∀ (e q d : ℕ), HypOdd q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L), IsLayer (e + 2) q d ζ a b →
    IsCyclotomicExtension {2 ^ (e + 2)} ℚ ℚ⟮ζ⟯ ∧
    (∀ x : ℚ⟮ζ⟯, x ∈ maximalRealSubfield ℚ⟮ζ⟯ ↔ (x : L) ∈ F1 ζ) ∧
    Module.finrank ℚ (F1 ζ) = 2 ^ e ∧
    (∀ x ∈ F1 ζ, ∀ φ : L →+* ℂ, starRingEnd ℂ (φ x) = φ x) ∧
    ∀ σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b,
      (galE e ζ a b σ).2 = 1 ↔ ∀ x : hostE ζ a b, (x : L) ∈ F1 ζ → σ x = x

def HostMu : Prop :=
  ∀ (e q d : ℕ), HostHyp q d → q ≠ 3 →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L), IsLayer (e + 2) q d ζ a b →
    ∀ x : hostE ζ a b, (∃ m : ℕ, 0 < m ∧ x ^ m = 1) → x = 1 ∨ x = -1

def HostFrob : Prop :=
  ∀ (e q d : ℕ), HypOdd q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L), IsLayer (e + 2) q d ζ a b →
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → p ≠ q → p ≠ d →
  ∀ (P : Ideal (𝓞 (hostE ζ a b))) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})],
    (∃ σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b, IsArithFrobAt ℤ σ P) ∧
    (∀ σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b, IsArithFrobAt ℤ σ P ↔
      ((((galE e ζ a b σ).1.1 : ℤˣ) : ℤ) = jacobiSym (-(q : ℤ)) p ∧
        (((galE e ζ a b σ).1.2 : ℤˣ) : ℤ) = jacobiSym (-(d : ℤ)) p ∧
        ∃ u : (ZMod (2 ^ (e + 2)))ˣ, (u : ZMod (2 ^ (e + 2))) = (p : ZMod _) ∧
          (galE e ζ a b σ).2 = hcl e u)) ∧
    ∀ σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b, (∀ x : 𝓞 (hostE ζ a b), σ • x - x ∈ P) ↔ σ = 1

def HostInertia : Prop :=
  ∀ (e q d : ℕ), HostHyp q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L), IsLayer (e + 2) q d ζ a b →
  ∀ (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b),
    (∀ (P : Ideal (𝓞 (hostE ζ a b))) [P.IsPrime] [P.LiesOver (span {(2 : ℤ)})],
      (∀ x : 𝓞 (hostE ζ a b), σ • x - x ∈ P) ↔ (galE e ζ a b σ).1 = 1) ∧
    (∀ (P : Ideal (𝓞 (hostE ζ a b))) [P.IsPrime] [P.LiesOver (span {(q : ℤ)})],
      (∀ x : 𝓞 (hostE ζ a b), σ • x - x ∈ P) ↔ (galE e ζ a b σ = 1 ∨ galE e ζ a b σ = sg e)) ∧
    (∀ (P : Ideal (𝓞 (hostE ζ a b))) [P.IsPrime] [P.LiesOver (span {(d : ℤ)})],
      (∀ x : 𝓞 (hostE ζ a b), σ • x - x ∈ P) ↔
        (galE e ζ a b σ = 1 ∨ galE e ζ a b σ = ((1, -1), 1)))

def HostUnramEF : Prop :=
  ∀ (e q d : ℕ), HostHyp q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L), IsLayer (e + 2) q d ζ a b →
  ∀ (P : Ideal (𝓞 (hostE ζ a b))), P.IsPrime → P ≠ ⊥ →
  ∀ σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b, galE e ζ a b σ = cc e →
    ¬ ∀ x : 𝓞 (hostE ζ a b), σ • x - x ∈ P

def HostDecomp : Prop :=
  ∀ (e q d : ℕ), HostHyp q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L), IsLayer (e + 2) q d ζ a b →
  ∀ (uq ud : (ZMod (2 ^ (e + 2)))ˣ), (uq : ZMod (2 ^ (e + 2))) = (q : ZMod _) →
    (ud : ZMod (2 ^ (e + 2))) = (d : ZMod _) →
  ∀ (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b),
    (∀ (P : Ideal (𝓞 (hostE ζ a b))) [P.IsPrime] [P.LiesOver (span {(2 : ℤ)})],
      σ ∈ MulAction.stabilizer _ P ↔ galE e ζ a b σ ∈ Psi e) ∧
    (∀ (P : Ideal (𝓞 (hostE ζ a b))) [P.IsPrime] [P.LiesOver (span {(q : ℤ)})],
      σ ∈ MulAction.stabilizer _ P ↔
        ((galE e ζ a b σ).1.2 = 1 ∧ ∃ k : ℕ, (galE e ζ a b σ).2 = hcl e uq ^ k)) ∧
    (∀ (P : Ideal (𝓞 (hostE ζ a b))) [P.IsPrime] [P.LiesOver (span {(d : ℤ)})],
      σ ∈ MulAction.stabilizer _ P ↔
        ∃ k : ℕ, (galE e ζ a b σ).1.1 = (-1) ^ k ∧ (galE e ζ a b σ).2 = hcl e ud ^ k)

def HostDecompConj : Prop :=
  ∀ (e q d : ℕ), HostHyp q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L), IsLayer (e + 2) q d ζ a b →
  ∀ (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b), galE e ζ a b σ = cc e →
  ∀ (p : ℕ), (p = 2 ∨ p = q ∨ (p = d ∧ 2 ≤ e)) →
  ∀ (P : Ideal (𝓞 (hostE ζ a b))) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})],
    σ ∉ MulAction.stabilizer _ P

def HostEFGTwo : Prop :=
  ∀ (e q d : ℕ), HostHyp q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L), IsLayer (e + 2) q d ζ a b →
    (span {(2 : ℤ)}).ramificationIdxIn (𝓞 (hostE ζ a b)) = 2 ^ e ∧
    (span {(2 : ℤ)}).inertiaDegIn (𝓞 (hostE ζ a b)) = 2 ∧
    (primesOver (span {(2 : ℤ)}) (𝓞 (hostE ζ a b))).ncard = 2 ∧
    (primesOver (span {(2 : ℤ)}) (𝓞 (hostF ζ a b))).ncard = 1 ∧
    (span {(2 : ℤ)}).ramificationIdxIn (𝓞 (hostF ζ a b)) = 2 ^ e ∧
    (span {(2 : ℤ)}).inertiaDegIn (𝓞 (hostF ζ a b)) = 2

def HostSplitK : Prop :=
  ∀ (e q d : ℕ), HostHyp q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L), IsLayer (e + 2) q d ζ a b →
    (∀ p : ℕ, p.Prime →
      ((primesOver (span {(p : ℤ)}) (𝓞 (Kd b))).ncard = 2 ↔
        (p = 2 ∨ (p ≠ 2 ∧ jacobiSym (-(d : ℤ)) p = 1)))) ∧
    (primesOver (span {(d : ℤ)}) (𝓞 (Kd b))).ncard = 1 ∧
    (primesOver (span {(q : ℤ)}) (𝓞 (Kd b))).ncard = 2 ∧
    ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → p ≠ q → p ≠ d →
    ∀ (P : Ideal (𝓞 (hostE ζ a b))) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})]
      (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b), IsArithFrobAt ℤ σ P →
      (galE e ζ a b σ ∈ Psi e ↔ (primesOver (span {(p : ℤ)}) (𝓞 (Kd b))).ncard = 2)

def HostCMType : Prop :=
  ∀ (e q d : ℕ), HypOdd q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L), IsLayer (e + 2) q d ζ a b →
    (∀ φ : hostE ζ a b →+* ℂ,
      φ ∈ cmType ζ a b d ↔ (starRingEnd ℂ).comp φ ∉ cmType ζ a b d) ∧
    (cmType ζ a b d).ncard = 2 ^ (e + 1) ∧
    ∀ φ ∈ cmType ζ a b d, ∀ σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b,
      φ.comp (σ : hostE ζ a b →+* hostE ζ a b) ∈ cmType ζ a b d ↔ galE e ζ a b σ ∈ Psi e

end Formalism.FrobeniusOrbits
end
end


section
-- Source: Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ZsmulGeneratorEqZeroOfProjection.lean

noncomputable section

namespace Formalism.HC

open Formalism.FrobeniusOrbits

def Idx (n : ℕ) : Type := Fin n

instance (n : ℕ) : Fintype (Idx n) := inferInstanceAs (Fintype (Fin n))
instance (n : ℕ) : DecidableEq (Idx n) := inferInstanceAs (DecidableEq (Fin n))

structure Frame where
  e : ℕ

  ord : ℕ
  grp : AddCommGroup (Idx ord)
  h0 : letI := grp; Idx ord →+ Additive (HGrp e)
  projection_surjective_field : Function.Surjective h0
  gen0 : Idx ord
  zsmul_generator_eq_zero_of_projection : letI := grp; ∀ k : ℤ, h0 (k • gen0) = 0 → k • gen0 = 0

namespace Frame

variable (φ : Frame)

def A : Type := Idx φ.ord

instance : AddCommGroup φ.A := φ.grp
instance : Fintype φ.A := inferInstanceAs (Fintype (Idx φ.ord))
instance : DecidableEq φ.A := inferInstanceAs (DecidableEq (Idx φ.ord))

def A.val {φ : Frame} (t : φ.A) : ℕ := Fin.val (n := φ.ord) t

theorem A.val_lt {φ : Frame} (t : φ.A) : t.val < φ.ord := by
  exact Fin.is_lt (n := φ.ord) t

theorem A.val_injective (φ : Frame) : Function.Injective (A.val : φ.A → ℕ) := by
  exact fun s t h => Fin.ext h

def A.ofVal {φ : Frame} (u : ℕ) (hu : u < φ.ord) : φ.A := (⟨u, hu⟩ : Fin φ.ord)

@[simp] theorem A.val_ofVal {φ : Frame} (u : ℕ) (hu : u < φ.ord) : (A.ofVal u hu : φ.A).val = u := rfl

theorem card_A : Fintype.card φ.A = φ.ord := by
  exact Fintype.card_fin φ.ord

theorem natCard_A : Nat.card φ.A = φ.ord := by
  rw [Nat.card_eq_fintype_card, card_A]

theorem ord_pos : 0 < φ.ord := by
  exact Fin.pos (n := φ.ord) (0 : φ.A)

def h : φ.A →+ Additive (HGrp φ.e) := φ.h0

theorem h_surj : Function.Surjective φ.h := by
  exact φ.projection_surjective_field

def a0 : φ.A := φ.gen0

def A0 : AddSubgroup φ.A := AddSubgroup.zmultiples φ.a0

theorem zsmul_generator_eq_zero_of_image (k : ℤ) (hk : φ.h (k • φ.a0) = 0) : k • φ.a0 = 0 := by
  exact φ.zsmul_generator_eq_zero_of_projection k hk

def n0 : ℕ := addOrderOf φ.a0

def o : ℕ := φ.ord / φ.n0

def dig (s : ℕ) : φ.A := s • φ.a0

theorem dig_def (s : ℕ) : φ.dig s = s • φ.a0 := rfl

def ofNat (u : ℕ) : φ.A := A.ofVal (u % φ.ord) (Nat.mod_lt _ φ.ord_pos)

theorem val_ofNat (u : ℕ) : (φ.ofNat u).val = u % φ.ord := rfl

theorem val_ofNat_of_lt {u : ℕ} (hu : u < φ.ord) : (φ.ofNat u).val = u := by
  rw [φ.val_ofNat u, Nat.mod_eq_of_lt hu]

@[simp] theorem ofNat_val (t : φ.A) : φ.ofNat t.val = t := by
  apply A.val_injective φ
  rw [φ.val_ofNat, Nat.mod_eq_of_lt (A.val_lt t)]

abbrev MA : Type := Multiplicative φ.A

abbrev GG : Type := G0 × φ.MA

def hH : φ.MA →* HGrp φ.e where
  toFun a := (φ.h a.toAdd).toMul
  map_one' := by simp
  map_mul' a b := by simp

def iota (t : φ.A) : φ.MA := Multiplicative.ofAdd t

def iotaInv (a : φ.MA) : φ.A := a.toAdd

def sg : φ.GG := ((-1, 1), 1)

def cc : φ.GG := (c0, 1)

def iod : φ.GG := ((1, -1), 1)

def chD : φ.GG →* ℤˣ := (MonoidHom.snd ℤˣ ℤˣ).comp (MonoidHom.fst G0 φ.MA)

def chQ : φ.GG →* ℤˣ := (MonoidHom.fst ℤˣ ℤˣ).comp (MonoidHom.fst G0 φ.MA)

def chC : φ.GG →* ℂˣ := (Units.map (Int.castRingHom ℂ).toMonoidHom).comp φ.chD

def Psi : Subgroup φ.GG := φ.chD.ker

theorem mem_Psi_iff {φ : Frame} (g : φ.GG) : g ∈ φ.Psi ↔ g.1.2 = 1 := by
  rw [Frame.Psi, MonoidHom.mem_ker]
  rfl

def placeOf {φ : Frame} (g : φ.GG) : φ.GG := if g.1.2 = 1 then g else φ.cc * g

def tau1 (t : φ.A) : φ.GG := ((1, 1), φ.iota t)

def tau2 (t : φ.A) : φ.GG := ((-1, 1), φ.iota t)

def TwoGroup : Prop := ∃ j : ℕ, φ.ord = 2 ^ j

theorem iota_add (s t : φ.A) : φ.iota (s + t) = φ.iota s * φ.iota t := rfl

theorem iota_zero : φ.iota 0 = 1 := rfl

@[simp] theorem iotaInv_iota (t : φ.A) : φ.iotaInv (φ.iota t) = t := rfl

@[simp] theorem iota_iotaInv (a : φ.MA) : φ.iota (φ.iotaInv a) = a := rfl

theorem iota_bijective : Function.Bijective φ.iota := by
  exact Multiplicative.ofAdd.bijective

theorem natCard_GG : Nat.card φ.GG = 4 * φ.ord := by
  show Nat.card (G0 × φ.MA) = _
  rw [Nat.card_prod]
  have h0 : Nat.card G0 = 4 := by
    show Nat.card (ℤˣ × ℤˣ) = 4
    rw [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_units_int]
  have h2 : Nat.card φ.MA = φ.ord := φ.natCard_A
  rw [h0, h2]

end Frame

end Formalism.HC

end
end


section
-- Source: Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ConjEMemHostFIff.lean

open NumberField IntermediateField Ideal
open scoped Pointwise

noncomputable section

namespace Formalism.HC

open Formalism.FrobeniusOrbits

structure HostRaw (φ : Frame) where
  q : ℕ
  d : ℕ

  QS : ℕ
  hyp : HostHyp q d
  two_le_e : 2 ≤ φ.e
  QS_pos : 0 < QS
  tower_dvd : 2 ^ (φ.e + 2) ∣ QS
  QS_coprime : Nat.Coprime QS (q * d)
  QS_split : ∀ l : ℕ, l.Prime → l ≠ 2 → l ∣ QS → jacobiSym (-(d : ℤ)) l = 1
  E : Type
  [instField : Field E]
  [instNF : NumberField E]
  galois : IsGalois ℚ E
  gal : (E ≃ₐ[ℚ] E) ≃* φ.GG

  sqd : E
  sqd_sq : sqd ^ 2 = -(d : E)
  gal_sqd : ∀ σ : E ≃ₐ[ℚ] E, σ sqd = ((((gal σ).1.2 : ℤˣ) : ℤ) : E) * sqd

  cycEmb : E →ₐ[ℚ] CyclotomicField (QS * q * d) ℚ
  cycZeta : CyclotomicField (QS * q * d) ℚ
  cycZeta_prim : IsPrimitiveRoot cycZeta (QS * q * d)

  art : (ZMod (QS * q * d))ˣ →* φ.GG
  art_spec : ∀ (u : (ZMod (QS * q * d))ˣ)
    (τ : CyclotomicField (QS * q * d) ℚ ≃ₐ[ℚ] CyclotomicField (QS * q * d) ℚ),
    τ cycZeta = cycZeta ^ (u : ZMod (QS * q * d)).val → ∀ x : E, cycEmb (gal.symm (art u) x) = τ (cycEmb x)
  art_neg_one : art (-1) = φ.cc
  art_h : ∀ (u : (ZMod (QS * q * d))ˣ) (v : (ZMod (2 ^ (φ.e + 2)))ˣ),
    (v : ZMod (2 ^ (φ.e + 2))) = (((u : ZMod (QS * q * d)).val : ℕ) : ZMod (2 ^ (φ.e + 2))) →
    φ.hH (art u).2 = hcl φ.e v
  art_d : ∀ u : (ZMod (QS * q * d))ˣ, (u : ZMod (QS * q * d)).val ≡ 1 [MOD QS * q] → art u = 1 ∨ art u = φ.iod
  art_q : ∀ u : (ZMod (QS * q * d))ˣ, (u : ZMod (QS * q * d)).val ≡ 1 [MOD QS * d] → art u ^ 2 = 1

attribute [instance] HostRaw.instField HostRaw.instNF

namespace HostRaw

variable {φ : Frame} (H : HostRaw φ)

abbrev condN : ℕ := H.QS * H.q * H.d

def small : Finset ℕ := H.QS.primeFactors

abbrev F : Subfield H.E := maximalRealSubfield H.E

def K : IntermediateField ℚ H.E := ℚ⟮H.sqd⟯

abbrev galE (σ : H.E ≃ₐ[ℚ] H.E) : φ.GG := H.gal σ

def conj : H.E ≃ₐ[ℚ] H.E := H.gal.symm φ.cc

def cmType : Set (H.E →+* ℂ) := {ψ | ψ H.sqd = Complex.I * (Real.sqrt H.d : ℂ)}

def psAt (p : ℕ) : ℤ :=
  if h : Nat.Coprime p H.condN then (((H.art (ZMod.unitOfCoprime p h)).1.1 : ℤˣ) : ℤ) else 0

def rd : ℝ := |(discr H.E : ℝ)| ^ ((1 : ℝ) / (Module.finrank ℚ H.E : ℝ))

def etaF (𝔭 : Ideal (𝓞 H.F)) : ℤ := if (primesOver 𝔭 (𝓞 H.E)).ncard = 2 then 1 else -1

def MuPM : Prop := ∀ x : H.E, (∃ m : ℕ, 0 < m ∧ x ^ m = 1) → x = 1 ∨ x = -1

def CoprimeFifteen : Prop := Nat.Coprime H.QS 15

def Exact : Prop := ∀ l : ℕ, l.Prime → l ∣ H.QS →
  ∃ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ 1 [MOD H.condN / l] ∧ H.art u ≠ 1

def PsQ : Prop := ∀ u : (ZMod H.condN)ˣ,
  (((H.art u).1.1 : ℤˣ) : ℤ) = jacobiSym (((u : ZMod H.condN).val : ℕ) : ℤ) H.q

end HostRaw

structure HostDer {φ : Frame} (H : HostRaw φ) : Prop where
  art_surj : Function.Surjective H.art
  cm : IsCMField H.E
  conj_iff : ∀ (ψ : H.E →+* ℂ) (σ : H.E ≃ₐ[ℚ] H.E), (∀ x, ψ (σ x) = starRingEnd ℂ (ψ x)) ↔ H.gal σ = φ.cc
  finrank_E : Module.finrank ℚ H.E = 4 * φ.ord
  finrank_F : Module.finrank ℚ H.F = 2 * φ.ord
  mem_F : ∀ x : H.E, x ∈ H.F ↔ H.conj x = x

  cmType : (∀ ψ : H.E →+* ℂ, ψ ∈ H.cmType ↔ (starRingEnd ℂ).comp ψ ∉ H.cmType) ∧ H.cmType.ncard = 2 * φ.ord ∧
    ∀ ψ ∈ H.cmType, ∀ σ : H.E ≃ₐ[ℚ] H.E, ψ.comp (σ : H.E →+* H.E) ∈ H.cmType ↔ H.gal σ ∈ φ.Psi

  ps_root : ∃ a : H.E, a ≠ 0 ∧ ∀ σ : H.E ≃ₐ[ℚ] H.E, σ a = ((((H.gal σ).1.1 : ℤˣ) : ℤ) : H.E) * a
  art_ch : ∀ u : (ZMod H.condN)ˣ, (((H.art u).1.2 : ℤˣ) : ℤ) = jacobiSym (((u : ZMod H.condN).val : ℕ) : ℤ) H.d

  ps_d : ∀ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ H.d [MOD H.QS * H.q] → (H.art u).1.1 = -1

  frob : ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ H.condN →
    ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})],
      (∃ σ : H.E ≃ₐ[ℚ] H.E, IsArithFrobAt ℤ σ P) ∧
      (∀ (σ : H.E ≃ₐ[ℚ] H.E) (u : (ZMod H.condN)ˣ), (u : ZMod H.condN) = (p : ZMod H.condN) →
        (IsArithFrobAt ℤ σ P ↔ H.gal σ = H.art u)) ∧
      (∀ σ : H.E ≃ₐ[ℚ] H.E, IsArithFrobAt ℤ σ P →
        (((H.gal σ).1.1 : ℤˣ) : ℤ) = H.psAt p ∧ (((H.gal σ).1.2 : ℤˣ) : ℤ) = jacobiSym (-(H.d : ℤ)) p ∧
        ∃ v : (ZMod (2 ^ (φ.e + 2)))ˣ, (v : ZMod (2 ^ (φ.e + 2))) = (p : ZMod _) ∧ φ.hH (H.gal σ).2 = hcl φ.e v) ∧
      ∀ σ : H.E ≃ₐ[ℚ] H.E, (∀ x : 𝓞 H.E, σ • x - x ∈ P) ↔ σ = 1

  frob_any : ∀ (l : ℕ) [Fact l.Prime] (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(l : ℤ)})] (σ : H.E ≃ₐ[ℚ] H.E),
    IsArithFrobAt ℤ σ P ↔
      ∃ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ l [MOD ordCompl[l] H.condN] ∧ H.gal σ = H.art u

  inertia : ∀ (l : ℕ) [Fact l.Prime] (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(l : ℤ)})] (σ : H.E ≃ₐ[ℚ] H.E),
    (∀ x : 𝓞 H.E, σ • x - x ∈ P) ↔
      ∃ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ 1 [MOD ordCompl[l] H.condN] ∧ H.gal σ = H.art u

  decomp : ∀ (l : ℕ) [Fact l.Prime] (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(l : ℤ)})] (σ : H.E ≃ₐ[ℚ] H.E),
    σ ∈ MulAction.stabilizer _ P ↔
      ∃ (u : (ZMod H.condN)ˣ) (k : ℕ), (u : ZMod H.condN).val ≡ l ^ k [MOD ordCompl[l] H.condN] ∧ H.gal σ = H.art u

  inertia_d : ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(H.d : ℤ)})] (σ : H.E ≃ₐ[ℚ] H.E),
    (∀ x : 𝓞 H.E, σ • x - x ∈ P) ↔ (H.gal σ = 1 ∨ H.gal σ = φ.iod)

  decomp_typeI : ∀ (l : ℕ), l.Prime → l ∣ H.QS * H.q →
    ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(l : ℤ)})] (σ : H.E ≃ₐ[ℚ] H.E),
      σ ∈ MulAction.stabilizer _ P → H.gal σ ∈ φ.Psi

  decompConj : ∀ (l : ℕ), l.Prime → l ∣ H.condN →
    ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(l : ℤ)})], H.conj ∉ MulAction.stabilizer _ P

  unramEF : ∀ (P : Ideal (𝓞 H.E)), P.IsPrime → P ≠ ⊥ → ¬ ∀ x : 𝓞 H.E, H.conj • x - x ∈ P

  splitK : ∀ p : ℕ, p.Prime →
    ((primesOver (span {(p : ℤ)}) (𝓞 H.K)).ncard = 2 ↔ (p = 2 ∨ (p ≠ 2 ∧ jacobiSym (-(H.d : ℤ)) p = 1)))

  ordinary : ∀ (p : ℕ) [Fact p.Prime] (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})],
    (∀ σ τ : H.E ≃ₐ[ℚ] H.E, τ ∈ MulAction.stabilizer _ P → (H.gal (σ * τ) ∈ φ.Psi ↔ H.gal σ ∈ φ.Psi)) ↔
      (primesOver (span {(p : ℤ)}) (𝓞 H.K)).ncard = 2

  eta : (∀ 𝔭 : Ideal (𝓞 H.F), 𝔭.IsPrime → 𝔭 ≠ ⊥ →
      (primesOver 𝔭 (𝓞 H.E)).ncard = 2 ∨ ((primesOver 𝔭 (𝓞 H.E)).ncard = 1 ∧ 𝔭.inertiaDegIn (𝓞 H.E) = 2)) ∧
    (∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ H.condN →
      ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] (σ : H.E ≃ₐ[ℚ] H.E), IsArithFrobAt ℤ σ P →
        (H.etaF (P.comap (algebraMap (𝓞 H.F) (𝓞 H.E))) = -1 ↔ φ.cc ∈ Subgroup.zpowers (H.gal σ))) ∧
    (∀ (p : ℕ) [Fact p.Prime], p ∣ H.condN →
      ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})],
        H.etaF (P.comap (algebraMap (𝓞 H.F) (𝓞 H.E))) = 1)

  diffSupport : ∀ P : Ideal (𝓞 H.E), P.IsPrime → P ∣ differentIdeal (𝓞 H.K) (𝓞 H.E) →
    ((H.QS * H.q : ℕ) : 𝓞 H.E) ∈ P

  principal : ∃ 𝔟 : Ideal (𝓞 H.E), differentIdeal (𝓞 H.K) (𝓞 H.E) = 𝔟 * (H.conj • 𝔟) ∧ 𝔟 ⊔ H.conj • 𝔟 = ⊤ ∧
    ∀ σ : H.E ≃ₐ[ℚ] H.E, H.gal σ ∈ φ.Psi → σ • 𝔟 = 𝔟

  unimodular : ∀ 𝔟 : Ideal (𝓞 H.E), differentIdeal (𝓞 H.K) (𝓞 H.E) = 𝔟 * (H.conj • 𝔟) → ∀ x : H.E,
    x ∈ ((𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 H.E)) H.E)⁻¹) ↔
      ∀ y ∈ ((𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 H.E)) H.E)⁻¹),
        Algebra.trace H.K H.E (x * H.conj y) ∈ (algebraMap (𝓞 H.K) H.K).range
  discr_sq : discr H.E = discr H.F ^ 2

  discr_primes : (∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr H.E → p ∣ H.condN) ∧ (2 : ℤ) ∣ discr H.E ∧ (H.d : ℤ) ∣ discr H.E
  rd_ge : (2 : ℝ) ^ ((φ.e : ℝ) + 1 - (2 : ℝ) ^ (-(φ.e : ℝ))) * Real.sqrt H.d ≤ H.rd
  rd_le : H.rd ≤ (H.QS : ℝ) / 2 * Real.sqrt ((H.q : ℝ) * H.d)
  rd_sq_ge : (4 * φ.ord : ℝ) ≤ H.rd ^ 2

  norm_mu : ∀ x : H.E, (∃ m : ℕ, 0 < m ∧ x ^ m = 1) → Algebra.norm H.K x = 1

def DerOfRaw : Prop := ∀ (φ : Frame) (H : HostRaw φ), HostDer H

structure HostAx (φ : Frame) extends HostRaw φ where
  der : HostDer toHostRaw

namespace HostAx

variable {φ : Frame} (H : HostAx φ)

theorem hostE_isGalois : IsGalois ℚ H.E := H.galois
theorem isCMField_hostE : IsCMField H.E := H.der.cm
theorem finrank_cmField : Module.finrank ℚ H.E = 4 * φ.ord := H.der.finrank_E
theorem finrank_hostF : Module.finrank ℚ H.F = 2 * φ.ord := H.der.finrank_F
theorem galE_mul (σ τ : H.E ≃ₐ[ℚ] H.E) : H.galE (σ * τ) = H.galE σ * H.galE τ := map_mul H.gal σ τ
theorem galE_bijective : Function.Bijective H.galE := H.gal.bijective
theorem galE_injective : Function.Injective H.galE := H.gal.injective
theorem galE_one : H.galE 1 = 1 := map_one H.gal
theorem galE_inv (σ : H.E ≃ₐ[ℚ] H.E) : H.galE σ⁻¹ = (H.galE σ)⁻¹ := map_inv H.gal σ
theorem galE_pow (σ : H.E ≃ₐ[ℚ] H.E) (k : ℕ) : H.galE (σ ^ k) = H.galE σ ^ k := map_pow H.gal σ k
theorem exists_galE_eq (g : φ.GG) : ∃ σ : H.E ≃ₐ[ℚ] H.E, H.galE σ = g := ⟨H.gal.symm g, H.gal.apply_symm_apply g⟩
theorem galE_eq_one_iff (σ : H.E ≃ₐ[ℚ] H.E) : H.galE σ = 1 ↔ σ = 1 := MulEquiv.map_eq_one_iff H.gal
theorem galE_conjE : H.galE H.conj = φ.cc := H.gal.apply_symm_apply φ.cc
theorem eq_conjE_iff (σ : H.E ≃ₐ[ℚ] H.E) : σ = H.conj ↔ H.galE σ = φ.cc := by
  exact MulEquiv.eq_symm_apply H.gal
theorem isConj_iff_galE (ψ : H.E →+* ℂ) (σ : H.E ≃ₐ[ℚ] H.E) :
    (∀ x, ψ (σ x) = starRingEnd ℂ (ψ x)) ↔ H.galE σ = φ.cc := H.der.conj_iff ψ σ
theorem conjE_apply (ψ : H.E →+* ℂ) (x : H.E) : ψ (H.conj x) = starRingEnd ℂ (ψ x) := (H.der.conj_iff ψ H.conj).2 H.galE_conjE x
theorem conjE_mem_hostF_iff (x : H.E) : x ∈ H.F ↔ H.conj x = x := H.der.mem_F x
theorem galE_bE (σ : H.E ≃ₐ[ℚ] H.E) : σ H.sqd = ((((H.galE σ).1.2 : ℤˣ) : ℤ) : H.E) * H.sqd := H.gal_sqd σ

theorem sqd_ne_zero : H.sqd ≠ 0 := by
  intro h
  have h1 := H.sqd_sq
  rw [h] at h1
  have hd : H.d = 0 := by simpa using h1.symm
  exact H.hyp.2.1.ne_zero hd

theorem galE_mem_Psi_iff (σ : H.E ≃ₐ[ℚ] H.E) : H.galE σ ∈ φ.Psi ↔ σ H.sqd = H.sqd := by
  have hs := H.sqd_ne_zero
  rw [H.galE_bE σ]
  change (H.galE σ).1.2 = 1 ↔ _
  rcases Int.units_eq_one_or (H.galE σ).1.2 with h | h <;> rw [h]
  · simp
  · constructor
    · intro h2
      exact absurd h2 (by decide)
    · intro h2
      exfalso
      apply hs
      have h4 : ((((-1 : ℤˣ) : ℤ) : H.E)) = -1 := by simp
      rw [h4] at h2
      have h3 : (2 : H.E) * H.sqd = 0 := by linear_combination -h2
      exact (mul_eq_zero.1 h3).resolve_left two_ne_zero

end HostAx

end Formalism.HC

end
end


section
-- Source: Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/PrimePairSizeCondition.lean

noncomputable section

namespace Formalism.HC

structure PChar where
  N : ℕ
  [ne : NeZero N]
  χ : DirichletCharacter ℂ N
  prim : χ.IsPrimitive

attribute [instance] PChar.ne

namespace PChar

def val (ψ : PChar) (a : ℕ) : ℂ := ψ.χ (a : ZMod ψ.N)

def one : PChar := ⟨1, 1, DirichletCharacter.isPrimitive_one_level_one⟩

def inv (ψ : PChar) : PChar :=
  ⟨ψ.N, ψ.χ⁻¹, by
    have h : ψ.χ.conductor = ψ.N := ψ.prim
    exact (DirichletCharacter.conductor_inv ψ.χ).trans h⟩

theorem inv_inv (ψ : PChar) : ψ.inv.inv = ψ := by
  cases ψ
  simp only [inv]
  congr 1
  exact _root_.inv_inv _

def of {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : PChar :=
  @PChar.mk χ.conductor ⟨χ.conductor_ne_zero⟩ χ.primitiveCharacter χ.primitiveCharacter_isPrimitive

def IsReal (ψ : PChar) : Prop := ∀ a : ZMod ψ.N, (ψ.χ a).im = 0

end PChar

structure KSet where
  KEPT : Finset PChar
  one_mem : PChar.one ∈ KEPT
  inv_mem : ∀ ψ ∈ KEPT, ψ.inv ∈ KEPT

  psK : Option PChar
  psK_spec : ∀ ψ, psK = some ψ → ψ ∈ KEPT ∧ ψ.χ.Odd ∧ ψ.IsReal

structure HType extends KSet where
  eps : ℝ
  eps_pos : 0 < eps
  eps_lt : eps < 1 / 52
  J : ℕ
  one_le_J : 1 ≤ J
  P0 : ℕ
  P0_pos : 0 < P0

  t : ℝ → ℕ
  Ct : ℝ
  t_le : ∀ x : ℝ, 1 ≤ x → (t x : ℝ) ≤ x ^ Ct

namespace HType

variable (T : HType)

def SM : Finset ℕ := (2 * T.P0 * ∏ ψ ∈ T.KEPT, ψ.N).primeFactors

def P : ℕ := ∏ p ∈ (∏ l ∈ T.SM, l * (l - 1)).primeFactors.erase 2, p

def z (X : ℝ) : ℝ := X ^ (T.eps / (5 * (T.J : ℝ)))

def z' (X : ℝ) : ℝ := T.z X * Real.log (X ^ ((1 : ℝ) / T.J)) ^ 2

def L (x : ℝ) : ℝ := x ^ T.eps

def b (x : ℝ) : ℝ := Real.exp (T.L x)

def X' (x : ℝ) : ℝ := Real.exp (x ^ (T.eps / 3))

def InRange (X x : ℝ) (e : ℕ) : Prop :=
  1 ≤ X ∧ X ^ ((1 : ℝ) / T.J) ≤ x ∧ x ≤ X ∧
    x ^ (2 + 8 * T.eps) / 2 ≤ (2 : ℝ) ^ e ∧ (2 : ℝ) ^ e ≤ 2 * x ^ (2 + 8 * T.eps)

end HType

structure HConst where

  oB : ℕ

  rB : ℕ

  c : ℝ
  c_pos : 0 < c

  C : ℝ

def Frame.TorsionIndexBounded (φ : Frame) (oB : ℕ) : Prop := φ.o ≤ oB

namespace HostRaw

variable {φ : Frame} (H : HostRaw φ)

theorem condN_pos : 0 < H.condN :=
  Nat.mul_pos (Nat.mul_pos H.QS_pos H.hyp.1.pos) H.hyp.2.1.pos

instance condN_neZero : NeZero H.condN := ⟨H.condN_pos.ne'⟩

def OddPrimesSplitBelow (z : ℝ) : Prop :=
  11 ≤ z ∧ ∀ p : ℕ, p.Prime → p ≠ 2 → (p : ℝ) ≤ z → jacobiSym (-(H.d : ℤ)) p = 1

def SmallPrimeSizeBounds (SM : Finset ℕ) (z : ℝ) : Prop := ∀ l ∈ H.small, l ∈ SM ∧ (l : ℝ) ≤ z / 4

def DiscriminantConductorSizes (z' : ℝ) : Prop :=
  z' / 2 < Real.log H.d ∧ Real.log H.d ≤ z' ∧ Real.log (H.condN : ℝ) ≤ 3 * z'

def ModulusSizeBounds (z : ℝ) : Prop := z / 2 < Real.log H.q ∧ Real.log H.q ≤ z

def PrimePairSizeCondition (z : ℝ) (rB rr rr' : ℕ) : Prop :=
  rr.Prime ∧ rr'.Prime ∧ rr ≠ 2 ∧ rr < rr' ∧ rr' < 2 * rr ∧ Nat.Coprime (rr * rr') H.condN ∧ (rr' : ℝ) ≤ z ∧ rr' ≤ rB

end HostRaw

structure PreHost (T : HType) (κ : HConst) (X x : ℝ) {φ : Frame} (H : HostAx φ) (rr rr' : ℕ) : Prop where
  range : T.InRange X x φ.e
  ha5 : φ.TorsionIndexBounded κ.oB
  ha6 : H.OddPrimesSplitBelow (T.z X)
  ha7 : H.SmallPrimeSizeBounds T.SM (T.z X)
  ha8 : H.DiscriminantConductorSizes (T.z' X)
  ha9 : H.ModulusSizeBounds (T.z X)
  ha12 : H.PrimePairSizeCondition (T.z X) κ.rB rr rr'

end Formalism.HC

end
end


section
-- Source: Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/Analytic.lean

noncomputable section

namespace Formalism.HC

namespace An

abbrev abelian₂ (n : ℕ) : ℝ := (ArithmeticFunction.vonMangoldt n : ℝ)

def logDerivativeAtOne {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : ℂ :=
  deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1

def G (y : ℝ) : ℝ :=
  (∑ n ∈ Finset.Icc 1 ⌊y⌋₊, abelian₂ n * max (y / n - 1) 0) -
    y * (Real.log y - 1 - Real.eulerMascheroniConstant)

def sumLamChi {N : ℕ} (χ : DirichletCharacter ℂ N) (y : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (abelian₂ n : ℂ) * χ (n : ZMod N) * ((max (y / n - 1) 0 : ℝ) : ℂ)

open Classical in

def gChi {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (y : ℝ) : ℂ :=
  if χ = 1 then ((G y : ℝ) : ℂ) else sumLamChi χ y + (y : ℂ) * logDerivativeAtOne χ

def Induces {N : ℕ} (χ : DirichletCharacter ℂ N) (f : ℕ → ℂ) (M : ℕ) : Prop :=
  χ.IsPrimitive ∧ ∀ a : ℕ, a.Coprime M → χ (a : ZMod N) = f a

private theorem pchar_ext_of_N_eq_of_heq (ψ ψ' : PChar) (hN : ψ.N = ψ'.N) (hχ : HEq ψ.χ ψ'.χ) : ψ = ψ' := by
  cases ψ
  cases ψ'
  cases hN
  cases hχ
  rfl

private theorem heq_of_changeLevel_eq_of_level_eq {N N' L : ℕ} [NeZero L] (χ : DirichletCharacter ℂ N)
    (χ' : DirichletCharacter ℂ N') (d1 : N ∣ L) (d2 : N' ∣ L) (hNN : N = N')
    (heq : DirichletCharacter.changeLevel d1 χ = DirichletCharacter.changeLevel d2 χ') : HEq χ χ' := by
  subst hNN
  exact heq_of_eq (DirichletCharacter.changeLevel_injective d1 heq)

theorem Induces.unique {ψ ψ' : PChar} {f : ℕ → ℂ} {M : ℕ} (hM : M ≠ 0) (h : Induces ψ.χ f M) (h' : Induces ψ'.χ f M) :
    ψ = ψ' := by
  haveI := ψ.ne
  haveI := ψ'.ne
  have hN0 : ψ.N ≠ 0 := NeZero.ne _
  have hN0' : ψ'.N ≠ 0 := NeZero.ne _
  haveI : NeZero (ψ.N * ψ'.N * M) := ⟨mul_ne_zero (mul_ne_zero hN0 hN0') hM⟩
  have d1 : ψ.N ∣ ψ.N * ψ'.N * M := ⟨ψ'.N * M, by ring⟩
  have d2 : ψ'.N ∣ ψ.N * ψ'.N * M := ⟨ψ.N * M, by ring⟩
  have heq : DirichletCharacter.changeLevel d1 ψ.χ = DirichletCharacter.changeLevel d2 ψ'.χ := by
    apply MulChar.ext
    intro u
    rw [DirichletCharacter.changeLevel_eq_cast_of_dvd, DirichletCharacter.changeLevel_eq_cast_of_dvd]
    have hcop : (u : ZMod (ψ.N * ψ'.N * M)).val.Coprime (ψ.N * ψ'.N * M) := ZMod.val_coe_unit_coprime u
    have hcM : (u : ZMod (ψ.N * ψ'.N * M)).val.Coprime M :=
      Nat.Coprime.coprime_dvd_right (dvd_mul_left M (ψ.N * ψ'.N)) hcop
    rw [ZMod.cast_eq_val, ZMod.cast_eq_val, h.2 _ hcM, h'.2 _ hcM]
  have hc : ψ.N = ψ'.N := by
    have e1 := DirichletCharacter.conductor_changeLevel ψ.χ d1
    have e2 := DirichletCharacter.conductor_changeLevel ψ'.χ d2
    rw [heq, e2] at e1
    calc ψ.N = ψ.χ.conductor := ((DirichletCharacter.isPrimitive_def ψ.χ).mp ψ.prim).symm
      _ = ψ'.χ.conductor := e1.symm
      _ = ψ'.N := (DirichletCharacter.isPrimitive_def ψ'.χ).mp ψ'.prim
  exact pchar_ext_of_N_eq_of_heq ψ ψ' hc (heq_of_changeLevel_eq_of_level_eq ψ.χ ψ'.χ d1 d2 hc heq)

theorem induces_of {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    Induces (PChar.of χ).χ (fun a => χ (a : ZMod N)) N := by
  refine ⟨DirichletCharacter.primitiveCharacter_isPrimitive χ, fun a ha => ?_⟩
  show χ.primitiveCharacter (a : ZMod χ.conductor) = χ (a : ZMod N)
  have hu : ((ZMod.unitOfCoprime a ha : (ZMod N)ˣ) : ZMod N) = (a : ZMod N) :=
    ZMod.coe_unitOfCoprime a ha
  conv_rhs => rw [← DirichletCharacter.changeLevel_primitiveCharacter χ, ← hu,
    DirichletCharacter.changeLevel_eq_cast_of_dvd, hu,
    ZMod.cast_natCast (DirichletCharacter.conductor_dvd_level χ)]

end An

namespace Frame

variable (φ : Frame)

abbrev Char : Type := φ.GG →* ℂˣ

def psC : φ.Char := (Units.map (Int.castRingHom ℂ).toMonoidHom).comp φ.chQ

def TrivialOnFirstFactor {φ : Frame} (θ : φ.Char) : Prop := ∀ s ∈ φ.A0, θ (φ.tau1 s) = 1

def Chat : Set φ.Char := {θ | TrivialOnFirstFactor θ ∧ θ φ.iod = 1 ∧ θ φ.cc = 1}

def Xp : Set φ.Char := {θ | TrivialOnFirstFactor θ ∧ θ φ.iod = 1}

def Xm : Set φ.Char := {θ | TrivialOnFirstFactor θ ∧ θ φ.iod = -1}

end Frame

namespace HostRaw

variable {φ : Frame} (H : HostRaw φ)

def dir (θ : φ.Char) : DirichletCharacter ℂ H.condN := MulChar.ofUnitHom (θ.comp H.art)

def dirAt (θ : φ.Char) (a : ℕ) : ℂ := H.dir θ (a : ZMod H.condN)

def IsPrimOf (θ : φ.Char) {N : ℕ} (χ : DirichletCharacter ℂ N) : Prop := An.Induces χ (H.dirAt θ) H.condN

def prim (θ : φ.Char) : PChar := PChar.of (H.dir θ)

theorem isPrimOf_prim (θ : φ.Char) : H.IsPrimOf θ (H.prim θ).χ :=
  An.induces_of (H.dir θ)

theorem isPrimOf_iff (θ : φ.Char) (ψ : PChar) : H.IsPrimOf θ ψ.χ ↔ ψ = H.prim θ := by
  constructor
  · intro h
    have hN : H.condN ≠ 0 := NeZero.ne _
    exact An.Induces.unique hN h (H.isPrimOf_prim θ)
  · rintro rfl
    exact H.isPrimOf_prim θ

theorem dir_unit (θ : φ.Char) (u : (ZMod H.condN)ˣ) : H.dir θ u = θ (H.art u) := by
  rw [dir, MulChar.ofUnitHom_coe]
  rfl

def IsCharE {N : ℕ} (χ : DirichletCharacter ℂ N) : Prop := ∃ θ : φ.Char, H.IsPrimOf θ χ

def Kept (S : Finset PChar) (θ : φ.Char) : Prop := ∃ ψ ∈ S, H.IsPrimOf θ ψ.χ

theorem kept_iff (S : Finset PChar) (θ : φ.Char) : H.Kept S θ ↔ H.prim θ ∈ S := by
  constructor
  · rintro ⟨ψ, hψ, h⟩
    rwa [(H.isPrimOf_iff θ ψ).mp h] at hψ
  · intro h
    exact ⟨H.prim θ, h, H.isPrimOf_prim θ⟩

def Bounded (S : Finset PChar) : Set φ.Char := {θ | (θ ∈ φ.Xp ∧ ¬ H.Kept S θ) ∨ θ ∈ φ.Xm}

def KeptInXp (S : Finset PChar) : Prop := ∀ ψ ∈ S, ∃ θ ∈ φ.Xp, H.IsPrimOf θ ψ.χ

def KeptEqChat (S : Finset PChar) : Prop :=
  (∀ ψ ∈ S, ∃ θ ∈ φ.Chat, H.IsPrimOf θ ψ.χ) ∧ ∀ θ ∈ φ.Chat, H.Kept S θ

def KeptEqXp (S : Finset PChar) : Prop := H.KeptInXp S ∧ ∀ θ ∈ φ.Xp, H.Kept S θ

def ChebyshevCharacterBound (x eps c : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), H.IsCharE χ →
    ∀ y : ℝ, Real.exp (x ^ (eps / 3)) / 3 ≤ y → ‖An.gChi χ y‖ ≤ y * Real.exp (-(c * x ^ (eps / 8)))

def LogDerivativeBound (S : Finset PChar) (X x eps C : ℝ) : Prop :=
  (∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), H.IsPrimOf φ.chC χ → ‖An.logDerivativeAtOne χ‖ ≤ x ^ eps) ∧
  ∀ θ ∈ H.Bounded S, ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), H.IsPrimOf θ χ →
    ‖An.logDerivativeAtOne χ‖ ≤ C * Real.log X

def BoundedCharsPointwise (S : Finset PChar) (x eps : ℝ) : Prop :=
  ∀ θ ∈ H.Bounded S, ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), H.IsPrimOf θ χ →
    ‖An.gChi χ x‖ ≤ x ^ ((1 : ℝ) / 2 + eps)

def ExceptionalCharacterKept (S : Finset PChar) (psK : Option PChar) : Prop :=
  (∀ ψ, psK = some ψ → H.IsPrimOf φ.psC ψ.χ) ∧ (psK = none → ¬ H.Kept S φ.psC)

end HostRaw

structure HostConditions (T : HType) (κ : HConst) (X x : ℝ) {φ : Frame} (H : HostRaw φ) : Prop where
  kept : H.KeptInXp T.KEPT
  a : H.ChebyshevCharacterBound x T.eps κ.c
  b : H.LogDerivativeBound T.KEPT X x T.eps κ.C
  c1 : H.BoundedCharsPointwise T.KEPT x T.eps
  e : H.ExceptionalCharacterKept T.KEPT T.psK

structure PreHostAn (T : HType) (κ : HConst) (X x : ℝ) {φ : Frame} (H : HostAx φ) (rr rr' : ℕ) : Prop
    extends PreHost T κ X x H rr rr' where
  ha10 : HostConditions T κ X x H.toHostRaw

end Formalism.HC

end
end


section
-- Source: Formalism/Statement.lean

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Formalism

open ArithmeticFunction in

def LamF {N : ℕ} (χ : DirichletCharacter ℂ N) (n : ℕ) : ℝ :=
  Λ n * (1 + (χ n).re)

def S {N : ℕ} (χ : DirichletCharacter ℂ N) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, LamF χ n * (x / n - 1)

def gammaF {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : ℝ :=
  Real.eulerMascheroniConstant +
    (deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1).re

def G {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (x : ℝ) : ℝ :=
  S χ x - x * Real.log x + (1 + gammaF χ) * x

instance fact_prime_seven : Fact (Nat.Prime 7) := ⟨by norm_num⟩

def quadraticCharFour : DirichletCharacter ℂ 4 := ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)

def quadraticCharThree : DirichletCharacter ℂ 3 := (quadraticChar (ZMod 3)).ringHomComp (Int.castRingHom ℂ)

def quadraticCharacterMod7 : DirichletCharacter ℂ 7 := (quadraticChar (ZMod 7)).ringHomComp (Int.castRingHom ℂ)

def LandauStep : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 → (∀ n : ℕ, (χ n).im = 0) →
  ∀ σ₀ : ℝ, 0 < σ₀ → σ₀ < 1 →
  (∀ σ : ℝ, σ₀ < σ → σ < 1 → DirichletCharacter.LFunction χ σ ≠ 0) →
  (∃ C : ℝ, ∀ x : ℝ, 1 ≤ x → -C * x ^ σ₀ ≤ G χ x) →
  ∀ s : ℂ, σ₀ < s.re → riemannZeta s ≠ 0 ∧ DirichletCharacter.LFunction χ s ≠ 0

def LandauStepEps : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 → (∀ n : ℕ, (χ n).im = 0) →
  ∀ σ₀ : ℝ, 0 ≤ σ₀ → σ₀ < 1 →
  (∀ σ : ℝ, σ₀ < σ → σ < 1 → DirichletCharacter.LFunction χ σ ≠ 0) →
  (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x → -C * x ^ (σ₀ + ε) ≤ G χ x) →
  ∀ s : ℂ, σ₀ < s.re → riemannZeta s ≠ 0 ∧ DirichletCharacter.LFunction χ s ≠ 0

def RHofG {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : Prop :=
  (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x → -C * x ^ ((1 : ℝ) / 2 + ε) ≤ G χ x) →
  RiemannHypothesis ∧ ∀ s : ℂ, 1 / 2 < s.re → DirichletCharacter.LFunction χ s ≠ 0

end Formalism
end
end


section
-- Source: Formalism/StatementOC.lean

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Formalism

open ArithmeticFunction in

def Sz (x : ℝ) : ℝ := ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Λ n * (x / n - 1)

def Gz (x : ℝ) : ℝ := Sz x - x * Real.log x + (1 + Real.eulerMascheroniConstant) * x

open ArithmeticFunction in

def Schi {N : ℕ} (χ : DirichletCharacter ℂ N) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Λ n * (χ n).re * (x / n - 1)

def Gchi {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (x : ℝ) : ℝ :=
  Schi χ x + (deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1).re * x

def OCStep : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 → (∀ n : ℕ, (χ n).im = 0) →
  ∀ θ : ℝ, 0 < θ → θ < 1 →
  (∃ C : ℝ, ∀ x : ℝ, 1 ≤ x → -C * x ^ θ ≤ Gz x - Gchi χ x) →
  (∀ σ : ℝ, θ < σ → σ < 1 → DirichletCharacter.LFunction χ σ ≠ 0) ∧
  ∀ s : ℂ, θ < s.re → s ≠ 1 →
    analyticOrderAt riemannZeta s = analyticOrderAt (DirichletCharacter.LFunction χ) s

def OCStepUpper : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 → (∀ n : ℕ, (χ n).im = 0) →
  ∀ θ : ℝ, 0 < θ → θ < 1 →
  (∀ σ : ℝ, θ < σ → σ < 1 → DirichletCharacter.LFunction χ σ ≠ 0) →
  (∃ C : ℝ, ∀ x : ℝ, 1 ≤ x → Gz x - Gchi χ x ≤ C * x ^ θ) →
  ∀ s : ℂ, θ < s.re → s ≠ 1 →
    analyticOrderAt riemannZeta s = analyticOrderAt (DirichletCharacter.LFunction χ) s

def OCAvg : Prop :=
  ∀ (ι : Type) [Fintype ι] (N : ι → ℕ) [∀ i, NeZero (N i)]
    (χ : (i : ι) → DirichletCharacter ℂ (N i)) (w : ι → ℝ),
  (∀ i, χ i ≠ 1) → (∀ i (n : ℕ), (χ i n).im = 0) → (∀ i, 0 ≤ w i) → 0 < ∑ i, w i →
  ∀ θ : ℝ, 0 < θ → θ < 1 →
  (∃ C : ℝ, ∀ x : ℝ, 1 ≤ x → -C * x ^ θ ≤ ∑ i, w i * (Gz x - Gchi (χ i) x)) →
  (∀ i, 0 < w i → ∀ σ : ℝ, θ < σ → σ < 1 → DirichletCharacter.LFunction (χ i) σ ≠ 0) ∧
  ∀ s : ℂ, θ < s.re → s ≠ 1 →
    analyticOrderAt riemannZeta s ≠ ⊤ ∧
    (∀ i, analyticOrderAt (DirichletCharacter.LFunction (χ i)) s ≠ ⊤) ∧
    (∑ i, w i) * (analyticOrderNatAt riemannZeta s : ℝ) =
      ∑ i, w i * (analyticOrderNatAt (DirichletCharacter.LFunction (χ i)) s : ℝ)

def OCAvgUpper : Prop :=
  ∀ (ι : Type) [Fintype ι] (N : ι → ℕ) [∀ i, NeZero (N i)]
    (χ : (i : ι) → DirichletCharacter ℂ (N i)) (w : ι → ℝ),
  (∀ i, χ i ≠ 1) → (∀ i (n : ℕ), (χ i n).im = 0) → (∀ i, 0 ≤ w i) → 0 < ∑ i, w i →
  ∀ θ : ℝ, 0 < θ → θ < 1 →
  (∀ i, 0 < w i → ∀ σ : ℝ, θ < σ → σ < 1 → DirichletCharacter.LFunction (χ i) σ ≠ 0) →
  (∃ C : ℝ, ∀ x : ℝ, 1 ≤ x → ∑ i, w i * (Gz x - Gchi (χ i) x) ≤ C * x ^ θ) →
  ∀ s : ℂ, θ < s.re → s ≠ 1 →
    analyticOrderAt riemannZeta s ≠ ⊤ ∧
    (∀ i, analyticOrderAt (DirichletCharacter.LFunction (χ i)) s ≠ ⊤) ∧
    (∑ i, w i) * (analyticOrderNatAt riemannZeta s : ℝ) =
      ∑ i, w i * (analyticOrderNatAt (DirichletCharacter.LFunction (χ i)) s : ℝ)

def RiemannHypothesisOfLowerBounds : Prop :=
  ∀ (ι : Type) (N : ι → ℕ) [∀ i, NeZero (N i)] (χ : (i : ι) → DirichletCharacter ℂ (N i)),
  (∀ i, χ i ≠ 1) → (∀ i (n : ℕ), (χ i n).im = 0) →
  (∀ i, ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x →
      -C * x ^ ((1 : ℝ) / 2 + ε) ≤ Gz x - Gchi (χ i) x) →
  (∀ s : ℂ, 1 / 2 < s.re → ∃ i, DirichletCharacter.LFunction (χ i) s ≠ 0) →
  RiemannHypothesis

end Formalism
end
end


section
-- Source: Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ExplicitFormulaErrorOfHostConditions.lean

noncomputable section

namespace Formalism.HC

structure Level extends KSet where
  o : ℕ

def PChar.ZeroFreeAbove (ψ : PChar) (θ : ℝ) : Prop :=
  ∀ s : ℂ, θ < s.re → DirichletCharacter.LFunction ψ.χ s ≠ 0

def ZeroFreeOn (Q : PChar → Prop) : Prop := ∀ ψ : PChar, Q ψ → ψ.ZeroFreeAbove (1 / 2)

def ZeroFreeEven : Prop := ZeroFreeOn fun ψ => ψ.χ.Even

def ZeroFreeAll : Prop := ZeroFreeOn fun _ => True

namespace Level

variable (Λ : Level)

def ZeroFreeAbove (θ : ℝ) : Prop := ∀ ψ ∈ Λ.KEPT, ψ.ZeroFreeAbove θ

def ZeroFreeLevel : Prop := Λ.ZeroFreeAbove (1 / 2)

def IsEven : Prop := ∀ ψ ∈ Λ.KEPT, ψ.χ.Even

open Classical in

def Nt : Finset PChar := Λ.KEPT.erase PChar.one

open Classical in

def wt (ψ : PChar) : ℝ := if Λ.psK = some ψ then 1 else (3 * (Λ.o : ℝ) + 1)⁻¹

def Gm (y : ℝ) : ℝ := Formalism.Gz y + ∑ ψ ∈ Λ.Nt, Λ.wt ψ * (An.gChi ψ.χ y).re

def ChebyshevGrowthImpliesZeroFree : Prop :=
  ∀ θ : ℝ, 0 < θ → θ < 1 → ∀ y0 : ℝ, (∀ y ≥ y0, Λ.Gm y ≤ y ^ θ) → Λ.ZeroFreeAbove θ

end Level

theorem zeroFreeOn_of_levels {Q : PChar → Prop} (h : ∀ ψ, Q ψ → ∃ Λ : Level, ψ ∈ Λ.KEPT ∧ Λ.ZeroFreeLevel) : ZeroFreeOn Q := by
  intro ψ hψ
  obtain ⟨Λ, h1, h2⟩ := h ψ hψ
  exact h2 ψ h1

private theorem pchar_mk_eq_of_changeLevel_eq_self_of_primitive {N d : ℕ} [NeZero N] [NeZero d] (χ : DirichletCharacter ℂ N)
    (ψ : DirichletCharacter ℂ d) (hd : d ∣ N) (hc : DirichletCharacter.changeLevel hd ψ = χ)
    (h1 : ψ.IsPrimitive) (h2 : χ.IsPrimitive) (he : d = N) :
    PChar.mk d ψ h1 = PChar.mk N χ h2 := by
  subst he
  rw [DirichletCharacter.changeLevel_self] at hc
  subst hc
  rfl

theorem PChar.of_self (ψ : PChar) : PChar.of ψ.χ = ψ := by
  haveI : NeZero ψ.χ.conductor := ⟨ψ.χ.conductor_ne_zero⟩
  exact pchar_mk_eq_of_changeLevel_eq_self_of_primitive ψ.χ ψ.χ.primitiveCharacter ψ.χ.conductor_dvd_level
    ψ.χ.changeLevel_primitiveCharacter ψ.χ.primitiveCharacter_isPrimitive ψ.prim ψ.prim

private theorem pchar_mk_eq_one_of_level_eq_one {d : ℕ} [NeZero d] (ψ : DirichletCharacter ℂ d) (h : ψ.IsPrimitive)
    (he : d = 1) : PChar.mk d ψ h = PChar.one := by
  subst he
  obtain rfl := DirichletCharacter.level_one ψ
  rfl

theorem PChar.of_one (M : ℕ) [NeZero M] : PChar.of (1 : DirichletCharacter ℂ M) = PChar.one := by
  haveI : NeZero (1 : DirichletCharacter ℂ M).conductor :=
    ⟨(1 : DirichletCharacter ℂ M).conductor_ne_zero⟩
  exact pchar_mk_eq_one_of_level_eq_one _ _ DirichletCharacter.conductor_one

private theorem pchar_mk_eq_of_changeLevel_eq_of_level_eq {M d e : ℕ} [NeZero M] [NeZero d] [NeZero e]
    (χ : DirichletCharacter ℂ M) (ψ : DirichletCharacter ℂ d) (φ : DirichletCharacter ℂ e)
    (hd : d ∣ M) (he' : e ∣ M) (hde : d = e) (hψ : DirichletCharacter.changeLevel hd ψ = χ)
    (hφ : DirichletCharacter.changeLevel he' φ = χ) (p1 : ψ.IsPrimitive) (p2 : φ.IsPrimitive) :
    PChar.mk d ψ p1 = PChar.mk e φ p2 := by
  subst hde
  have hq : ψ = φ := DirichletCharacter.changeLevel_injective hd (hψ.trans hφ.symm)
  subst hq
  rfl

private theorem conductor_inv_dvd_conductor {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) :
    χ⁻¹.conductor ∣ χ.conductor := by
  apply DirichletCharacter.conductor_dvd_of_mem_conductorSet
  exact ⟨χ.conductor_dvd_level, χ.primitiveCharacter⁻¹,
    by rw [map_inv, DirichletCharacter.changeLevel_primitiveCharacter]⟩

private theorem conductor_inv_eq_conductor {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) :
    χ⁻¹.conductor = χ.conductor := by
  apply Nat.dvd_antisymm (conductor_inv_dvd_conductor χ)
  simpa using conductor_inv_dvd_conductor χ⁻¹

theorem PChar.of_inv {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) : PChar.of χ⁻¹ = (PChar.of χ).inv := by
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  haveI : NeZero χ⁻¹.conductor := ⟨χ⁻¹.conductor_ne_zero⟩
  exact pchar_mk_eq_of_changeLevel_eq_of_level_eq χ⁻¹ χ⁻¹.primitiveCharacter χ.primitiveCharacter⁻¹ χ⁻¹.conductor_dvd_level
    χ.conductor_dvd_level (conductor_inv_eq_conductor χ) χ⁻¹.changeLevel_primitiveCharacter
    (by rw [map_inv, DirichletCharacter.changeLevel_primitiveCharacter]) _ _

open Classical in

def Level.ofSub {M : ℕ} [NeZero M] (Ξ : Subgroup (DirichletCharacter ℂ M)) : Level where
  KEPT := (Finset.univ.filter fun χ : DirichletCharacter ℂ M => χ ∈ Ξ).image PChar.of
  one_mem := Finset.mem_image.2 ⟨1, Finset.mem_filter.2 ⟨Finset.mem_univ _, Ξ.one_mem⟩, PChar.of_one M⟩
  inv_mem := by
    intro ψ h
    obtain ⟨χ, h1, rfl⟩ := Finset.mem_image.1 h
    exact Finset.mem_image.2 ⟨χ⁻¹, Finset.mem_filter.2 ⟨Finset.mem_univ _, Ξ.inv_mem (Finset.mem_filter.1 h1).2⟩, PChar.of_inv χ⟩
  psK := none
  psK_spec := fun _ h => by cases h
  o := Nat.card Ξ

theorem Level.mem_ofSub {M : ℕ} [NeZero M] (Ξ : Subgroup (DirichletCharacter ℂ M)) (ψ : PChar) :
    ψ ∈ (Level.ofSub Ξ).KEPT ↔ ∃ χ ∈ Ξ, PChar.of χ = ψ := by
  classical
  simp [Level.ofSub]

def Level.cyc (ψ : PChar) : Level := Level.ofSub (Subgroup.zpowers ψ.χ)

theorem Level.mem_cyc (ψ : PChar) : ψ ∈ (Level.cyc ψ).KEPT :=
  (Level.mem_ofSub _ _).2 ⟨ψ.χ, Subgroup.mem_zpowers _, ψ.of_self⟩

theorem zeroFreeOn_of_cyc {Q : PChar → Prop} (h : ∀ ψ, Q ψ → (Level.cyc ψ).ZeroFreeLevel) : ZeroFreeOn Q :=
  zeroFreeOn_of_levels fun ψ hψ => ⟨_, Level.mem_cyc ψ, h ψ hψ⟩

namespace Frame

variable (φ : Frame)

open Classical in

def lam (γ : φ.A) : ℝ := (if γ ∈ φ.A0 then 4 else 3) / (3 * (φ.o : ℝ) + 1)

open Classical in

def Shares (TT : Finset φ.A) (δ : ℝ) : Prop :=
  ∀ γ : φ.A, |((TT.filter fun t => t - γ ∈ φ.A0).card : ℝ) - φ.lam γ * (TT.card : ℝ)| ≤ δ * (TT.card : ℝ)

end Frame

structure EAtH (Λ : Level) {φ : Frame} (H : HostRaw φ) (TT : Finset φ.A) (x eps C : ℝ) : Prop where
  o_eq : φ.o = Λ.o
  kept : H.KeptInXp Λ.KEPT
  ps : H.ExceptionalCharacterKept Λ.KEPT Λ.psK
  shares : φ.Shares TT (x ^ (-1 + eps))
  bdG : H.BoundedCharsPointwise Λ.KEPT x eps
  bdL : ∀ θ ∈ H.Bounded Λ.KEPT, ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), H.IsPrimOf θ χ →
    ‖An.logDerivativeAtOne χ‖ ≤ C * Real.log x

def HType.level (T : HType) (o : ℕ) : Level := ⟨T.toKSet, o⟩

theorem EAtH.explicit_formula_error_of_host_conditions {T : HType} {κ : HConst} {X x : ℝ} {φ : Frame} {H : HostRaw φ} (hr : T.InRange X x φ.e) (hC : 0 ≤ κ.C)
    (h : HostConditions T κ X x H) {TT : Finset φ.A} (hs : φ.Shares TT (x ^ (-1 + T.eps))) :
    EAtH (T.level φ.o) H TT x T.eps (κ.C * T.J) := by
  refine ⟨rfl, h.kept, h.e, hs, h.c1, fun θ hθ N _ χ hχ => (h.b.2 θ hθ N χ hχ).trans ?_⟩
  obtain ⟨h1, h2, -⟩ := hr
  have hJ : (0 : ℝ) < T.J := by exact_mod_cast T.one_le_J
  have h3 := Real.log_le_log (Real.rpow_pos_of_pos (by linarith) _) h2
  rw [Real.log_rpow (by linarith), div_mul_eq_mul_div, one_mul, div_le_iff₀ hJ] at h3
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (by linarith) hC

end Formalism.HC

end
end


section
-- Source: Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean

noncomputable section

open NumberField

namespace UpperTheory.Top

open Formalism.HC

def VVle (E : Type) [Field E] [NumberField E] (t : ℕ) (B : ℝ) : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (ld : ∀ (p : ℕ) [Fact p.Prime], Formalism.GaloisCohomology.LData E Ω p),
    (∀ (p : ℕ) [Fact p.Prime] (e : ℕ), 0 < e → e < t → Formalism.GaloisCohomology.shaLen (ld p) (e : ℤ) ≠ ⊤) ∧
    ∀ S : Finset Nat.Primes,
      ∑ l ∈ S, Real.log (l : ℕ) *
        ∑ e ∈ Finset.Ico 1 t, ((@Formalism.GaloisCohomology.shaLen E Ω _ _ _ _ _ l ⟨l.2⟩ (@ld l ⟨l.2⟩) (e : ℤ)).toNat : ℝ) ≤ B

def IsChiField (ψ : PChar) (e q d : ℕ) (E : Type) [Field E] [NumberField E] : Prop :=
  ∃ (N : ℕ) (_ : NeZero N) (j : E →ₐ[ℚ] CyclotomicField N ℚ) (ζ : CyclotomicField N ℚ),
    2 ^ (e + 2) ∣ N ∧ ψ.N ∣ N ∧ q ∣ N ∧ d ∣ N ∧ IsPrimitiveRoot ζ N ∧
    ∀ (τ : CyclotomicField N ℚ ≃ₐ[ℚ] CyclotomicField N ℚ) (a : ℕ), τ ζ = ζ ^ a →
      ((∀ x : E, τ (j x) = j x) ↔
        (a ≡ 1 [MOD 2 ^ (e + 2)] ∨ a + 1 ≡ 0 [MOD 2 ^ (e + 2)]) ∧ ψ.val a = 1 ∧
          jacobiSym (a : ℤ) q = 1 ∧ jacobiSym (a : ℤ) d = 1)

structure WinPair (eps Y : ℝ) (q d : ℕ) : Prop where
  q_prime : q.Prime
  q_mod : q % 8 = 3
  q_lo : Y ^ (eps / 5) / 2 < Real.log q
  q_up : Real.log q ≤ Y ^ (eps / 5)
  d_prime : d.Prime
  d_mod : d % 16 = 7
  d_lo : Y ^ (eps / 5) * Real.log Y ^ 2 / 2 < Real.log d
  d_up : Real.log d ≤ Y ^ (eps / 5) * Real.log Y ^ 2
  d_q : q ∣ d + 1
  d_small : ∀ p : ℕ, p.Prime → p ≠ 2 → (p : ℝ) ≤ Y ^ (eps / 5) → p ∣ d + 1

def PageN (eps x : ℝ) (e : ℕ) : Prop := x ^ (2 + 8 * eps) ≤ (2 : ℝ) ^ e ∧ (2 : ℝ) ^ e ≤ 2 * x ^ (2 + 8 * eps)

def VAt (ψ : PChar) (eps Ct : ℝ) (q d e : ℕ) (x : ℝ) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E], IsChiField ψ e q d E → VVle E ⌊x ^ Ct⌋₊ (Real.sqrt (Real.exp (x ^ eps)))

def VWinAt (ψ : PChar) (Ct : ℝ) : Prop :=
  ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∀ e : ℝ → ℕ, (∀ x ≥ (1 : ℝ), PageN eps x (e x)) →
    ∃ J : ℝ, 1 ≤ J ∧ ∃ X0 : ℝ, ∀ X ≥ X0, ∀ q d : ℕ, WinPair eps (X ^ (1 / J)) q d →
      ∃ Y : ℝ, X ^ (1 / J) ≤ Y ∧ Y ^ (2 : ℝ) ≤ X ∧ ∀ x : ℝ, Y ≤ x → x ≤ Y ^ (2 : ℝ) → VAt ψ eps Ct q d (e x) x

def VWin : Prop := ∀ ψ : PChar, VWinAt ψ 401

theorem VVle.mono {E : Type} [Field E] [NumberField E] {t t' : ℕ} {B B' : ℝ} (h : VVle E t B) (ht : t' ≤ t) (hB : B ≤ B') :
    VVle E t' B' := by
  intro Ω _ _ _ ld
  obtain ⟨h1, h2⟩ := h Ω ld
  refine ⟨fun p _ e he1 he2 => h1 p e he1 (lt_of_lt_of_le he2 ht), fun S => ?_⟩
  refine le_trans ?_ (le_trans (h2 S) hB)
  apply Finset.sum_le_sum
  intro l _
  apply mul_le_mul_of_nonneg_left _ (Real.log_natCast_nonneg _)
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro e he
    simp only [Finset.mem_Ico] at he ⊢
    omega
  · intro e _ _
    positivity

theorem exists_pageN (eps : ℝ) (he : 0 < eps) : ∃ e : ℝ → ℕ, ∀ x ≥ (1 : ℝ), PageN eps x (e x) := by
  have : ∀ x : ℝ, ∃ e : ℕ, x ≥ 1 → PageN eps x e := by
    intro x
    by_cases hx : x ≥ 1
    · have h1 : (1 : ℝ) ≤ x ^ (2 + 8 * eps) := Real.one_le_rpow hx (by linarith)
      obtain ⟨n, a, b⟩ := exists_nat_pow_near h1 (by norm_num : (1 : ℝ) < 2)
      refine ⟨n + 1, fun _ => ⟨b.le, ?_⟩⟩
      rw [pow_succ]; linarith
    · exact ⟨0, fun h => absurd h hx⟩
  choose e he using this
  exact ⟨e, he⟩

end UpperTheory.Top

end
end


section
-- Source: Joint/LengthBudget.lean

/-! The finite sums in Alpöge’s conductor-one cohomological bound have an
equivalent formulation in terms of divisibility of a single positive integer. -/

namespace Joint.LengthBudget

private def mass (L : Nat.Primes → ℕ) (S : Finset Nat.Primes) : ℕ :=
  ∏ p ∈ S, (p:ℕ)^(L p)

private theorem mass_pos (L : Nat.Primes → ℕ) (S : Finset Nat.Primes) : 0 < mass L S :=
  Finset.prod_pos (fun p _ => pow_pos p.2.pos _)

private theorem log_mass (L : Nat.Primes → ℕ) (S : Finset Nat.Primes) :
    Real.log (mass L S) = ∑ p ∈ S, Real.log (p:ℕ) * L p := by
  unfold mass
  rw [Nat.cast_prod,Real.log_prod (fun p _ => Nat.cast_ne_zero.mpr (pow_ne_zero _ p.2.ne_zero))]
  apply Finset.sum_congr rfl
  intro p _
  rw [Nat.cast_pow,Real.log_pow,mul_comm]

private theorem mass_dvd {L : Nat.Primes → ℕ} {M : ℕ}
    (h : ∀ p : Nat.Primes, (p:ℕ)^(L p) ∣ M) (S : Finset Nat.Primes) : mass L S ∣ M := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [mass]
  | @insert p S hp hS =>
    have cop : ((p:ℕ)^(L p)).Coprime (mass L S) := by
      apply Nat.Coprime.prod_right
      intro q hq
      have hpq : (p:ℕ) ≠ (q:ℕ) := fun hh => hp (Subtype.ext hh ▸ hq)
      exact (((Nat.coprime_primes p.2 q.2).2 hpq).pow_left _).pow_right _
    simpa [mass,hp] using cop.mul_dvd_of_dvd_of_dvd (h p) hS

/-- All finite subsums are bounded exactly when one integer in the prescribed
size budget contains every required prime power. The constant B is unchanged. -/
theorem bounded_iff_common_multiple (L : Nat.Primes → ℕ) (B : ℝ) :
    (∀ S : Finset Nat.Primes, ∑ p ∈ S, Real.log (p:ℕ) * L p ≤ B) ↔
      ∃ M : ℕ, 0 < M ∧ Real.log M ≤ B ∧ ∀ p : Nat.Primes, (p:ℕ)^(L p) ∣ M := by
  classical
  constructor
  · intro h
    let bound := ⌊Real.exp B⌋₊
    let attained (a : ℕ) := ∃ S : Finset Nat.Primes, mass L S = a
    let M := Nat.findGreatest attained bound
    have hb (S : Finset Nat.Primes) : mass L S ≤ bound :=
      Nat.le_floor ((Real.log_le_iff_le_exp (by exact_mod_cast mass_pos L S)).mp
        (by rw [log_mass]; exact h S))
    have h0 : attained (mass L ∅) := ⟨∅,rfl⟩
    obtain ⟨S,hS⟩ : attained M := Nat.findGreatest_spec (hb ∅) h0
    refine ⟨M,hS ▸ mass_pos L S,by rw [← hS,log_mass]; exact h S,fun p => ?_⟩
    have hle : mass L (insert p S) ≤ M :=
      Nat.le_findGreatest (hb _) (show attained (mass L (insert p S)) from ⟨_,rfl⟩)
    have hge : M ≤ mass L (insert p S) := by
      rw [← hS]
      exact Nat.le_of_dvd (mass_pos _ _) (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.subset_insert _ _))
    rw [← le_antisymm hle hge]
    exact Finset.dvd_prod_of_mem _ (Finset.mem_insert_self p S)
  · rintro ⟨M,hM,hl,hp⟩ S
    rw [← log_mass]
    exact (Real.log_le_log (by exact_mod_cast mass_pos L S)
      (by exact_mod_cast Nat.le_of_dvd hM (mass_dvd hp S))).trans hl

/-- This is the finite-subset bound in VVle for one choice of local data.
The non-infinite length condition is retained since ENat.toNat sends infinity to zero. -/
theorem local_lengths_iff (a : Nat.Primes → ℕ → ℕ∞) (t : ℕ) (B : ℝ) :
    ((∀ (p : Nat.Primes) (e : ℕ), 0 < e → e < t → a p e ≠ ⊤) ∧
      ∀ S : Finset Nat.Primes, ∑ p ∈ S, Real.log (p:ℕ) *
        ∑ e ∈ Finset.Ico 1 t, ((a p e).toNat : ℝ) ≤ B) ↔
    ((∀ (p : Nat.Primes) (e : ℕ), 0 < e → e < t → a p e ≠ ⊤) ∧
      ∃ M : ℕ, 0 < M ∧ Real.log M ≤ B ∧ ∀ p : Nat.Primes,
        (p:ℕ)^(∑ e ∈ Finset.Ico 1 t, (a p e).toNat) ∣ M) := by
  apply and_congr_right
  intro _
  simpa only [Nat.cast_sum] using
    bounded_iff_common_multiple (fun p => ∑ e ∈ Finset.Ico 1 t, (a p e).toNat) B

end Joint.LengthBudget

#print axioms Joint.LengthBudget.bounded_iff_common_multiple
#print axioms Joint.LengthBudget.local_lengths_iff
end


section
-- Source: Compaction/LengthCertificates.lean

/-! A valuation certificate includes the finiteness of the lengths, rather than
separately converting possibly infinite lengths to natural numbers. Based on
Anton's `Joint.LengthBudget.local_lengths_iff`. -/

namespace Compaction.LengthCertificates

def Budget (a : Nat.Primes → ℕ → ℕ∞) (t : ℕ) (B : ℝ) : Prop :=
  ∃ M : ℕ, 0 < M ∧ Real.log M ≤ B ∧ ∀ p : Nat.Primes,
    ∑ e ∈ Finset.Ico 1 t, a p e ≤ (M.factorization p : ℕ∞)

private theorem cast_sum {a : Nat.Primes → ℕ → ℕ∞} {t : ℕ}
    (hf : ∀ p e, 0 < e → e < t → a p e ≠ ⊤) (p : Nat.Primes) :
    ((∑ e ∈ Finset.Ico 1 t, (a p e).toNat : ℕ) : ℕ∞) =
      ∑ e ∈ Finset.Ico 1 t, a p e := by
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro e he
  exact ENat.natCast_toNat (hf p e (Nat.succ_le_iff.mp (Finset.mem_Ico.mp he).1)
    (Finset.mem_Ico.mp he).2)

/-- The finite-subset bound is equivalent to domination by the valuations of
one positive integer. Infinite lengths cannot satisfy the right-hand side. -/
theorem local_lengths_iff (a : Nat.Primes → ℕ → ℕ∞) (t : ℕ) (B : ℝ) :
    ((∀ p e, 0 < e → e < t → a p e ≠ ⊤) ∧
      ∀ S : Finset Nat.Primes, ∑ p ∈ S, Real.log (p : ℕ) *
        ∑ e ∈ Finset.Ico 1 t, ((a p e).toNat : ℝ) ≤ B) ↔ Budget a t B := by
  rw [Joint.LengthBudget.local_lengths_iff]
  constructor
  · rintro ⟨hf, M, hM, hB, hp⟩
    refine ⟨M, hM, hB, fun p => ?_⟩
    rw [← cast_sum hf p]
    exact_mod_cast (p.2.pow_dvd_iff_le_factorization hM.ne').mp (hp p)
  · rintro ⟨M, hM, hB, hp⟩
    have hf (p : Nat.Primes) (e : ℕ) (he : 0 < e) (ht : e < t) : a p e ≠ ⊤ := by
      apply ne_top_of_le_ne_top (ENat.natCast_ne_top _)
      exact (Finset.single_le_sum (fun i _ => (zero_le : (0 : ℕ∞) ≤ a p i))
        (Finset.mem_Ico.mpr ⟨Nat.succ_le_iff.mpr he, ht⟩)).trans (hp p)
    refine ⟨hf, M, hM, hB, fun p => ?_⟩
    apply (p.2.pow_dvd_iff_le_factorization hM.ne').mpr
    have h := hp p
    rw [← cast_sum hf p] at h
    exact_mod_cast h

end Compaction.LengthCertificates

#print axioms Compaction.LengthCertificates.local_lengths_iff
end


section
-- Source: Compaction/WindowCertificates.lean

/-! A direct arithmetic interface for the quantitative Selmer-window target.

This extends Anton's `Joint.LengthBudget` and conductor-one adapter to every
`PChar`, without choosing a model for its host field. The final theorem permits
polynomial logarithmic budgets on the original windows. It does not construct
the integer certificates: that is the remaining arithmetic problem.
-/

noncomputable section

namespace Compaction.WindowCertificates

open NumberField Formalism.GaloisCohomology Formalism.HC UpperTheory.Top Filter

def LocalCertificate {E Ω : Type} [Field E] [NumberField E] [Field Ω]
    [Algebra E Ω] [IsAlgClosure E Ω]
    (ld : ∀ (p : ℕ) [Fact p.Prime], LData E Ω p) (t : ℕ) (B : ℝ) : Prop :=
  Compaction.LengthCertificates.Budget
    (fun p e => @shaLen E Ω _ _ _ _ _ p ⟨p.2⟩ (@ld p ⟨p.2⟩) (e : ℤ)) t B

def FieldCertificate (E : Type) [Field E] [NumberField E] (t : ℕ) (B : ℝ) : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (ld : ∀ (p : ℕ) [Fact p.Prime], LData E Ω p), LocalCertificate ld t B

/-- Exact equivalence, including finiteness of every length, with unchanged B. -/
theorem vvle_iff {E : Type} [Field E] [NumberField E] (t : ℕ) (B : ℝ) :
    VVle E t B ↔ FieldCertificate E t B := by
  constructor
  · intro h Ω _ _ _ ld
    obtain ⟨hf, hs⟩ := h Ω ld
    exact (Compaction.LengthCertificates.local_lengths_iff
      (fun p e => @shaLen E Ω _ _ _ _ _ p ⟨p.2⟩ (@ld p ⟨p.2⟩) (e : ℤ)) t B).mp
      ⟨fun p e he ht => @hf p ⟨p.2⟩ e he ht, hs⟩
  · intro h Ω _ _ _ ld
    have h' := (Compaction.LengthCertificates.local_lengths_iff
      (fun p e => @shaLen E Ω _ _ _ _ _ p ⟨p.2⟩ (@ld p ⟨p.2⟩) (e : ℤ)) t B).mpr
      (h Ω ld)
    refine ⟨?_, h'.2⟩
    intro p hp e he ht
    exact h'.1 ⟨p, Fact.out⟩ e he ht

def At (ψ : PChar) (Ct B : ℝ) (q d e : ℕ) (x : ℝ) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E], IsChiField ψ e q d E →
    FieldCertificate E ⌊x ^ Ct⌋₊ B

theorem at_iff (ψ : PChar) (eps Ct : ℝ) (q d e : ℕ) (x : ℝ) :
    VAt ψ eps Ct q d e x ↔ At ψ Ct (Real.sqrt (Real.exp (x ^ eps))) q d e x := by
  constructor
  · intro h E _ _ hE
    exact (vvle_iff _ _).mp (h E hE)
  · intro h E _ _ hE
    exact (vvle_iff _ _).mpr (h E hE)

/-- Any fixed real power, with any fixed multiplier, fits the original budget
eventually. The threshold may depend on eps, C, and k, but not on q, d or E. -/
theorem polynomial_budget (C k : ℝ) {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ x : ℝ in atTop, C * x ^ k ≤ Real.sqrt (Real.exp (x ^ eps)) := by
  have h := ((isLittleO_rpow_exp_pos_mul_atTop (k / eps)
    (by norm_num : (0 : ℝ) < 1 / 2)).const_mul_left C).bound (by norm_num : (0 : ℝ) < 1)
  have hc := (tendsto_rpow_atTop heps).eventually h
  filter_upwards [hc, eventually_gt_atTop (0 : ℝ)] with x hx hx0
  have hk : eps * (k / eps) = k := by field_simp
  have hp : (x ^ eps) ^ (k / eps) = x ^ k := by rw [← Real.rpow_mul hx0.le, hk]
  have hb : C * x ^ k ≤ Real.exp ((1 / 2) * x ^ eps) := by
    calc
      C * x ^ k ≤ ‖C * x ^ k‖ := le_abs_self _
      _ ≤ Real.exp ((1 / 2) * x ^ eps) := by
        simpa only [hp, one_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hx
  simpa only [one_div_mul_eq_div, Real.exp_half] using hb

/-- This predicate retains the original order: choose J and an outer threshold,
then q,d, then one Y, before requiring the bound for every x in [Y,Y²]. -/
def PolynomialWindows (ψ : PChar) (Ct : ℝ) : Prop :=
  ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∀ e : ℝ → ℕ,
    (∀ x ≥ (1 : ℝ), PageN eps x (e x)) →
    ∃ J : ℝ, 1 ≤ J ∧ ∃ C k X0 : ℝ, ∀ X ≥ X0, ∀ q d : ℕ,
      WinPair eps (X ^ (1 / J)) q d →
      ∃ Y : ℝ, X ^ (1 / J) ≤ Y ∧ Y ^ (2 : ℝ) ≤ X ∧
        ∀ x : ℝ, Y ≤ x → x ≤ Y ^ (2 : ℝ) → At ψ Ct (C * x ^ k) q d (e x) x

/-- A polynomial bound for the logarithms of actual certificates suffices for
the archive's full Selmer-window target, for an arbitrary primitive character. -/
theorem polynomial_windows_suffice {ψ : PChar} {Ct : ℝ}
    (h : PolynomialWindows ψ Ct) : VWinAt ψ Ct := by
  intro eps heps hu e he
  obtain ⟨J, hJ, C, k, X0, hw⟩ := h eps heps hu e he
  obtain ⟨R, hR⟩ := eventually_atTop.mp (polynomial_budget C k heps)
  have hJpos : 0 < 1 / J := by positivity
  obtain ⟨A, hA⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop hJpos).eventually (eventually_ge_atTop R))
  refine ⟨J, hJ, max X0 A, ?_⟩
  intro X hX q d hp
  obtain ⟨Y, hY, hYX, hs⟩ := hw X (le_trans (le_max_left _ _) hX) q d hp
  refine ⟨Y, hY, hYX, fun x hxl hxu => ?_⟩
  intro E _ _ hE
  exact ((vvle_iff _ _).mpr (hs x hxl hxu E hE)).mono le_rfl
    (hR x ((hA X (le_trans (le_max_right _ _) hX)).trans (hY.trans hxl)))

theorem all_characters_suffice (h : ∀ ψ : PChar, PolynomialWindows ψ 401) : VWin :=
  fun ψ => polynomial_windows_suffice (h ψ)

end Compaction.WindowCertificates

#print axioms Compaction.WindowCertificates.vvle_iff
#print axioms Compaction.WindowCertificates.at_iff
#print axioms Compaction.WindowCertificates.polynomial_budget
#print axioms Compaction.WindowCertificates.polynomial_windows_suffice
#print axioms Compaction.WindowCertificates.all_characters_suffice
end
end
