import Mathlib

set_option autoImplicit false

section
-- Source: Development/AutomorphicArithmetic/CharacterBoxes/HalfPlane.lean

def Claim.HalfPlane : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ), 1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0

def Claim.Strip : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ), 0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2

def Claim.Zeta : Prop :=
  ∀ s : ℂ, riemannZeta s = 0 → (¬ ∃ n : ℕ, s = -2 * (n + 1)) → s ≠ 1 → s.re = 1 / 2
end


section
-- Source: Development/AutomorphicArithmetic/CharacterBoxes/EveryCharacterStatement.lean

def UpperTheory.EveryCharacter : Prop := Claim.HalfPlane
end


section
-- Source: Formalism/GammaFactorNonvanishing/RhOfRight.lean

open Complex

theorem Formalism.VW.rh_of_right (hz : ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → riemannZeta s ≠ 0) : RiemannHypothesis := by
  intro s hs htriv hs1
  rcases lt_trichotomy s.re (1 / 2) with hlt | heq | hgt
  · have hs0 : s ≠ 0 := by
      rintro rfl
      norm_num [riemannZeta_zero] at hs
    have hG : Gammaℝ s ≠ 0 := by
      intro hg
      obtain ⟨n, hn⟩ := Gammaℝ_eq_zero_iff.mp hg
      cases n with
      | zero => exact hs0 (by simpa using hn)
      | succ n => exact htriv ⟨n, by rw [hn]; push_cast; ring⟩
    rw [riemannZeta_def_of_ne_zero hs0, div_eq_zero_iff] at hs
    have hc := hs.resolve_right hG
    have ht : 1 - s ≠ 1 := fun e => hs0 (by linear_combination -e)
    have hright : 1 / 2 < (1 - s).re := by
      rw [sub_re, one_re]
      linarith
    apply False.elim (hz (1 - s) hright ht ?_)
    rw [riemannZeta_def_of_ne_zero (sub_ne_zero.mpr hs1.symm),
      completedRiemannZeta_one_sub, hc, zero_div]
  · exact heq
  · exact False.elim (hz s hgt hs1 hs)
end


section
-- Source: Formalism/GammaFactorNonvanishing/GammaFactor.lean

open Complex DirichletCharacter

theorem Formalism.VW.gammaFactor_ne_zero {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 0 < s.re) : gammaFactor χ s ≠ 0 := by
  rcases χ.even_or_odd with h | h
  · rw [h.gammaFactor_def]; exact Gammaℝ_ne_zero_of_re_pos hs
  · rw [h.gammaFactor_def]; exact Gammaℝ_ne_zero_of_re_pos (by rw [add_re, one_re]; linarith)

theorem Formalism.VW.differentiable_gammaFactor_inv {N : ℕ} (χ : DirichletCharacter ℂ N) :
    Differentiable ℂ (fun s => (DirichletCharacter.gammaFactor χ s)⁻¹) := by
  rcases χ.even_or_odd with h | h <;> simp only [h.gammaFactor_def]
  · exact Complex.differentiable_Gammaℝ_inv
  · exact Complex.differentiable_Gammaℝ_inv.comp (differentiable_id.add_const 1)

theorem Formalism.VW.rootNumber_ne_zero {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) : χ.rootNumber ≠ 0 := by
  intro h
  have h1 := hχ.completedLFunction_one_sub (-1)
  rw [h, mul_zero, zero_mul] at h1
  have h2 := χ.LFunction_eq_completed_div_gammaFactor (1 - -1) (Or.inl (by norm_num))
  rw [h1, zero_div] at h2
  exact χ.LFunction_ne_zero_of_one_le_re (Or.inr (by norm_num)) (by norm_num) h2
end


section
-- Source: Development/AutomorphicArithmetic/CharacterBoxes/EulerFactors.lean

open Complex

namespace Claim

theorem factor_ne_zero {M : ℕ} (ψ : DirichletCharacter ℂ M) {s : ℂ} (hs : 0 < s.re) (p : ℕ)
    (hp : p.Prime) : (1 : ℂ) - ψ p * (p : ℂ) ^ (-s) ≠ 0 := by
  intro h
  have h1 : ψ p * (p : ℂ) ^ (-s) = 1 := by linear_combination -h
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hpow : ‖(p : ℂ) ^ (-s)‖ < 1 := by
    rw [Complex.norm_natCast_cpow_of_pos hp.pos, Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
  have hn : ‖ψ p * (p : ℂ) ^ (-s)‖ < 1 := by
    rw [norm_mul]
    calc ‖ψ p‖ * ‖(p : ℂ) ^ (-s)‖ ≤ 1 * ‖(p : ℂ) ^ (-s)‖ := by
          gcongr; exact ψ.norm_le_one _
      _ < 1 := by rw [one_mul]; exact hpow
  rw [h1, norm_one] at hn
  exact lt_irrefl _ hn

end Claim
end


section
-- Source: Development/AutomorphicArithmetic/CharacterBoxes/ClaimStrip.lean

open Complex

namespace Claim

theorem prim_zero {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) [NeZero χ.conductor] {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1) (h : DirichletCharacter.LFunction χ s = 0) :
    DirichletCharacter.LFunction χ.primitiveCharacter s = 0 := by
  have hs : s ≠ 1 := fun e => by rw [e, Complex.one_re] at hs1; exact lt_irrefl _ hs1
  have key := DirichletCharacter.LFunction_changeLevel χ.conductor_dvd_level
    χ.primitiveCharacter (Or.inr hs)
  rw [χ.changeLevel_primitiveCharacter, h] at key
  exact (mul_eq_zero.mp key.symm).resolve_right
    (Finset.prod_ne_zero_iff.mpr fun p hp =>
      factor_ne_zero _ hs0 p (Nat.prime_of_mem_primeFactors hp))

theorem gamma_ne_zero {M : ℕ} [NeZero M] (φ : DirichletCharacter ℂ M) {t : ℂ} (ht : 0 < t.re) :
    DirichletCharacter.gammaFactor φ t ≠ 0 :=
  Formalism.VW.gammaFactor_ne_zero φ ht

theorem prim_reflect {M : ℕ} [NeZero M] (ψ : DirichletCharacter ℂ M) (hψ : ψ.IsPrimitive) {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1) (h : DirichletCharacter.LFunction ψ s = 0) :
    DirichletCharacter.LFunction ψ⁻¹ (1 - s) = 0 := by
  have hs0' : s ≠ 0 := fun e => by rw [e, Complex.zero_re] at hs0; exact lt_irrefl _ hs0
  have ht0 : 0 < (1 - s).re := by rw [Complex.sub_re, Complex.one_re]; linarith
  have ht0' : 1 - s ≠ 0 := fun e => by rw [e, Complex.zero_re] at ht0; exact lt_irrefl _ ht0
  have hc : DirichletCharacter.completedLFunction ψ s = 0 := by
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor ψ s (Or.inl hs0'),
      div_eq_zero_iff] at h
    exact h.resolve_right (gamma_ne_zero ψ hs0)
  have hψ' : (ψ⁻¹).IsPrimitive := by
    rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]; exact hψ
  have fe := hψ'.completedLFunction_one_sub s
  rw [inv_inv, hc, mul_zero] at fe
  rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor ψ⁻¹ (1 - s) (Or.inl ht0'), fe,
    zero_div]

theorem strip (h : HalfPlane) : Strip := by
  unfold HalfPlane at h
  intro N _ χ s hs0 hs1 hz
  have hs : s ≠ 1 := fun e => by rw [e, Complex.one_re] at hs1; exact lt_irrefl _ hs1
  have hs0' : s ≠ 0 := fun e => by rw [e, Complex.zero_re] at hs0; exact lt_irrefl _ hs0
  rcases lt_trichotomy s.re (1 / 2) with hlt | heq | hgt
  · exfalso
    haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    have hp := prim_zero χ hs0 hs1 hz
    have hr := prim_reflect χ.primitiveCharacter χ.primitiveCharacter_isPrimitive hs0 hs1 hp
    have ht : (1 : ℂ) - s ≠ 1 := fun e => hs0' (sub_eq_self.mp e)
    exact h χ.conductor χ.primitiveCharacter⁻¹ (1 - s)
      (by rw [Complex.sub_re, Complex.one_re]; linarith) (Or.inr ht) hr
  · exact heq
  · exact absurd hz (h N χ s hgt (Or.inr hs))

theorem zeta (h : HalfPlane) : Zeta :=
  Formalism.VW.rh_of_right fun s hs hs1 => by
    simpa only [DirichletCharacter.LFunction_modOne_eq] using
      h 1 (1 : DirichletCharacter ℂ 1) s hs (Or.inr hs1)

theorem zeta_iff : Zeta ↔ RiemannHypothesis := Iff.rfl

end Claim
end


section
-- Source: Formalism/GammaFactorNonvanishing/CritLine.lean

open Complex DirichletCharacter

theorem Formalism.VW.critLine (h : UpperTheory.EveryCharacter) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (s : ℂ)
    (h0 : 0 < s.re) (h1 : s.re < 1) (hz : LFunction χ s = 0) : s.re = 1 / 2 :=
  Claim.strip h N χ s h0 h1 hz

theorem Formalism.VW.rh_of_every (h : UpperTheory.EveryCharacter) : RiemannHypothesis :=
  Claim.zeta h
end


section
-- Source: exact PChar and ZeroFree definitions
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

def PChar.ZeroFreeAbove (ψ : PChar) (θ : ℝ) : Prop :=
  ∀ s : ℂ, θ < s.re → DirichletCharacter.LFunction ψ.χ s ≠ 0

def ZeroFreeOn (Q : PChar → Prop) : Prop := ∀ ψ : PChar, Q ψ → ψ.ZeroFreeAbove (1 / 2)

def ZeroFreeEven : Prop := ZeroFreeOn fun ψ => ψ.χ.Even

def ZeroFreeAll : Prop := ZeroFreeOn fun _ => True

end Formalism.HC
end
end


section
-- Source: Development/AutomorphicArithmetic/CharacterBoxes/Imprimitive.lean

open Formalism.HC

theorem UpperTheory.Top.imprimitive :
    ZeroFreeAll → ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ), 1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) →
      DirichletCharacter.LFunction χ s ≠ 0 := by
  intro h N _ χ s hs hχs
  haveI : NeZero χ.conductor := (PChar.of χ).ne
  have hL : DirichletCharacter.LFunction χ.primitiveCharacter s ≠ 0 := h (PChar.of χ) trivial s hs
  have hχ' : χ.primitiveCharacter ≠ 1 ∨ s ≠ 1 := by
    rcases hχs with hχ | hs1
    · left
      intro h1
      apply hχ
      rw [← χ.changeLevel_primitiveCharacter, h1, DirichletCharacter.changeLevel_one]
    · exact Or.inr hs1
  have hrw := DirichletCharacter.LFunction_changeLevel χ.conductor_dvd_level χ.primitiveCharacter hχ'
  rw [χ.changeLevel_primitiveCharacter] at hrw
  rw [hrw]
  refine mul_ne_zero hL (Finset.prod_ne_zero_iff.mpr fun p hp => ?_)
  exact Claim.factor_ne_zero χ.primitiveCharacter (by linarith) p
    (Nat.prime_of_mem_primeFactors hp)
end


section
-- Source: exact PI.ZW.Transfer definition
noncomputable section
namespace PI.ZW
def Transfer : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 →
    DirichletCharacter.LFunction χ ρ = 0 →
    DirichletCharacter.LFunction χ⁻¹ (1 - ρ) = 0 ∧
    analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ ≤
      analyticOrderNatAt (DirichletCharacter.LFunction χ⁻¹) (1 - ρ)

end PI.ZW
end
end


section
-- Source: Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZeroWindow/Transfer.lean

noncomputable section

open Complex Filter Topology

namespace PI.ZW

open DirichletCharacter

lemma differentiable_gammaFactor_inv {N : ℕ} (χ : DirichletCharacter ℂ N) :
    Differentiable ℂ (fun s => (gammaFactor χ s)⁻¹) :=
  Formalism.VW.differentiable_gammaFactor_inv χ

lemma gammaFactor_ne_zero_of_re_pos {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 0 < s.re) : gammaFactor χ s ≠ 0 :=
  Formalism.VW.gammaFactor_ne_zero χ hs

lemma isPrimitive_inv {N : ℕ} {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    χ⁻¹.IsPrimitive := by
  rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]
  exact (DirichletCharacter.isPrimitive_def χ).mp hχ

lemma rootNumber_ne_zero {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    rootNumber χ ≠ 0 :=
  Formalism.VW.rootNumber_ne_zero hχ

lemma isOpen_strip : IsOpen {s : ℂ | 0 < s.re ∧ s.re < 1} := by
  exact (isOpen_lt continuous_const Complex.continuous_re).inter (isOpen_lt Complex.continuous_re continuous_const)

theorem transfer : Transfer := by
  intro N _ χ hχ ρ h0 h1 hz
  have hχi := isPrimitive_inv hχ
  have hstrip : ∀ s : ℂ, 0 < s.re → s.re < 1 → 0 < (1 - s).re := fun s _ h => by simp; linarith
  have hfun : ∀ s : ℂ, 0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ⁻¹ (1 - s) =
      ((N : ℂ) ^ (s - 1 / 2) * rootNumber χ⁻¹ * gammaFactor χ s * (gammaFactor χ⁻¹ (1 - s))⁻¹) *
        DirichletCharacter.LFunction χ s := by
    intro s hs0 hs1
    have h1s := hstrip s hs0 hs1
    have hg1 := gammaFactor_ne_zero_of_re_pos χ⁻¹ h1s
    have hg0 := gammaFactor_ne_zero_of_re_pos χ hs0
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ⁻¹ (1 - s)
        (Or.inl fun h => by rw [h] at h1s; simp at h1s),
      hχi.completedLFunction_one_sub s, inv_inv,
      DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s (Or.inl fun h => by rw [h] at hs0; simp at hs0)]
    field_simp
  refine ⟨by rw [hfun ρ h0 h1, hz, mul_zero], ?_⟩
  have hρU : {s : ℂ | 0 < s.re ∧ s.re < 1} ∈ 𝓝 ρ := isOpen_strip.mem_nhds ⟨h0, h1⟩
  have hHd : DifferentiableOn ℂ (fun s : ℂ => (N : ℂ) ^ (s - 1 / 2) * rootNumber χ⁻¹ * gammaFactor χ s *
      (gammaFactor χ⁻¹ (1 - s))⁻¹) {s | 0 < s.re ∧ s.re < 1} := by
    intro s hs
    have hg0 := gammaFactor_ne_zero_of_re_pos χ hs.1
    have hdg : DifferentiableAt ℂ (gammaFactor χ) s := by
      have h := ((differentiable_gammaFactor_inv χ) s).inv (inv_ne_zero hg0)
      have e : (fun x => (gammaFactor χ x)⁻¹)⁻¹ = gammaFactor χ := funext fun x => by
        simp only [Pi.inv_apply, inv_inv]
      rwa [e] at h
    have hdg1 : DifferentiableAt ℂ (fun s => (gammaFactor χ⁻¹ (1 - s))⁻¹) s :=
      ((differentiable_gammaFactor_inv χ⁻¹) (1 - s)).comp s ((differentiableAt_const 1).sub differentiableAt_id)
    have hcp : DifferentiableAt ℂ (fun s : ℂ => (N : ℂ) ^ (s - 1 / 2)) s :=
      (differentiableAt_id.sub_const _).const_cpow (Or.inl (by exact_mod_cast NeZero.ne N))
    exact (((hcp.mul_const _).mul hdg).mul hdg1).differentiableWithinAt
  have hLd : DifferentiableOn ℂ (DirichletCharacter.LFunction χ) {s | 0 < s.re ∧ s.re < 1} :=
    fun s hs => (DirichletCharacter.differentiableAt_LFunction χ s
      (Or.inl fun h => by rw [h] at hs; simp at hs)).differentiableWithinAt
  have hHa := hHd.analyticAt hρU
  have hLa := hLd.analyticAt hρU
  have hH0 : (N : ℂ) ^ (ρ - 1 / 2) * rootNumber χ⁻¹ * gammaFactor χ ρ * (gammaFactor χ⁻¹ (1 - ρ))⁻¹ ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ (rootNumber_ne_zero hχi))
      (gammaFactor_ne_zero_of_re_pos χ h0)) (inv_ne_zero (gammaFactor_ne_zero_of_re_pos χ⁻¹ (hstrip ρ h0 h1)))
    rw [Ne, Complex.cpow_eq_zero_iff]
    simp [NeZero.ne N]
  have key : analyticOrderAt (DirichletCharacter.LFunction χ⁻¹) (1 - ρ) =
      analyticOrderAt (DirichletCharacter.LFunction χ) ρ := by
    have e1 := analyticOrderAt_comp_of_deriv_ne_zero (f := DirichletCharacter.LFunction χ⁻¹)
      (g := fun s : ℂ => 1 - s) (z₀ := ρ) (analyticAt_const.sub analyticAt_id) (by simp)
    rw [← e1]
    have e2 : (DirichletCharacter.LFunction χ⁻¹ ∘ fun s : ℂ => 1 - s) =ᶠ[𝓝 ρ]
        ((fun s : ℂ => (N : ℂ) ^ (s - 1 / 2) * rootNumber χ⁻¹ * gammaFactor χ s * (gammaFactor χ⁻¹ (1 - s))⁻¹) *
          DirichletCharacter.LFunction χ) :=
      Filter.eventually_of_mem hρU fun s hs => hfun s hs.1 hs.2
    rw [analyticOrderAt_congr e2, analyticOrderAt_mul hHa hLa, (hHa.analyticOrderAt_eq_zero).mpr hH0, zero_add]
  have e : analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ =
      analyticOrderNatAt (DirichletCharacter.LFunction χ⁻¹) (1 - ρ) := by
    simp only [analyticOrderNatAt, key]
  exact e.le

end PI.ZW
end
end


section
-- Source: exact GlobalTheory.Mem.An.zmult definition
noncomputable section
namespace GlobalTheory.Mem.An
def zmult {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (ρ : ℂ) : ℕ :=
  analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ

end GlobalTheory.Mem.An
end
end


section
-- Source: Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/DirichletLZeroSymmetry.lean

open Filter Topology Complex GlobalTheory.Mem.An

namespace GlobalTheory.Mem.An

section
variable {q : ℕ}

theorem zsym_gammaFactor_ne_zero (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 0 < s.re) :
    χ.gammaFactor s ≠ 0 :=
  Formalism.VW.gammaFactor_ne_zero χ hs

theorem zsym_differentiable_gammaFactor_inv (χ : DirichletCharacter ℂ q) :
    Differentiable ℂ (fun s => (χ.gammaFactor s)⁻¹) :=
  Formalism.VW.differentiable_gammaFactor_inv χ

variable [NeZero q]

theorem zsym_rootNumber_ne_zero {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) :
    χ.rootNumber ≠ 0 :=
  Formalism.VW.rootNumber_ne_zero hχ

noncomputable def zsymFactor (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  (q : ℂ) ^ ((1 - s) - 1 / 2) * χ.rootNumber * (χ.gammaFactor s)⁻¹ / (χ⁻¹.gammaFactor (1 - s))⁻¹

theorem zsym_eq {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) {s : ℂ} (h0 : 0 < s.re)
    (h1 : s.re < 1) : χ.LFunction s = zsymFactor χ s * χ⁻¹.LFunction (1 - s) := by
  have hs0 : s ≠ 0 := by rintro rfl; simp at h0
  have hs1 : 1 - s ≠ 0 := by
    intro h; rw [sub_eq_zero] at h; subst h; simp at h1
  have h2 := hχ.completedLFunction_one_sub (1 - s)
  rw [sub_sub_cancel] at h2
  have g1 := zsym_gammaFactor_ne_zero χ h0
  have g2 := zsym_gammaFactor_ne_zero χ⁻¹ (s := 1 - s) (by simp; linarith)
  rw [χ.LFunction_eq_completed_div_gammaFactor s (Or.inl hs0),
    χ⁻¹.LFunction_eq_completed_div_gammaFactor (1 - s) (Or.inl hs1), h2, zsymFactor]
  field_simp

theorem zsymFactor_ne_zero {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) : zsymFactor χ s ≠ 0 := by
  have g1 := zsym_gammaFactor_ne_zero χ h0
  have g2 := zsym_gammaFactor_ne_zero χ⁻¹ (s := 1 - s) (by simp; linarith)
  have g3 := zsym_rootNumber_ne_zero hχ
  have g4 : (q : ℂ) ^ ((1 - s) - 1 / 2) ≠ 0 := by
    simp [cpow_eq_zero_iff, NeZero.ne q]
  unfold zsymFactor
  exact div_ne_zero (mul_ne_zero (mul_ne_zero g4 g3) (inv_ne_zero g1)) (inv_ne_zero g2)

theorem zsymFactor_analyticAt (χ : DirichletCharacter ℂ q) {s : ℂ}
    (h1 : s.re < 1) : AnalyticAt ℂ (zsymFactor χ) s := by
  have g2 := zsym_gammaFactor_ne_zero χ⁻¹ (s := 1 - s) (by simp; linarith)
  have d1 : Differentiable ℂ (fun s : ℂ => (q : ℂ) ^ ((1 - s) - 1 / 2)) := by
    have : NeZero (q : ℂ) := ⟨by exact_mod_cast NeZero.ne q⟩
    fun_prop
  have d2 : Differentiable ℂ (fun s : ℂ => (χ⁻¹.gammaFactor (1 - s))⁻¹) :=
    (zsym_differentiable_gammaFactor_inv χ⁻¹).comp (differentiable_id.const_sub 1)
  have d3 := (d1.mul_const χ.rootNumber).mul (zsym_differentiable_gammaFactor_inv χ)
  exact (d3.analyticAt s).div (d2.analyticAt s) (inv_ne_zero g2)

theorem zsym_analyticAt_LFunction (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : s ≠ 1) :
    AnalyticAt ℂ χ.LFunction s := by
  refine DifferentiableOn.analyticAt (s := {1}ᶜ) (fun z hz => ?_)
    (isOpen_compl_singleton.mem_nhds hs)
  exact (χ.differentiableAt_LFunction z (Or.inl hz)).differentiableWithinAt

end

theorem zeros_symm_one_sub : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
    ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 →
      ((DirichletCharacter.LFunction χ ρ = 0 ↔ DirichletCharacter.LFunction χ⁻¹ (1 - ρ) = 0) ∧
        zmult χ ρ = zmult χ⁻¹ (1 - ρ)) := by
  intro q _ χ hχ ρ h0 h1
  have hne := zsymFactor_ne_zero hχ h0 h1
  refine ⟨by rw [zsym_eq hχ h0 h1]; simp [hne], ?_⟩
  have hev : χ.LFunction =ᶠ[𝓝 ρ] zsymFactor χ * (χ⁻¹.LFunction ∘ fun s => 1 - s) := by
    have a : ∀ᶠ s : ℂ in 𝓝 ρ, 0 < s.re := (isOpen_lt continuous_const continuous_re).mem_nhds h0
    have b : ∀ᶠ s : ℂ in 𝓝 ρ, s.re < 1 := (isOpen_lt continuous_re continuous_const).mem_nhds h1
    filter_upwards [a, b] with s a b
    exact zsym_eq hχ a b
  have hρ : 1 - ρ ≠ 1 := by
    intro h; rw [sub_eq_self] at h; subst h; simp at h0
  have hL := zsym_analyticAt_LFunction χ⁻¹ hρ
  have hg : AnalyticAt ℂ (fun s : ℂ => 1 - s) ρ := by fun_prop
  have hf := zsymFactor_analyticAt χ h1
  unfold zmult analyticOrderNatAt
  congr 1
  rw [analyticOrderAt_congr hev, analyticOrderAt_mul hf (AnalyticAt.comp hL hg),
    hf.analyticOrderAt_eq_zero.2 hne, zero_add,
    analyticOrderAt_comp_of_deriv_ne_zero hg (by simp)]

end GlobalTheory.Mem.An
end


section
-- Source: src/Development/AutomorphicArithmetic/MeanSquareBounds/PsiThin.lean exact changed declaration
namespace CompactionReflectionCheck0
private theorem pt_zero_symm {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) {ρ : ℂ}
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hz : DirichletCharacter.LFunction χ ρ = 0) :
    DirichletCharacter.LFunction χ⁻¹ (1 - ρ) = 0 :=
  Claim.prim_reflect χ hχ h0 h1 hz
#print axioms pt_zero_symm
end CompactionReflectionCheck0
end


section
-- Source: src/Formalism/SharpRestriction/GlobalSchurBounds/ShortIntervalPrimes.lean exact changed declaration
namespace CompactionReflectionCheck1
theorem isPrimitive_inv {N : ℕ} {χ : DirichletCharacter ℂ N} (h : χ.IsPrimitive) :
    χ⁻¹.IsPrimitive :=
  by
  rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]
  exact h
#print axioms isPrimitive_inv
end CompactionReflectionCheck1
end


section
-- Source: src/Formalism/SharpRestriction/GlobalSchurBounds/ShortIntervalPrimes.lean exact changed declaration
namespace CompactionReflectionCheck2
theorem zero_symm {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) {ρ : ℂ}
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hz : DirichletCharacter.LFunction χ ρ = 0) :
    DirichletCharacter.LFunction χ⁻¹ (1 - ρ) = 0 :=
  Claim.prim_reflect χ hχ h0 h1 hz
#print axioms zero_symm
end CompactionReflectionCheck2
end

example : UpperTheory.EveryCharacter = Claim.HalfPlane := rfl
#print axioms Formalism.VW.rh_of_right
#print axioms Formalism.VW.gammaFactor_ne_zero
#print axioms Formalism.VW.differentiable_gammaFactor_inv
#print axioms Formalism.VW.rootNumber_ne_zero
#print axioms Claim.factor_ne_zero
#print axioms Claim.strip
#print axioms Claim.zeta
#print axioms Formalism.VW.critLine
#print axioms Formalism.VW.rh_of_every
#print axioms UpperTheory.Top.imprimitive
#print axioms PI.ZW.transfer
#print axioms GlobalTheory.Mem.An.zeros_symm_one_sub
