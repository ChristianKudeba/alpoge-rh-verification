import Mathlib
namespace AggressiveDependencies
set_option autoImplicit false
set_option relaxedAutoImplicit false


def Claim.HalfPlane : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ), 1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0

def Claim.Strip : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ), 0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2

def Claim.Zeta : Prop :=
  ∀ s : ℂ, riemannZeta s = 0 → (¬ ∃ n : ℕ, s = -2 * (n + 1)) → s ≠ 1 → s.re = 1 / 2


def UpperTheory.EveryCharacter : Prop := Claim.HalfPlane


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


theorem UpperTheory.zeta_ne_zero_of_everyCharacter (h : UpperTheory.EveryCharacter) : ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → riemannZeta s ≠ 0 := fun s hs h1 => by
  have := h 1 1 s hs (Or.inr h1)
  rwa [DirichletCharacter.LFunction_modOne_eq] at this

theorem UpperTheory.riemannHypothesis_of_everyCharacter (h : UpperTheory.EveryCharacter) : RiemannHypothesis :=
  Formalism.VW.rh_of_right (UpperTheory.zeta_ne_zero_of_everyCharacter h)

example : UpperTheory.EveryCharacter = Claim.HalfPlane := rfl
example (h : UpperTheory.EveryCharacter) :
    UpperTheory.riemannHypothesis_of_everyCharacter h =
      Formalism.VW.rh_of_right (UpperTheory.zeta_ne_zero_of_everyCharacter h) := rfl
#print axioms UpperTheory.zeta_ne_zero_of_everyCharacter
#print axioms UpperTheory.riemannHypothesis_of_everyCharacter
#print axioms Formalism.VW.rh_of_right
end AggressiveDependencies
