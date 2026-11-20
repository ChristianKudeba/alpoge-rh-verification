import Main

/-!
Complete-proof entrypoints: importing Main requires the full substantive
Alpöge source tree and its pinned dependencies. This file is not self-contained.
No conditional nonvanishing assumption is introduced by these wrappers.
-/

namespace PrincipiaFullVerification

theorem riemannHypothesis : RiemannHypothesis :=
  _root_.riemannHypothesis

theorem riemannZeta_eq_zero_re :
    ∀ s : ℂ, riemannZeta s = 0 →
      (¬ ∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) → s ≠ 1 → s.re = 1 / 2 :=
  _root_.riemannZeta_eq_zero_re

theorem LFunction_ne_zero_of_half_lt_re :
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
      1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) →
      DirichletCharacter.LFunction χ s ≠ 0 :=
  _root_.LFunction_ne_zero_of_half_lt_re

theorem LFunction_eq_zero_re :
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
      0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 →
      s.re = 1 / 2 :=
  _root_.LFunction_eq_zero_re

theorem LFunction_eq_zero_re_of_isPrimitive :
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
      ∀ s : ℂ, 0 < s.re → s.re < 1 →
        DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2 :=
  _root_.LFunction_eq_zero_re_of_isPrimitive

end PrincipiaFullVerification
