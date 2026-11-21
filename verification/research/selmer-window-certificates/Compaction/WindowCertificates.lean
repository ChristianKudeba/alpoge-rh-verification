import Compaction.LengthCertificates
import Development.AutomorphicArithmetic.CharacterBoxes.ExistsPageN

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
