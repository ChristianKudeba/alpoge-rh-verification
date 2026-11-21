import Compaction.Weber
import Compaction.ClosedCohomologyInputs
import Compaction.DyadicWindows
import Joint.DyadicRankWindow
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.ABoundOfIsTower
import Development.AutomorphicArithmetic.AutomorphicVarieties.CMFieldExponentialBounds.AdmissibleOfPageN

/-! Closed conductor-one dyadic certificates with the explicit rank 24 window.
The proved Weber theorem supplies the zero-rank cyclotomic base. This route
does not import the general Ferrero--Washington proof. -/

noncomputable section
namespace Compaction.PrincipalDyadicClosed
open NumberField Formalism.HC Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V

theorem tower_bound : Two.TowerBound :=
  fun l _ L _ _ R h => PropA.aBound_of_isTower ClosedCohomologyInputs.duality
    ClosedCohomologyInputs.local_finiteness ClosedCohomologyInputs.local_tate l L R h

/-- The exceptional-set cardinality is exactly the uniform bound 24, using the
proved zero-rank pure cyclotomic base and two moving quadratic characters. -/
theorem control {CK Ct eps : ℝ} (hCK : 0 < CK) (hCt : 0 ≤ Ct) (heps : 0 < eps)
    (hK : LemmaK CK) (e : ℝ → ℕ)
    (admit : admitted 4 Ct e fun x => ⌊x^Ct⌋₊) :
    DyadicWindows.Control PChar.one 24 (eps/(2*CK)) Ct eps e := by
  have hexc := Joint.DyadicRankWindow.exceptions Weber.weber tower_bound hCK hCt heps hK e admit
  intro J hJ
  obtain ⟨x₀, H⟩ := hexc J hJ
  refine ⟨x₀, fun X q d pair hlog => ?_⟩
  obtain ⟨exc, small, bound⟩ := H X q d pair hlog
  refine ⟨exc, small, fun x hx hxl hxu hg E _ _ hE => ?_⟩
  exact bound x hx hxl hxu hg E ((isCompField_ofChar PChar.one (e x) q d E).mpr hE)

def exponent (CK Ct eps : ℝ) : ℝ := 2^25*(2*CK*Ct/eps)^24

/-- The exact original window quantifiers hold at the explicit exponent,
with actual integers 2^(sum of Selmer lengths) and their proved size budgets. -/
theorem windows_at {CK Ct eps : ℝ} (hCK : 1 ≤ CK) (hCt : 1 ≤ Ct)
    (heps : 0 < eps) (htiny : eps < 1/52) (hK : LemmaK CK)
    (e : ℝ → ℕ) (page : ∀ x ≥ (1:ℝ), PageN eps x (e x)) :
    1 ≤ exponent CK Ct eps ∧ DyadicWindows.Window PChar.one (exponent CK Ct eps) Ct eps e := by
  have hCKpos : 0 < CK := by linarith
  have heta : 0 < eps/(2*CK) := by positivity
  have hsmall : eps/(2*CK) ≤ Ct := by
    apply le_trans _ hCt
    rw [div_le_one (by positivity)]
    linarith
  have hratio : 1 ≤ 2*CK*Ct/eps := by
    rw [one_le_div heps]
    have hprod := one_le_mul_of_one_le_of_one_le hCK hCt
    nlinarith
  refine ⟨one_le_mul_of_one_le_of_one_le (by norm_num : (1:ℝ) ≤ 2^25)
    (one_le_pow₀ hratio), ?_⟩
  have h := DyadicWindows.select_window PChar.one 24 (eps/(2*CK)) Ct eps e heta hsmall heps
    (control hCKpos (by linarith) heps hK e (admissible_of_pageN heps htiny hCt page))
  have heq : Ct/(eps/(2*CK)) = 2*CK*Ct/eps := by rw [div_div_eq_mul_div]; ring
  simpa only [heq, exponent] using h

/-- A single closed exponent CK supplies all conductor-one dyadic certificate
windows. There is no unproved Weber or class-field input among the arguments. -/
theorem windows : ∃ CK : ℝ, 1 ≤ CK ∧ ∀ Ct eps : ℝ, 1 ≤ Ct → 0 < eps → eps < 1/52 →
    ∀ e : ℝ → ℕ, (∀ x ≥ (1:ℝ), PageN eps x (e x)) →
      1 ≤ exponent CK Ct eps ∧ DyadicWindows.Window PChar.one (exponent CK Ct eps) Ct eps e := by
  obtain ⟨CK, hCK, hK⟩ := ClosedCohomologyInputs.high_twist
  exact ⟨CK, hCK, fun Ct eps hCt heps htiny e page => windows_at hCK hCt heps htiny hK e page⟩

end Compaction.PrincipalDyadicClosed

#print axioms Compaction.PrincipalDyadicClosed.tower_bound
#print axioms Compaction.PrincipalDyadicClosed.control
#print axioms Compaction.PrincipalDyadicClosed.windows_at
#print axioms Compaction.PrincipalDyadicClosed.windows
