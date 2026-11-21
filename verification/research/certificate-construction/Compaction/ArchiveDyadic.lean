import Compaction.DyadicWindows
import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.PartA
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.IsAlgClosureRat
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.FerreroWashington
import Development.AutomorphicArithmetic.AutomorphicVarieties.CMFieldExponentialBounds.AdmissibleOfPageN
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.ABoundOfIsTower

/-! Actual archive suppliers for the all-character dyadic certificates.
Ferrero--Washington gives a finite rank R uniformly in the two moving primes.
Its exact numerical value is unnecessary. No Weber hypothesis is used.
This source must be compiled against the pinned archive before being presented
as an independently checked adapter; the exact certificate constructor has a
separate complete hosted check. -/

noncomputable section
namespace Compaction.ArchiveDyadic
open NumberField Formalism.HC Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.Win

/-- PartA's exceptional-twist bound works uniformly for every fixed character;
the rank is supplied by Ferrero--Washington, without a Weber assumption. -/
theorem control (hFW : Published.FerreroWashington) (towerBound : Two.TowerBound)
    (ψ : PChar) {CK Ct eps : ℝ} (hCK : 0 < CK) (hCt : 0 ≤ Ct) (heps : 0 < eps)
    (hK : LemmaK CK) (e : ℝ → ℕ) (admit : admitted 4 Ct e fun x => ⌊x^Ct⌋₊) :
    ∃ R : ℕ, DyadicWindows.Control ψ R (eps/(2*CK)) Ct eps e := by
  let M := AbF.ofChar ψ
  obtain ⟨R, hR⟩ := Two.towerTwo hFW M
  refine ⟨R, fun J hJ => ?_⟩
  obtain ⟨x₀, H⟩ := partA CK hCK hK M R J Ct eps 4 hJ hCt heps
  refine ⟨x₀, fun X q d pair hlog => ?_⟩
  have hp : PrimePair M.m q d := pair
  obtain ⟨L, _, _, hL⟩ := Two.abExists (Two.base2 M q d)
  obtain ⟨exc, small, bound⟩ := H e _ admit X q d hp hlog L
    (Two.twoBase M q d hp L hL) (towerBound 2 L R (hR q d hp L hL).2)
  refine ⟨exc, small, fun x hx hxl hxu hg E _ _ hE => ?_⟩
  exact bound x hx hxl hxu hg E ((isCompField_ofChar ψ (e x) q d E).mpr hE)

/-- The chosen exponent is uniform in q,d, and the chosen Y works simultaneously
for all x, fields, algebraic closures and actual local cohomological data. -/
theorem windows (hFW : Published.FerreroWashington) (towerBound : Two.TowerBound)
    (ψ : PChar) {CK Ct eps : ℝ} (hCK : 1 ≤ CK) (hCt : 1 ≤ Ct)
    (heps : 0 < eps) (htiny : eps < 1/52) (hK : LemmaK CK)
    (e : ℝ → ℕ) (page : ∀ x ≥ (1:ℝ), PageN eps x (e x)) :
    ∃ J : ℝ, 1 ≤ J ∧ DyadicWindows.Window ψ J Ct eps e := by
  have hCKpos : 0 < CK := by linarith
  have heta : 0 < eps/(2*CK) := by positivity
  have hsmall : eps/(2*CK) ≤ Ct := by
    apply le_trans _ hCt
    rw [div_le_one (by positivity)]
    linarith
  obtain ⟨R, hc⟩ := control hFW towerBound ψ hCKpos (by linarith) heps hK e
    (admissible_of_pageN heps htiny hCt page)
  refine ⟨2^(R+1)*(Ct/(eps/(2*CK)))^R, ?_,
    DyadicWindows.select_window ψ R (eps/(2*CK)) Ct eps e heta hsmall heps hc⟩
  exact one_le_mul_of_one_le_of_one_le
    (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))
    (one_le_pow₀ ((one_le_div heta).mpr hsmall))

/-- Ferrero--Washington and the tower estimate are supplied by archive theorems.
Only the original cohomological duality inputs and high-twist bound remain as
arguments; this theorem introduces no new arithmetic hypothesis. -/
theorem from_archive (pt : GlobalTheory.Published.PoitouTateDuality)
    (lf : LocalFinitenessK) (ltate : LocalTateDualityK)
    (ψ : PChar) {CK Ct eps : ℝ} (hCK : 1 ≤ CK) (hCt : 1 ≤ Ct)
    (heps : 0 < eps) (htiny : eps < 1/52) (hK : LemmaK CK)
    (e : ℝ → ℕ) (page : ∀ x ≥ (1:ℝ), PageN eps x (e x)) :
    ∃ J : ℝ, 1 ≤ J ∧ DyadicWindows.Window ψ J Ct eps e :=
  windows UpperTheory.V.FW.ferreroWashington
    (fun l _ L _ _ R h => PropA.aBound_of_isTower pt lf ltate l L R h)
    ψ hCK hCt heps htiny hK e page

end Compaction.ArchiveDyadic

#print axioms Compaction.ArchiveDyadic.control
#print axioms Compaction.ArchiveDyadic.windows
#print axioms Compaction.ArchiveDyadic.from_archive
