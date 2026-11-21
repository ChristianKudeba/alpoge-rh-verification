import Joint.DyadicAvoidance
import Joint.WeberTower
import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.PartA

noncomputable section
namespace Joint.DyadicRankWindow
open NumberField Formalism.HC UpperTheory.Top UpperTheory.V UpperTheory.V.Two UpperTheory.V.Win

theorem exceptions (web : Joint.WeberBase.Weber) (towerBound : TowerBound)
    {CK Ct eps : ℝ} (hCK : 0 < CK) (hCt : 0 ≤ Ct) (heps : 0 < eps)
    (hK : LemmaK CK) (e : ℝ → ℕ) (admit : admitted 4 Ct e fun x => ⌊x^Ct⌋₊) :
    Joint.DyadicAvoidance.Exceptions 24 (eps/(2*CK)) Ct eps e := by
  intro J hJ
  let M := AbF.ofChar PChar.one
  obtain ⟨x₀,H⟩ := partA CK hCK hK M 24 J Ct eps 4 hJ hCt heps
  refine ⟨x₀,fun X q d pair hlog => ?_⟩
  obtain ⟨L,_,_,hL⟩ := abExists (base2 M q d)
  have tower := (Joint.WeberTower.tower web q d pair L hL).2
  exact H e _ admit X q d pair hlog L (twoBase M q d pair L hL) (towerBound 2 L 24 tower)

theorem explicit_window (web : Joint.WeberBase.Weber) (towerBound : TowerBound)
    {CK Ct eps : ℝ} (hCK : 1 ≤ CK) (hCt : 1 ≤ Ct) (heps : 0 < eps) (htiny : eps < 1/52)
    (hK : LemmaK CK) (e : ℝ → ℕ) (admit : admitted 4 Ct e fun x => ⌊x^Ct⌋₊) :
    Joint.DyadicAvoidance.Window ((2:ℝ)^25*(2*CK*Ct/eps)^24) Ct eps e := by
  have hCK₀ : 0 < CK := by linarith
  have hη : 0 < eps/(2*CK) := by positivity
  have small : eps/(2*CK) ≤ Ct := by
    apply le_trans _ hCt
    rw [div_le_one (by positivity)]
    linarith
  have h := Joint.DyadicAvoidance.select_window 24 (eps/(2*CK)) Ct eps e hη small heps
    (exceptions web towerBound hCK₀ (by linarith) heps hK e admit)
  rwa [show Ct/(eps/(2*CK)) = 2*CK*Ct/eps by rw [div_div_eq_mul_div]; ring] at h

end Joint.DyadicRankWindow
#print axioms Joint.DyadicRankWindow.explicit_window

