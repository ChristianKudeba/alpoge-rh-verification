import Joint.PowerWindow
import Development.AutomorphicArithmetic.AutomorphicVarieties.CMFieldExponentialBounds.logpair
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimeSetBoundDataOfPrimitiveChar

noncomputable section
namespace Joint.DyadicAvoidance
open NumberField Formalism.HC UpperTheory.Top UpperTheory.V UpperTheory.V.Win

def Exceptions (R : ℕ) (eta Ct eps : ℝ) (e : ℝ → ℕ) : Prop :=
  ∀ J : ℝ, 0 < J → ∃ x₀ : ℝ, ∀ (X : ℝ) (q d : ℕ), PrimePair 1 q d →
    Real.log ((q:ℝ)*d) ≤ X^(eps/(4*J)) → ∃ exc : Finset ℕ, exc.card ≤ R ∧
      ∀ x ≥ x₀, X^(1/J) ≤ x → x ≤ X → Good eta Ct exc x →
        BaAt (AbF.ofChar PChar.one) eps e (fun z => ⌊z^Ct⌋₊) q d x

def Window (J Ct eps : ℝ) (e : ℝ → ℕ) : Prop :=
  ∃ X₀ : ℝ, ∀ X ≥ X₀, ∀ q d : ℕ, WinPair eps (X^(1/J)) q d →
    ∃ Y : ℝ, InRange J X Y ∧ ∀ x : ℝ, Y ≤ x → x ≤ Y^(2:ℝ) →
      BaAt (AbF.ofChar PChar.one) eps e (fun z => ⌊z^Ct⌋₊) q d x

theorem select_window (R : ℕ) (eta Ct eps : ℝ) (e : ℝ → ℕ)
    (hη : 0 < eta) (hle : eta ≤ Ct) (heps : 0 < eps)
    (exceptions : Exceptions R eta Ct eps e) : Window (2^(R+1)*(Ct/eta)^R) Ct eps e := by
  let J : ℝ := 2^(R+1)*(Ct/eta)^R
  have hCt := hη.trans_le hle
  have hJ : 0 < J := by dsimp [J]; positivity
  obtain ⟨x₀,H⟩ := exceptions J hJ
  obtain ⟨Y₀,logbound⟩ := log_mul_le_rpow_of_winPair eps heps
  let L := max 2 (max Y₀ x₀)
  have hL : 2 ≤ L := le_max_left _ _
  have hL₀ : 0 ≤ L := by linarith
  have hLY : Y₀ ≤ L := (le_max_left _ _).trans (le_max_right _ _)
  have hLx : x₀ ≤ L := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨max 2 (L^J),?_⟩
  intro X hX q d pair
  have hX2 : 2 ≤ X := (le_max_left _ _).trans hX
  have hX0 : 0 ≤ X := by linarith
  have hlow : L ≤ X^(1/J) := by
    have hh := Real.rpow_le_rpow (Real.rpow_nonneg hL₀ _)
      ((le_max_right _ _).trans hX) (one_div_pos.mpr hJ).le
    rwa [←Real.rpow_mul hL₀,mul_one_div_cancel hJ.ne',Real.rpow_one] at hh
  have hlog := logbound _ (hLY.trans hlow) q d pair
  have hp : (X^(1/J))^(eps/4) = X^(eps/(4*J)) := by
    rw [←Real.rpow_mul hX0]
    congr 1
    field_simp
  rw [hp] at hlog
  obtain ⟨exc,small,bound⟩ := H X q d
    ⟨pair.q_prime,pair.q_mod,pair.d_prime,pair.d_mod,Nat.coprime_one_right _⟩ hlog
  obtain ⟨Y,hY,avoid⟩ := Joint.PowerWindow.square_window eta Ct X R exc hη hle (by linarith) small
  exact ⟨Y,hY,fun x lo hi => bound x (hLx.trans (hlow.trans (hY.1.trans lo)))
    (hY.1.trans lo) (hi.trans hY.2) (avoid x lo hi)⟩

end Joint.DyadicAvoidance
#print axioms Joint.DyadicAvoidance.select_window

