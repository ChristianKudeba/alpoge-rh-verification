import Joint.PowerWindow
import Development.AutomorphicArithmetic.AutomorphicVarieties.CMFieldExponentialBounds.logpair
import Development.AutomorphicArithmetic.AutomorphicVarieties.CMFieldExponentialBounds.bigpair
import Compaction.PrimeCertificate

/-! Convert a uniformly bounded finite set of exceptional twists into
all-character dyadic integer certificates on the exact original windows.
The exceptional-control hypothesis is supplied by the archive's partA below
in ArchiveDyadic.lean; this file proves the entire window quantifier step. -/

noncomputable section
namespace Compaction.DyadicWindows
open NumberField Formalism.HC Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.Win

def At (ψ : PChar) (eps Ct : ℝ) (e : ℝ → ℕ) (q d : ℕ) (x : ℝ) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E], IsChiField ψ (e x) q d E →
    VVat 2 E ⌊x^Ct⌋₊ (Real.exp (x^(4*eps/5)))

def CertificatesAt (ψ : PChar) (eps Ct : ℝ) (e : ℝ → ℕ) (q d : ℕ) (x : ℝ) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E], IsChiField ψ (e x) q d E →
    ∀ (Ω : Type) [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (D : LData E Ω 2),
      0 < PrimeCertificate.certificate D ⌊x^Ct⌋₊ ∧
      Real.log (PrimeCertificate.certificate D ⌊x^Ct⌋₊) ≤
        Real.log 2 * Real.exp (x^(4*eps/5)) ∧
      ∑ k ∈ Finset.Ico 1 ⌊x^Ct⌋₊, shaLen D (k : ℤ) =
        ((PrimeCertificate.certificate D ⌊x^Ct⌋₊).factorization 2 : ℕ∞)

def Control (ψ : PChar) (R : ℕ) (eta Ct eps : ℝ) (e : ℝ → ℕ) : Prop :=
  ∀ J : ℝ, 0 < J → ∃ x₀ : ℝ, ∀ (X : ℝ) (q d : ℕ), PrimePair ψ.N q d →
    Real.log ((q:ℝ)*d) ≤ X^(eps/(4*J)) →
    ∃ exc : Finset ℕ, exc.card ≤ R ∧ ∀ x ≥ x₀, X^(1/J) ≤ x → x ≤ X →
      Good eta Ct exc x → At ψ eps Ct e q d x

def Window (ψ : PChar) (J Ct eps : ℝ) (e : ℝ → ℕ) : Prop :=
  ∃ X₀ : ℝ, ∀ X ≥ X₀, ∀ q d : ℕ, WinPair eps (X^(1/J)) q d →
    ∃ Y : ℝ, X^(1/J) ≤ Y ∧ Y^(2:ℝ) ≤ X ∧
      ∀ x : ℝ, Y ≤ x → x ≤ Y^(2:ℝ) → CertificatesAt ψ eps Ct e q d x

/-- J and the outer cutoff are fixed before q,d; Y is chosen before every x,
field, algebraic closure and choice of local data. -/
theorem select_window (ψ : PChar) (R : ℕ) (eta Ct eps : ℝ) (e : ℝ → ℕ)
    (hη : 0 < eta) (hle : eta ≤ Ct) (heps : 0 < eps)
    (control : Control ψ R eta Ct eps e) :
    Window ψ (2^(R+1)*(Ct/eta)^R) Ct eps e := by
  let J : ℝ := 2^(R+1)*(Ct/eta)^R
  have hCtpos : 0 < Ct := hη.trans_le hle
  have hJ : 0 < J := by dsimp [J]; positivity
  obtain ⟨x₀, H⟩ := control J hJ
  obtain ⟨Y₀, logbound⟩ := log_mul_le_rpow_of_winPair eps heps
  obtain ⟨XB, large⟩ := eventually_winPair_gt_power eps J Ct (ψ.N : ℝ) heps hJ
  let L := max 2 (max Y₀ x₀)
  have hL : 2 ≤ L := le_max_left _ _
  have hL₀ : 0 ≤ L := by linarith
  have hLY : Y₀ ≤ L := (le_max_left _ _).trans (le_max_right _ _)
  have hLx : x₀ ≤ L := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨max XB (max 2 (L^J)), ?_⟩
  intro X hX q d pair
  have hXB : XB ≤ X := (le_max_left _ _).trans hX
  have hX2 : 2 ≤ X := (le_max_left _ _).trans ((le_max_right _ _).trans hX)
  have hX0 : 0 ≤ X := by linarith
  have hlow : L ≤ X^(1/J) := by
    have hh := Real.rpow_le_rpow (Real.rpow_nonneg hL₀ _)
      ((le_max_right _ _).trans ((le_max_right _ _).trans hX))
      (one_div_pos.mpr hJ).le
    rwa [←Real.rpow_mul hL₀, mul_one_div_cancel hJ.ne', Real.rpow_one] at hh
  have hlog := logbound _ (hLY.trans hlow) q d pair
  have hp : (X^(1/J))^(eps/4) = X^(eps/(4*J)) := by
    rw [←Real.rpow_mul hX0]
    congr 1
    field_simp
  rw [hp] at hlog
  obtain ⟨_, _, hqN, hdN⟩ := large X hXB q d pair
  have hcop (r : ℕ) (hr : r.Prime) (hb : (ψ.N : ℝ) < r) : r.Coprime ψ.N := by
    apply (Nat.Prime.coprime_iff_not_dvd hr).mpr
    intro hdvd
    have hrN := Nat.le_of_dvd (NeZero.pos ψ.N) hdvd
    have hlt : ψ.N < r := by exact_mod_cast hb
    omega
  have hpair : PrimePair ψ.N q d :=
    ⟨pair.q_prime, pair.q_mod, pair.d_prime, pair.d_mod,
      (hcop q pair.q_prime hqN).mul (hcop d pair.d_prime hdN)⟩
  obtain ⟨exc, small, bound⟩ := H X q d hpair hlog
  obtain ⟨Y, hY, avoid⟩ := Joint.PowerWindow.square_window eta Ct X R exc hη hle
    (by linarith) small
  refine ⟨Y, hY.1, hY.2, ?_⟩
  intro x hlo hhi E _ _ hE Ω _ _ _ D
  have hat := bound x (hLx.trans (hlow.trans (hY.1.trans hlo)))
    (hY.1.trans hlo) (hhi.trans hY.2) (avoid x hlo hhi)
  exact PrimeCertificate.dyadic (hat E hE) Ω D

end Compaction.DyadicWindows

#print axioms Compaction.DyadicWindows.select_window
