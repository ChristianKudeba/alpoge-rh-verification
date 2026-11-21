import Joint.WeberRank

noncomputable section
namespace Joint.WeberTower
open NumberField Formalism.HC Formalism.ConjugateSelfDual ReciprocityTheory.Gal
  Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two

theorem tower (web : Joint.WeberBase.Weber) (q d : ℕ) (pair : PrimePair 1 q d)
    (L : Type) [Field L] [NumberField L] (realized : IsAbField (base2 (AbF.ofChar PChar.one) q d) L) :
    Tower.GenLE ℤ_[2] (Tower.XX 2 L) 24 ∧ Tower.IsTower 2 L 24 := by
  haveI := isAlgClosure_rat L (AlgebraicClosure L)
  have rank := Joint.WeberRank.moving_rank web (AlgebraicClosure L) q d pair
  have mu := hasMuQ.2.2 _ q d L realized
  exact ⟨genLE_of_abRk 1 L realized rank,complex_of_root (by norm_num) mu,mu,by decide,
    genLE_of_abRk 2 L realized rank⟩

end Joint.WeberTower
#print axioms Joint.WeberTower.tower

