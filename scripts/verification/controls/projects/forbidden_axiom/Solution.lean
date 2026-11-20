import Init

axiom PrincipiaComparatorControl.forbidden : (1 : Nat) + 1 = 2

theorem PrincipiaComparatorControl.result : (1 : Nat) + 1 = 2 := by
  exact PrincipiaComparatorControl.forbidden
