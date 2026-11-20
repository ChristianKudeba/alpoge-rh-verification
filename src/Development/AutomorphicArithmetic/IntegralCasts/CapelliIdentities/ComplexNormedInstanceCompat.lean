import Mathlib

noncomputable def UpperTheory.Reformulated.B.Re3.Jm :
    {n : Nat} → (Fin n → Bool) → Matrix (Fin n) (Fin n) Complex :=
    fun {n : Nat} (ε : Fin n → Bool) ↦
      @Matrix.diagonal (Fin n) Complex (instDecidableEqFin n) Complex.instZero fun (a : Fin n) ↦
        @ite Complex (@Eq Bool (ε a) Bool.true) (instDecidableEqBool (ε a) Bool.true)
          (@OfNat.ofNat Complex (nat_lit 1) (@One.toOfNat1 Complex Complex.instOne))
          (@Neg.neg Complex Complex.instNeg (@OfNat.ofNat Complex (nat_lit 1) (@One.toOfNat1 Complex Complex.instOne)))

noncomputable def UpperTheory.Reformulated.B.Re3.inUJ :
    {n : Nat} → (Fin n → Bool) → Matrix (Fin n) (Fin n) Complex → Prop :=
    fun {n : Nat} (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) Complex) ↦
      @Eq (Matrix (Fin n) (Fin n) Complex)
        (@HMul.hMul (Matrix (Fin n) (Fin n) Complex) (Matrix (Fin n) (Fin n) Complex) (Matrix (Fin n) (Fin n) Complex)
          (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid (Fin n) (Fin n) (Fin n) Complex (Fin.fintype n) Complex.instMul
            Complex.instAddCommMonoid)
          (@HMul.hMul (Matrix (Fin n) (Fin n) Complex) (Matrix (Fin n) (Fin n) Complex) (Matrix (Fin n) (Fin n) Complex)
            (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid (Fin n) (Fin n) (Fin n) Complex (Fin.fintype n) Complex.instMul
              Complex.instAddCommMonoid)
            (@Matrix.conjTranspose (Fin n) (Fin n) Complex
              (@InvolutiveStar.toStar Complex
                (@StarAddMonoid.toInvolutiveStar Complex
                  (@AddCommMonoid.toAddMonoid Complex
                    (@NonUnitalNonAssocSemiring.toAddCommMonoid Complex
                      (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring Complex
                        (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing Complex
                          (@NonUnitalCommRing.toNonUnitalNonAssocCommRing Complex Complex.instNonUnitalCommRing)))))
                  (@StarRing.toStarAddMonoid Complex
                    (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring Complex
                      (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing Complex
                        (@NonUnitalCommRing.toNonUnitalNonAssocCommRing Complex Complex.instNonUnitalCommRing)))
                    Complex.instStarRing)))
              g)
            (@UpperTheory.Reformulated.B.Re3.Jm n ε))
          g)
        (@UpperTheory.Reformulated.B.Re3.Jm n ε)

theorem UpperTheory.Reformulated.B.Re3.aux3 :
    ∀ {n : Nat} (ε : Fin n → Bool)
      {g h :
        @Units (Matrix (Fin n) (Fin n) Complex)
          (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
            (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))},
      @Membership.mem
          (@Units (Matrix (Fin n) (Fin n) Complex)
            (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
              (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
          (Set
            (@Units (Matrix (Fin n) (Fin n) Complex)
              (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))))
          (@Set.instMembership
            (@Units (Matrix (Fin n) (Fin n) Complex)
              (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))))
          (@Set.ofPred
            (@Units (Matrix (Fin n) (Fin n) Complex)
              (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
            fun
              (g :
                @Units (Matrix (Fin n) (Fin n) Complex)
                  (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))) ↦
            @UpperTheory.Reformulated.B.Re3.inUJ n ε
              (@Units.val (Matrix (Fin n) (Fin n) Complex)
                (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                  (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))
                g))
          g →
        @Membership.mem
            (@Units (Matrix (Fin n) (Fin n) Complex)
              (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
            (Set
              (@Units (Matrix (Fin n) (Fin n) Complex)
                (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                  (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))))
            (@Set.instMembership
              (@Units (Matrix (Fin n) (Fin n) Complex)
                (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                  (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))))
            (@Set.ofPred
              (@Units (Matrix (Fin n) (Fin n) Complex)
                (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                  (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
              fun
                (g :
                  @Units (Matrix (Fin n) (Fin n) Complex)
                    (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                      (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))) ↦
              @UpperTheory.Reformulated.B.Re3.inUJ n ε
                (@Units.val (Matrix (Fin n) (Fin n) Complex)
                  (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))
                  g))
            h →
          @Membership.mem
            (@Units (Matrix (Fin n) (Fin n) Complex)
              (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
            (Set
              (@Units (Matrix (Fin n) (Fin n) Complex)
                (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                  (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))))
            (@Set.instMembership
              (@Units (Matrix (Fin n) (Fin n) Complex)
                (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                  (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))))
            (@Set.ofPred
              (@Units (Matrix (Fin n) (Fin n) Complex)
                (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                  (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
              fun
                (g :
                  @Units (Matrix (Fin n) (Fin n) Complex)
                    (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                      (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))) ↦
              @UpperTheory.Reformulated.B.Re3.inUJ n ε
                (@Units.val (Matrix (Fin n) (Fin n) Complex)
                  (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))
                  g))
            (@HMul.hMul
              (@Units (Matrix (Fin n) (Fin n) Complex)
                (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                  (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
              (@Units (Matrix (Fin n) (Fin n) Complex)
                (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                  (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
              (@Units (Matrix (Fin n) (Fin n) Complex)
                (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                  (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
              (@instHMul
                (@Units (Matrix (Fin n) (Fin n) Complex)
                  (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                (@MulOne.toMul
                  (@Units (Matrix (Fin n) (Fin n) Complex)
                    (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                      (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                  (@MulOneClass.toMulOne
                    (@Units (Matrix (Fin n) (Fin n) Complex)
                      (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                        (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                    (@Monoid.toMulOneClass
                      (@Units (Matrix (Fin n) (Fin n) Complex)
                        (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                          (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                      (@DivInvMonoid.toMonoid
                        (@Units (Matrix (Fin n) (Fin n) Complex)
                          (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                            (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                        (@Group.toDivInvMonoid
                          (@Units (Matrix (Fin n) (Fin n) Complex)
                            (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                              (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n)
                                (instDecidableEqFin n))))
                          (@Units.instGroup (Matrix (Fin n) (Fin n) Complex)
                            (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                              (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n)
                                (instDecidableEqFin n))))))))))
              g h) := by
  intro n ε g h hg hh
  have hg' : (g : Matrix (Fin n) (Fin n) ℂ).conjTranspose * UpperTheory.Reformulated.B.Re3.Jm ε * g = UpperTheory.Reformulated.B.Re3.Jm ε := hg
  have hh' : (h : Matrix (Fin n) (Fin n) ℂ).conjTranspose * UpperTheory.Reformulated.B.Re3.Jm ε * h = UpperTheory.Reformulated.B.Re3.Jm ε := hh
  show ((g * h : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ).conjTranspose * UpperTheory.Reformulated.B.Re3.Jm ε *
    ((g * h : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = UpperTheory.Reformulated.B.Re3.Jm ε
  rw [Units.val_mul, Matrix.conjTranspose_mul]
  calc _ = (h : Matrix (Fin n) (Fin n) ℂ).conjTranspose *
        ((g : Matrix (Fin n) (Fin n) ℂ).conjTranspose * UpperTheory.Reformulated.B.Re3.Jm ε * g) * h := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hg', hh']

theorem UpperTheory.Reformulated.B.Re3.aux4 :
    ∀ {n : Nat} (ε : Fin n → Bool),
      @Eq (Matrix (Fin n) (Fin n) Complex)
        (@HMul.hMul (Matrix (Fin n) (Fin n) Complex) (Matrix (Fin n) (Fin n) Complex) (Matrix (Fin n) (Fin n) Complex)
          (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid (Fin n) (Fin n) (Fin n) Complex (Fin.fintype n) Complex.instMul
            Complex.instAddCommMonoid)
          (@HMul.hMul (Matrix (Fin n) (Fin n) Complex) (Matrix (Fin n) (Fin n) Complex) (Matrix (Fin n) (Fin n) Complex)
            (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid (Fin n) (Fin n) (Fin n) Complex (Fin.fintype n) Complex.instMul
              Complex.instAddCommMonoid)
            (@Matrix.conjTranspose (Fin n) (Fin n) Complex
              (@InvolutiveStar.toStar Complex
                (@StarAddMonoid.toInvolutiveStar Complex
                  (@AddCommMonoid.toAddMonoid Complex
                    (@NonUnitalNonAssocSemiring.toAddCommMonoid Complex
                      (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring Complex
                        (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing Complex
                          (@NonUnitalCommRing.toNonUnitalNonAssocCommRing Complex Complex.instNonUnitalCommRing)))))
                  (@StarRing.toStarAddMonoid Complex
                    (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring Complex
                      (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing Complex
                        (@NonUnitalCommRing.toNonUnitalNonAssocCommRing Complex Complex.instNonUnitalCommRing)))
                    Complex.instStarRing)))
              (@Units.val (Matrix (Fin n) (Fin n) Complex)
                (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                  (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))
                (@OfNat.ofNat
                  (@Units (Matrix (Fin n) (Fin n) Complex)
                    (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                      (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                  (nat_lit 1)
                  (@One.toOfNat1
                    (@Units (Matrix (Fin n) (Fin n) Complex)
                      (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                        (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                    (@MulOne.toOne
                      (@Units (Matrix (Fin n) (Fin n) Complex)
                        (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                          (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                      (@MulOneClass.toMulOne
                        (@Units (Matrix (Fin n) (Fin n) Complex)
                          (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                            (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                        (@Monoid.toMulOneClass
                          (@Units (Matrix (Fin n) (Fin n) Complex)
                            (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                              (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n)
                                (instDecidableEqFin n))))
                          (@DivInvMonoid.toMonoid
                            (@Units (Matrix (Fin n) (Fin n) Complex)
                              (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                                (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n)
                                  (instDecidableEqFin n))))
                            (@Group.toDivInvMonoid
                              (@Units (Matrix (Fin n) (Fin n) Complex)
                                (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                                  (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n)
                                    (instDecidableEqFin n))))
                              (@Units.instGroup (Matrix (Fin n) (Fin n) Complex)
                                (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                                  (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n)
                                    (instDecidableEqFin n)))))))))))))
            (@UpperTheory.Reformulated.B.Re3.Jm n ε))
          (@Units.val (Matrix (Fin n) (Fin n) Complex)
            (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
              (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))
            (@OfNat.ofNat
              (@Units (Matrix (Fin n) (Fin n) Complex)
                (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                  (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
              (nat_lit 1)
              (@One.toOfNat1
                (@Units (Matrix (Fin n) (Fin n) Complex)
                  (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                (@MulOne.toOne
                  (@Units (Matrix (Fin n) (Fin n) Complex)
                    (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                      (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                  (@MulOneClass.toMulOne
                    (@Units (Matrix (Fin n) (Fin n) Complex)
                      (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                        (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                    (@Monoid.toMulOneClass
                      (@Units (Matrix (Fin n) (Fin n) Complex)
                        (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                          (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                      (@DivInvMonoid.toMonoid
                        (@Units (Matrix (Fin n) (Fin n) Complex)
                          (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                            (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                        (@Group.toDivInvMonoid
                          (@Units (Matrix (Fin n) (Fin n) Complex)
                            (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                              (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n)
                                (instDecidableEqFin n))))
                          (@Units.instGroup (Matrix (Fin n) (Fin n) Complex)
                            (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                              (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n)
                                (instDecidableEqFin n)))))))))))))
        (@UpperTheory.Reformulated.B.Re3.Jm n ε) := by
  intro n ε
  simp

theorem UpperTheory.Reformulated.B.Re3.aux5 :
    ∀ {n : Nat} (ε : Fin n → Bool)
      {g :
        @Units (Matrix (Fin n) (Fin n) Complex)
          (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
            (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))},
      @Membership.mem
          (@Units (Matrix (Fin n) (Fin n) Complex)
            (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
              (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
          (Set
            (@Units (Matrix (Fin n) (Fin n) Complex)
              (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))))
          (@Set.instMembership
            (@Units (Matrix (Fin n) (Fin n) Complex)
              (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))))
          (@Set.ofPred
            (@Units (Matrix (Fin n) (Fin n) Complex)
              (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
            fun
              (g :
                @Units (Matrix (Fin n) (Fin n) Complex)
                  (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))) ↦
            @UpperTheory.Reformulated.B.Re3.inUJ n ε
              (@Units.val (Matrix (Fin n) (Fin n) Complex)
                (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                  (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))
                g))
          g →
        @Membership.mem
          (@Units (Matrix (Fin n) (Fin n) Complex)
            (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
              (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
          (Set
            (@Units (Matrix (Fin n) (Fin n) Complex)
              (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))))
          (@Set.instMembership
            (@Units (Matrix (Fin n) (Fin n) Complex)
              (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))))
          (@Set.ofPred
            (@Units (Matrix (Fin n) (Fin n) Complex)
              (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
            fun
              (g :
                @Units (Matrix (Fin n) (Fin n) Complex)
                  (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))) ↦
            @UpperTheory.Reformulated.B.Re3.inUJ n ε
              (@Units.val (Matrix (Fin n) (Fin n) Complex)
                (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                  (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))
                g))
          (@Inv.inv
            (@Units (Matrix (Fin n) (Fin n) Complex)
              (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
            (@InvOneClass.toInv
              (@Units (Matrix (Fin n) (Fin n) Complex)
                (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                  (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
              (@DivInvOneMonoid.toInvOneClass
                (@Units (Matrix (Fin n) (Fin n) Complex)
                  (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                (@DivisionMonoid.toDivInvOneMonoid
                  (@Units (Matrix (Fin n) (Fin n) Complex)
                    (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                      (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                  (@Group.toDivisionMonoid
                    (@Units (Matrix (Fin n) (Fin n) Complex)
                      (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                        (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                    (@Units.instGroup (Matrix (Fin n) (Fin n) Complex)
                      (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                        (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))))))
            g) := by
  intro n ε g hg
  have hg' : (g : Matrix (Fin n) (Fin n) ℂ).conjTranspose * UpperTheory.Reformulated.B.Re3.Jm ε * g = UpperTheory.Reformulated.B.Re3.Jm ε := hg
  show ((g⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ).conjTranspose * UpperTheory.Reformulated.B.Re3.Jm ε *
    ((g⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = UpperTheory.Reformulated.B.Re3.Jm ε
  calc _ = ((g⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ).conjTranspose *
        ((g : Matrix (Fin n) (Fin n) ℂ).conjTranspose * UpperTheory.Reformulated.B.Re3.Jm ε * g) *
        ((g⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) := by rw [hg']
    _ = ((g : Matrix (Fin n) (Fin n) ℂ) * ((g⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)).conjTranspose *
        UpperTheory.Reformulated.B.Re3.Jm ε *
        ((g : Matrix (Fin n) (Fin n) ℂ) * ((g⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [Units.mul_inv, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

noncomputable def UpperTheory.Reformulated.B.Re3.UJ :
    {n : Nat} →
      (Fin n → Bool) →
        @Subgroup
          (@Units (Matrix (Fin n) (Fin n) Complex)
            (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
              (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
          (@Units.instGroup (Matrix (Fin n) (Fin n) Complex)
            (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
              (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))) :=
    fun {n : Nat} (ε : Fin n → Bool) ↦
      @Subgroup.mk
        (@Units (Matrix (Fin n) (Fin n) Complex)
          (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
            (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
        (@Units.instGroup (Matrix (Fin n) (Fin n) Complex)
          (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
            (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
        (@Submonoid.mk
          (@Units (Matrix (Fin n) (Fin n) Complex)
            (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
              (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
          (@Monoid.toMulOneClass
            (@Units (Matrix (Fin n) (Fin n) Complex)
              (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
            (@DivInvMonoid.toMonoid
              (@Units (Matrix (Fin n) (Fin n) Complex)
                (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                  (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
              (@Group.toDivInvMonoid
                (@Units (Matrix (Fin n) (Fin n) Complex)
                  (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                (@Units.instGroup (Matrix (Fin n) (Fin n) Complex)
                  (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))))))
          (@Subsemigroup.mk
            (@Units (Matrix (Fin n) (Fin n) Complex)
              (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
            (@MulOne.toMul
              (@Units (Matrix (Fin n) (Fin n) Complex)
                (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                  (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
              (@MulOneClass.toMulOne
                (@Units (Matrix (Fin n) (Fin n) Complex)
                  (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                (@Monoid.toMulOneClass
                  (@Units (Matrix (Fin n) (Fin n) Complex)
                    (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                      (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                  (@DivInvMonoid.toMonoid
                    (@Units (Matrix (Fin n) (Fin n) Complex)
                      (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                        (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                    (@Group.toDivInvMonoid
                      (@Units (Matrix (Fin n) (Fin n) Complex)
                        (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                          (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                      (@Units.instGroup (Matrix (Fin n) (Fin n) Complex)
                        (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                          (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n)
                            (instDecidableEqFin n)))))))))
            (@Set.ofPred
              (@Units (Matrix (Fin n) (Fin n) Complex)
                (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                  (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
              fun
                (g :
                  @Units (Matrix (Fin n) (Fin n) Complex)
                    (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                      (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))) ↦
              @UpperTheory.Reformulated.B.Re3.inUJ n ε
                (@Units.val (Matrix (Fin n) (Fin n) Complex)
                  (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))
                  g))
            (@UpperTheory.Reformulated.B.Re3.aux3 n ε))
          (@UpperTheory.Reformulated.B.Re3.aux4 n ε))
        (@UpperTheory.Reformulated.B.Re3.aux5 n ε)

@[reducible] noncomputable def UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ :
    (n : Nat) → (ε : Fin n → Bool) → MeasurableSpace ↥(@UpperTheory.Reformulated.B.Re3.UJ n ε) :=
    fun (n : Nat) (ε : Fin n → Bool) ↦
      @borel (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε))
        (@instTopologicalSpaceSubtype
          (@Units (Matrix (Fin n) (Fin n) Complex)
            (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
              (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
          (fun
              (x :
                @Units (Matrix (Fin n) (Fin n) Complex)
                  (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))) ↦
            @Membership.mem
              (@Units (Matrix (Fin n) (Fin n) Complex)
                (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                  (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
              (@Subgroup
                (@Units (Matrix (Fin n) (Fin n) Complex)
                  (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                (@Units.instGroup (Matrix (Fin n) (Fin n) Complex)
                  (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))))
              (@SetLike.instMembership
                (@Subgroup
                  (@Units (Matrix (Fin n) (Fin n) Complex)
                    (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                      (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                  (@Units.instGroup (Matrix (Fin n) (Fin n) Complex)
                    (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                      (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))))
                (@Units (Matrix (Fin n) (Fin n) Complex)
                  (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                (@Subgroup.instSetLike
                  (@Units (Matrix (Fin n) (Fin n) Complex)
                    (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                      (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                  (@Units.instGroup (Matrix (Fin n) (Fin n) Complex)
                    (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                      (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))))
              (@UpperTheory.Reformulated.B.Re3.UJ n ε) x)
          (@Units.instTopologicalSpaceUnits (Matrix (Fin n) (Fin n) Complex)
            (@instTopologicalSpaceMatrix (Fin n) (Fin n) Complex
              (@UniformSpace.toTopologicalSpace Complex
                (@PseudoMetricSpace.toUniformSpace Complex
                  (@SeminormedRing.toPseudoMetricSpace Complex
                    (@SeminormedCommRing.toSeminormedRing Complex
                      (@NormedCommRing.toSeminormedCommRing Complex
                        (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex)))))))
            (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
              (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))))
attribute [local instance] UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ

theorem UpperTheory.Reformulated.B.Re3.aux8 :
    ∀ {n : Nat} (ε : Fin n → Bool),
      @IsTopologicalGroup (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε))
        (@instTopologicalSpaceSubtype
          (@Units (Matrix (Fin n) (Fin n) Complex)
            (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
              (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
          (fun
              (x :
                @Units (Matrix (Fin n) (Fin n) Complex)
                  (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))) ↦
            @Membership.mem
              (@Units (Matrix (Fin n) (Fin n) Complex)
                (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                  (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
              (@Subgroup
                (@Units (Matrix (Fin n) (Fin n) Complex)
                  (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                (@Units.instGroup (Matrix (Fin n) (Fin n) Complex)
                  (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))))
              (@SetLike.instMembership
                (@Subgroup
                  (@Units (Matrix (Fin n) (Fin n) Complex)
                    (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                      (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                  (@Units.instGroup (Matrix (Fin n) (Fin n) Complex)
                    (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                      (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))))
                (@Units (Matrix (Fin n) (Fin n) Complex)
                  (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                (@Subgroup.instSetLike
                  (@Units (Matrix (Fin n) (Fin n) Complex)
                    (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                      (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                  (@Units.instGroup (Matrix (Fin n) (Fin n) Complex)
                    (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                      (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))))
              (@UpperTheory.Reformulated.B.Re3.UJ n ε) x)
          (@Units.instTopologicalSpaceUnits (Matrix (Fin n) (Fin n) Complex)
            (@instTopologicalSpaceMatrix (Fin n) (Fin n) Complex
              (@UniformSpace.toTopologicalSpace Complex
                (@PseudoMetricSpace.toUniformSpace Complex
                  (@SeminormedRing.toPseudoMetricSpace Complex
                    (@SeminormedCommRing.toSeminormedRing Complex
                      (@NormedCommRing.toSeminormedCommRing Complex
                        (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex)))))))
            (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
              (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))))
        (@Subgroup.toGroup
          (@Units (Matrix (Fin n) (Fin n) Complex)
            (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
              (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
          (@Units.instGroup (Matrix (Fin n) (Fin n) Complex)
            (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
              (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
          (@UpperTheory.Reformulated.B.Re3.UJ n ε)) := by
  intro n ε
  infer_instance

theorem UpperTheory.Reformulated.B.Re3.aux9 :
    ∀ (n : Nat) (ε : Fin n → Bool),
      @BorelSpace (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε))
        (@instTopologicalSpaceSubtype
          (@Units (Matrix (Fin n) (Fin n) Complex)
            (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
              (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
          (fun
              (x :
                @Units (Matrix (Fin n) (Fin n) Complex)
                  (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))) ↦
            @Membership.mem
              (@Units (Matrix (Fin n) (Fin n) Complex)
                (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                  (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
              (@Subgroup
                (@Units (Matrix (Fin n) (Fin n) Complex)
                  (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                (@Units.instGroup (Matrix (Fin n) (Fin n) Complex)
                  (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))))
              (@SetLike.instMembership
                (@Subgroup
                  (@Units (Matrix (Fin n) (Fin n) Complex)
                    (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                      (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                  (@Units.instGroup (Matrix (Fin n) (Fin n) Complex)
                    (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                      (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))))
                (@Units (Matrix (Fin n) (Fin n) Complex)
                  (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                (@Subgroup.instSetLike
                  (@Units (Matrix (Fin n) (Fin n) Complex)
                    (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                      (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                  (@Units.instGroup (Matrix (Fin n) (Fin n) Complex)
                    (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                      (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))))
              (@UpperTheory.Reformulated.B.Re3.UJ n ε) x)
          (@Units.instTopologicalSpaceUnits (Matrix (Fin n) (Fin n) Complex)
            (@instTopologicalSpaceMatrix (Fin n) (Fin n) Complex
              (@UniformSpace.toTopologicalSpace Complex
                (@PseudoMetricSpace.toUniformSpace Complex
                  (@SeminormedRing.toPseudoMetricSpace Complex
                    (@SeminormedCommRing.toSeminormedRing Complex
                      (@NormedCommRing.toSeminormedCommRing Complex
                        (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex)))))))
            (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
              (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))))
        (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε) := by
  intro n ε
  exact ⟨rfl⟩

theorem UpperTheory.Reformulated.B.Re3.laurent_T_neg_one_mul_T_one :
    ∀ (n : Nat) (ε : Fin n → Bool),
      @LocallyCompactSpace (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε))
        (@instTopologicalSpaceSubtype
          (@Units (Matrix (Fin n) (Fin n) Complex)
            (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
              (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
          (fun
              (x :
                @Units (Matrix (Fin n) (Fin n) Complex)
                  (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))) ↦
            @Membership.mem
              (@Units (Matrix (Fin n) (Fin n) Complex)
                (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                  (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
              (@Subgroup
                (@Units (Matrix (Fin n) (Fin n) Complex)
                  (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                (@Units.instGroup (Matrix (Fin n) (Fin n) Complex)
                  (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))))
              (@SetLike.instMembership
                (@Subgroup
                  (@Units (Matrix (Fin n) (Fin n) Complex)
                    (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                      (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                  (@Units.instGroup (Matrix (Fin n) (Fin n) Complex)
                    (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                      (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))))
                (@Units (Matrix (Fin n) (Fin n) Complex)
                  (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                (@Subgroup.instSetLike
                  (@Units (Matrix (Fin n) (Fin n) Complex)
                    (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                      (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                  (@Units.instGroup (Matrix (Fin n) (Fin n) Complex)
                    (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                      (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))))
              (@UpperTheory.Reformulated.B.Re3.UJ n ε) x)
          (@Units.instTopologicalSpaceUnits (Matrix (Fin n) (Fin n) Complex)
            (@instTopologicalSpaceMatrix (Fin n) (Fin n) Complex
              (@UniformSpace.toTopologicalSpace Complex
                (@PseudoMetricSpace.toUniformSpace Complex
                  (@SeminormedRing.toPseudoMetricSpace Complex
                    (@SeminormedCommRing.toSeminormedRing Complex
                      (@NormedCommRing.toSeminormedCommRing Complex
                        (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex)))))))
            (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
              (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))) := by
  intro n ε
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))
  have hc : IsClosed (UpperTheory.Reformulated.B.Re3.UJ ε : Set (Matrix (Fin n) (Fin n) ℂ)ˣ) := by
    show IsClosed {g : (Matrix (Fin n) (Fin n) ℂ)ˣ |
      (g : Matrix (Fin n) (Fin n) ℂ).conjTranspose * UpperTheory.Reformulated.B.Re3.Jm ε * g = UpperTheory.Reformulated.B.Re3.Jm ε}
    exact isClosed_eq
      ((Units.continuous_val.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul Units.continuous_val)
      continuous_const
  exact hc.locallyCompactSpace

noncomputable def UpperTheory.Reformulated.B.Re3.muG :
    {n : Nat} →
      (ε : Fin n → Bool) → @MeasureTheory.Measure (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε) :=
    fun {n : Nat} (ε : Fin n → Bool) ↦
      @MeasureTheory.Measure.haar (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε))
        (@Subgroup.toGroup
          (@Units (Matrix (Fin n) (Fin n) Complex)
            (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
              (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
          (@Units.instGroup (Matrix (Fin n) (Fin n) Complex)
            (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
              (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
          (@UpperTheory.Reformulated.B.Re3.UJ n ε))
        (@instTopologicalSpaceSubtype
          (@Units (Matrix (Fin n) (Fin n) Complex)
            (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
              (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
          (fun
              (x :
                @Units (Matrix (Fin n) (Fin n) Complex)
                  (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))) ↦
            @Membership.mem
              (@Units (Matrix (Fin n) (Fin n) Complex)
                (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                  (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
              (@Subgroup
                (@Units (Matrix (Fin n) (Fin n) Complex)
                  (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                (@Units.instGroup (Matrix (Fin n) (Fin n) Complex)
                  (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))))
              (@SetLike.instMembership
                (@Subgroup
                  (@Units (Matrix (Fin n) (Fin n) Complex)
                    (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                      (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                  (@Units.instGroup (Matrix (Fin n) (Fin n) Complex)
                    (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                      (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))))
                (@Units (Matrix (Fin n) (Fin n) Complex)
                  (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                (@Subgroup.instSetLike
                  (@Units (Matrix (Fin n) (Fin n) Complex)
                    (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                      (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                  (@Units.instGroup (Matrix (Fin n) (Fin n) Complex)
                    (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                      (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))))
              (@UpperTheory.Reformulated.B.Re3.UJ n ε) x)
          (@Units.instTopologicalSpaceUnits (Matrix (Fin n) (Fin n) Complex)
            (@instTopologicalSpaceMatrix (Fin n) (Fin n) Complex
              (@UniformSpace.toTopologicalSpace Complex
                (@PseudoMetricSpace.toUniformSpace Complex
                  (@SeminormedRing.toPseudoMetricSpace Complex
                    (@SeminormedCommRing.toSeminormedRing Complex
                      (@NormedCommRing.toSeminormedCommRing Complex
                        (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex)))))))
            (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
              (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))))
        (@UpperTheory.Reformulated.B.Re3.aux8 n ε) (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε) (UpperTheory.Reformulated.B.Re3.aux9 n ε)
        (UpperTheory.Reformulated.B.Re3.laurent_T_neg_one_mul_T_one n ε)

theorem UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex :
    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).AtLeastTwo := by
  exact ⟨le_refl 2⟩

@[reducible] noncomputable def UpperTheory.Reformulated.B.Re3.L2 :
    {n : Nat} → (Fin n → Bool) → Type :=
    fun {n : Nat} (ε : Fin n → Bool) ↦
      ↥(@MeasureTheory.Lp (↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) Complex (UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ n ε)
          Complex.instNormedAddCommGroup
          (@OfNat.ofNat ENNReal (nat_lit 2)
            (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
              (@AddMonoidWithOne.toNatCast ENNReal
                (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
              UpperTheory.Reformulated.B.Re3.algebra_smulCommClass_complex))
          (@UpperTheory.Reformulated.B.Re3.muG n ε))

noncomputable def UpperTheory.Reformulated.B.Re3.d15 :
    {n : Nat} → (Fin n → Bool) → Matrix (Fin n) (Fin n) Complex :=
    fun {n : Nat} (ε : Fin n → Bool) ↦
      @Matrix.diagonal (Fin n) Complex (instDecidableEqFin n) Complex.instZero fun (a : Fin n) ↦
        @ite Complex (@Eq Bool (ε a) Bool.true) (instDecidableEqBool (ε a) Bool.true)
          (@OfNat.ofNat Complex (nat_lit 1) (@One.toOfNat1 Complex Complex.instOne))
          (@Neg.neg Complex Complex.instNeg (@OfNat.ofNat Complex (nat_lit 1) (@One.toOfNat1 Complex Complex.instOne)))

noncomputable def UpperTheory.Reformulated.B.Re3.Kset :
    {n : Nat} → (Fin n → Bool) → Set (Matrix (Fin n) (Fin n) Complex) :=
    fun {n : Nat} (ε : Fin n → Bool) ↦
      @Set.ofPred (Matrix (Fin n) (Fin n) Complex) fun (g : Matrix (Fin n) (Fin n) Complex) ↦
        And
          (@Membership.mem (Matrix (Fin n) (Fin n) Complex)
            (@Submonoid (Matrix (Fin n) (Fin n) Complex)
              (@MulZeroOneClass.toMulOneClass (Matrix (Fin n) (Fin n) Complex)
                (@instMulZeroOneClassOfSemiring (Matrix (Fin n) (Fin n) Complex)
                  (@Matrix.semiring (Fin n) Complex
                    (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing)) (Fin.fintype n)
                    (instDecidableEqFin n)))))
            (@SetLike.instMembership
              (@Submonoid (Matrix (Fin n) (Fin n) Complex)
                (@MulZeroOneClass.toMulOneClass (Matrix (Fin n) (Fin n) Complex)
                  (@instMulZeroOneClassOfSemiring (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.semiring (Fin n) Complex
                      (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing)) (Fin.fintype n)
                      (instDecidableEqFin n)))))
              (Matrix (Fin n) (Fin n) Complex)
              (@Submonoid.instSetLike (Matrix (Fin n) (Fin n) Complex)
                (@MulZeroOneClass.toMulOneClass (Matrix (Fin n) (Fin n) Complex)
                  (@instMulZeroOneClassOfSemiring (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.semiring (Fin n) Complex
                      (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing)) (Fin.fintype n)
                      (instDecidableEqFin n))))))
            (@Matrix.unitaryGroup (Fin n) (instDecidableEqFin n) (Fin.fintype n) Complex Complex.commRing
              Complex.instStarRing)
            g)
          (@Eq (Matrix (Fin n) (Fin n) Complex)
            (@HMul.hMul (Matrix (Fin n) (Fin n) Complex) (Matrix (Fin n) (Fin n) Complex) (Matrix (Fin n) (Fin n) Complex)
              (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid (Fin n) (Fin n) (Fin n) Complex (Fin.fintype n) Complex.instMul
                Complex.instAddCommMonoid)
              g (@UpperTheory.Reformulated.B.Re3.d15 n ε))
            (@HMul.hMul (Matrix (Fin n) (Fin n) Complex) (Matrix (Fin n) (Fin n) Complex) (Matrix (Fin n) (Fin n) Complex)
              (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid (Fin n) (Fin n) (Fin n) Complex (Fin.fintype n) Complex.instMul
                Complex.instAddCommMonoid)
              (@UpperTheory.Reformulated.B.Re3.d15 n ε) g))

theorem UpperTheory.Reformulated.B.Re3.complex_normed_instance_compat :
    @IsBoundedSMul Complex Complex
      (@SeminormedRing.toPseudoMetricSpace Complex
        (@SeminormedCommRing.toSeminormedRing Complex
          (@NormedCommRing.toSeminormedCommRing Complex (@NormedField.toNormedCommRing Complex Complex.instNormedField))))
      (@SeminormedAddCommGroup.toPseudoMetricSpace Complex
        (@NonUnitalSeminormedRing.toSeminormedAddCommGroup Complex
          (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Complex
            (@SeminormedCommRing.toNonUnitalSeminormedCommRing Complex
              (@NormedCommRing.toSeminormedCommRing Complex
                (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex))))))
      (@MulZeroClass.toZero Complex
        (@instMulZeroClassOfSemiring Complex
          (@DivisionSemiring.toSemiring Complex
            (@Semifield.toDivisionSemiring Complex
              (@Field.toSemifield Complex (@NormedField.toField Complex Complex.instNormedField))))))
      (@NegZeroClass.toZero Complex
        (@SubNegZeroMonoid.toNegZeroClass Complex
          (@SubtractionMonoid.toSubNegZeroMonoid Complex
            (@SubtractionCommMonoid.toSubtractionMonoid Complex
              (@AddCommGroup.toDivisionAddCommMonoid Complex
                (@SeminormedAddCommGroup.toAddCommGroup Complex
                  (@NonUnitalSeminormedRing.toSeminormedAddCommGroup Complex
                    (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Complex
                      (@SeminormedCommRing.toNonUnitalSeminormedCommRing Complex
                        (@NormedCommRing.toSeminormedCommRing Complex
                          (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex)))))))))))
      (@SMulZeroClass.toSMul Complex Complex
        (@AddZero.toZero Complex
          (@AddZeroClass.toAddZero Complex
            (@AddMonoid.toAddZeroClass Complex
              (@SubNegMonoid.toAddMonoid Complex
                (@AddGroup.toSubNegMonoid Complex
                  (@AddCommGroup.toAddGroup Complex
                    (@SeminormedAddCommGroup.toAddCommGroup Complex
                      (@NonUnitalSeminormedRing.toSeminormedAddCommGroup Complex
                        (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Complex
                          (@SeminormedCommRing.toNonUnitalSeminormedCommRing Complex
                            (@NormedCommRing.toSeminormedCommRing Complex
                              (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex))))))))))))
        (@DistribSMul.toSMulZeroClass Complex Complex
          (@AddMonoid.toAddZeroClass Complex
            (@SubNegMonoid.toAddMonoid Complex
              (@AddGroup.toSubNegMonoid Complex
                (@AddCommGroup.toAddGroup Complex
                  (@SeminormedAddCommGroup.toAddCommGroup Complex
                    (@NonUnitalSeminormedRing.toSeminormedAddCommGroup Complex
                      (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Complex
                        (@SeminormedCommRing.toNonUnitalSeminormedCommRing Complex
                          (@NormedCommRing.toSeminormedCommRing Complex
                            (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex))))))))))
          (@DistribMulAction.toDistribSMul Complex Complex
            (@Semiring.toMonoid Complex
              (@DivisionSemiring.toSemiring Complex
                (@Semifield.toDivisionSemiring Complex
                  (@Field.toSemifield Complex (@NormedField.toField Complex Complex.instNormedField)))))
            (@SubNegMonoid.toAddMonoid Complex
              (@AddGroup.toSubNegMonoid Complex
                (@AddCommGroup.toAddGroup Complex
                  (@SeminormedAddCommGroup.toAddCommGroup Complex
                    (@NonUnitalSeminormedRing.toSeminormedAddCommGroup Complex
                      (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Complex
                        (@SeminormedCommRing.toNonUnitalSeminormedCommRing Complex
                          (@NormedCommRing.toSeminormedCommRing Complex
                            (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex)))))))))
            (@Module.toDistribMulAction Complex Complex
              (@DivisionSemiring.toSemiring Complex
                (@Semifield.toDivisionSemiring Complex
                  (@Field.toSemifield Complex (@NormedField.toField Complex Complex.instNormedField))))
              (@AddCommGroup.toAddCommMonoid Complex
                (@SeminormedAddCommGroup.toAddCommGroup Complex
                  (@NonUnitalSeminormedRing.toSeminormedAddCommGroup Complex
                    (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Complex
                      (@SeminormedCommRing.toNonUnitalSeminormedCommRing Complex
                        (@NormedCommRing.toSeminormedCommRing Complex
                          (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex)))))))
              (@NormedSpace.toModule Complex Complex Complex.instNormedField
                (@NonUnitalSeminormedRing.toSeminormedAddCommGroup Complex
                  (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Complex
                    (@SeminormedCommRing.toNonUnitalSeminormedCommRing Complex
                      (@NormedCommRing.toSeminormedCommRing Complex
                        (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex)))))
                (@NonUnitalCStarAlgebra.toNormedSpace Complex
                  (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra Complex
                    (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra Complex instCommCStarAlgebraComplex)))))))) := by
  infer_instance

@[reducible] noncomputable def UpperTheory.Reformulated.B.Re3.umat :
    {n : Nat} → {ε : Fin n → Bool} → ↥(@UpperTheory.Reformulated.B.Re3.UJ n ε) → Matrix (Fin n) (Fin n) Complex :=
    fun {n : Nat} {ε : Fin n → Bool} (g : ↥(@UpperTheory.Reformulated.B.Re3.UJ n ε)) ↦
      @Units.val (Matrix (Fin n) (Fin n) Complex)
        (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
          (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))
        (@Subtype.val
          (@Units (Matrix (Fin n) (Fin n) Complex)
            (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
              (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
          (fun
              (x :
                @Units (Matrix (Fin n) (Fin n) Complex)
                  (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))) ↦
            @Membership.mem
              (@Units (Matrix (Fin n) (Fin n) Complex)
                (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                  (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
              (@Subgroup
                (@Units (Matrix (Fin n) (Fin n) Complex)
                  (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                (@Units.instGroup (Matrix (Fin n) (Fin n) Complex)
                  (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))))
              (@SetLike.instMembership
                (@Subgroup
                  (@Units (Matrix (Fin n) (Fin n) Complex)
                    (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                      (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                  (@Units.instGroup (Matrix (Fin n) (Fin n) Complex)
                    (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                      (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))))
                (@Units (Matrix (Fin n) (Fin n) Complex)
                  (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                (@Subgroup.instSetLike
                  (@Units (Matrix (Fin n) (Fin n) Complex)
                    (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                      (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                  (@Units.instGroup (Matrix (Fin n) (Fin n) Complex)
                    (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                      (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))))
              (@UpperTheory.Reformulated.B.Re3.UJ n ε) x)
          g)

section

attribute [local instance] UpperTheory.Reformulated.B.Re3.instMeasurableSpaceUJ

noncomputable def UpperTheory.Reformulated.B.Re3.rregG {n : ℕ} (ε : Fin n → Bool) (y : UpperTheory.Reformulated.B.Re3.UJ ε) :
    UpperTheory.Reformulated.B.Re3.L2 ε →L[ℂ] UpperTheory.Reformulated.B.Re3.L2 ε := by
  classical
  exact if hm : MeasureTheory.MeasurePreserving (fun x => x * y)
      (UpperTheory.Reformulated.B.Re3.muG ε) (UpperTheory.Reformulated.B.Re3.muG ε) then
    (MeasureTheory.Lp.compMeasurePreservingₗᵢ ℂ (fun x => x * y) hm).toContinuousLinearMap
  else 1

noncomputable def UpperTheory.Reformulated.B.Re3.rreg {n : ℕ} (ε : Fin n → Bool)
    (g : Matrix (Fin n) (Fin n) ℂ) : UpperTheory.Reformulated.B.Re3.L2 ε →L[ℂ] UpperTheory.Reformulated.B.Re3.L2 ε := by
  classical
  exact if h : ∃ y : UpperTheory.Reformulated.B.Re3.UJ ε, UpperTheory.Reformulated.B.Re3.umat y = g then
    UpperTheory.Reformulated.B.Re3.rregG ε h.choose
  else 1

end

noncomputable def UpperTheory.Reformulated.B.Re3.d21 :
    {n : Nat} → (Fin n → Bool) → Set (Matrix (Fin n) (Fin n) Complex) :=
    fun {n : Nat} (ε : Fin n → Bool) ↦
      @Set.ofPred (Matrix (Fin n) (Fin n) Complex) fun (g : Matrix (Fin n) (Fin n) Complex) ↦
        And
          (@Membership.mem (Matrix (Fin n) (Fin n) Complex)
            (@Submonoid (Matrix (Fin n) (Fin n) Complex)
              (@MulZeroOneClass.toMulOneClass (Matrix (Fin n) (Fin n) Complex)
                (@instMulZeroOneClassOfSemiring (Matrix (Fin n) (Fin n) Complex)
                  (@Matrix.semiring (Fin n) Complex
                    (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing)) (Fin.fintype n)
                    (instDecidableEqFin n)))))
            (@SetLike.instMembership
              (@Submonoid (Matrix (Fin n) (Fin n) Complex)
                (@MulZeroOneClass.toMulOneClass (Matrix (Fin n) (Fin n) Complex)
                  (@instMulZeroOneClassOfSemiring (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.semiring (Fin n) Complex
                      (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing)) (Fin.fintype n)
                      (instDecidableEqFin n)))))
              (Matrix (Fin n) (Fin n) Complex)
              (@Submonoid.instSetLike (Matrix (Fin n) (Fin n) Complex)
                (@MulZeroOneClass.toMulOneClass (Matrix (Fin n) (Fin n) Complex)
                  (@instMulZeroOneClassOfSemiring (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.semiring (Fin n) Complex
                      (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing)) (Fin.fintype n)
                      (instDecidableEqFin n))))))
            (@Matrix.unitaryGroup (Fin n) (instDecidableEqFin n) (Fin.fintype n) Complex Complex.commRing
              Complex.instStarRing)
            g)
          (@Eq (Matrix (Fin n) (Fin n) Complex)
            (@HMul.hMul (Matrix (Fin n) (Fin n) Complex) (Matrix (Fin n) (Fin n) Complex) (Matrix (Fin n) (Fin n) Complex)
              (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid (Fin n) (Fin n) (Fin n) Complex (Fin.fintype n) Complex.instMul
                Complex.instAddCommMonoid)
              g (@UpperTheory.Reformulated.B.Re3.Jm n ε))
            (@HMul.hMul (Matrix (Fin n) (Fin n) Complex) (Matrix (Fin n) (Fin n) Complex) (Matrix (Fin n) (Fin n) Complex)
              (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid (Fin n) (Fin n) (Fin n) Complex (Fin.fintype n) Complex.instMul
                Complex.instAddCommMonoid)
              (@UpperTheory.Reformulated.B.Re3.Jm n ε) g))

noncomputable def UpperTheory.Reformulated.B.Re3.IsKStableOn.{u_1} {n : ℕ} {H : Type u_1}
    [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H]
    (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → H →L[ℂ] H)
    (S : Submodule ℂ H) : Prop :=
  ∀ g ∈ UpperTheory.Reformulated.B.Re3.d21 ε, ∀ v ∈ S, σ g v ∈ S


noncomputable def UpperTheory.Reformulated.B.Re3.IsWtOn.{u_1} {n : ℕ} {H : Type u_1}
    [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H]
    (G : Set (Matrix (Fin n) (Fin n) ℂ)) (σ : Matrix (Fin n) (Fin n) ℂ → H →L[ℂ] H)
    (μ : Fin n → ℝ) (v : H) : Prop :=
  ∀ θ : Fin n → ℝ,
    (Matrix.diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I)) ∈ G →
      σ (Matrix.diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I)) v =
        Complex.exp ((∑ a, μ a * θ a : ℝ) * Complex.I) • v


noncomputable def UpperTheory.Reformulated.B.Re3.root :
    {n : Nat} → Fin n → Fin n → Fin n → Real :=
    fun {n : Nat} (a b : Fin n) ↦
      @HSub.hSub (Fin n → Real) (Fin n → Real) (Fin n → Real)
        (@instHSub (Fin n → Real) (@Pi.instSub (Fin n) (fun (j : Fin n) ↦ Real) fun (i : Fin n) ↦ Real.instSub))
        (@Pi.single (Fin n) (fun (a : Fin n) ↦ Real) (fun (i : Fin n) ↦ Real.instZero) (instDecidableEqFin n) a
          (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne)))
        (@Pi.single (Fin n) (fun (a : Fin n) ↦ Real) (fun (i : Fin n) ↦ Real.instZero) (instDecidableEqFin n) b
          (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne)))

noncomputable def UpperTheory.Reformulated.B.Re3.CDom :
    {n : Nat} → (Fin n → Bool) → (Fin n → Real) → (Fin n → Real) → Prop :=
    fun {n : Nat} (ε : Fin n → Bool) (μ Λ : Fin n → Real) ↦
      ∃ (c : Fin n → Fin n → Nat),
        And
          (∀ (a b : Fin n),
            @Ne Nat (c a b) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
              And (@LT.lt (Fin n) (@instLTFin n) a b) (@Eq Bool (ε a) (ε b)))
          (@Eq (Fin n → Real)
            (@HSub.hSub (Fin n → Real) (Fin n → Real) (Fin n → Real)
              (@instHSub (Fin n → Real) (@Pi.instSub (Fin n) (fun (a : Fin n) ↦ Real) fun (i : Fin n) ↦ Real.instSub)) Λ μ)
            (∑ a : Fin n,
              ∑ b : Fin n,
                @HSMul.hSMul Real (Fin n → Real) (Fin n → Real)
                  (@instHSMul Real (Fin n → Real) (@Function.hasSMul (Fin n) Real Real (@instSMulOfMul Real Real.instMul)))
                  (@Nat.cast Real Real.instNatCast (c a b)) (@UpperTheory.Reformulated.B.Re3.root n a b)))

noncomputable def UpperTheory.Reformulated.B.Re3.IsKTypeOf.{u_1} {n : ℕ} {H : Type u_1}
    [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H]
    (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → H →L[ℂ] H)
    (Λ : Fin n → ℝ) (S : Submodule ℂ H) : Prop :=
  FiniteDimensional ℂ S ∧ UpperTheory.Reformulated.B.Re3.IsKStableOn ε σ S ∧
    (∀ S' ≤ S, UpperTheory.Reformulated.B.Re3.IsKStableOn ε σ S' → S' = ⊥ ∨ S' = S) ∧
    (∃ v ∈ S, v ≠ 0 ∧ UpperTheory.Reformulated.B.Re3.IsWtOn (UpperTheory.Reformulated.B.Re3.d21 ε) σ Λ v) ∧
    ∀ (μ : Fin n → ℝ), ∀ v ∈ S, v ≠ 0 →
      UpperTheory.Reformulated.B.Re3.IsWtOn (UpperTheory.Reformulated.B.Re3.d21 ε) σ μ v → UpperTheory.Reformulated.B.Re3.CDom ε μ Λ

private theorem UpperTheory.Reformulated.B.Re3.transfer_gen {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ε : Fin n → Bool} {Λ : Fin n → ℝ} (σ : Matrix (Fin n) (Fin n) ℂ → H →L[ℂ] H) (A : H →ₗ[ℂ] H)
    (hA : ∀ k ∈ UpperTheory.Reformulated.B.Re3.d21 ε, ∀ x : H, A (σ k x) = σ k (A x))
    {S : Submodule ℂ H} (hinj : ∀ w ∈ S, A w = 0 → w = 0)
    (hS : UpperTheory.Reformulated.B.Re3.IsKTypeOf ε σ Λ S) :
    UpperTheory.Reformulated.B.Re3.IsKTypeOf ε σ Λ (Submodule.map A S) := by
  obtain ⟨hfd, hst, hirr, ⟨v, hvS, hv0, hvw⟩, hdom⟩ := hS
  refine ⟨inferInstance, ?_, ?_, ?_, ?_⟩
  · rintro g hg _ ⟨w, hw, rfl⟩
    exact ⟨σ g w, hst g hg w hw, hA g hg w⟩
  · intro S' hS' hst'
    have hT : UpperTheory.Reformulated.B.Re3.IsKStableOn ε σ (S ⊓ Submodule.comap A S') := by
      intro g hg w hw
      refine ⟨hst g hg w hw.1, ?_⟩
      show A (σ g w) ∈ S'
      rw [hA g hg w]
      exact hst' g hg _ hw.2
    rcases hirr _ inf_le_left hT with h | h
    · left
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨w, hw, rfl⟩ := hS' hx
      have hw0 : w ∈ S ⊓ Submodule.comap A S' := ⟨hw, hx⟩
      rw [h, Submodule.mem_bot] at hw0
      simp [hw0]
    · right
      refine le_antisymm hS' ?_
      rintro _ ⟨w, hw, rfl⟩
      have hw1 : w ∈ S ⊓ Submodule.comap A S' := by rw [h]; exact hw
      exact hw1.2
  · refine ⟨A v, ⟨v, hvS, rfl⟩, fun h => hv0 (hinj v hvS h), ?_⟩
    intro θ hθ
    rw [← hA _ hθ, hvw θ hθ, map_smul]
  · rintro μ _ ⟨w, hw, rfl⟩ hw0 hwt
    refine hdom μ w hw (fun h => hw0 (by simp [h])) ?_
    intro θ hθ
    apply sub_eq_zero.mp
    apply hinj _ (S.sub_mem (hst _ hθ w hw) (S.smul_mem _ hw))
    rw [map_sub, map_smul, hA _ hθ, hwt θ hθ, sub_self]

theorem UpperTheory.Reformulated.B.Re3.hloweq_transfer :
    ∀ {n : ℕ} {ε : Fin n → Bool} {Λ : Fin n → ℝ}
      (A : UpperTheory.Reformulated.B.Re3.L2 ε →ₗ[ℂ] UpperTheory.Reformulated.B.Re3.L2 ε),
      (∀ k ∈ UpperTheory.Reformulated.B.Re3.Kset ε, ∀ x : UpperTheory.Reformulated.B.Re3.L2 ε,
        A (UpperTheory.Reformulated.B.Re3.rreg ε k x) = UpperTheory.Reformulated.B.Re3.rreg ε k (A x)) →
      ∀ {S : Submodule ℂ (UpperTheory.Reformulated.B.Re3.L2 ε)},
        (∀ w ∈ S, A w = 0 → w = 0) →
        UpperTheory.Reformulated.B.Re3.IsKTypeOf ε (UpperTheory.Reformulated.B.Re3.rreg ε) Λ S →
        UpperTheory.Reformulated.B.Re3.IsKTypeOf ε (UpperTheory.Reformulated.B.Re3.rreg ε) Λ (Submodule.map A S) := by
  intro n ε Λ A hA S hinj hS
  exact UpperTheory.Reformulated.B.Re3.transfer_gen (UpperTheory.Reformulated.B.Re3.rreg ε) A hA hinj hS
