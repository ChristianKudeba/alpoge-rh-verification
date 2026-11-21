# Audit of a possible smaller fixed-rank congruence-number argument

This is a source audit, not a newly proved replacement theorem. The certificate
modules still take the archive's actual `PropGK` as input.

The proposed strategy of bounding a fixed definite-unitary class set, multiplying
by a finite level index and the dimension of an algebraic coefficient module is
already the mathematical strategy of the archive's `CountK` producer. In
`AutomorphicForms/TemperedLocalComponents/KlevThree.lean`, `cardK` combines the
Weyl coefficient-dimension bound, the cohomological injection, and unconditional
`cohBoundFree`. The latter's proof in `CohBoundFree.lean` uses:

* `finite_adelic_double_cosets` for the fixed level-one quotient;
* level subgroup index at most `M^([K:Q]*n^2)`;
* Shapiro/coinduction and bounded cohomology of the finitely many stabilizers.

For `Kstar 3`, rank three, that level exponent is 18. The base-level constants
are fixed, independent of M and the varying weight. No effective discriminant
estimate or uniform Haar-volume estimate is needed at this stage. The general
complex-arithmetic-group boundedness is proved in `BddArith.lean` from a bounded
simplicial-complex model and finite cell stabilizers. Class number one of the
Eisenstein integers can simplify the adelic quotient, but does not by itself
supply the required contractible, finite-orbit complex for GL3 or its
cohomology bound. An explicit Eisenstein-lattice retract could replace this
general complex, but would require a new reduction/classification argument.

`numberU3_of_admissible` in
`AutomorphicForms/TemperedLocalComponents/CongruenceNumberRankThree.lean` combines
the `CountK` and `CountQ` eigensystem counts with the actual finite-product norm
construction. At the fixed field of discriminant -3, its field-dependent
constants become fixed constants. This observation does not remove its
automorphy, purity, integrality, or Galois-conjugacy inputs.

The actual `CountQ` does not rely mathematically on the general real-field
fixed-point branch of `bddArith`. Its supplier is
`GaloisLibrary/CrystallineBaseChange/CountQuadraticOfHyp.lean`:
`count_quadratic_of_hypotheses` restricts a representation over Q to a fixed
finite family of imaginary quadratic fields, uses `CountP`, and bounds the
quadratic-twist fibres. Thus simply replacing its use of real arithmetic-group
cohomology is not an available reduction: that proposed route was already
avoided by the existing proof.

There is a concrete alternative GL2 route worth pursuing, but it is unfinished.
The archive's `Adm2` literally contains a classical normalized `Newform`, whose
underlying cusp form is Mathlib's `CuspForm (Gamma1 M) k`. Pinned Mathlib has
`ModularForm.norm`, norm nonvanishing, and the full level-one Sturm bound in
`Mathlib/NumberTheory/ModularForms/{NormTrace,LevelOne/DimensionFormula}.lean`.
If one proves that the norm's q-order at infinity is at least the original
form's q-order, level-one Sturm gives the general Gamma1 finite-jet injection.
The index can be bounded by `M^4` just by reduction into 2-by-2 matrices over
ZMod M, which is already quantitatively adequate.

The missing analytic bridge is precise: the norm is a product of coset
translates, each bounded at infinity, but individual translates need not have
period one. A finite-product quotient `norm(f)/f` can instead be constructed
by omitting the identity coset. The identity coset is fixed by Gamma1 M, so
this complementary product is again a modular form, is bounded at the cusps,
and has period one. Multiplicativity of q-expansions then gives the desired
order inequality. No general-level norm/order or Sturm theorem was found in
the pinned library.

After that bridge, one still needs an eigensystem-counting argument for the
normalized newforms and the same purity/integrality/Galois-conjugacy guarantees
needed by the integer norm construction. Simultaneous Hecke eigenvectors can
be treated by explicit linear recurrence operators on Fourier coefficients,
but this has not been formalized here. This is a genuine alternative to the
quadratic-restriction counting branch, not yet a verified source reduction.
