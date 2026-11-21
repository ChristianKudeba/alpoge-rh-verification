# Actual plus-cohomology certificates

This work constructs certificates from the archive's actual `PropGK` integer
producer. It does not replace that producer's automorphy proof, and it does not
yet bound the remaining resonant contributions. No axiom or weakened RH target
has been introduced.

## New arithmetic refinement

`PrincipalNonresonant.gd` proves that, for a principal host and every odd prime p
with p-1 not dividing 2e, the archive's actual `GD` conditions hold over the fixed
auxiliary field `Kstar 3 = Q(sqrt(-3))`. Its class number is proved to equal one
directly from the discriminant -3 and Minkowski's bound.

The original generic route uses `Kstar 7` and leaves both 3 and 7 exceptional.
In the new route, p=3 is automatically resonant, and 7 needs no exceptional
treatment when 3 does not divide e. The proof preserves the character parity,
the prime-to-p character order and index requirements, the local component
condition, and the required inertia condition. It applies to the actual host
characters, not placeholder coefficient data.

## Integer construction and uniform size

For each rational character orbit H, `PropGK` supplies two nonzero integers
n_H(r), n_H(s), where r and s are distinct good auxiliary primes. The first
integer controls all coefficient primes other than r; the second controls all
other than s. `PairCertificate` constructs

    M_H = (|n_H(r)| * |n_H(s)|)^2.

Its valuations dominate the entire orbit at every coefficient prime. The exact
logarithmic cost is twice the sum of the logarithms of the two integers.

`AllOrbitCertificate` multiplies over the fixed finite set of all cyclic-quotient
kernels in `(ZMod N)^units`. This set is chosen before the coefficient prime,
coefficient ring, Galois realization, and finite character family. The archive's
`orbSum` inequality bounds the sum of phi(index H) by phi(N), hence by N. Thus
one integer controls all permitted character families simultaneously. This
avoids the original proof's finite-prime-subset-dependent choice of orbit set.

`PlusCertificate` transfers the normalized character-length estimate through
the actual `redPrime` comparison to the ENat-valued `plusLen`. It proves
finiteness before converting any length to a natural number.

Root's checked `AuxiliaryPrimes.exists_pair` constructs r,s avoiding `90*N`
and bounds their logarithmic cost by `3*(1+(90*N)^2)`. Substituting these actual
primes yields `PrincipalCertificate.nonresonant_at`: there exist fixed c,A such
that the per-twist certificate M_e satisfies

    log M_e <= 48606*c*N^3*(N*(e+1))^A,
    plusLen(D,e) <= v_p(M_e)

for every odd nonresonant p. The same integer works for every relevant host
field realization, algebraic closure, and local cohomology datum.

`PrincipalTwistCertificate.nonresonant_budget` takes the finite product over
1 <= e < t. Its output P satisfies

    log P <= 48606*c*N^3*t*(N*t)^A,
    sum_{1 <= e < t, p-1 does not divide 2e} plusLen(D_p,e) <= v_p(P)

for every odd p, uniformly in all field and local data. The extended-natural
valuation domination itself proves the lengths finite. The remaining resonant
prime condition implies p < 2*t; this is separately proved in
`resonant_prime_lt`.

`RegularOneCertificate` also records the actual certificate M=1 for the trivial
character at p=3 and p=7 over every positive twist, using Anton's newly verified
`RegularCharacterHeight` result. This does not claim the nontrivial character
components vanish.

`ResonantCertificate` constructs the explicit factor `((2*t)!)^(t*R)` whenever
each remaining resonant length is bounded by a natural number R. Its logarithm
is at most `4*t^3*R`. This factor is selected before the whole family of lengths.
`FullPlusCertificate.with_resonant_bound` combines it with the nonresonant
certificate, yielding one integer controlling all odd plus lengths over every
relevant field and local datum, with total logarithmic budget

    48606*c*N^3*t*(N*t)^A + 4*t^3*R.

The explicit remaining assumption here is a uniform pointwise resonant bound
R. It includes the nontrivial p=3,e=1 case, which CountII (requiring e>=2) cannot
supply. Taking R polynomial in Nt gives a polynomial total logarithmic budget;
this assembly does not prove that pointwise estimate itself.

## Remaining hard arithmetic

`PropGK` is still an explicit theorem input. The archive derives it from an
integer congruence-number estimate and `OneChar` (automorphy/deformation
arguments). Its actual current supplier is
`Z.J.propGK_of_numberU3U_of_oneCharU`, applied inside
`DenseThresholdCases/LinkedUnlE.count_i_of_printed_bound_k_kato_automorphy`.
There is no reliance on the older unused conditional `CorG` definition.

The closed supplier can be assembled from the original RowSrc theorem, the
closed local/automorphic/cohomological/CM literature records shown in
`TopMainZj`, `published_hypotheses_from_patching_alt`, KatoTwoW, and the same
literal-automorphy/linked-end constructions used in the existing full proof.
Importing those broad existing modules directly requires a 160,594-module
closure, so this research does not pretend to have independently rebuilt that
closed supplier. Using that route would reuse the original large proof rather
than establish a new short proof of the arithmetic estimate.

The next independent quantitative obligation is the nontrivial resonant
character contribution for p < 2t. The archive has an actual symplectic
congruence-number integer NN in `VWinNumN`/`CountS`; retaining it could construct
the remaining finite prime product, but its geometric estimate has not been
replaced here. Generic K-theory bounds or residual p-rank bounds alone do not
supply the required uniform size estimate.

## Verification and credit

The new source modules have been compiled with Lean 4.33.1 and the pinned Mathlib
revision `0df444a360eaa60ab8c11dca51a86af692955474` against the independently
SHA-256-verified community dependency cache. Every printed new theorem inventory
contains only `propext`, `Classical.choice`, and `Quot.sound`. Per-module JSON and
logs record the exact source hashes and exit codes.

Some modules also passed the `-t0` option, but source inspection found this is
not sufficient evidence of independently replaying imported proof constants.
The matrix agent is implementing explicit `Lean.Environment.replay` checks;
those results must be reported separately.

For the combined project, `staged-source-manifest.json` records a coherent copy
of these files under the matrix workstream's research root. Its `Root*` helper
modules are one-line import shims for the canonical `Compaction` modules, rather
than duplicate copies of their public declarations. The resonant wrapper's file
is named `HeightResonantCertificate.lean` there to avoid a module-name clash;
the theorem namespace remains unchanged.

Anton's `ConductorOneCases` and `RegularCharacterHeight` are copied exactly from
the inspected community supplement; `contributor-source-manifest.json` records
their hashes. Root supplied the auxiliary-prime construction and certificate
assembly lemmas. The fixed-orbit and Kstar3 arguments, plus their actual-length
adapters, were constructed in this height workstream. An independent review by
the contribution watcher found no moving-character/prime-set quantifier leak or
discarded finiteness condition in the adapters.
