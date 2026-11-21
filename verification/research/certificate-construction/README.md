# Constructed Selmer certificates and uniform bounds

Work session started 21 November 2026 at 08:11:36 UTC. This directory contains
checked certificate constructions, a new proof of Weber's odd-class-number
theorem, and a stronger principal-character reduction. It does not remove the
large original height/counting argument or claim a new complete RH proof.

The original `src`, Challenge, Solution, Comparator targets and manifest are
unchanged. These are research modules with their own aggregate entry point,
[AllCertificates.lean](AllCertificates.lean).

## Odd-minus certificates: closed

For every cyclotomic conductor N≥1 and cutoff t≥2, the construction supplies

    M_minus(N,t) = M_Bern(N,t) * (N!)^(t * ceil(2*C*N^7*t^3)).

Here C≥0 is one universal constant from the archive's proved pointwise bound.
M_Bern is a finite product of actual nonzero integer Bernoulli products, taken
over all characters of the required parity. The factorial covers the small
primes. The integer is selected before the field E, algebraic closure, local
data and prime p. For every CM field E embedding in Q(ζ_N) and every odd p,

    sum_(1≤e<t) minusLen(D_p,e) ≤ v_p(M_minus)

in the extended natural numbers. The same integer has the uniform bound

    log M_minus ≤ 3*N*t²*log(t*N) + (2*C*N^7*t³+1)*t*N²
                ≤ (2*C+4)*(N*t)^9.

No unproved arithmetic hypothesis remains in
`Compaction.AllOddMinusCertificateClosed.exists_uniform_certificates`.
The Bernoulli integrality and pointwise cohomology estimates are supplied by
the original archive. This construction retains and assembles their integer
witnesses instead of choosing a witness from an assumed final prime-sum bound.

## Dyadic certificates: closed

The certificate is explicitly

    M_2(D,t) = 2^(sum_(1≤e<t) shaLen(D,e)).

Finiteness is proved before converting lengths to natural numbers.
`ArchiveDyadicClosed.windows` supplies the original ordered windows for every
fixed primitive character, with

    log M_2 ≤ log(2) * exp(x^(4*eps/5)).

J and the outer threshold precede q,d; one Y precedes all x in [Y,Y²], all
fields, closures and local data. All arithmetic inputs of the closed endpoint
are supplied by proved archive theorems.

The principal-character route has a new independent arithmetic proof:
`Compaction.Weber.weber` proves oddness of the class number of Q(ζ_(2^n)) using
class-field quotients, Minkowski inertia generation and finite 2-groups.
`PrincipalDyadicClosed.windows` then obtains rank 24 and the explicit exponent

    J = 2^25 * (2*CK*Ct/eps)^24.

This principal route avoids importing the general Ferrero–Washington proof.
Its Weber supplier has an approximately 83,400-line standalone source closure;
that comparison is not a deletion from the full Main closure.

## Plus certificates: constructed interfaces; counting inputs remain

The new `PrincipalNonresonant.gd` uses Q(√−3), whose class number is proved to be
one, to handle every odd nonresonant prime on principal hosts. In particular,
7 needs no separate treatment when 3 does not divide the twist.

`PrincipalTwistCertificate.nonresonant_budget` constructs one integer from the
archive's actual trace-difference integers, over a fixed set of character
orbits and all twists. It is selected before every field and prime. Its bound is

    log M_nonres ≤ 48606*c*N³*t*(N*t)^A.

The substantial `PropGK` producer is still an explicit input. We have not
replaced its original automorphy/counting proof with a short proof.

The remaining resonant pairs satisfy p−1 | 2e and therefore p<2t. Given a uniform
pointwise natural bound R for those actual plus lengths,
`FullPlusCertificate.with_resonant_bound` constructs

    M_plus = M_nonres * ((2*t)!)^(t*R),
    log M_plus ≤ 48606*c*N³*t*(N*t)^A + 4*t³*R.

The resonant pointwise bound remains explicit. This includes nontrivial
characters at the single low-twist pair p=3,e=1; the rank-four e≥2 argument does
not cover that pair. Trivial-character contributions at 3 and 7 vanish by
Anton's checked regular-prime result, giving certificate 1.

## Assembly and a simpler window argument

`SelmerAssembly.construct` forms M_2*M_plus*M_minus and proves domination of the
actual total Selmer lengths, with exact addition of logarithmic costs.
`MixedGrowth.mixed_budget` absorbs polynomial terms and fixed multiples of
exp(C*x^delta), delta<eps, into sqrt(exp(x^eps)).

The checked `JointWindowWithoutMinus.vwin_of_joint` derives the original VWin
from JointWin alone. It replaces the separate ThmBc handoff with the closed
minus certificates and enlarges a polynomial exponent before choosing the
moving window data. The JointWin height/counting input remains unchanged.

## Verification

The coherent aggregate compiled in Lean 4.33.1 with Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`. All eight printed aggregate endpoints
report only `propext`, `Classical.choice`, and `Quot.sound`. See
[aggregate-native.log](verification/aggregate-native.log) and
[source-manifest.json](source-manifest.json).

Three large endpoints received additional explicit proof-term replay into an
empty kernel environment using the official `Lean.Environment.replay` API:

| Endpoint | Declarations replayed | Result |
| --- | ---: | --- |
| Closed odd-minus certificate | 133,455 | Passed; standard three axioms |
| Weber theorem | 98,821 | Passed; standard three axioms |
| JointWin → VWin closing argument | 133,735 | Passed; standard three axioms |

The [replay driver](verification/ReplayCertificate.lean) rejects unsafe/partial
dependencies and additional axioms, reconstructs the dependency environment,
and checks that the target type and proof are unchanged. Its deliberately
corrupted-proof control was rejected by the kernel. Logs are under
`verification/`.

These are genuine replay results. Earlier `--trust=0` runs are ordinary
import-based compilation evidence, not imported-proof replay. This work does
not establish a full Main Comparator pass or independently rebuild every
cached source module. Archive caches were pinned and hash checked; the new
modules were compiled from the source snapshots recorded here.

For reproduction, supply a build of the pinned archive and Mathlib, add this
directory's compiled output to LEAN_PATH, and compile the local modules in the
order in `source-manifest.json`. Compile AllCertificates last. To replay an
endpoint after compilation, use `lean --run verification/ReplayCertificate.lean`
followed by its module and fully qualified theorem name. The historical native
commands and compiler identity are recorded in the evidence JSON files.

## Collaboration and remaining target

We periodically refreshed Principia and the community repository throughout
the session. Anton's PowerWindow, conductor-one reductions, regular-prime
vanishing and logarithmic-cubic bound informed this work. Exact contributor
source commits, hashes and independent Linux-check links are recorded in
[contribution-sources.json](notes/contribution-sources.json). The Bernoulli,
class-field, duality, trace and tower inputs are credited to Alpöge's archive.

A short replacement for the remaining plus-side producers is still needed
before the proposed 1.23-million-line branch can be deleted. No such deletion
is claimed here. Detailed component notes are under `notes/`.
