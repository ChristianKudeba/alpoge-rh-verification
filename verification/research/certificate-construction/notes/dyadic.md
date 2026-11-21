# Constructed dyadic Selmer certificates with uniform bounds

The dyadic component is now closed for every primitive character. The actual
certificate is

    M_2(D,t) = 2^(sum_{1 <= k < t} shaLen(D,k)),

with the exponent interpreted as a natural number only after finiteness is
proved. Its 2-adic valuation equals the sum of the extended-natural lengths;
no infinite length can be lost through `ENat.toNat`. The additional
`PrimeCertificateAsOrders` module identifies it with the product of the orders
of the actual finite Selmer groups, using `FiniteLengthCard`.

`ArchiveDyadicClosed.windows` proves, for every fixed character and every
0<eps<1/52, that the original ordered square windows admit these certificates
with the uniform logarithmic bound

    log M_2 <= log(2) * exp(x^(4*eps/5)).

J and the outer threshold are chosen before the moving primes q,d; one Y is
chosen before all x in [Y,Y^2], all host fields, algebraic closures and local
cohomological data. The construction supplies all inputs from proved archive
theorems, including the general Ferrero--Washington theorem. None is left as
an unproved assumption of the closed endpoint.

The logarithmic budget is subexponential in x. It need not be polynomial.
Since 4*eps/5<eps, it fits the target sqrt(exp(x^eps)) budget eventually; the
parent research task supplies the mixed-budget absorption proof.

## A sharper closed principal route

`PrincipalDyadicClosed.windows` proves the same construction at conductor one
with an explicit window exponent

    J = 2^25 * (2*CK*Ct/eps)^24,

where one fixed CK>=1 works for all admissible Ct, eps and PageN functions.
`ClosedCohomologyInputs` supplies the global/local duality and high-twist inputs.
The newly proved `Compaction.Weber.weber` supplies the exact rank-zero pure
2-power cyclotomic base, and the two moving quadratic characters cost at most
24 generators. The principal route does not import the actual general
Ferrero--Washington proof module.

The Weber proof uses the elementary Hilbert class quotient, conjugation
equivariance of Artin, Minkowski inertia generation, and finite 2-group normal
generation. Its theorem proves **odd class number**, not the stronger assertion
that all real 2-power cyclotomic fields have class number one. See
`weber/README.md` and `weber/WEBER_ROUTE.md` for its statement and proof.

## Scope and evidence

All new source files are research modules and do not modify Main or the five
public theorem targets. `native-manifest.json` records per-file verification
status, exact source hashes, pinned compiler/cache metadata, and the printed
axiom inventories. Native elaboration evidence in `evidence/` is distinguished
from imported-proof kernel replay, whose separate outcome is collected by the
root matrix agent. It is not a full Main Comparator result.

The prime-power constructor also has Principia hosted check
`260fb3ef5e25c4162dc670dac5b5d15e`: a complete 22-module archive support bundle
plus the new constructor passed with zero placeholders and only the three
standard axioms. Its source manifest and server verdict are preserved in
`evidence/hosted-constructor-*` and bound to the current constructor hash.

The integers have explicit mathematical definitions; their decimal values have
not been numerically evaluated. CK is supplied by an existence theorem, rather
than a computed numerical constant.

The odd-prime plus/height estimate is still needed for complete all-prime
certificates. This work does not prove RH or establish a million-line deletion.
Standalone dependency comparisons in `weber/manifest.json` must not be counted
as whole-Main savings because the full proof shares dependencies elsewhere.

Credit: Anton supplied `Joint.LengthBudget`, `Joint.PowerWindow`,
`Joint.DyadicRankWindow`, the conductor-one framework, and the class-counting
supplier `Joint.TwistCohomologyBound`. This work supplies the actual integer
certificate adapters, the all-character window adapter, the closed Weber
proof, and the two closed dyadic endpoints.

To refresh the source-bound native evidence after checks finish, run
`python collect_native_evidence.py --require-complete` in this directory.
