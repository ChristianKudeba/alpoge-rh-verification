# Direct Selmer-window reduction and contribution audit

Research snapshot, 21 November 2026. This is progress on the strongest identified
replacement target, not a new proof of RH or a completed deletion from the main
proof. The existing five public targets and their independent Challenge remain
unchanged.

## Checked result

`Compaction/LengthCertificates.lean` extends Anton's
[`Joint/LengthBudget.lean`](https://principia-math.com/projects/d16ab288ed353bc5b10e292ace0ddbc1/editor?file=b6fa1e4537ff47a8435d533b0de10983).
For lengths `a(p,e)` valued in the extended natural numbers, the original
finiteness and bounded-finite-prime-sum conditions are equivalent to the existence
of one positive integer M such that

    log M <= B,   and   sum_{1 <= e < t} a(p,e) <= v_p(M) for every prime p.

This version proves finiteness from valuation domination itself. It never uses
`ENat.toNat` to discard an infinite length. Anton proved the underlying integer
common-multiple equivalence; the valuation formulation is the extension here.

`Compaction/WindowCertificates.lean` applies this equivalence to the archive's
actual `shaLen`, `VVle`, and `VAt` definitions for **every** `PChar`. It also proves
that integer certificates whose logarithms have a fixed polynomial bound on the
specified windows suffice for `VWinAt`; having these for every character suffices
for the original `VWin` at exponent 401. Polynomial growth is a sufficient
condition, not asserted to be equivalent to the original window estimate.

The original quantifier order is retained: J, C, k and the outer threshold are
chosen before X and q,d; then one Y is chosen before all x in [Y,Y²]. The same C,k
must work for all relevant fields and local data. The certificate M itself may
depend on the field, local data and x, as in the exact `VVle` equivalence.

Principia scratch check `1a873d8154de69e45832eaff1f8c9e9c` passed with zero
placeholders. All eight printed axiom inventories contain only `propext`,
`Classical.choice`, and `Quot.sound`. The check contains the complete sources of
all 20 internal dependencies of `ExistsPageN`, Anton's helper, and both new
modules. It substitutes no arithmetic definitions or unproved axioms.

The self-contained `checked-bundle.lean`, `bundle-manifest.json` and
`check-result.json` record exactly what was checked. To reproduce, use Lean
4.33.1 and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, then run
`lake env lean checked-bundle.lean` in that environment.

`python verification/research/selmer-window-certificates/build_bundle.py`, run at
the repository root, checks that the stored bundle can be reconstructed exactly
from its source files and that every hash matches the checked manifest. This
reconstruction check supplements, rather than replaces, the Lean check.

## What remains before a large deletion

The direct `VWin` route has a conditional import-closure ceiling of 12,323 modules
and 1,228,752 physical source lines. That ceiling is not a saving already earned.
We still need to **construct the certificates and prove their uniform size
bounds**. The new theorems identify an arithmetic obligation; they do not supply
it.

I checked the archive's general `LemmaK` estimate as a possible replacement. Its
`kBound` bounds a logarithmic cohomology size by
`exp((2*e*n)^C * log(2*abs(discriminant)))`. This is too coarse to directly yield
the required window budget when t grows as x^401 and the field degree also grows
with x. Finiteness alone, or a bound on the dimension of p-torsion alone, does not
bound the total module length; groups Z/p^r have p-rank one and unbounded length.

Anton's principal-character plus estimate can use bottom-layer class numbers 1
at primes 3 and 7, eliminating a higher auxiliary-layer assumption in that step.
It still assumes `PointHV`, the substantial height theorem. His residual descent
also needs a genuine vanishing condition on unramified residual characters.
Those hypotheses cannot be silently dropped.

## Recent contributions inspected

| Contributor and source | Contribution | Validation/scope relevant here |
| --- | --- | --- |
| Anton, [PR 12](https://github.com/leanprover-community/riemann-hypothesis/pull/12), head `9430017510358b5ed1ab12c8bb900fd706e60a32` | One upper bound on a signed combination of three character errors controls nearby finite-group signal values. | A genuine local mathematical simplification. PR supplies a hosted check and an independent Linux build for its three declarations; the signed estimate remains an input. Open, 139 added lines, not a demonstrated net reduction of the full proof. |
| Anton, `Joint/LengthBudget`, `PrincipalCohomology`, `ResidualDescent`, `ResidualSha`, `PrincipalPlus` | Integer budgets, a conductor-one adapter, residual cocycle descent, and simpler bottom-layer arithmetic. | Useful ingredients for the direct Selmer attack. The new all-character criterion above builds on the budget lemma. Remaining class-field/height hypotheses are recorded explicitly. |
| Anton, [combined conductor-one argument](https://principia-math.com/projects/d16ab288ed353bc5b10e292ace0ddbc1/editor?file=b64c07f1e23480429eacd6b354f04f26) | Collects a principal-character route and supplies several duality and cohomology inputs from archive lemmas. | Its final RH theorem still takes Weber, a principal height estimate, and a family connection as inputs. Reading its source is not an independent full build. It proves ordinary RH conditionally, rather than all five original targets unconditionally. |
| Anton, [TwistCohomologyBound](https://principia-math.com/projects/d16ab288ed353bc5b10e292ace0ddbc1/editor?file=bfbab30acefd7ae1104b474728e96184) | Obtains the coarse high-twist bound through the class-counting chain instead of the older K-bridge producer. | The new standalone source closure is 249,987 lines versus 3,828,671 for the older producer. But simulating that one replacement in our full Main closure removes only 13 existing modules/660 lines: almost all of the apparent standalone saving is still used elsewhere. Signatures differ, and this simulation is not a checked patch. |
| @uimspeedrun, [Mellin specialization](https://principia-math.com/projects/d16ab288ed353bc5b10e292ace0ddbc1/editor?file=5949389e56cf6f09ac963bc1083cc6fd) | Derives the real Mellin identity from the complex identity; reports 17 nonblank proof lines versus 41 previously. | Same mathematical route already used in our earlier Mellin reduction. Credit the contribution; do not count the overlapping saving twice. |
| @deancureton, [PR 8](https://github.com/leanprover-community/riemann-hypothesis/pull/8) | Removes six unused modules and simplifies entry-point imports. | Open; +2/-288 lines. Structural cleanup, overlapping our earlier reachability pruning. |
| @deancureton, [PR 9](https://github.com/leanprover-community/riemann-hypothesis/pull/9) | Removes redundant imports and heartbeat settings in 20,637 files. | Draft; 20,824 lines removed. This is Lean cleanup rather than a shorter mathematical argument. |
| @deancureton, [PR 10](https://github.com/leanprover-community/riemann-hypothesis/pull/10) | Simplifies generated proof fallback expressions. | Draft; 45,721 lines replaced by 45,721 lines, so no net line-count reduction. |
| @thorimur, [PR 4](https://github.com/leanprover-community/riemann-hypothesis/pull/4), head `01ea40c4ff736e6f7f7fec583f5d9d9b06ee750a` | Large import minimization using agitate. | Draft, full rebuild not established in the author's description. +594,656/-590,138 lines, net +4,518. Its lenient elaborator overrides must not be treated as a kernel-checking shortcut. |
| @nisorussian, harness `ea048496f84022f7890544d2de654dc4` | Verified an audit/equivalence involving a trace condition and GRH. | The contributor explicitly corrected the automatic solved announcement: the hard trace condition remains unproved. This is not a completed RH proof. |

The community repository has moved to
[`leanprover-community/riemann-hypothesis`](https://github.com/leanprover-community/riemann-hypothesis).
Its published module cache improves verification logistics; it is not a
mathematical line-count reduction. None of the open PR counts above should be
added to our savings without checking overlap and an independent build.

## Full verification status

The older baseline full Comparator run `44831224495` and candidate run
`44842005347` both finished with exit 124 after the configured five-hour timeout.
They did not reach a mathematical verdict. The focused checks in this report
passed; this does not establish a full Comparator pass for our modified project.

No new hundred-thousand-line deletion is claimed in this research update.

These files live under `verification/research` and are not imported by Main.
Principia accepted `Compaction/LengthCertificates.lean` into its editor, then
rejected further uploads because the project exceeded its staging editor limits.
The complete bundle and audit are therefore preserved in the connected GitHub
repository and linked from the ongoing harness log.
