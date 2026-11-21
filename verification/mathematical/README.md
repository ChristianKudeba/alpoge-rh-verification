# Mathematical proof reductions

This pass replaces longer arguments with stronger abstractions or alternative
proofs. It removes **823 net physical lines, 850 nonblank lines and 44,723 bytes**,
including the cost of four new shared modules. Seventeen existing modules change.
The substantive source now has 165,124 modules and 16,624,300 physical lines.

The source baseline is `51c81ba76f4f038169ae93ced8a6ac91b8ce15fc`. Its Lean source
matches `82828c352`; the intervening commits concern the manuscript. Family audits
may therefore refer to either baseline. The five final statements, independent
Challenge/Solution entrypoints, allowed axioms, toolchain, dependencies and build
options remain unchanged. **Full-project Comparator verification is pending.**

## Mathematical changes

| Reduction | Net lines removed, including new helpers |
| --- | ---: |
| Integral dual family replaces Smith normal form | 152 |
| General submersion normal form and Haar change of variables | 216 |
| General convergence theorem for continuous densities | 180 |
| Tensor pushout/cancellation and localization span theorem | 73 |
| Differentiate an elementary Mellin identity | 54 |
| Obtain its real specialization from the complex identity | 27 |
| Share logarithmic-derivative continuation | 17 |
| Share coefficient-level smoothed-sum estimates | 77 |
| First-order comparison replaces an energy argument | 27 |
| **Total** | **823** |

The duality reduction gives a stronger reusable result: a finite independent
family with a nondegenerate pairing has an integral right-dual family whenever
its integral dual lattice lies in the original lattice. The coefficient pairing
is an injective endomorphism of a finite-dimensional space, hence surjective.
The original lattice theorem follows by taking every exponent equal to `N`.
Its Smith normal form, divisibility and parity calculations disappear. The new
lemma needs no discrete valuation ring or uniformizer. The old public hypotheses
are retained for compatibility; no integral-basis claim is added.

The submersion abstraction constructs coordinates from a right inverse of the
derivative, then proves a general local change-of-variables theorem for Haar
measure. Three coordinate-specific proofs and a fourth normal-form construction
specialize this result. The separate density abstraction proves closure under
approximations bounded by a common integrable envelope. Three consumers retain
their approximation constructions and use this general limit theorem; supporting
subtraction, scaling, positivity and comparison proofs are shared too.

The tensor proof uses the pushout property and cancellation equivalence instead
of constructing inverse maps by hand. The localization proof invokes the existing
denominator-clearing span theorem. Analytically, differentiation produces the
logarithmic Mellin integrand, taking real parts supplies a real identity, and a
single continuation lemma handles two logarithmic differential equations.
Character-specific smoothed sums become instances of a coefficient-norm bound.
Finally, for the differential comparison, `v = u' + c*u` has exponential lower
growth while convexity and the original moderate-growth hypothesis give a
polynomial upper bound, replacing an auxiliary energy and threshold calculation.

## Search and verification

The search ranked 1,787 long proof-body candidates for retained files from the
existing declaration index and identified 32 Mathlib-only candidates, alongside the
main analytic route and repeated proof families. This is a systematic selection
process, not a claim to have exhaustively reviewed every theorem. Other reviewed
Smith-normal-form arguments genuinely require integral bases or elementary-divisor
orders, so the dual-family shortcut was not applied to them.

Every included reduction has a successful focused hosted Lean check with zero
sorries. Printed inventories of the checked conclusions contain only `propext`,
`Classical.choice` and `Quot.sound`. The checks use complete replacement modules
or exact proof bundles with actual supporting definitions and proofs. They do
not replace supporting mathematics by assumed statements. Family audit files
record the exact scope, source hashes and check IDs.

Some checks compile both original and replacement proofs and compare their
theorem types explicitly. Other families preserve the original statement text,
definitions and declaration scopes and check the complete replacement consumers;
those are not claimed to have a separate old/new elaborated-type comparison.
An independent review checked the duality, submersion and density arguments and
48 existing declaration headers, finding no strengthened consumer assumptions.

The fresh whole-source audit found no import cycles or missing internal imports;
all retained source modules remain reachable from `Main`. Reproduce it with:

```sh
python verification/aggressive/audit_snapshot.py \
  --base 51c81ba76f4f038169ae93ced8a6ac91b8ce15fc --out /tmp/mathematical-audit.json
```

`source-audit.json` contains the exact changes and input hashes. Its module-removal
count is `-4` because four reusable modules were added. Counts cover `src/**/*.lean`
and include comments; they exclude Mathlib, verification fixtures and manuscript
files. Large comparison snippets remain in the harness workspace, identified by
the recorded hashes, rather than duplicating expanded original proofs here.

These checks establish the reported local reductions. The complete RH import
graph and all five final targets still require the new commit's full Comparator.
