# Alpöge RH proof: full-source verification and compaction

This repository preserves the complete mirrored Lean source of the
Alpöge/Claude claimed proof of RH and Dirichlet GRH in Git history and develops
a compact candidate in `src/`. **The full proof has not been independently
verified by this work.**

## Current prose edition

[Read the single 209-page PDF](https://github.com/ChristianKudeba/alpoge-rh-verification/releases/download/short-route-43722f46fd2854e1b325d9c1fc16c8ed02bc4193/rh-short-route.pdf) or [its standalone LaTeX](https://github.com/ChristianKudeba/alpoge-rh-verification/releases/download/short-route-43722f46fd2854e1b325d9c1fc16c8ed02bc4193/rh-short-route.tex).

**This is an incomplete working exposition, not a standalone unconditional proof of RH.** The first part presents the shorter ordinary-zeta route with reductions from Principia contributors. The earlier working translations remain as supporting chapters in this same manuscript.

The current edition proves uniform dyadic matrix congruences, cokernel growth, fixed centers and at most 24 exceptional twists on a whole horizon, an explicit discriminant bound at depth seven, and the common-window dyadic estimate with K_2(24) now supplied by the global cohomology bound. It computes the local cohomology terms exactly throughout the tower: the H² length is s_2(L_m,a)+m+2+v_2(a), whenever finite. The determinant-prescribed fractional-ideal lattice comparison is proved by an explicit CRT construction, with valuation equivalence and exact Minkowski covolume scaling. The Q(sqrt(-3)) auxiliary packet covers every odd nonresonant prime. These new prose arguments have not been separately formalized.

The manuscript also contains the analytic endpoint, signed finite-group comparison, conductor-one arithmetic, prime-to-degree minus bound, rational trivial-character vanishing at the exceptional and resonant primes, and assembly of the plus-height estimate from two rational-character bounds. The newer checked certificate constructions are reviewed with their remaining producer assumptions retained.

The new Section 9 derives the global high-twist bound from integral homology, with uniform exponent 24, including the prime 2. It prints the normal-cone acyclicity, common-frame orbit count, finite-stabilizer torsion bounds, Kummer generator estimate and numerical absorptions, and states the published comparison theorems it uses. Section 10.5 also proves the twist-one character estimate of any fixed bounded order at 3 and 7. These new prose arguments have not been separately formalized or independently refereed.

The full two rational-character estimates, uniform in unbounded order and the required twists (or a valid weaker cubic-logarithmic plus-height bound), and the connected geometric construction with the required uniform theta, ramified, cusp/metric and integral-model estimates remain unproved in this exposition. This describes the prose manuscript's completeness, not a demonstrated gap in the original formal archive.

The [build report](https://github.com/ChristianKudeba/alpoge-rh-verification/releases/download/short-route-43722f46fd2854e1b325d9c1fc16c8ed02bc4193/build-report.json) records successful reference, glyph and title-credit checks, identical text from the chapter-based and flattened sources, rendering of every page, and no words outside the page. These are document checks; they do not establish mathematical completeness. See [the explicit status](translation/SHORT_ROUTE_STATUS.md) and [the source manifest](translation/short-route-sources.json). The [current consolidated manuscript](https://principia-math.com/api/ws/files/2ee1c508abb5f50dfda689e69cc9ae9c) and its single LaTeX project are published on [Principia's papers page](https://principia-math.com/projects/d16ab288ed353bc5b10e292ace0ddbc1/paper). Earlier uploads explaining this same RH route have been consolidated; the separate Masullo audit and other contributors' papers remain unchanged.

The [216,211-volume record edition](https://github.com/ChristianKudeba/alpoge-rh-verification/releases/tag/rh-literal-audit-v1) is a lossless typesetting of the formal export and must not be described as a finished explanatory paper. Its reverse-conversion audit verifies transcription fidelity.

Principia project: [Unpacking the proof of RH](https://principia-math.com/projects/d16ab288ed353bc5b10e292ace0ddbc1).
The [Machine Verification page](https://principia-math.com/projects/d16ab288ed353bc5b10e292ace0ddbc1/forge)
holds the canonical statement, solution entrypoint, and verification configuration.
The substantive module tree is in this repository's `src/` directory.

## Source and preserved baseline

- Source mirror: [CocoSgt/riemann-hypothesis-lean](https://github.com/CocoSgt/riemann-hypothesis-lean).
- Original mirror commit: `7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`.
- Unchanged baseline tag: `alpoge-source-7cbf7a0c`.
- First compaction commit: `fb97c4c5a1624d02c8ddfa0d403a29becff79c9e`.
- Original pins: Lean `v4.33.1`; Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`.

The original mirror README, attribution, archive links, and licensing notice are
preserved in [UPSTREAM_README.md](UPSTREAM_README.md). The upstream archive states
no license; this repository does not infer or grant one. Provenance against the
author's original multipart archive has not been independently established here.

## What the Comparator checks

`Challenge.lean` independently states all five public conclusions using Mathlib
only. Its intentional `sorry` placeholders specify the targets. `Solution.lean`
imports the full `Main` development and supplies each unconditional theorem.
The solution cannot be checked from the four entry files alone.

`comparator.json` selects all five declarations and permits only `propext`,
`Classical.choice`, and `Quot.sound`. A full successful run must build the entire
required source, compare the independent statements, and check proof dependencies.
A missing dependency, resource exhaustion, tooling failure, or timeout is not a
successful verification. The historical Comparator profile does not use Nanoda.

The dedicated candidate workflow checks its exact Git commit. The original-source
baseline diagnostic is a separate workflow; its result must not be presented as
verification of a modified candidate commit. See `formalization.yaml` and the
workflow logs for the scope and current status.

## Incremental simplification

The first two passes edit 19 files and remove **265 net lines and 16,746 bytes**.
They share repeated gamma/Euler-factor arguments and theta-lift helpers, shorten
zeta reflection, and remove unnecessary imports from the main entrypoint.

The compact analytic bundle passed Principia's hosted Lean checks. Six deeper
theta/Galois files have structural checks only and still require the full build.
Those partial checks do not verify RH. Evidence is in
[verification/compaction/COMPACTION.txt](verification/compaction/COMPACTION.txt).

The next pass removes **748,827 more source lines and 10,070 modules**:

| Substantive Lean source | Before this pass | After |
| --- | ---: | ---: |
| Modules | 175,190 | 165,120 |
| Lines | 17,373,950 | 16,625,123 |

A checked RH wrapper eliminates unnecessary imports, allowing unused modules to
be removed. Four expanded Mathlib-only files shrink from 20,554 to 1,551 lines;
all 53 changed declarations have exact comparison checks, and all four replacement
modules passed hosted Lean. Repeated archive proofs are also shared. The combined
candidate still needs the full Comparator. See the
[audit and verification limits](verification/aggressive/README.md).

The mathematical pass removes another **823 net lines**, including four new
shared modules. It replaces Smith normal form with finite-dimensional duality,
manual tensor inverses with pushout/cancellation, repeated coordinate and density
arguments with general theorems, and analytic calculations with differentiation,
specialization and comparison arguments. All included reductions passed focused
Lean checks; the combined full-project Comparator remains pending. The source
now contains 165,124 modules and 16,624,300 lines. See the
[mathematical explanations and checks](verification/mathematical/README.md).

Follow [verification/HARNESS.md](verification/HARNESS.md) for every new pass:
change actual source files, preserve theorem statements, commit the edits, sync
Machine Verification to that source revision, and record the exact checks.
