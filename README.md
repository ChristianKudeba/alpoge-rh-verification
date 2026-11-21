# Alpöge RH proof: full-source verification and compaction

This repository preserves the complete mirrored Lean source of the
Alpöge/Claude claimed proof of RH and Dirichlet GRH in Git history and develops
a compact candidate in `src/`. **The full proof has not been independently
verified by this work.**

## Current prose edition

[Read the single 194-page PDF](https://github.com/ChristianKudeba/alpoge-rh-verification/releases/download/short-route-35d65233980e51bda663ec97c44d5e9b3189680d/rh-short-route.pdf) or [its standalone LaTeX](https://github.com/ChristianKudeba/alpoge-rh-verification/releases/download/short-route-35d65233980e51bda663ec97c44d5e9b3189680d/rh-short-route.tex).

**This is an incomplete working exposition, not a standalone unconditional proof of RH.** The new first part follows Anton's shorter ordinary-zeta route. It prints the analytic implication, signed finite-group comparison, and conductor-one arithmetic and geometric comparisons. The earlier working translations remain as supporting chapters.

This revision reviews all five current PDFs on Principia and Anton's 552-line conductor-one reduction, its 630-line cubic-logarithmic revision and the subsequent two-character height reduction. It assembles the odd prime-to-degree minus bound from the internally printed descent and Bernoulli integer argument. It also writes out the uniform 24-generator dyadic tower bound, the full dual-module identification, finite-twist descent and the return to the CM field with restriction kernel length at most one. The trivial rational character vanishes at 3 and 7 for all positive twists and at resonant primes; the paper derives the plus-height bound from two remaining character estimates and proves the weaker cubic-logarithmic absorption. A centered prime-distribution identity and spectral uniqueness argument compare the two analytic routes. These new prose arguments have not been independently formalized.

The uniform plus-height bound (or its cubic-logarithmic weakening), uniform orders of the identified dyadic cokernels, high-twist and exceptional-set estimates, and the required global theta, ramified, cusp/metric and integral geometric constructions remain unproved in this exposition. This is a statement about the prose manuscript's completeness, not a demonstrated gap in the original formal archive.

The [build report](https://github.com/ChristianKudeba/alpoge-rh-verification/releases/download/short-route-35d65233980e51bda663ec97c44d5e9b3189680d/build-report.json) records successful reference/glyph checks, identical text from the chapter-based and flattened sources, rendering of every page, and no words outside the page. These are document checks. They do not establish mathematical completeness. See [the explicit status](translation/SHORT_ROUTE_STATUS.md) and [source versions and reviewed PDF hashes](translation/short-route-sources.json). The [current consolidated manuscript](https://principia-math.com/api/ws/files/c532a07c96ea42d67bf46ff0858324a5) and its single LaTeX project are published on [Principia's papers page](https://principia-math.com/projects/d16ab288ed353bc5b10e292ace0ddbc1/paper). Our superseded Alpöge manuscript uploads have been removed; the separate Masullo audit is retained.

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
