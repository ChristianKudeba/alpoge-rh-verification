# Alpöge RH proof: full-source verification and compaction

This repository preserves the complete mirrored Lean source of the
Alpöge/Claude claimed proof of RH and Dirichlet GRH in Git history and develops
a compact candidate in `src/`. **The full proof has not been independently
verified by this work.**

## Current prose edition

[Read the single 499-page PDF](https://github.com/ChristianKudeba/alpoge-rh-verification/releases/download/short-route-e91c5c8b4951a4ddc93a3f9258e9c0343c990c64/rh-short-route.pdf) or [its standalone LaTeX](https://github.com/ChristianKudeba/alpoge-rh-verification/releases/download/short-route-e91c5c8b4951a4ddc93a3f9258e9c0343c990c64/rh-short-route.tex).

**This remains an incomplete working exposition, not a completed standalone unconditional proof of RH.** It presents the shorter ordinary-zeta route with reductions from Principia contributors and retains the earlier translations as supporting chapters in the same manuscript.

The current edition assembles both uniform rational-character estimates in prose, using the generic rank-three and exceptional rank-four endpoint constructions. It also contains the global high-twist cohomology bound, the dyadic common-window estimate, the plus-height assembly, the analytic endpoint and a general Hodge maximal-slope bound. These prose arguments have not been separately formalized or independently refereed.

The theta chapters develop real and unramified matching, the compact base case, cone evaluation and its finite-vacuum Euler factor, four constant terms, square-integrability and quotient descent. The full compatible theta induction and the integral/geometric common-window construction remain under review. In particular, the uniform section/covolume estimates and their compatibility with the same fields, models, metrics and windows are still required before a standalone conclusion can be claimed.

The added height-budget chapter proves the determinant cancellation and numerical absorption with the model, saturation and integral-comparison premises still explicit.

The review of [Chojecki's 23-page companion](https://www.ulam.ai/research/rh-short.pdf) records its shorter analytic exposition and its explicit use of the arithmetic construction and cohomological window as cited inputs in Sections 6–7. It does not replace those construction proofs.

Part II begins on page 341. The [build report](https://github.com/ChristianKudeba/alpoge-rh-verification/releases/download/short-route-e91c5c8b4951a4ddc93a3f9258e9c0343c990c64/build-report.json) records successful compilation, reference/glyph/title checks, identical chapter-based and flattened text, and rendering of every page. Those document checks do not establish mathematical completeness.

The [current Principia PDF](https://principia-math.com/api/ws/files/cca76507fe3aab3634da04d935689d92) is the same 499-page edition. The [paper page](https://principia-math.com/projects/d16ab288ed353bc5b10e292ace0ddbc1/paper) contains one current manuscript and one five-input LaTeX project for this route. The separate Masullo audit and other contributors' papers are unchanged. Source details are recorded in [the status](translation/SHORT_ROUTE_STATUS.md), [source manifest](translation/short-route-sources.json), and [publication record](translation/principia-publication.json).

The completed literal edition contains formal-term renderings and generated dependent-type annotations. It does not mean that all mathematical proofs have already been reconstructed as explanatory prose. The [reading guide](translation/kernel/reading.md) and [annotation generator](translation/kernel/prose_records.py) specify that scope.

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
