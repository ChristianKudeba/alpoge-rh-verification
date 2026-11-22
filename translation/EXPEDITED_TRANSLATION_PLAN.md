# Plan to finish the standalone prose translation more efficiently

21 November 2026. This is an execution plan, not a claim that the current manuscript proves RH.

## Deliverable and fixed scope

Produce one coherent ordinary-RH manuscript in the existing Principia paper. Retain all valid work already in the 499-page edition. Complete the construction-specific arguments without requiring the reader to consult the Lean archive. Standard established background may be cited with its precise hypotheses and primary reference.

Use the existing conductor-one route and its current source baseline, `alpoge-source-7cbf7a0c` / `7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`. Record exceptions when a contributor's checked reduction is used. Freeze the Lean and Mathlib pins. Do not mix later upstream simplifications into the mathematical baseline without a separate comparison.

Postpone new alternative proofs, generalizations and page-count optimization until the faithful translation is complete. Existing alternative drafts may be used only after their fidelity or independent correctness is checked. A difficult source proof is translated as written before a shorter substitute is attempted.

## 1. Establish the actual remaining work once

The initial ledger is `translation/proof-coverage-ledger.json`. It lists known work packages; it is not yet an exhaustive dependency graph.

For every construction-specific theorem needed by the ordinary-RH endpoint, record:
- exact source file, declaration and revision;
- its mathematical statement with relevant custom definitions and implicit hypotheses expanded;
- immediate nonstandard dependencies and whether a previously reviewed section already proves them;
- the manuscript section/draft and its current status;
- assigned writer, independent reviewer and review result.

Status is one of: located, drafted, checked, integrated. Original kernel verification and prose review are separate fields. A statement is not marked checked merely because its source compiles, a PDF compiles, or a similarly named theorem exists.

Stop expansion at correctly stated, established mathematical background. Avoid translating unused general-GRH branches, wrappers and boilerplate unless they carry a substantive assumption. Do not use module/page counts as effort estimates.

## 2. Four-agent operating model

| Role | Primary responsibility | Concrete output |
| --- | --- | --- |
| Translation lane A | Integral models, actual Hodge lattices, FlatDegree/FlatSat, Frobenius and determinant extension | Faithful prose for one bounded source argument at a time, with exact model and specialization scope |
| Translation lane B | Uniform short integral theta sections, common denominators, carrying sections, height/volume/covolume | Complete quantitative argument retaining the same section, level and constants |
| Independent reviewer | Check each delivered argument against its exact source; begin with the existing theta-induction drafts | Accept/reject report with precise missing step or hypothesis; no silent repairs |
| Integrator | Maintain the ledger, resolve notation, integrate accepted text and track the common-window assembly | One consistent manuscript and one current Principia PDF |

The reviewer and integrator can exchange roles for independent checks of integrator-written material. Give each unit one writer and one reviewer. Do not have all four agents independently read the same large closure.

The six existing theta drafts are reviewed and integrated before anyone re-derives their mathematics. Reuse valid existing arithmetic and height-budget chapters. Review drafts remain outside the proved manuscript until accepted.

## 3. Prioritize the actual critical path

1. Resolve the outstanding formal-Hodge/model/Frobenius and determinant-extension joins beneath FlatSat.
2. Complete the bounded integral spanning-family construction: one clearing integer, all embeddings, actual divided weights.
3. Construct the carrying section with simultaneous arithmetic valuations and archimedean bounds.
4. Supply geometric section/function-field/degree comparisons on that same compactified model.
5. Complete height-to-volume and covolume assembly, preserving its exact leading coefficient.
6. Join the theta, arithmetic, metric and lattice data into the actual common-window family.

The theta-induction review can proceed in parallel with items1–4. The final same-window assembly depends on all these branches and should not be announced complete from separate existence results.

## 4. Small work units and explicit handoffs

Use work units corresponding to a theorem or a short connected cluster of source lemmas. Each handoff contains:
- source declaration(s) and revision;
- exact statement and notation;
- full argument, including any construction-specific case split;
- hypotheses used and constants with their dependency order;
- the immediately required inputs, with links to their proofs;
- any unresolved step, explicitly labelled.

If a unit is too large to review in one pass, split it at an actual intermediate lemma. If a cited theorem is too weak, first trace the original source's application/reduction. Do not improvise a stronger theorem or conceal the mismatch in an unnamed compatibility assertion.

Use 30–45-minute work checkpoints as scheduling targets, not proof-completion promises. At a checkpoint, preserve the exact source position and unresolved claim rather than restarting the argument.

## 5. Reduce operational overhead

- Cache source statements, expanded definitions and contributor reviews in memory/remote files, so they are not rediscovered on every turn.
- Share compact progress notes containing links, precise scope and blockers; do not repeatedly paste the entire manuscript or dependency tree.
- Use Principia's documented `POST /api/rh/progress` route with the existing signed-in browser session for compact notes. The 'RH Harness Run' chat demonstrated this route and verified the saved entries. Do not create/rotate personal-agent credentials.
- Run LaTeX compilation/render checks after a reviewed batch or a structural change. Continue independent mathematical work while remote builds run.
- Update the same Principia manuscript after the batch passes document checks. Preserve all other contributors' papers.
- Use focused Lean inspection/checks when they resolve an actual ambiguity about a statement, inference or proposed replacement. Repeatedly rebuilding the unchanged full original proof is not a translation milestone.
- Keep manuscript artifacts and new work on GitHub/Principia. Do not save them to the user's local computer.

## 6. Definition of completion

The paper is complete only when:
1. Every construction-specific premise of the final ordinary-RH theorem has a printed proof or an explicit correctly matched established background theorem.
2. The field, integral model, lattices, sections, actions and metrics used in those proofs are identified as the same objects.
3. The exact leading terms, normalizations, prime/twist ranges and constant/threshold order are retained.
4. One compatible common-window witness has been assembled, rather than separate witnesses for individual estimates.
5. An independent end-to-end mathematical review finds no open construction-specific assumption.
6. The single PDF passes references, glyphs and visual checks.

Compilation/layout checks alone do not certify mathematical completion. Newly written prose is not automatically kernel-certified.

## First checkpoint and forecast

Use the next 60–90-minute working block to finish the critical dependency inventory and pilot two representative hard source arguments: one integral-model/Frobenius argument and one bounded-section/covolume argument. Aim to finish their translation/review, but record the exact residual source work if they do not close.

At that checkpoint report: newly checked terminal arguments, their review time, remaining dependency chains, and actual blockers. Give a completion forecast only from those observations. Do not promise a date from page count, raw export size or the existence of the original formal proof.

## Immediate coordination facts

The current paper is the 499-page working edition from source `e91c5c8b4951a4ddc93a3f9258e9c0343c990c64`, artifact `cca76507fe3aab3634da04d935689d92`. It remains incomplete.

The existing [translation audit and reusable height calculations](https://github.com/ChristianKudeba/alpoge-rh-verification/blob/33613ca46e11c0a50b42dea1912eef9d79cbf69d/translation/research-notes/2026-11-21-prose-translation-audit.md) contain two checked elementary deductions and scoped contributor findings.

The nine [geometry review drafts](https://github.com/ChristianKudeba/alpoge-rh-verification/tree/924a03f25a9fd0f81a5501e737f2d72ceaeaba78/translation/review-drafts) are preserved, with their outstanding joins stated. They must not be represented as already integrated proofs.
