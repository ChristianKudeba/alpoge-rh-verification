# Current RH manuscript

[Read the consolidated 347-page manuscript](https://principia-math.com/api/ws/files/abbc587cbe529d1d0d337a66f4552119).

This is our single current Alpöge/RH working manuscript on Principia, with reductions from Principia contributors. It consolidates our earlier explanatory papers and supporting translations. **It is not a completed standalone unconditional proof of RH.**

## One editable LaTeX project

The master is [alpoge-rh-working-translation.tex](https://principia-math.com/projects/d16ab288ed353bc5b10e292ace0ddbc1/editor?file=9c8cc33a546414334e2d4da3aade5210). It includes three parts of the same paper:

- `alpoge-translation/arithmetic.tex`
- `alpoge-translation/theta-and-geometry.tex`
- `alpoge-translation/prime-sums-and-zeros.tex`

These stable paths are reused. Their part boundaries were adjusted to keep every editor file below Principia's 512 KB limit; they are not separate manuscripts. Expanding the inputs reproduces the [standalone LaTeX](https://github.com/ChristianKudeba/alpoge-rh-verification/releases/download/short-route-eb4a9b483869b4b3c07606d80375cc58534e3cfd/rh-short-route.tex) byte for byte.

The edition is pinned to [source commit eb4a9b483869](https://github.com/ChristianKudeba/alpoge-rh-verification/commit/eb4a9b483869b4b3c07606d80375cc58534e3cfd). The [build report](https://github.com/ChristianKudeba/alpoge-rh-verification/releases/download/short-route-eb4a9b483869b4b3c07606d80375cc58534e3cfd/build-report.json) records identical text from distributed and flattened sources, successful reference, glyph and credit checks, all pages rendered, no overfull boxes and no words outside the page. Representative page sheets were inspected. PDF SHA-256: `00f9d7a1311995a462a0a7c34c304895e6d7a233e7e94310ec659b3d40818e87`. These are document checks, not a mathematical verification.

## Current mathematical contents

Part I occupies pages 6–187; Part II begins on page 188 and preserves the supporting longer-route translations. The current revision develops the analytic fourth-power criterion, signed comparisons, conductor-one packet, uniform dyadic window and global high-twist estimate. It supplies the bounded-order exceptional character case and the fixed-prime integer absorptions.

The expanded arithmetic chapters now include finite Cayley–Hamilton quotients, paired determinant algebra, the Selmer-to-presentation conversion, common patched support, ordinary function modules, classical control, and integral old/new maps. The CaseII seed and Gaussian local rigidity are written with their remaining classical and arithmetic realization inputs retained. The geometry chapters include integral descent, short generators, finite theta tests, the common ambient Weil system, heat jets, frame-slab reproduction and denominator calculations with their model and comparison hypotheses displayed.

The finite-level first- and second-Selmer bounds, finite regular trace detectors and actual Taylor–Wiles group tower/common limit are now proved for the displayed nice-point hypotheses. The rank3 curve argument proves N1 and N3, and the exact V0ok matrix argument proves N4. The actual CaseII Hecke quotient, compact integral determinant interpolation, seed membership and residual Speh exclusion are matched. The full uniform generic and nontrivial character estimates still require the remaining compatible curve/link selection, seed/support insertion and quadratic descent with full local data. The classical anisotropic doubling and Eisenstein-continuation inputs are matched with their exact normalizations. The canonical cusp-weight mean has uniform constant four; a quadratic CM elliptic witness is constructed and its period computed with the exact metric and discriminant corrections. The geometry still requires compatible window data with `ThetaIntegralsAgree`, `LocalMatching` and `CovolumeBoundOfX`. The new prose has not been independently refereed or separately formalized.

## Contributor and community review

The other contributor's current 725-page draft was reviewed at its opening reduction and selected character, cohomology, patching and support passages. Its conditional endpoints have not been treated as complete proofs. Other users' papers and source files remain unchanged.

The latest queue snapshot for this edition reports 2,021 translated and 1,630 reviewed modules. Translation/review counts are distinct from literal proof-record coverage.

The [community repository](https://github.com/leanprover-community/riemann-hypothesis) was checked at commit `7da4577eb40dd74b09218d111114ca43bc2ad226`. PR45 is merged; PR44 remains open at `c9b3e57f0fe987012d32c2523635387bfe56d5a5`, with its combined clean build and independent comparison still pending in the checked snapshot. The [LUMI verification discussion](https://github.com/aapolipponen/rh-lean-check-lumi/issues/2) and the frozen definitions clarify that `FamilyClassConnected` means a compatible eventual `ChainTied` family. The degenerate final DivX shell preserves substantive lattices, metrics and numerical data; it does not discharge the three independent theta and covolume inputs.

The [Zulip discussion supplied by the user](https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/Discussion.3A.20Alp.C3.B6ge.20Proves.20the.20Riemann.20Hypothesis/near/642250042) could not be read through the available live or archive access. It has not been cited as verified evidence. Both resources will be rechecked every few hours during active work.

## Literal records and archives

The [216,211-volume literal edition](https://github.com/ChristianKudeba/alpoge-rh-verification/releases/tag/rh-literal-audit-v1) renders formal records with generated dependent-type annotations. Its transcription audit does not mean that every argument has already been translated into explanatory prose. The obligations above describe this manuscript's unfinished coverage; they do not demonstrate a mathematical gap in the original formal proof.

The previous 214-page PDF remains preserved in its [source-pinned release](https://github.com/ChristianKudeba/alpoge-rh-verification/releases/tag/short-route-e52042ab25cc04c0c282c1caa55b311fafc6374b). Earlier source versions and the consolidation inventory are [archived on GitHub](https://github.com/ChristianKudeba/alpoge-rh-verification/blob/b5d5f465049e6f9df7af49f9b486164dee5acd60/translation/archive/principia-before-194-page-consolidation.json).

Our [Masullo zero-count audit](https://principia-math.com/api/ws/files/b561b940f8dd3d3b8f8a2d1d83b359dc) remains separate because it concerns a different proof attempt. The three other retained PDF attachments are unchanged. The project-wide research notes reached their 400,000-character limit, so this index also records the current progress without overwriting shared notes.
