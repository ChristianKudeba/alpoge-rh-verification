# Checked lightweight RH wrapper and exact source-pruning candidates

The original `RiemannHypothesisOfEveryCharacter.lean` had 231 physical lines and
roughly 209 imports, although its two declarations only derive zeta
nonvanishing and RH from `UpperTheory.EveryCharacter`. Both theorem signatures
are preserved. The replacement imports `EveryCharacterStatement` and the
already-shared `Formalism.GammaFactorNonvanishing.RhOfRight`, retains the exact
zeta proof, and uses that reflection theorem for RH.

The owned file is now 9 lines and 576 bytes, from 231 lines and 20,673 bytes.
No other source file was edited by this analysis agent, and this agent did not
delete source modules or alter either running GitHub verification job.

Principia scratch check `cc4347d59ca91570ba37d9ecda8f4d65` passed the exact
flattened helper sources, the replacement, and definitional consistency tests
with `autoImplicit = false` and `relaxedAutoImplicit = false`. The printed axiom
inventories for both wrappers and the shared reflection theorem contain only
`propext`, `Classical.choice`, and `Quot.sound`, with zero `sorry`. The checked
file and response are `ExactHelpersCheck.lean` and `hosted-helper-check.json`.
This is a helper check, not full-project verification or evidence of a full
Lean 4.33.1 build. Existing GitHub jobs concern the earlier commit.

## Exact graph result for this edit alone

Compared against `a6f8e4806fc188e1b5053df51f440df74d6fd2cb`:

| Main import closure | Before | After |
|---|---:|---:|
| Project modules | 175,184 | 165,120 |
| Physical lines | 17,373,664 | 16,645,125 |
| Nonblank lines | 15,531,244 | 14,865,007 |
| Bytes | 1,030,497,602 | 981,690,456 |

`newly-unreachable-paths.txt` contains exactly 10,064 paths: 728,317 physical
lines, 666,015 nonblank lines, and 48,787,049 bytes. `all-unreachable-paths.txt`
adds the six source modules already outside Main's closure, for 10,070 paths,
728,603 physical lines, 666,261 nonblank lines, and 48,804,555 bytes.
These are actual candidate deletions, not a claim that the files were removed
by this agent. The 222-line wrapper reduction is additional to the listed
unreachable files.

The entire revised source import graph is acyclic. The external import set is
unchanged. There are no imports from retained source modules into the removal
set. The six previously unreachable modules also import none of the newly
unreachable modules. `Main`'s explicit library roots (`Statements`, `Main`) are
both retained. All other source libraries use wildcard globs, so pruning the
entire unreachable set creates no missing explicit source roots. Root-level
`Challenge` and `Solution` are untouched; the five public Main goals remain the
verification targets. A full build remains necessary to validate elaboration
after changed transitive imports.

`review_rh_candidate.py` reproduces these findings from the pinned original
graph, Git changes through `a6f8e480`, and only the owned current wrapper file.
It deliberately excludes other concurrent edits. Recompute the combined
closure before pruning if another agent changes imports. The baseline source
remains available in Git under `alpoge-source-7cbf7a0c`.

## Other graph candidates

`analyze_bottlenecks.py` computes immediate dominators of the exact Main import
DAG, using LCA of topologically prior predecessors. A module's dominated subtree
is only a conditional removal bound; a short theorem may require its entire
large dependency. `bottlenecks.json`, `dominators.json.gz`, and
`thin-heavy-import-candidates.json` retain the reproducible data.

The next large thin wrappers involve genuine geometry, Galois, and theta
claims. Their short bodies alone do not justify deleting those proofs. The
CharacterBoxes follow-up audit separately records failed pruning candidates
to avoid confusing a large local closure with a globally removable branch.
