# Dependency pruning and proof-source compaction

This candidate removes **748,827 source lines (4.31%)** and **10,070 modules**
relative to integration commit `a6f8e4806fc188e1b5053df51f440df74d6fd2cb`.
Full candidate compilation and Comparator verification are still pending.

| All substantive `src/` Lean source | Before | After |
| --- | ---: | ---: |
| Modules | 175,190 | 165,120 |
| Physical lines, including comments | 17,373,950 | 16,625,123 |
| Nonblank lines | 15,531,490 | 14,845,036 |
| UTF-8 bytes | 1,030,515,108 | 980,062,909 |

These counts exclude Mathlib and verification fixtures. The original mirror had
175,187 modules; earlier compaction added three helpers. The unchanged original
remains available at tag `alpoge-source-7cbf7a0c`. Git history retains deleted
files; they are not hidden in a generator or loaded from an encoded archive.

## Changes

The RH wrapper `RiemannHypothesisOfEveryCharacter.lean` is reduced from 231 to
9 lines by reusing the existing zeta/Dirichlet identification and right-half-plane
RH theorem. Both public statements are retained. Its import cut makes 10,064
modules unreachable from `Main`; another six were already unreachable. Removing
these 10,070 files saves 728,603 lines. Every removed file matched its baseline
hash before removal. The remaining 165,120-module import graph is acyclic, has no
imports into the removed set, and is exactly the closure required by `Main`.

Four Mathlib-only files replace expanded explicit typeclass arguments with
ordinary inferred arguments. They preserve reducibility, public names and
definition values; theorem comparisons preserve exact types, using Lean's proof
irrelevance. The replacements compile without a source generator.

| File | Original lines | Compact lines |
| --- | ---: | ---: |
| `MemOfClosed.lean` | 5,746 | 140 |
| `ComplexNormedInstanceCompat.lean` | 3,669 | 1,122 |
| `MulMemIntA.lean` | 4,969 | 78 |
| `CovariantDegrees.lean` | 6,170 | 211 |

These four files remove 19,003 lines. Fifteen further files share repeated proofs
and replace exact duplicate modules with forwarding imports, saving 999 lines.
Together with the 222-line RH wrapper reduction, retained-file edits save 20,224
lines in addition to pruning.

## Verification and its limits

- All four compact Mathlib-only modules passed complete hosted checks under the
  original build options. Exact `rfl` comparisons cover 53 edited declarations
  (including CovariantDegrees' private helpers). Printed axiom inventories contain
  only the configured standard axioms; not every declaration was printed.
- The RH wrapper was checked with the exact helper statements and proofs.
  Two additional checks validate the shared submersion and characteristic-polynomial
  arguments. These are helper checks, not RH verification.
- Other archive-dependent sharing edits have structural signature, scope and
  dependency checks. They still require full project elaboration. An acyclic
  import graph does not establish that all downstream proofs compile after an
  umbrella import is narrowed.
- Review of all three direct consumers of the RH wrapper found retained providers
  for every matched explicit project symbol in each consumer's own import closure,
  and no concrete missing instance or simp dependency. This remains a static review;
  see `rh-wrapper/consumer-review.json`.
- `Challenge.lean`, `Solution.lean`, all five Comparator targets, permitted axioms,
  `Main`, `Statements`, Lean/Mathlib pins and build options are unchanged.
- The candidate workflow checks its exact commit. Its concurrency key includes
  that commit so earlier full checks can finish while this candidate is checked.
  An earlier commit's successful result would not verify this candidate.

The individual audit JSON files record declaration names, source hashes and
hosted check IDs. `hosted-check-results.json` preserves successful raw responses;
large original-versus-compact scratch snippets remain in the harness workspace
instead of duplicating expanded proof source in this repository. Original terms
are available from the pinned baseline, and compact terms are in `src/`.

Reproduce the complete source counts, preserved inputs, reachability and cycle
audit without modifying the checkout:

```sh
python verification/aggressive/audit_snapshot.py --out /tmp/compaction-audit.json
```

`source-audit.json` records that audit; `pruned-files.json` records every removed
path and original hash. These static reports are not a Comparator acceptance.
