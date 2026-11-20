# Comparator controls and workflow drafts

These are **unexecuted templates** for historical Comparator
`c0c5a52d2aff92b457c3e5ed4a68c1ebc5795809` and lean4export
`15f6055e299ad5b89345e533cc2192f4cc00f659`, compiled unchanged using Lean
`v4.33.1`. They have not established either tool compatibility or RH.

Install `projects/`, `expected.json`, and `run-controls.py` together at
`scripts/verification/controls/`. The two workflow drafts belong under
`.github/workflows/` after review. The installer and isolated launcher are
provided separately by the parent integration task.

## Required launcher contract

```
scripts/verification/prepare-tools.sh TOOL_ROOT
scripts/verification/run-comparator-isolated.sh PROJECT_DIR CONFIG_PATH LOG_PATH
```

The installer writes `TOOL_ROOT/environment.sh`, containing the trusted concrete
executable paths needed by the launcher. It must pin the exact Comparator,
exporter and Landrun sources and record build/tool hashes. Current Landrun pin:
`ec104f6edc1e14d7fec6d31146f1ec6f9c192c5a`.

The launcher must require Linux, a non-root user, real Landlock ABI >= 6, and
passing actual denial probes. It must also enforce the reviewed additive
seccomp restriction, including AF_UNIX/socket creation, before launching the
genuine Comparator. Missing kernel support is an environment failure, never a
reason to use fake Landrun or remove isolation. The local host currently
reports Landlock `ENOSYS`; semantic controls remain unrun until a suitable host
is used.

The launcher preserves complete combined Comparator output at LOG_PATH and
returns its actual exit code. It must not turn process loss, a timeout, a
resource limit, missing prerequisites, or a child build failure into success.
An ordinary `lake build Main` must not run in the trusted checking workspace.
Comparator builds Challenge, exports it, then builds Solution (including its
Main import closure) and exports/replays that proof itself inside Landrun.

## Semantic controls

Every fixture has the same permitted axiom list as the full RH configuration:
`propext`, `Classical.choice`, and `Quot.sound`; NanoDa is explicitly disabled.
The Challenge's deliberate `sorry` fixes the trusted statement. Each fixture
is copied to a new work directory before the launcher runs. No fixture build
cache is reused.

| Control | Solution | Required result |
|---|---|---|
| positive | `1 + 1 = 2` by `rfl` | exit 0, `Lean default kernel accepts the solution`, `Your solution is okay!` |
| sorry | Same type, proof `sorry` | exit 1, `Illegal axiom detected: 'sorryAx'` |
| forbidden_axiom | Same type, proof uses `PrincipiaComparatorControl.forbidden` | exit 1, `Illegal axiom detected: 'PrincipiaComparatorControl.forbidden'` |
| statement_mismatch | Proves `2 + 2 = 4` under the same theorem name | exit 1, `Challenge and solution theorem statement do not match: 'PrincipiaComparatorControl.result'` |

The negative messages are taken from pinned upstream `Comparator/Axioms.lean`
and `Comparator/Compare.lean`. A nonzero exit without the expected semantic
diagnostic does **not** pass. These four controls test semantics, not isolation;
both controls and launcher denial probes are required.

Example after installing the tools and launcher:

```sh
source "$RUNNER_TEMP/verification-tools/environment.sh"
python3 scripts/verification/controls/run-controls.py \
  --launcher "$PWD/scripts/verification/run-comparator-isolated.sh" \
  --logs "$RUNNER_TEMP/evidence/controls"
```

Use a fresh logs directory for each run. `controls-report.json` records the
actual exit codes, expected diagnostic matches, input hashes, launcher hash,
and log paths. Full logs remain beside it.

## Workflow identity and evidence

Only `.github/workflows/alpoge-comparator.yml` is a candidate attestation. It
checks the exact workflow commit with the unchanged independent Challenge and
all five RH/Dirichlet-GRH entry declarations. Configure **this exact path** in
Principia's `comparator_workflow_path`.

`.github/workflows/alpoge-baseline-diagnostic.yml` instead copies the original
source commit `7cbf7a0c32fca1badf05931879a37c3f8a2b03b4` and adds the current
four canonical integration files and wrapper library declarations. Run this
first as a diagnostic. **Never select it as Principia's Comparator workflow.**
Its GitHub `head_sha` identifies integration instructions, not the restored
baseline source. Principia does not inspect workflow inputs or artifact scope.
A baseline pass must never certify an edited candidate.

Both drafts use separate dispatch-only workflows so baseline-first sequencing
is explicit. No matrix is needed. A six-hour job timeout bounds the run; the
full Comparator invocation has a five-hour subprocess timeout, leaving time
for preparation, controls and evidence upload. The standard Ubuntu runner may
still run out of memory or time on this source tree. Those outcomes are
recorded as limits, not mathematical rejections or successful verification.

An accepted Comparator verdict covers the configured declarations and their
proof dependency closure. It does not establish that every unused module in
the repository was rebuilt. A separate whole-repository build, if required,
must use the same reviewed sandbox and must not replace the Comparator gate.

The drafts deliberately omit the current Principia template's `module`-header
check and 4.35-only built-in Comparator script: those are incompatible with
this preserved 4.33.1 source tree. They do not weaken the trusted statements or
permitted axioms. Licensing and Principia source-import/profile limits remain
separate integration blockers.
