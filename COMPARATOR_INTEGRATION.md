# Full-source Comparator integration

This integration checks all five conclusions in `Solution.lean` against
independent Mathlib statements in `Challenge.lean`. Importing `Main` requires
the substantive source tree. The four entry files alone are not the proof.

## Toolchain and tool provenance

- Project and Mathlib toolchain: `leanprover/lean4:v4.33.1`.
- Lean release commit: `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`.
- Project Mathlib revision: `0df444a360eaa60ab8c11dca51a86af692955474`.
- Genuine `leanprover/comparator` revision:
  `c0c5a52d2aff92b457c3e5ed4a68c1ebc5795809`.
- Its pinned `lean4export` revision:
  `15f6055e299ad5b89345e533cc2192f4cc00f659`.
- Landrun revision: `ec104f6edc1e14d7fec6d31146f1ec6f9c192c5a`.

The historical Comparator declares Lean 4.33.0. Its unchanged sources and
unchanged exporter sources successfully compiled under 4.33.1, in 21 Lake build
jobs. This is a tested patch-version build adaptation, not an upstream 4.33.1
release. The project toolchain and Mathlib pin have not been upgraded.
`enable_nanoda: false` uses Comparator's in-process Lean kernel replay; no
independent NanoDa replay is claimed.

The local build produced these SHA256 digests (binary hashes can differ across
build environments; CI records its own):

```text
b642ef735d34ea12e4b0d3197c84f69c6eebd34be00726eb5b4bb91da35c4e02 comparator
805ab4cc6a88dcef109644d201c3142261f524aecaf58b04913a9f029e21e9b5 lean4export
13859fe34190358d9e64dcd308f33cb46c12730dec35b896ac8491d3b7ef6bd9 landrun
```

## Isolation and actual checking

The launcher calls genuine Comparator, which builds Challenge and Solution in
genuine Landrun subprocesses, exports their target closures, compares statement
dependencies, checks the permitted axiom list, and replays proofs in the Lean
kernel. It does not substitute `#print axioms`, source grep, or an LLM review.

Comparator documents an AF_UNIX vulnerability in Landrun on kernels older than
7.1. The additional Linux x86-64 launcher imposes a seccomp filter inherited by
children. It closes inherited nonstandard descriptors and denies socket,
socketpair and io_uring creation, including AF_UNIX; rejects root; and requires
Landlock ABI at least 6. These restrictions supplement Landrun. Before checking,
a probe requires protected writes to fail, permitted writes to work, and socket
creation to fail. There is no fake-Landrun or unsandboxed fallback. Kernel,
hardware, trusted challenge, trusted Lake configuration, and trusted dependency
cache remain part of the trust assumptions described by upstream Comparator.

The current local container returns ENOSYS for `landlock_create_ruleset`.
Accordingly, no isolated local semantic-control pass or full Comparator pass is
claimed. Shell syntax, Python syntax, C compilation with warnings as errors,
and the actual Comparator/exporter/Landrun builds passed. The sandbox launcher
correctly refused the unavailable Landlock environment. CI must run the
positive control and reject the sorry, forbidden-axiom, and changed-statement
controls for their expected semantic reasons before running the full target.

## Reproducing a run

From a checkout with the root wrapper libraries added to its original
`lakefile.toml`:

```sh
scripts/verification/prepare-tools.sh /absolute/path/to/verification-tools
source /absolute/path/to/verification-tools/environment.sh
# Fetch the trusted, pinned Mathlib cache before isolation. Preserve the manifest.
lake exe cache get
scripts/verification/run-comparator-isolated.sh \
  "$PWD" "$PWD/comparator.json" /absolute/path/to/comparator.log
```

Only `lake exe cache get` is intended outside the checking sandbox. Do not run
`lake build Main` before Comparator on the verification runner. The launcher
requires all dependencies to be fetched before isolation because networking is
denied during the checked build.

The exact-candidate workflow and the original-source baseline diagnostic are
separate. Principia must select only `.github/workflows/alpoge-comparator.yml`,
which checks the complete source at the workflow's exact commit. A baseline
diagnostic restores source from the original commit and cannot attest the
candidate commit even if it succeeds.

The full source has roughly 175,000 modules and over 1 GB of Lean text. There is
no measured full-build runtime or peak memory. Comparator retains exports and
parsed environments in memory, so the full comparison may need more memory than
module compilation. The GitHub job has a six-hour ceiling. Resource exhaustion,
missing kernel features, compilation failures, and timeouts are unresolved
verification outcomes, never proof success. Baseline and compacted candidate
must be distinguished in all reports.
