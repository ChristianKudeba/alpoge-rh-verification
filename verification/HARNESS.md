# Incremental compaction workflow

This project audits the full Alpöge/Claude claimed proof of RH and Dirichlet GRH.
The source is a mirror; full independent verification is pending.

Original source: `CocoSgt/riemann-hypothesis-lean` at
`7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`.
Preserve the `alpoge-source-7cbf7a0c` tag as the original baseline.

For every compaction pass:

1. Read the current repository commit, Machine Verification files, and accessible
   harness notes. Other users' private runs are not available automatically.
2. Choose a concrete duplication or unnecessarily long proof in the actual source.
   Preserve public theorem types and the independent statements in `Challenge.lean`.
3. Record the hypothesis and target files in the harness. Check the replacement
   with Lean. A standalone helper check is evidence for that helper only.
4. Edit and commit the actual source files. Record before/after line and byte
   counts, the base and candidate commits, and the Lean check identifiers.
5. Push the candidate source to the connected verification repository. Pull the
   canonical Machine Verification files from that same commit into Principia.
   Confirm the saved bytes and references; a patch in the editor alone is not a
   synchronized source update.
6. Run the full Comparator against the unchanged RH statement. Report the exact
   checked commit, status, and failure, timeout, or resource limits. Only a
   successful full run can establish the configured proof was checked.

The workflows are dispatched explicitly to avoid duplicate full builds on every
small metadata push. After each completed source pass, run:

```sh
gh workflow run alpoge-comparator.yml --repo ChristianKudeba/alpoge-rh-verification --ref main
```

The separate `alpoge-baseline-diagnostic.yml` checks the preserved original
source. Select only `.github/workflows/alpoge-comparator.yml` in Principia's
Machine Verification configuration; a baseline result cannot attest a candidate.

Do not replace the full RH target with a conditional lemma, loosen the permitted
axioms, treat an unstarted check as running, or mark the project verified because
a compact helper passed. Preserve any failing candidate separately from the last
verified source. The full-source build remains a separate requirement when a
hosted harness can load only Mathlib.

Current integration constraint: the exposed Principia MCP upload accepts only
`Challenge.lean`, `Solution.lean`, `comparator.json`, and `formalization.yaml`
(plus a repository README). The full module tree must live in the connected Git
repository. Do not describe those four entry files as a full on-site source upload.
