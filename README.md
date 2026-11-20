# Riemann Hypothesis in Lean — by Levent Alpöge (with Claude)

**This proof is the work of [Levent Alpöge](https://alpo.ge/)**, who announced on 2026-11-20 that, working with Claude, he had found a proof of the Riemann Hypothesis, extending to the Generalized Riemann Hypothesis, and formalized it in Lean without assumptions.

All credit belongs to Levent Alpöge (and Claude). This repository is only an unmodified mirror of the Lean code he published, so it can be browsed and cloned on GitHub.

本仓库只是镜像：证明由数学家 Levent Alpöge（和 Claude 合作）完成，版权与署名归他所有。

## Sources

- Announcement: https://alpo.ge/remark.pdf
- Original download (14 parts): https://alpo.ge/lean.tar.gz.part01 … https://alpo.ge/lean.tar.gz.part14
- The parts concatenated (`cat lean.tar.gz.part* > lean.tar.gz`) give a 239,275,554-byte archive with SHA-256
  `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`.
  The merged archive is attached to this repository's Releases; the `src/` tree here is its extracted content, unchanged.

## What is in it

- Lean toolchain `leanprover/lean4:v4.33.1`, Mathlib at `0df444a360eaa60ab8c11dca51a86af692955474`
- About 175,000 `.lean` files, about 17.4 million lines
- `src/Statements.lean` states the targets; `src/Main.lean` proves them, starting with
  `theorem riemannHypothesis : RiemannHypothesis` (Mathlib's own definition)

## Status

As of the date of mirroring, no independent check of this code has been published.

```bash
lake exe cache get && lake build
```
