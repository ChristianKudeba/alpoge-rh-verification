# Translating Alpöge’s formal proof of the Riemann hypothesis

[Read the manuscript source](manuscript.tex). It follows the released proof through Dirichlet-character nonvanishing to classical RH. Each chapter records the estimates it derives and the assumptions imported at that point. The closing section lists outstanding proofs for the standalone prose edition.

The source for this translation is Alpöge’s release of 20 November 2026. The concatenated 14-part source archive has SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`. References in the chapters identify declarations in the release mirror at `40e56bab026552e089d7afcfeff08d2defb9c005`. The translation follows that release even where this repository has subsequent Lean edits. [Author’s announcement](https://alpo.ge/remark.pdf) · [Independent formal verification](https://math.mit.edu/~drew/grh/)

The [kernel renderer](kernel/kernel_tex.py) typesets proof terms in indexed notation for dependent type theory. [The sample](kernel/sample/kernel-00001.tex) contains the first 105 records of the solution export. A proof term’s notation and the mathematical prose are distinct deliverables.
