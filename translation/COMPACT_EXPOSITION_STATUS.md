# Compact exposition status — 27 November 2026

The same Principia LaTeX record is the master: `9c8cc33a546414334e2d4da3aade5210`, path `alpoge-rh-working-translation.tex`. The PDF is `alpoge-rh-consolidated-manuscript.pdf`; read `compact-publication.json` for its current receipt. Work was kept in memory and remote services; no manuscript files were written to the user's computer.

Formal source: lsernau/grh-lean at 72fead102f663d5c7a407964a13dc0cf9d977207, grh-compact. Reading notes: nasqret/riemann-rev at 82252d4e71d9f4db30a38e370dba78283ab3a921.

The manuscript is PARTIAL, not a standalone RH proof. It has 43 intermediate proof environments; this is not a mathematical coverage percentage. New work includes finite Selmer coordinates, auxiliary anticyclotomic primes, global reciprocity using the stated classical Greenberg–Wiles formula, bounded pencils, generic tilting, removal of ties, full simultaneous twist selection under explicit local/value hypotheses, local row balancing from the IsRow assumptions, double Cramer, the explicit one-prime first-order operator, the obeying-cocycle graph, the row-block Fitting bound, and glued lattice/indicator/class-sum proofs. Classical inputs (CFT, Chebotarev, Tate duality, Bloch–Kato, Amitsur) are explicitly distinguished from the new exposition. These prose proofs have been compared with source; LaTeX/visual checks are not independent mathematical certification.

Remaining source-specific input packages:

1. Integral interpolation and Euler-factor norm relations for the Hecke values.
2. Full denominator application: triangular primes, odd Tate-class estimate, character-block first-order Fitting bound, crystalline block defects, Hecke root-string identities and multi-prime patching, with all numerical losses.
3. Global theta product/period/vanishing identities, convergence, filling/separation, integral Fock/Cartan gauges and metric/height estimates for comparison forms.
4. Chain factorization with controlled scalar cost.
5. Crude integral completion rows.

Then integrate A/B, admissible data, weighted-prime comparison and good-window analytic conclusion. Do not label any unexpanded package as proved merely by citing its Lean declaration. Do not replace the corrected patched eigenvalue valuation bound with equality to the Ribet coefficient. Keep the distinction between vacuum at T and vacuum outside T.

Principia write_file currently returns an edit conflict even when it saved the body: always read back and compare. Existing-name PDF uploads fail; preserve a hash-verified remote release backup, then replace only our own PDF under the same filename. Never edit others' papers. See publication receipt. Keep incomplete status in the paper and workflow release.
