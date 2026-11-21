# Shared estimates for smoothed Mangoldt sums

The original proof repeats the same finite-sum argument for two functions:

- `GPsi D ell ψ y`, in the nontrivial-character case `ψ ≠ 0`;
- `Br.Fc c ell y`, for arbitrary coefficients satisfying `‖c n‖ ≤ Λ n`.

For `ψ ≠ 0`, the first function is exactly the second with
`c n = (Λ n : ℂ) * primVal D ψ n` and constant `ell ψ`. The established
`AN.norm_coef_le` supplies the only extra mathematical input. The group,
inertia, Frobenius, and character structure have no other role in these
three finite-sum estimates.

The replacement proves the coefficient-level statements once under the
new `AN.smoothedSum` definition, and specializes them to both functions.
It preserves the exact constants and all arguments of the original six
theorems, including the unused lower bound on the second argument in
`deriv_char`. `Br.Fc`, `GPsi`, `primVal`, and every existing definition
remain unchanged. Separately, the real finite truncation identity is now
obtained by casting the already established complex identity (`truncC`).

There is no new nonvanishing hypothesis or assertion about the Riemann
Hypothesis here. This is reuse of a stronger existing coefficient theorem.
Placing the generic proof in `LipschitzWeightAndMinimum` preserves the
existing import direction and introduces no cycle. No imports, instances,
attributes, notation, or initializers change. `floor_div_le` is moved
earlier in the same namespace without changing its statement or proof.

The two files lose 77 lines in total (81 nonblank lines). The structural
review preserves the text of all 217 existing theorem signatures and all
existing definitions. See `structural-review.json` and `source.patch`.

`build-check.py` assembles `proof-bundle-check.lean` from the exact current
source, including the actual definitions of `ArithData`, `cosetMean`,
`primVal`, and `GPsi`, the unchanged coefficient norm proofs, the unchanged
Mertens and Chebyshev estimates, and all ten changed/new proofs. No
supporting mathematical statement is replaced by an axiom or an assumed
variable. The check requests axiom reports for every changed/new proof.
The exact snippet hash and scope are in `proof-bundle-manifest.json`.

The exact proof bundle passed Principia's hosted checker on the first
submission, check `7d16a9bfd3b1315f6fe903de57dfcdfe`. It reported zero
sorries and no custom axioms. All ten requested axiom reports contain only
`propext`, `Classical.choice`, and `Quot.sound`. The sole warning concerns
an unused `DecidableEq H` parameter in the unchanged supporting
`norm_cosetMean_le` theorem. See `hosted-result.json`.

Tested bundle SHA-256:
`84dbf8f74f1098bfa80a1352f16c0b727de0183d092ea4a50e286eb59c675d9b`.
The proof-bundle check is not a whole-project build and does not establish
the full RH claim. The final project build and comparator remain required.
