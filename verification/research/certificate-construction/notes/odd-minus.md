# Constructed uniform certificates for the odd-minus component

This work constructs an integer from generalized Bernoulli products and a
factorial. It does not choose an integer after assuming the desired total
Selmer-length estimate. The plus eigenspace and the prime two are not covered
by this certificate.

Fix a cyclotomic conductor N≥1 and a twist cutoff t≥2. The original archive
proves one universal constant C≥0 in its pointwise Stickelberger estimate.
The certificate constructed here is

    M(N,t) = M_Bern(N,t) * (N!)^(t * ceil(2*C*N^7*t^3)).

For each twist 1≤e<t, the Bernoulli factor is the absolute value of the actual
nonzero rational integer given by the product of the integral generalized
Bernoulli values over **all characters of the correct parity modulo N**. The
integrality, rationality and nonvanishing come from the archive's `b_prodint`.
Their finite product over e is M_Bern. The original `prodVal` theorem discarded
these integers and retained only their valuations; the new interface retains
the integer certificates themselves.

The same M works for every CM number field E embedding in Q(ζ_N), every
algebraic closure Ω and every local-data family. For every odd prime p,

    sum_(1≤e<t) minusLen(ld_p,e) ≤ v_p(M)

in the extended natural numbers. Consequently none of these lengths can be
infinite. The code never concludes finiteness by converting infinity to zero.

## Proof and size bound

For p>N, the embedding gives [E:Q]≤φ(N)≤N<p, so p does not divide the degree.
The archive's pointwise Bernoulli comparison (`Odd.atPrime`) applies. The
Bernoulli integer dominates the entire eligible character subsum at every prime;
positive log p allows cancellation to obtain the valuation bound.

For p≤N, the archive's pointwise `StickBound` applies to every odd p. Its real
length bound is at most `2*C*N^7*t^3`, using `log p≥1/2`, degree≤N and e<t.
Every such prime divides N!, so the factorial power dominates the sum over
all t-1 relevant twists. This replaces a field-specific list of primes
dividing the degree by one explicit factorial.

The resulting uniform bound is

    log M ≤ 3*N*t^2*log(t*N) + (2*C*N^7*t^3 + 1)*t*N^2
          ≤ (2*C+4)*(N*t)^9.

The first inequality follows from the character count φ(N)≤N, the elementary
factorial bound in the Bernoulli coefficients, `log(N!)≤N²`, and the ceiling
bound. The second inequality is proved in `OddMinusBudgetBound.lean`.

The polynomial degree is deliberately coarse. In the original windows, the
logarithm of the conductor is small compared with x^eps, so a fixed polynomial
in N and t can fit the target exponential budget. The certificate construction
is uniform in the character because it covers every CM cyclotomic subfield.

The proof bodies underlying the archive's existential constants use 30 in
`bdxLog`, retain 30 in `killPow`, and multiply by eight for `StickBound`.
Thus a separately exposed numerical API could use 240, factorial exponent
`480*N^7*t^4`, and the bound `483*(N*t)^9`. The public theorems expose only
existential constants. Making the numerical statement a checked public theorem
would currently require replaying roughly 208 source lines including two private
helper chains; that optional refactor was not added here. The checked theorem
retains its rigorous existential universal constant C.

## Lean files and exact scope

- `BernoulliProductCertificate.lean` retains the actual integer produced by
  the existing nonzero integral Bernoulli product.
- `BernoulliLengthCertificate.lean` proves character count≤N and chooses a
  conductor-only integer before all eligible length families.
- `BernoulliTwistCertificate.lean` forms the across-twist product, with the
  exact bound `3*N*t²*log(t*N)`. Its comparison hypothesis is explicit.
- `OddMinusCertificate.lean` supplies that comparison from the archive's
  actual `atPrime` and `actEx` theorems.
- `FactorialSmallPrimeCertificate.lean` constructs the factorial certificate,
  proves the coarse pointwise bound, and proves degree≤conductor.
- `AllOddMinusCertificate.lean` combines the two actual certificates. Its
  arithmetic inputs are `PsiBound` and `StickBound C`.
- `AllOddMinusCertificateClosed.lean` supplies both inputs from existing
  archive proofs of Poitou–Tate duality, unramified orthogonality and
  Stickelberger estimates. Its final theorem has **no unproved arithmetic,
  height or family-connection premise**. The conclusion concerns odd-minus
  lengths, not all of `shaLen` or RH.
- `OddMinusBudgetBound.lean` proves the degree-nine polynomial envelope.
- `OddMinusVVle.lean` derives the actual `VVminusLe` finite-prime-sum interface
  from the integer certificate, retaining every finiteness condition.
- `PolynomialAbsorption.lean` absorbs the fixed polynomial error into a larger
  height exponent, chosen before the scale and host parameters.
- `JointWindowWithoutMinus.lean` proves `JointWin Ct → VWinAt ψ Ct` for Ct≥1,
  and hence `JointWin 401 → VWin`, with no separate `ThmBc` premise. It retains
  the exact original window quantifier order and final target.

## A simplified consumer

The original `vwinAt_of_joint` takes both `JointWin Ct` and `ThmBc Ct`. The new
consumer derives the odd-minus estimate from the constructed certificates and
absorbs its polynomial error in the existing height term by increasing its
fixed exponent. It then uses the original numerical window absorption theorem.
The extra exponent is selected before X,q,d,Y and all the inner points x.

This removes a separate arithmetic hypothesis from the closing interface.
It does **not** discharge `JointWin`: its height estimate and dyadic/window
inputs remain necessary. The old entry point and Main are not replaced by
these research files.

## Checks

The exact 34-module Bernoulli support plus the three certificate modules passed
Principia's hosted check `f1cab776f56826d1c1e72d99d0bd8dec`, with zero placeholders
and all six printed axiom inventories equal to the three permitted axioms
`propext`, `Classical.choice`, `Quot.sound`. The 81,536-character snippet has SHA256
`5ea0055aa37939f2dd09894e561461db9344a4ebcdabc4747d52c336d5bd15e7`.
The bundle, server response and per-source hashes are in `bernoulli-universal-*`.

The actual archive adapters, the closed odd-minus theorem, the polynomial
envelope and both simplified consumer endpoints have compiled
successfully in the pinned Lean 4.33.1 / Mathlib environment using the selected
original-project cache. Their printed axiom inventories contain only the same
three axioms. The matrix agent records exact compiler commands and source
hashes in `../matrix/checks/`. Separate dependency-kernel replay is being
performed there; compilation of the new declarations is not presented as a
fresh source rebuild of every cached dependency or a full Comparator run.

The closed odd-minus endpoint has additionally passed fresh replay of all
133,455 required declarations into an empty Lean kernel environment. The replay
accepted only `Classical.choice`, `Quot.sound`, and `propext`; see
`../matrix/replay-odd-closed.log`. This checks imported proof terms independently
of trusting the compiled-module cache. Replay of the simplified window consumer
is recorded separately by the matrix agent.

`actual-check-manifest.json` binds eight native module checks to the SHA256 of
each source file. The three Bernoulli modules are separately bound by the
hosted check and its complete source manifest.

The pointwise height bound needed for the odd-plus component remains a separate
problem. No completed full Selmer certificate or million-line deletion is
claimed by these results alone.
