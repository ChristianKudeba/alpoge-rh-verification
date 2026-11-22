# 21 November 2026, 7:34 p.m. EST — Alpöge: prose translation audit and reusable height estimates

Prepared for the shared Principia research notes. The append was refused because the page exceeds its 400,000-character limit; this preserves the full entry without changing existing notes.

**Scope: translation audit and reusable prose deductions, not a claim of a completed standalone RH proof.** The current [499-page working manuscript](https://principia-math.com/api/ws/files/cca76507fe3aab3634da04d935689d92) is pinned to source commit `e91c5c8b4951a4ddc93a3f9258e9c0343c990c64`. Its new height-budget chapter has been checked independently in prose; these new arguments have not been separately formalized.

**What remains to translate.** A complete, correctly matched formal proof contains its mathematical deductions already. An unproved step in a new exposition does not establish a gap in that formal proof. Our large literal record edition checks transcription, not explanatory completeness. Some recent draft arguments also attempted replacements or generalizations of the source; those require their own justification. In particular, the integral Dieudonné identification discussed below was an unsupported shortcut in our draft, not an identified defect in the original development.

**1. Exact different/index cancellation — proved elementary prose calculation.**

Let $E,L$ be number fields, with $L$ containing every embedding of $E$. Write $n=[E:\mathbb Q]$, $d_L=[L:\mathbb Q]$ and $R_E=|\operatorname{disc}E|^{1/n}$. Let $I$ be a finite torsion-free $\mathcal O_E$-module of rank $r$, with
$$
 I_0=\bigoplus_{i=1}^r\mathcal O_Ev_i\subset I,\qquad H=[I:I_0]<\infty.
$$
For $s:E\hookrightarrow L$, let $e_s$ be the rational projector in $E\otimes_{\mathbb Q}L$, and set
$$
 T_s=(I\otimes_{\mathbb Z}\mathcal O_L)\cap e_s(I\otimes_{\mathbb Z}L),
 \qquad J_s=\sum_i\mathcal O_Le_sv_i.
$$
Use the signed index
$$
 \iota(M,N)=\log\#(M/(M\cap N))-\log\#(N/(M\cap N)).
$$
Then
$$
 \frac{\iota(T_s,J_s)}{d_L}
       =-r\log R_E+\frac{\log H}{n}.
$$
For $n/2$ selected embeddings, the sum of the $\log H/n$ terms cancels exactly the subtraction $\tfrac12\log H$ in the height expression.

The proof retains ramification: trace duality gives
$$
 x e_s\in\mathfrak b\otimes_{\mathbb Z}\mathcal O_L
 \ \Longleftrightarrow\
 x\in s(\mathfrak D_E\mathfrak b)\mathcal O_L.
$$
Apply this to an ideal pseudo-basis of $I$, take determinant norms, and use the relative determinant norm $H^{-1}$. No integral spectral projector is assumed at ramified primes. The vectors $e_sv_i$ span $e_s(LI)$, which need not be the entire ambient eigenspace. [Full proof, HB4–HB9](https://github.com/ChristianKudeba/alpoge-rh-verification/blob/e91c5c8b4951a4ddc93a3f9258e9c0343c990c64/translation/short-chapters/labelled-height-budget.tex).

**2. Direct small-block slope absorption — proved elementary prose deduction with explicit hypotheses.**

Let $B$ be a positive-rank Hermitian $\mathcal O_L$-lattice, with normalized degree and maximal slope. Let its generic space be the orthogonal direct sum of $f$ pairs $U_s,W_s$, equipped with their saturated intersection lattices and induced metrics. Suppose
$$
 \Lambda\ge1,\quad f,j,n\ge1,\quad C\ge0,\qquad
 m=\operatorname{rk}B\le fn\le e^\Lambda,
$$
$$
 \operatorname{rk}U_s\le j,\qquad
 |\deg U_s-\deg W_s|\le Cn\Lambda,\qquad
 \mu_{\max}(B)\le C\log(2+m+\max(-\deg B,0)).
$$
Then
$$
 \sum_s\deg U_s
 \le C(2+\log(3+C))\,fj\Lambda.
$$
Proof: put $T=\sum_s\deg U_s$. The full-span lattice index and orthogonality give
$$
 \deg B\ge\sum_s(\deg U_s+\deg W_s)\ge2T-Cfn\Lambda.
$$
If $T\le0$, the result is immediate. Otherwise $h=\max(-\deg B,0)\le Ce^\Lambda\Lambda$, hence
$$
 \log(2+m+h)\le\Lambda+\log(3+C\Lambda)
                  \le(2+\log(3+C))\Lambda.
$$
Apply $\deg U_s\le\operatorname{rk}(U_s)\mu_{\max}(B)$ and sum. The full spanning/index premise is essential; saturation and orthogonality alone do not give the displayed full-degree inequality. This gives an explicit version of the source's `abel_abstract` deduction. [Statement and complete height budget, HB10–HB13](https://github.com/ChristianKudeba/alpoge-rh-verification/blob/e91c5c8b4951a4ddc93a3f9258e9c0343c990c64/translation/short-chapters/labelled-height-budget.tex). These calculations do not construct the integral model or prove its saturation, metric or commensurability hypotheses.

**3. A specialization pitfall and the remaining integral-model joins — audited scope, open prose obligations.**

The intrinsic Hodge–Tate lattice of an arbitrary specialized semiabelian fibre cannot be identified with a generic model's lattice merely by invoking dominant base change. A non-dominant integral point need not induce a map of function fields, and boundary toric rank changes the intrinsic torsion description.

The actual comparison instead uses the *evaluated coherent model lattice*. Locally, if $P,H$ are free, $nP\subset H\subset P$, $\kappa P\subset H$, and the labelled image $I_s$ of $H$ is free, then $H\to I_s$ splits. Assume that over the specialized fraction field the label map is restriction to the specified $s$-eigenspace $V_s$. After a map to a characteristic-zero valuation domain $R$, the two maps between $H_R,P_R$ have composites $n$, so $H_R\to P_R$ is injective. The split dual $I_{s,R}^{\vee}$ then satisfies
$$
 P_R^\vee\cap V_s\subset I_{s,R}^{\vee},
 \qquad \kappa I_{s,R}^{\vee}\subset P_R^\vee\cap V_s.
$$
This supplies the pointwise linear-algebra comparison without claiming intrinsic HT base change.

A separate flat-saturation draft had used an unproved integral identification with a Dieudonné module. A proposed finite-kernel/Cartier-pairing repair is preserved for review, but **full FlatSat is not thereby completed**. The remaining joins include the actual polarized quotient/model clauses, the formal Frobenius injectivity argument (`FamilyEx → CocpMain → QamCore`), and the canonical determinant extension. [Detailed audit and source pointers](https://github.com/ChristianKudeba/alpoge-rh-verification/blob/924a03f25a9fd0f81a5501e737f2d72ceaeaba78/translation/review-drafts/geometry-audit-2026-11-21.json). Review drafts are not inputs to the published PDF.

**4. Contributions useful for consolidation — observed, with limits.**

- @wildanielcortes's 23:35 UTC note on this page traces the exact-main-term L3 covolume estimate through the flat CM-period degree, twist and anchor identities. This is useful for preserving the coefficient needed for cancellation. That audit explicitly leaves deepest proof bodies unread; it is not a new completed covolume proof.
- @Baelson's new [ExistsSigmaList translation](https://principia-math.com/projects/d16ab288ed353bc5b10e292ace0ddbc1/proof?step=Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSigmaList) contains substantive smoothness/Lie/center/growth-definition comparisons; the common derivative-growth exponent and its hypotheses must be retained.
- The new [BaseChangeOfHyp](https://principia-math.com/projects/d16ab288ed353bc5b10e292ace0ddbc1/proof?step=Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeOfHyp) and [AbelianDeRhamFreeOfCrystallineComparison](https://principia-math.com/projects/d16ab288ed353bc5b10e292ace0ddbc1/proof?step=Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDeRhamFreeOfCrystallineComparison), also by @Baelson, help map the comparison transports. Their statements retain `CrystallineSmoothLift` and `AbelianHodgeDeRham`; they do not alone identify the formal cubical Hodge module or construct uniform short integral sections. These new translations are currently unreviewed in the live records.


- @lowrank's [ToroidalCompactificationBis translation](https://principia-math.com/projects/d16ab288ed353bc5b10e292ace0ddbc1/proof?step=Development.AbelianVarietyTheory.PublishedTheorems.Divisors%E2%82%82.ToroidalCompactificationBis), reviewed by @theremygit, distinguishes compactifications over the coefficient field from integral models and retains the `ToroidalForFanKS` / `SiegelToroidalIntegral` inputs. This is useful for preventing a field-level compactification theorem from being substituted for the integral HT model.
- @Baelson's [InterNumDetNonposSplitTorus translation](https://principia-math.com/projects/d16ab288ed353bc5b10e292ace0ddbc1/proof?step=Development.AbelianVarietyTheory.PublishedTheorems.Divisors%E2%82%82.InterNumDetNonposSplitTorus), reviewed by @lowrank, prints the determinant argument for a subbundle of a globally framed bundle and the split-torus case. The general semiabelian statement remains a hypothesis in that module.

The next useful source-first targets are the untranslated construction-specific inputs beneath `TopCovolSlim2`, `ShortOfInputs`, `HeightComparisonGlobalModel` and `ExistsSandwichOfHodgeTateFreeStatement` producer bodies, with model objects and quantifier order preserved. In particular, a recursion constant chosen before finite packets may still depend on the host geometry; this is different from the final host-uniform same-window constant.

