# Reading the literal proof-term edition

Start with the record for `riemannHypothesis` in the completed edition's target index. The theorem record specifies two expression numbers. The type is the statement it proves. The value is its proof. A constant inside that value refers to a previously declared theorem or definition by name and universe arguments. Expression numbers and record numbers use different sequences. A volume boundary leaves their meaning unchanged.

## A worked example from the solution export

[Records 2–60 in the sample](sample/kernel-00001.tex) give the equality type, its constructor and its elimination rule. The name numbered 1 is `Eq`, the name numbered 9 is `Eq.refl`, and the name numbered 10 is `Eq.rec`. Read the exact equations for expressions 0–12 as follows.

| Expression | Meaning in its surrounding context |
|---|---|
| E₀, E₃ | The sort at universe parameter U₁, and the sort of propositions. |
| E₁, E₂ | The most recently bound variable and the one immediately outside it. |
| E₄–E₆ | Bind a type α and two elements of α. The result has type Prop. Thus equality has the signature (α : Sort u) → α → α → Prop, with the α argument implicit. |
| E₇–E₁₀ | In the context (α, a), apply equality first to α, then to a, then to a again. The resulting proposition is a = a. |
| E₁₁, E₁₂ | Bind a and α around this proposition to obtain the type of reflexivity. |

Record 60 groups the type, constructor and recursor. The recursor takes a family of conclusions depending on an endpoint b and an equality proof e : a = b. A proof at (a, refl) gives a proof at (b, e). Its computation rule on the reflexivity constructor uses expression 41. Thus even the basic inference of substitution in equality has an explicit rule in the edition. The original short identifier is a convenience. The numbered expression is the full definition.

## Following a theorem value

Read a dependent product ∏(x : A) B as the type of functions taking a term a of A to a term of B with a substituted for x. For propositional B this is universal quantification. Read a lambda with that same binder as a function or proof depending on x. Application removes the binder by substitution. An open expression reused under two different binders is interpreted in the context of each use. This matters in particular for E₁ and E₂ above.

A named theorem can be used by applying its value's declared type at the given arguments. To audit that theorem, follow its own value reference. A declaration classified as an axiom has no proof value. Inductive declarations carry constructors, recursors and their constructor reduction rules. The export's quotient primitives have their own computation rules. Checking these on a machine is a different operation from rendering their mathematical notation. [Lean's reference on equality](https://lean-lang.org/doc/reference/latest/Basic-Propositions/Propositional-Equality/) · [Quotients](https://lean-lang.org/doc/reference/latest/The-Type-System/Quotients/) · [Format specification](https://github.com/leanprover/lean4export/blob/v4.33.0/format_ndjson.md)

The sample ends at record 105. The RH theorem occurs later in the solution export. Only a release manifest covering the entire solution and all five target declarations establishes that the literal edition has reached the theorem. [Independent audit and published checksums](https://math.mit.edu/~drew/grh/)
