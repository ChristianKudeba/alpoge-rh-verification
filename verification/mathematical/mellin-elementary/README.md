# Mellin logarithmic moment by differentiation

The exact public statement of `Formalism.mellinElem_part4` is preserved:

`Re(s) > 1` implies `∫₁∞ (x log x) x^(-s-1) dx = 1/(s-1)^2`.

The original proof explicitly constructs an antiderivative, proves its integrability, establishes its limit at infinity, and applies the improper-integral fundamental theorem. The replacement instead specializes the existing elementary Mellin identity (`mellinElem_part3`) to exponent 1 and differentiates it with the already proved `mellinDeriv`. The derivative of the integrand introduces `-log x`; uniqueness of derivatives then gives the claimed identity. This is a mathematical proof substitution, not an import-only change.

The only source change is `src/Formalism/ZetaNonvanishing/MellinElem.lean`. It now imports `MellinDeriv`, which itself imports precisely the file formerly imported by `MellinElem`; there is no new dependency cycle. All public declarations and statements remain unchanged. File length decreases from 139 to 85 physical lines (54 fewer). No unreferenced source files were deleted.

Hosted check `ba0e3945350d3ed91fa5f6338421d052` checked the complete old and new file bodies together with the unchanged proof of `mellinDeriv`, after flattening imports and including their exact proposition definitions. It also checked proof equality for the old/new `mellinElem_part4` and old/new aggregate `mellinElem`; because those expressions have identical types, proof irrelevance applies. The check passed with zero sorry. Axiom inventories for the new theorem, aggregate, and original theorem contain only `propext`, `Classical.choice`, and `Quot.sound`.

The first draft check `baedc13208cfac2107acda9505b7019a` failed on two elaboration details (explicit typing of a set-membership inequality and reduction of `id s`). Those were corrected before the successful check. No claims rely on that failed draft.

This hosted scratch check validates this mathematical replacement and the included dependencies. It is not the full five-target Comparator run and does not establish a verdict on the complete RH development. The original Lean and Mathlib pins were not changed. The shared scratch lock was acquired with successful `mkdir`, held through each check's final verdict, and released after the successful check.
