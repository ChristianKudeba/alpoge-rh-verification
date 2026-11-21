# FixPiIff statement and proof compaction check

The final check validates the actual 33-line source snapshot `FixPiIffActual.lean`, SHA256 `02ee771e754045d82860f3e2ec66928113661e9ff22647470fce9c2ffef1f235`. This matches the source file after all checks. The earlier PR44-only 36-line trial remains in `FixPiIffCandidate.lean` with logs named `fixpi-*`; final logs and results are named `fixpi-actual-*`.

Lean 4.33.1 compiled the complete replacement theorem against the pinned project and Mathlib imports. Its public theorem `UpperTheory.Reformulated.B.Gr34.mem_UC` has exactly the original compiled kernel type expression; the comparison reads the original immutable archive's constant directly without importing its obsolete proof. Both universe parameter lists match. The type expression representation SHA256 is `09074c3bd0fb7a4b462d759e7184b1070a9b0b34f04b2971fcff29aefed5be9c`.

The final theorem and all transitive proof/type dependencies were then replayed into an empty Lean kernel environment: 38790 declarations passed. Its only axioms are `propext`, `Classical.choice`, and `Quot.sound`. The replay verifier source has SHA256 `c7d342991c8f8e7a722359269049bc930ef47adae876a1907104fa764847d939` and is the same verifier previously exercised with successful positive and rejected corrupted-proof controls.

The archived import closure comprises 1,780 project modules. Restoring 43 missing module archives required 2,544,810 compressed bytes, each checked against the pinned manifest digest. Cache identity checking alone does not validate proof terms; the separate empty-kernel replay supplies that check for this target's actual dependencies.

To repeat with the recorded local toolchain and cache paths:

```sh
python3 verification/research/nov21-compaction/verification/restore-fixpi-cache.py
python3 verification/research/nov21-compaction/verification/validate-fixpi-actual.py
```

The helper proof now uses Mathlib's stabilizer and subgroup lattice lemmas. Most of the 8,029-to-33 line reduction removes an explicitly expanded theorem type; it is not a comparable reduction in the mathematical argument. This is a targeted theorem check, not a full Main or Comparator verdict.
