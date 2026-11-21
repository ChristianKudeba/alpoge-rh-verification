# Isotypic representation proof validation

The final source snapshot is `IsoSepActual.lean`, SHA256 `48137a89210acb1fea033a672334c7d6d24b56b463be1e66f1f082d68298c689`, matching the actual source after validation. It has 16 lines, compared with 139 lines in `IsoSep.before.lean`. Both were compiled with Lean 4.33.1 and the pinned Mathlib.

The public theorem `GlobalTheory.IsoSep.main` has exactly the original compiled kernel type expression, including the retained isotypy hypothesis. The kernel type expression representation SHA256 is `cc3b0e2434b14ddd1798df607a49ae77a579c7c3cd369326026013ebc1354b21`. The comparison reads the two independently compiled constant records directly.

The replacement imports `Lemmata.IsotypicGeneration`, whose source snapshot SHA256 is `34bc182c864fac8d33d916be00244ad14dc584091119d8a509aa07d277657667`. This matches the successful helper compilation receipt in `fixed-vectors/IsotypicGeneration.json`. The replacement uses the generic `intertwiner` theorem, which obtains separating maps from the semisimple/isotypic module structure instead of constructing and projecting onto an irreducible subrepresentation manually.

Native compilation passed with only `propext`, `Classical.choice`, and `Quot.sound`. The new theorem's full transitive proof/type closure was then replayed into an empty Lean kernel environment: 12291 declarations passed with exactly those three axioms. The replay verifier SHA256 is `c7d342991c8f8e7a722359269049bc930ef47adae876a1907104fa764847d939`, matching the previously positive-tested and corruption-tested verifier.

The final native check, exact type comparison and kernel replay took 3.67, 0.77, and 13.72 seconds, respectively. `validation-summary.json` binds the source, helper, compiled modules and type fingerprint to the recorded checks.

To repeat after the generic helper has been compiled in `fixed-vectors/output`, run:

```sh
python3 verification/research/nov21-compaction/isotypic/validate-isotypic.py
```

The original backup compilation and the first rejected attempt using abbreviated dot notation are retained separately. This is a targeted theorem verification, not a full Main or Comparator verdict.
