# 3152: Indexed object theorem-base constructor

Date: 2026-10-28

Added `IndexedSourceObjectTheoremBaseConstructorInput` and its
`toPackage` conversion in `ConnesWeilRH/Source/ObjectTheoremBasePackage.lean`.

This constructor derives the package's `ccm25Model` from
`IndexedCCM25SourceArithmeticConstructorInput.toIndexedCCM25SourceModel`, so
the indexed finite-prime provenance reaches the theorem-base package without
changing the established `SourceObjectTheoremBasePackage` shape or its legacy
constructor. The dependent S2-B1 input is indexed against the derived model's
Weil symbols, and the read-back theorem checks the package projection.

This is still a constructor migration boundary. It does not replace the
normalized root, remove legacy consumers, establish `SourceRH`, or prove RH.

Verification:

```text
lake build ConnesWeilRH.Route.RouteTheorem
```

Result: `Build completed successfully (2969 jobs)` in the Linux ext4
verification copy.

