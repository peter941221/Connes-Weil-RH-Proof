# 3157: Indexed common normalization owner bridge

Date: 2026-10-28

The existing `IndexedCommonFinitePrimeArithmeticSourceData` contains an
indexed support skeleton, but it does not contain the two rows required by the
minimal normalization boundary: arbitrary-pair restricted-index coverage and
arbitrary-pair finite-prime term normalization.

Added `IndexedCommonFinitePrimeNormalizationSourceData` in
`ConnesWeilRH/Source/CCM25Concrete/FinitePrimeSourceData.lean`. It preserves the
indexed support selector and adds exactly these missing rows, together with the
existing scoped archimedean balance row.

Added the constructor
`fixedLambdaIndexedArithmeticSourceTestCertificatesForAllTests`, which converts
this owner into the indexed source-test certificate family consumed by the
minimal interface.

Added
`SourceWeilFormData.finitePrimeDominance_of_indexed_common_normalization_data`
in `ConnesWeilRH/Source/AnalyticSourceModel.lean`. Therefore a genuinely
constructed indexed normalization owner now discharges `finitePrimeDominance`
without using the legacy all-natural-number arithmetic certificate.

This is a consumer bridge, not a root construction. The normalized project root
still lacks a real `IndexedCommonFinitePrimeNormalizationSourceData` instance;
no SourceRH or RH claim follows.

Verification:

```text
lake build ConnesWeilRH.Route.RouteTheorem
```

Result: successful, 2969 jobs. The new dominance bridge was audited with
`#print axioms` and depends only on `[propext, Classical.choice, Quot.sound]`.