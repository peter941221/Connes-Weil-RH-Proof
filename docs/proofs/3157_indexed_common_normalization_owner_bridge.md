# 3157: Indexed common normalization owner bridge

Date: 2026-10-28

The existing `IndexedCommonFinitePrimeArithmeticSourceData` contains an
indexed support skeleton. Its support certificate already derives arbitrary-pair
restricted-index coverage; the remaining row required by the minimal
normalization boundary is arbitrary-pair finite-prime term normalization.

Added `IndexedCommonFinitePrimeNormalizationSourceData` in
`ConnesWeilRH/Source/CCM25Concrete/FinitePrimeSourceData.lean`. It preserves the
indexed support selector and adds the remaining term-normalization row, together
with the existing scoped archimedean balance row. Restricted coverage is
derived directly from each indexed support skeleton.

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
