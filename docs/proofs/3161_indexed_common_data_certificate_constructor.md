# 3161: indexed common-data certificate constructor

Date: 2026-10-29.

Status: Lean-verified source API extraction. This record does not construct an
indexed common-data producer, replace the legacy root, or claim SourceRH/RH.

## Change

`ConnesWeilRH/Source/AnalyticSourceModel.lean` now names the construction that
was previously duplicated inside the finite-prime dominance theorem:

```text
IndexedCommonFinitePrimeArithmeticSourceData
        |
        +-- indexed source-test certificates for every (f, g)
        |
        +-- SourceWeilFormData term-normalization readback
        v
FixedLambdaIndexedArithmeticSourceTestCertificatesForAllTests
        |
        v
IndexedCCM25SourceArithmeticConstructorInput
```

Added definitions:

- `SourceWeilFormData.indexedSourceTestCertificates_of_indexed_common_arithmetic_source_data`
- `SourceWeilFormData.toIndexedCCM25SourceArithmeticConstructorInput_of_indexed_common_arithmetic_source_data`

The restricted coverage row is read from each indexed support certificate.
The finite-prime term normalization row is read from the actual source
evaluation data, not stored as a new axiom or copied from the legacy root.

## Boundary

This is a real consumer/constructor bridge, not the missing producer. The
remaining producer obligation is now isolated as construction of one
`IndexedCommonFinitePrimeArithmeticSourceData` for the selected source model,
including its arbitrary-pair indexed certificate data and scoped archimedean
balance.

## Verification

```text
lake build ConnesWeilRH.Source.AnalyticSourceModel
lake build ConnesWeilRH.Route.RouteTheorem
lake env lean ConnesWeilRH/Dev/IndexedProducerApiAudit3161.lean
```

Both builds completed successfully: 2943 jobs for the source module and 2969
jobs for the route target. The two new definitions audit to exactly
`[propext, Classical.choice, Quot.sound]`.
