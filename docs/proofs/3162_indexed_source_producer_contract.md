# 3162: indexed source producer contract

Date: 2026-10-29.

Status: Lean-verified minimal producer contract. This record does not
construct a producer instance, replace the legacy root, or claim SourceRH/RH.

## Direction correction

The per-common support object cannot supply arbitrary `(f,g)` coverage. Record
3156 gives an axiom-clean countermodel for that shortcut. The source layer now
states the missing producer input directly through
`SourceWeilFormData.IndexedFinitePrimeProducer`.

Its independent fields are:

```text
source Weil-form data
    + arbitrary source-test selector
    + support skeleton for every (f, g, lambda > 1)
    + support/source-test readback
    + common-pair source-test readback
    + scoped archimedean balance
    -> IndexedCommonFinitePrimeArithmeticSourceData
```

The producer contract automatically derives:

- indexed source-test certificates for every test pair;
- restricted-index coverage from each support skeleton;
- finite-prime term normalization from source evaluation data;
- indexed common source data through the existing constructor.

## Change

Added to `ConnesWeilRH/Source/AnalyticSourceModel.lean`:

- `SourceWeilFormData.IndexedFinitePrimeProducer`
- `SourceWeilFormData.IndexedFinitePrimeProducer.indexedSourceTestCertificates`
- `SourceWeilFormData.IndexedFinitePrimeProducer.toIndexedCommonFinitePrimeArithmeticSourceData`

## Boundary

The remaining mathematical task is now to construct one instance for the
selected source model. No existing per-common support object may be promoted to
that instance without an arbitrary-pair support theorem.

## Verification

```text
lake build ConnesWeilRH.Source.AnalyticSourceModel
lake build ConnesWeilRH.Route.RouteTheorem
lake env lean ConnesWeilRH/Dev/IndexedProducerApiAudit3161.lean
```

Results: 2943 source jobs, 2969 route jobs, and all four new definitions audit
to exactly `[propext, Classical.choice, Quot.sound]`.
