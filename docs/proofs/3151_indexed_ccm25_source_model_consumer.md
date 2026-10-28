# 3151: Indexed CCM25 source-model consumer

Date: 2026-10-28

Added indexed row projections in
`ConnesWeilRH/Source/CCM25Concrete/Rows.lean` and the parallel constructor
`ccm25_source_model_of_indexed_arithmetic_rows` in
`ConnesWeilRH/Source/CCM25SourceModel.lean`.

`IndexedCCM25SourceArithmeticConstructorInput` now exposes
`toIndexedCCM25SourceModel` and a read-back theorem showing that the resulting
model preserves the original `WeilFormSymbols`. The indexed source-model
consumer obtains finite-prime normalization only through
`finite_prime_normalization_of_indexed_arithmetic_rows`; it does not convert
indexed certificates into the legacy all-natural-number certificate.

The legacy source-model constructor remains unchanged. The normalized root,
`ObjectTheoremBasePackage`, `SourceRH`, and RH are not migrated or proved by
this record.

Verification:

```text
lake build ConnesWeilRH.Route.RouteTheorem
```

Result: `Build completed successfully (2969 jobs)` in the Linux ext4
verification copy.

