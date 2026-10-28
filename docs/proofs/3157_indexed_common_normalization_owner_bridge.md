# 3157: Indexed common arithmetic owner bridge

Date: 2026-10-28

The existing `IndexedCommonFinitePrimeArithmeticSourceData` already contains the
indexed support skeleton for every test pair and every `lambda`. Its support
certificate derives both global and restricted index coverage.

The remaining normalization fact does not need another owner field. For a
`SourceWeilFormData`, the finite-prime term identity is already an unconditional
read-off from `SourceFinitePrimeData.finitePrimeTerm_convolutionStar`.

Added in `ConnesWeilRH/Source/AnalyticSourceModel.lean`:

- `SourceWeilFormData.finite_prime_term_normalization_statement_of_source_data`
- `SourceWeilFormData.finitePrimeDominance_of_indexed_common_arithmetic_source_data`

The second bridge consumes the existing indexed common arithmetic owner,
derives restricted coverage from each indexed support certificate, derives term
normalization from the source evaluation data, and then proves
`finitePrimeDominance`. No legacy all-natural-number arithmetic certificate is
used by this bridge.

This is still a consumer bridge, not a construction of the normalized indexed
owner. The normalized project root remains incomplete; no SourceRH or RH claim
follows.

Verification:

```text
lake build ConnesWeilRH.Route.RouteTheorem
```

Result: successful, 2969 jobs. The new dominance bridge was audited with
`#print axioms` and depends only on `[propext, Classical.choice, Quot.sound]`.