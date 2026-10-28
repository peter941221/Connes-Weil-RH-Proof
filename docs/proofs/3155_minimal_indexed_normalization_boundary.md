# 3155: Minimal indexed normalization boundary

Date: 2026-10-28

The previous indexed arithmetic certificate family retained the full support
skeleton, including reverse `globalIndexData` and `restrictedIndexData` for
every member of the fixed index sets. That is stronger than the actual
`FinitePrimeVisibilityStatement` consumer and can require arbitrary
`(f,g)`-pair visibility that is not needed for normalization.

Added `IndexedFinitePrimeNormalizationCertificatesForTest` and its all-tests
family in `ConnesWeilRH/Source/CCM25Concrete/FinitePrimeInterface.lean`.
It carries exactly:

```text
global index coverage
restricted index coverage for lambda > 1
finite-prime term normalization
```

Added the following bridges in
`ConnesWeilRH/Source/AnalyticSourceModel.lean`:

- `finitePrimeDominance_of_indexed_normalization_certificates`
- `indexedNormalizationCertificates_of_dominance`

The first bridge proves source prime-support dominance from the minimal
global coverage row plus the existing per-common reverse support. The second
shows that, once dominance is supplied, the source model's own normalization
theorem constructs the minimal indexed certificate family.

This does not prove dominance for the normalized concrete root. It isolates
that remaining obligation without retaining the legacy impossible
all-natural-number atom certificate or the stronger reverse-support burden.

Verification:

```text
lake build ConnesWeilRH.Route.RouteTheorem
```

Result: `Build completed successfully (2969 jobs)` after forcing the changed
analytic source-model module to rebuild. The new bridges report only
`[propext, Classical.choice, Quot.sound]`.

