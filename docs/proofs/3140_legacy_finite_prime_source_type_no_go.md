# Record 3140: legacy finite-prime source type is empty

Date: 2026-10-28.

Status: Lean-verified structural no-go. This record does not claim SourceRH
or RH.

## Finding

The legacy certificate data still stores
`SourceFinitePrimeArithmeticNormalizationForSourceTest`, whose `atIndex` is
total over all natural numbers. At `n = 1`, its payload contains
`IsPrimePow 1`, which is false. Therefore the following types are empty for
every owner and source test:

```text
FixedLambdaArithmeticCertificateSourceTestData
    -> SourceFinitePrimeArithmeticData
    -> CommonFinitePrimeArithmeticSourceData
```

The formal chain is exposed in
`ConnesWeilRH/Source/CCM25Concrete/FinitePrimeSourceData.lean`:

```text
not_fixedLambdaArithmeticCertificateSourceTestData
not_finitePrimeArithmeticSourceData
not_commonFinitePrimeArithmeticSourceData
```

The first theorem applies the stored atom normalization at `n = 1` and
contradicts `not_isPrimePow_one`. The second specializes any finite-prime
source-data certificate at `lambda = 2`; the third projects the contradiction
through the `finitePrimeData` field.

## Consequence

The `normalizedCoreCCM25FinitePrimeArithmeticSourceDataRoot` axiom is not a
missing numerical certificate under the current type. It inhabits an empty
type. The additive index-set adapters added earlier do not repair this because
the legacy total `atoms` field remains upstream.

The sound next implementation is a genuine retyping of certificate atoms to
the finite global/restricted index set, followed by migration of all consumers
and a fresh axiom audit. Do not replace this root with `Classical.choice` or a
stored artifact.

## Verification

WSL2 ext4 build:

```text
lake build ConnesWeilRH.Route.RouteTheorem
Build completed successfully (2969 jobs).
```

All three no-go theorems audit to exactly
`[propext, Classical.choice, Quot.sound]`; no `sorryAx` is present.
