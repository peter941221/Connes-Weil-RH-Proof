# 3158: legacy finite-prime root inconsistency audit

Date: 2026-10-28.

Status: Lean-verified audit. This record does not claim SourceRH or RH.

## Finding

The existing `normalizedCoreCCM25FinitePrimeArithmeticSourceDataRoot` has type
`CommonFinitePrimeArithmeticSourceData W`. That legacy type contains a total
atom-normalization field. At index `n = 1`, the field requires `IsPrimePow 1`,
which is false.

The source layer proves the emptiness chain:

```text
not_isPrimePow_one
  -> not_fixedLambdaArithmeticCertificateSourceTestData
  -> not_finitePrimeArithmeticSourceData
  -> not_commonFinitePrimeArithmeticSourceData
```

The development skeleton now exposes the direct consequence as
`normalizedCoreCCM25FinitePrimeArithmeticSourceDataRoot_is_inconsistent`.
Therefore the current root axiom implies `False`; it is not a legitimate
producer certificate and must not be used as evidence for RH.

## Consequence

The indexed boundary is required for sound migration. A legacy-to-indexed
projection can preserve the existing axiom but cannot repair it. The next
valid producer must construct `IndexedCommonFinitePrimeArithmeticSourceData`
directly, with arithmetic data only on the finite global/restricted index sets.

## Verification

Expected command:

```text
lake build ConnesWeilRH.Route.RouteTheorem
```

The new audit theorem is intentionally dependent on the named legacy root
axiom; it is a diagnostic of the current skeleton, not an axiom-clean proof.