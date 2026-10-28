# 3141: Indexed finite-prime certificate boundary

Date: 2026-10-28

## Result

The legacy `FixedLambdaFinitePrimeArithmeticCertificate` remains unchanged and
still has the known empty-type obstruction: its `atomsWithSourceTest` field
requires arithmetic data at every natural number, including `n = 1`, while the
field proves `IsPrimePow n`.

This record adds the non-breaking indexed boundary
`FixedLambdaFinitePrimeIndexedArithmeticCertificate` in
`ConnesWeilRH/Source/CCM25Concrete/FinitePrimeCertificate.lean`.

The new boundary retains the existing arithmetic support skeleton and exposes
only two finite-index read-offs:

- `globalArithmeticData` on `W.globalPrimeIndexSet`;
- `restrictedArithmeticData` on `W.restrictedPrimeIndexSet lambda`.

Both read-offs obtain data from the support skeleton's source-visible
arithmetic data. They do not construct data for non-indexed natural numbers,
and they do not alter the legacy consumers.

## Verification

Command:

```text
lake build ConnesWeilRH.Route.RouteTheorem
```

Environment: Linux ext4 verification copy, Lean 4.30.0.

Result: `Build completed successfully (2969 jobs).`

The result is a type-boundary repair only. It does not provide the missing
common finite-prime source root, does not close the Route A producer, and does
not prove `SourceRH` or RH.
