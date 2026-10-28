# 3142: Indexed source-data owner boundary

Date: 2026-10-28

## Result

The indexed finite-prime boundary is now exposed above the certificate layer.

`FinitePrimeInterface.lean` adds
`FixedLambdaIndexedArithmeticSourceTestCertificatesForTest` and
`FixedLambdaIndexedArithmeticSourceTestCertificatesForAllTests`. Their
fixed-lambda payload is
`FixedLambdaFinitePrimeIndexedArithmeticCertificate`, so no field asks for
arithmetic data at every natural number.

`FinitePrimeSourceData.lean` adds
`IndexedFinitePrimeArithmeticSourceData`, carrying the source-test selector,
indexed fixed-lambda certificates, and the certificate/source-test read-off.
The legacy source-data owner remains unchanged while consumers migrate.

## Verification

Command:

```text
lake build ConnesWeilRH.Route.RouteTheorem
```

Environment: Linux ext4 verification copy, Lean 4.30.0.

Result: `Build completed successfully (2969 jobs).`

This is an additive migration boundary. The normalized common source root is
still legacy and axiom-backed; no `SourceRH` or RH claim follows from this
record.