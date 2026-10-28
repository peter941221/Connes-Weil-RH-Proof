# 3143: Indexed source-data constructor

Date: 2026-10-28

Added `indexedFinitePrimeArithmeticSourceDataOfSourceTestCertificates` in
`ConnesWeilRH/Source/CCM25Concrete/FinitePrimeSourceData.lean`.

The constructor assembles the new indexed source-data owner directly from
`FixedLambdaIndexedArithmeticSourceTestCertificatesForAllTests`, preserving the
selector/source-test read-off and avoiding the legacy all-natural-number atom
normalization.

Verification:

```text
lake build ConnesWeilRH.Route.RouteTheorem
```

Result in the Linux ext4 verification copy: `Build completed successfully
(2969 jobs).`

This remains an additive migration step. The legacy normalized source root is
not replaced by this record, and no `SourceRH` or RH conclusion follows.