# 3144: Indexed source-data evaluator read-offs

Date: 2026-10-28

Added `IndexedFinitePrimeArithmeticSourceData.globalArithmeticData` and
`restrictedArithmeticData`. These expose the exact finite-index evaluator data
from the indexed source-data owner, so future balance consumers can avoid the
legacy all-natural-number normalization.

Verification:

```text
lake build ConnesWeilRH.Route.RouteTheorem
```

Result: `Build completed successfully (2969 jobs)` in the Linux ext4
verification copy.

The legacy normalized source root remains unchanged and axiom-backed. This
record does not prove `SourceRH` or RH.