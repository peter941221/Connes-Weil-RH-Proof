# 3149: Indexed CCM25 arithmetic rows boundary

Date: 2026-10-28

Added `ConcreteCCM25IndexedArithmeticRows` in
`ConnesWeilRH/Source/CCM25Concrete/Rows.lean`.

The row boundary carries indexed source-test certificates and exposes
`finite_prime_normalization_of_indexed_arithmetic_rows`. It is additive and
does not change the legacy rows, allowing the CCM25 interface migration to be
performed without creating an invalid intermediate root.

Verification:

```text
lake build ConnesWeilRH.Route.RouteTheorem
```

Result: `Build completed successfully (2969 jobs)` in the Linux ext4
verification copy.