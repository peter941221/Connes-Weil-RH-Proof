# 3146: Indexed common source-data owner

Date: 2026-10-28

Added `IndexedCommonFinitePrimeArithmeticSourceData` and its constructor from
indexed source-test certificates. The owner preserves the existing scoped
archimedean balance as an explicit field while replacing only the impossible
legacy finite-prime certificate payload.

The migration shape is now:

```text
indexed certificates
    -> indexed finite-prime source data
    -> indexed common source data
    -> future consumer migration
```

Verification:

```text
lake build ConnesWeilRH.Route.RouteTheorem
```

Result: `Build completed successfully (2969 jobs)` in the Linux ext4
verification copy.

The normalized root is still legacy and axiom-backed. No `SourceRH` or RH
claim is made.