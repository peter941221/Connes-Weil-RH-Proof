# 3147: Indexed dominance consumer

Date: 2026-10-28

Added `SourceWeilFormData.finitePrimeDominance_of_indexed_certificates` in
`ConnesWeilRH/Source/AnalyticSourceModel.lean`.

This is the first analytic consumer that accepts the indexed certificate family
directly. It derives global finite-prime dominance from the indexed global
coverage route, while restricted coverage and term normalization remain
explicit fields of the indexed certificate family.

Verification:

```text
lake build ConnesWeilRH.Route.RouteTheorem
```

Result: `Build completed successfully (2969 jobs)` in the Linux ext4
verification copy.

The legacy normalized root remains in place; this theorem does not prove
`SourceRH` or RH.