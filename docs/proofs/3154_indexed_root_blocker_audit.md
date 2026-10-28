# 3154: Indexed root blocker audit

Date: 2026-10-28

The current `UnconditionalSkeleton` still obtains
`CommonFinitePrimeArithmeticSourceData` from the legacy axiom
`normalizedCoreCCM25FinitePrimeArithmeticSourceDataRoot` at line 659. The
indexed object-package provenance wrapper does not remove this dependency.

The indexed migration now has a verified path through:

```text
indexed certificates
  -> indexed arithmetic rows
  -> indexed CCM25 source model
  -> indexed theorem-base constructor input
  -> indexed object-package provenance wrapper
```

The remaining root obligation is stronger than a type conversion: construct
indexed source-test certificates for every test pair `(f, g)` and every
`lambda > 1`, including the explicit restricted-index coverage and finite
prime-term normalization fields. The existing concrete prime-2 probe only
constructs a per-common source support object; it does not provide those
arbitrary-pair certificates. Therefore the legacy root must not yet be
replaced by a cast or by an indexed certificate placeholder.

Verification of the completed migration layers:

```text
lake build ConnesWeilRH.Route.RouteTheorem
```

Result: `Build completed successfully (2969 jobs)` in the Linux ext4
verification copy. The provenance read-back declarations report only
`[propext, Classical.choice, Quot.sound]`.

