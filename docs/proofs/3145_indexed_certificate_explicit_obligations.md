# 3145: Indexed certificate explicit obligations

Date: 2026-10-28

The indexed source-test certificate family now carries two obligations that
cannot be derived from the support skeleton alone:

- `restrictedPrimeIndexCoverage`, because the support reverse route requires
  the numerical conditions `1 < n` and `n <= lambda^2`;
- `finitePrimeTermNormalization`, because support data alone does not identify
  the finite-prime term with the von Mangoldt/pairing expression.

The family also has
`finite_prime_visibility_of_indexed_source_test_certificates`, which derives
the broad visibility statement from those explicit obligations and the global
support route.

Verification:

```text
lake build ConnesWeilRH.Route.RouteTheorem
```

Result: `Build completed successfully (2969 jobs)` in the Linux ext4
verification copy.

This is an honest retyping boundary, not an RH proof and not a replacement of
the legacy normalized source root yet.