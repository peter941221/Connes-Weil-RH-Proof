# 3148: Indexed root migration boundary audit

Date: 2026-10-28

## Finding

A direct replacement of the normalized root type with
`IndexedCommonFinitePrimeArithmeticSourceData` is not a one-file change.
A direct `UnconditionalSkeleton` compile exposed three distinct legacy
consumers:

- `CCM25SourceArithmeticConstructorInput` still stores
  `CommonFinitePrimeArithmeticSourceData`;
- `ConcreteCCM25ArithmeticRows` and `Interface` still consume the legacy
  source-test certificate family and its full atom certificate methods;
- `ObjectTheoremBasePackage` and the normalized development projections still
  expose legacy finite-prime data accessors.

The indexed source-data owner is therefore a valid replacement boundary, but
it must be propagated through the CCM25 rows/interface and theorem-base
constructor as one coherent migration. A partial root substitution is rejected
because it creates type mismatches rather than silently weakening obligations.

## Reversion

The partial uncommitted root substitution was reverted after the direct compile
so the worktree contains no half-migrated source API. Previously committed
indexed certificate, source-data, common-owner, and analytic-dominance changes
remain intact.

## Verification evidence

The uncommitted direct compile reached the actual errors in
`UnconditionalSkeleton.lean` before the reversion. The existing committed
indexed boundary continues to pass:

```text
lake build ConnesWeilRH.Route.RouteTheorem
Build completed successfully (2969 jobs)
```

No `SourceRH` or RH conclusion follows from this audit.