# 1236 - Canonical internal identity counterterm: finite-part no-go

Date: 2026-09-09.

Status: FORMAL consequence of existing Lean lemmas; no new producer is
claimed. Consumer: the healthy-`CompactLog` B5 projection-cutoff route.

## Candidate

The Stage-3 kernel satisfies `0 ≤ K_{lambda,S} ≤ I`. Its insertion defect is
the compressed difference

```text
D(a,c) = Z† (K_{lambda,S} - I) Z,
```

so the canonical sign-safe internal correction is `M = I - K`. At the
operator level this gives `K + M = I` and `Q_n = C_n† I C_n`.

## Verdict

The candidate cannot satisfy the projection-cutoff limit contract on a
nonzero detector. The existing theorem
`cutoffPositiveBasisData_trace_re_unbounded_of_test_ne_zero` proves that the
real trace of `C_n† I C_n` is cofinally unbounded. Therefore it has no finite
limit equal to `qw(g)`. This is the same bulk-growth obstruction encoded by
`not_projectionCutoffLimitContracts_of_fixedResponse_and_traceDefect_vanishing`.

This is not a no-go for every possible two-channel `M_n`; it kills only the
canonical identity-complement correction. Any survivor must retain the genuine
`P_r(lambda)`/`P_V(S)` geometry and supply a new positivity proof plus
same-owner finite-part readback. External trace subtraction remains invalid.

## Evidence

- `C1ProjectionSquareOrderGuard.lean`: `stage3ProjectionKernel_le_id` and
  `kernelInsertionDefect_le_zero`.
- `C1Stage3ProjectionDefectBounds.lean`:
  `kernelInsertionDefect_eq_compressedKernelDifference`.
- `C1PositiveTraceCutoffGrowth.lean`:
  `cutoffPositiveBasisData_trace_re_unbounded_of_test_ne_zero`.
- `C1Stage3ProjectionContractObstruction.lean`:
  `not_projectionCutoffLimitContracts_of_fixedResponse_and_traceDefect_vanishing`.

RH is not claimed.
