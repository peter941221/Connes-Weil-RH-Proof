# 1257 — G8 same-owner readback consumer

Date: 2026-09-10

Status: formal consumer wiring; no positivity producer and no RH conclusion.

## Finding

The G8 adjoint-shear Gram route already had, for every finite cutoff, a
trace-class positive operator on the healthy source owner.  The missing link
was not a new abstract trace interface: it was the precise same-owner limit
readback needed by the existing P2 positive-trace consumer.

`C1G8AdjointShearGram.lean` now defines the G8-specific
`G8SameOwnerReadbackData` contract.  Its only analytic fields are

1. a real remainder tending to zero; and
2. convergence of the cutoff ordinary traces minus that remainder to
   `C1SameOwnerWeil.qw owner.sourceTest`.

The cutoff trace-class and positivity fields are supplied by the already
formalized G8 theorems, not stored as assumptions.  The adapter
`g8PositiveTraceOperatorLimitFamily` feeds this concrete family to the
existing `PositiveTraceOperatorLimitFamily` consumer, and
`qw_nonnegative_of_g8SameOwnerReadbackData` derives the same-owner
`0 ≤ qw owner.sourceTest` consequence.

## What this does not prove

No remainder estimate, cutoff convergence, finite-prime arithmetic readback,
or sign theorem is proved here.  Therefore the active P2 obligation remains
the construction of `G8SameOwnerReadbackData` for the pinned healthy orbit
detector.  This is a formal consumer narrowing, not evidence that the
readback exists.

## Verification

The authoritative retry log is
`/home/peter/rh/build-logs/1257_g8_readback_contract_retry2.log`.
It reports `Build completed successfully (3922 jobs)`, zero `error:` lines,
zero `sorryAx`, and the audit declarations depend only on
`[propext, Classical.choice, Quot.sound]` (audit lines 34–36).

## Classification

Formal Lean result and route-consumer narrowing.  The readback fields remain
an open analytic producer obligation; no numerical experiment is used.
