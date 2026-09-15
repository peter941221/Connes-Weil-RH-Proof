# 1466 — R3 moving-scale source commutator trace legality

**Date:** 2026-09-15.

**Status:** formal trace-legality result; supporting R3 brick, not a sign or RH
claim.

**Consumer:** the healthy-`CompactLog`, B5-shaped statement
`0 <= C1SameOwnerWeil.qw g` for the same detector selected against a
hypothetical off-line zero, followed by the existing same-detector
contradiction and `SourceRH` wrapper.

## Result

For every selected owner, every selected Sonin scale, every compact source
support interval with its boundary input bases, and every named global basis
of `finiteSCarrier`, Lean proves

```text
IsTraceClassAlong globalBasis
  (cc20Commutator (sourceSoninProjection lambda)
    (detectorOperator owner))
```

The theorem is
`sourceSoninDetectorCommutator_isTraceClassAlong_all_scales` in
`ConnesWeilRH/Dev/C1G8R3ScaleSourceTraceLegality.lean`. It rewrites the source
commutator by the exact `sourceSoninCommutator_eq_threeBranch` identity and
applies the existing three-branch source trace theorem to the all-scale
prolate-factor square-sum from [1465](1465_r3_moving_scale_detector_root_range_energy.md).
The basis and source support data stay explicit in the theorem statement.

The same leaf also proves
`sourceSoninDetectorCommutator_trace_eq_outerPair_add_remainder_all_scales`.
For the same owner, scale, boundary bases, and global basis, it identifies the
ordinary trace of the full source commutator exactly as

```text
trace(source Sonin commutator)
  = trace(outer branch + reflected outer branch)
    + trace(source second-support/prolate remainder).
```

The source remainder receives trace legality from the same all-scale factor
square-sum. This exposes the complete signed source trace ledger in one named
basis, while retaining the coupled remainder intact.

This closes moving-scale source-side trace legality for the complete signed
commutator. It does not estimate the leakage branch in isolation, identify a
G8 finite cutoff with the source commutator, prove a vanishing cutoff
remainder, or read the resulting trace limit back as `qw`.

## Consumer and boundary

The result serves the exact tower-selected detector on the healthy
`CompactLog` B5 route. Its proof uses only the source commutator identity,
source support/boundary bases, and the formal all-scale prolate square-sum; it
does not use a Weil sign, `SourceRH`, or a universal positivity gate.

The remaining analytic bridge is still the R3 readback contract:

```text
source/G8 cutoff compatibility
  -> signed same-owner remainder convergence
  -> G8SameOwnerReadbackData
  -> 0 <= qw g for the selected detector
```

The same-owner `qw` readback, detector-specific semi-local positivity, C3,
and RH remain open.

## Lean evidence

The paired audit is
`ConnesWeilRH/Dev/C1G8R3ScaleSourceTraceLegalityAudit.lean`. Accepted log:
`20260915_r3_source_trace_decomposition_try2.log` (WSL ext4 build log).
It reports `Build completed successfully (3288 jobs)`, zero `error:` lines,
zero `sorryAx`, and two standard-axiom audit terminators; both declarations
have exactly `[propext, Classical.choice, Quot.sound]`.
