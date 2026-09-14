# 1432 — R3 weighted finite-stage commutator ledger

Date: 2026-09-14

## Result

The finite-stage algebraic entry point for the detector-weighted
alternating-projection route is now formal.  For arbitrary continuous linear
operators `T` and `D` on the committed finite-S source carrier, define the
recursive stage
`weightedCommutatorStage T D n` by

```text
stage 0     = 0
stage (n+1) = T * stage n + (T * D - D * T) * T^n.
```

The new theorem proves the exact identity

```text
T^n * D - D * T^n = weightedCommutatorStage T D n.
```

The same theorem is instantiated with the source-owned doubled-shift
alternating product `p_b * q * p_b`, where `p_b` is the doubled-shift radial
projection and `q` is the unit-scale Fourier-support projection.

The same module proves the two structural facts needed to make this product
a legitimate spectral-endpoint object: `p_b * q * p_b` is positive and
self-adjoint for every `b`.  The proof uses only positivity of an orthogonal
projection and the adjoint-conjugation rule; it does not assume a spectral
gap.

## Formal artifacts

- `ConnesWeilRH/Dev/C1G8R3WeightedFiniteStage.lean`
  - `operatorCommutator`
  - `weightedCommutatorStage`
  - `operator_pow_commutator_eq_weightedStage`
  - `doubledShiftAlternatingProduct_isPositive`
  - `doubledShiftAlternatingProduct_isSelfAdjoint`
  - `doubledShiftAlternatingProduct_commutator_stage`
- paired audit module:
  `ConnesWeilRH/Dev/C1G8R3WeightedFiniteStageAudit.lean`

## Acceptance evidence

Build log:
`build-logs/1432_weighted_finite_stage_try3.log` in the standard WSL build
mirror.

```text
Build completed successfully (3177 jobs).
^error: count = 0
sorryAx count = 0
10 audited declarations, all [propext, Classical.choice, Quot.sound]
```

## Scope judgment

This closes the exact finite-stage commutator identity (015-C).  It does not
prove that the stages converge to the intersection projection, does not prove
any trace-class or trace-norm estimate, and does not reconnect to
`G8SameOwnerReadbackData`.  The remaining R3 obstacle is therefore analytic:
detector-weighted summability at the spectral endpoint, followed by the named
global-basis witness and same-owner limit.
