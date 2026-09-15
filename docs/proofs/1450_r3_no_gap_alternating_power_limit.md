# 1450 — R3 no-gap alternating-power limit

**Date:** 2026-09-14

**Consumer:** the healthy-`CompactLog`, B5-shaped same-owner detector
conclusion `0 <= C1SameOwnerWeil.qw g`.

## Formal result

The paired Lean leaf
`ConnesWeilRH/Dev/C1G8R3PowerProjectionBridge.lean` now proves
`doubledShiftAlternatingProduct_tendsto_intersectionProjection_no_gap` for the
actual finite-S carrier. Its proof has no spectral-gap premise and no new
axiom. The paired Audit leaf prints the standard axiom set only.

Acceptance evidence:

```text
log: /home/peter/rh/build-logs/1450_nogap_acceptance.log
Build completed successfully (3180 jobs)
error: 0
sorryAx: 0
```

## Proof mechanism

For a self-adjoint contraction `T`, let `K` be its fixed-space submodule and
let `A = T - I`. The formal bridge proves:

1. `A` is self-adjoint and `ker A = K`.
2. Mathlib's adjoint range theorem gives
   `closure(range A) = K`-orthogonal-complement.
3. On `range A`, the power orbit telescopes:
   `T^n (A u) = T^(n+1) u - T^n u`.
4. The step-difference limit and uniform contraction bound make the set of
   vectors whose power orbit tends to zero closed. It therefore contains the
   whole orthogonal complement of `K`.
5. Splitting `v` into its projection onto `K` and its orthogonal residual gives
   `T^n v -> projection_K v`.

For the concrete product `T_b = p_b q p_b`, the earlier step estimate was
proved for radial inputs. The new identity `T_b p_b = T_b` promotes it to all
carrier vectors after the finite initial index, which is enough at `atTop`.

## Boundary

This closes the no-gap power-limit/existence bone only. Strong convergence is
not trace-class convergence. The exact detector-root Hilbert--Schmidt
square-sum, same-basis signed trace witness, and G8 cutoff/readback
reconnection remain open. No `qw` sign, `SourceRH`, or RH conclusion follows
from this brick.
