# 017 — R3 no-gap alternating-power limit

**Date:** 2026-09-14.

**Status:** formal analytic brick; supporting route record, not an RH claim.

**Consumer:** the healthy-`CompactLog`, B5-shaped statement
`0 <= C1SameOwnerWeil.qw g` for the same tower-selected detector.

## 1. Result

The actual finite-S alternating product

```text
T_b = p_b q p_b
```

now has a formal strong limit on the actual `finiteSCarrier`:

```text
T_b^n v -> r_b v
```

with no uniform Friedrichs gap and no operator-norm convergence claim. The
consumer theorem is
`doubledShiftAlternatingProduct_tendsto_intersectionProjection_no_gap` in
`ConnesWeilRH/Dev/C1G8R3PowerProjectionBridge.lean`.

The focused paired build was accepted from
`build-logs/1450_nogap_acceptance.log`:

```text
Build completed successfully (3180 jobs)
error: 0
sorryAx: 0
```

The paired Audit leaf prints only the standard three axioms. The acceptance
log contains 46 wrapped `Quot.sound]` axiom-set endings, matching the audited
declaration count.

## 2. New argument

Let `A = T - I`, and let `K` be the fixed-space submodule. The proof has four
steps.

1. Self-adjointness of `T` makes `A` self-adjoint. Mathlib's adjoint range
   theorem gives `closure(range A) = ker(A)^⊥`, while the fixed-space theorem
   gives `ker(A) = K`. Thus `range(T-I)` is dense in `K^⊥`.
2. For a range vector `A u`, the power orbit telescopes exactly:
   `T^n(A u) = T^(n+1)u - T^n u`. Existing defect estimates prove the right
   side tends to zero.
3. The set of vectors whose power orbit tends to zero is closed. This uses
   the uniform contraction bound on all powers, expressed as uniform
   equicontinuity, so the telescoping limit extends from `range(A)` to its
   closure.
4. Every vector splits as `(v - r_b v) + r_b v`; the first summand lies in
   `K^⊥`, and the second is fixed. Therefore the full orbit converges to
   `r_b v`.

For the concrete product, the earlier defect theorem was stated first for
radial inputs. A new right-absorption identity `T_b p_b = T_b` promotes its
step-norm convergence to every carrier vector after discarding the finite
initial index, which is harmless at `atTop`.

## 3. What this closes and what it does not

Closed:

- actual no-gap strong convergence of the alternating powers;
- the existence part previously represented by the defect-series exhaustion
  socket;
- the strong-convergence premise needed by the existing strong-to-Hilbert--Schmidt
  transfer.
- the unit-scale prolate-range completed detector leg's square-summability and
  its weighted energy limit, via record 1451.

Still open:

- the full exact square-summability of the detector-root factor columns: the
  band-minus-prolate leakage leg and common-right finite-Euler leg remain;
- a same-basis trace witness for the signed detector remainder;
- cutoff/source reconnection into `G8SameOwnerReadbackData` and hence the
  detector-specific nonnegative `qw` conclusion.

Record 1452 rewrites the leakage leg on the same carrier as the selected root
conjugated against the doubled-shift defect `p_b - T_b`; it adds no trace or
positivity conclusion.

Strong convergence alone is not trace-class convergence and does not supply a
Weil sign. The active route remains the healthy `CompactLog` B5 consumer; no
B1 globalization, ROOT-density lift, or RH conclusion is introduced here.
