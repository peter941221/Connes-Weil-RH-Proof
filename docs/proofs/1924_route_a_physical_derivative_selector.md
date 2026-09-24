# 1924 — Route A physical-derivative-controlled selector

Date: 2026-09-24.

Status: partial formal progress. The selector is formal; the signed residual
margin and RH remain open.

## Construction

The old `ResidualCorrectionFamily` selected a compact test with finite Mellin
interpolation and support, but exposed no physical derivative information. The
new owner in
`ConnesWeilRH/Dev/C1PhysicalDerivativeControlledCorrection.lean` is
`SelectedPhysicalDerivativeCorrection`.

For every finite assignment `y`, it stores:

```text
value y                         : CompactLogTest
support (value y).test          subset of the selected residual window
laplaceAt (value y) z           = y z
derivativeCost y                >= 0
||deriv (value y).test x||      <= derivativeCost y   for every x
```

The selector is constructed by choosing the existing finite-window
interpolant, then defining `derivativeCost y` as the zeroth Schwartz seminorm
of its Schwartz derivative. Mathlib's `SchwartzMap.derivCLM` proves that this
derivative is again Schwartz, and `SchwartzMap.norm_le_seminorm` gives the
pointwise bound.

This is not circular: the owner does not store `residual_budget`, the desired
gate inequality, or any conclusion equivalent to it.

## Verification

Focused build:

```text
20260924_physical_derivative_selector2.log
Build completed successfully (3662 jobs)
```

The paired audit prints only `[propext, Classical.choice, Quot.sound]` for the
selector and its three readback theorems; no `sorryAx` occurs.

## What this removes and what remains

Removed: the current-selector API underdetermination identified in record
1923. The selected owner now carries independently proved physical derivative
control.

Still open: turn that control into the strict signed budget

```text
archimedeanTerm(square) + integral(-t * aggregateDerivative(t)) < 0
```

while retaining cancellation in the grouped finite visible-prime aggregate.
An absolute-value primewise estimate is still not an acceptable substitute.
