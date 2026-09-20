# 1751 — Physical point with finite Mellin interpolation

Date: 2026-09-20

## Result

The formal theorem `exists_physicalPoint_mellinInterpolation` constructs a
genuine `CompactLogTest` whose value at a prescribed positive physical log
point is one, while its Laplace values at every node of an arbitrary finite
complex node set equal arbitrary prescribed targets.

The construction is explicit at the owner level: a compact-log physical bump
is placed around the sample point, and the existing residual-window
correction is assigned the target minus the bump's Laplace vector. The two
supports are separated, so the correction vanishes at the physical point.

## Route meaning

This is the first formal bridge between the actual finite-prime profile
coordinates and the triple Mellin-vanishing constraint on the same genuine
`CompactLogTest` owner. It does not yet interpolate several physical points
simultaneously, prove a rank statement for a finite prime profile, or prove
the signed budget, detector health, semi-local positivity, or RH.

## Evidence

Focused owner plus Audit build:

`build-logs/shortest_route_20260920_physical_mellin_v2.log`

The log reports `Build completed successfully (3653 jobs)`, zero `error:`
lines, and the Audit axiom list
`[propext, Classical.choice, Quot.sound]`.
