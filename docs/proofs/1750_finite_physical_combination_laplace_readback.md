# 1750 — Finite physical combinations and exact Laplace readback

Date: 2026-09-20

## Result

The new formal leaf `C1P2FinitePhysicalCombination` defines a genuine
`CompactLogTest` from a finite coefficient family and a finite family of
physical compact-log tests. It proves the exact readback

`laplaceAt (sum_i coeff_i • basis_i) s = sum_i coeff_i * laplaceAt (basis_i) s`.

The support proof is carried by finite-union compact support and the Laplace
identity by `MeasureTheory.integral_finsetSum`, with each Schwartz integrand
proved integrable. The paired Audit prints the standard three axioms and no
`sorryAx` occurs.

## Route meaning

This is the finite-dimensional matrix interface needed to impose the three
critical Mellin vanishings while retaining a physical-space coefficient
description. It does not provide invertibility, a support-preserving
surjectivity theorem, a signed-budget estimate, semi-local positivity, or an
RH conclusion. The active healthy-`CompactLog` B5 consumer remains the
detector-specific signed budget from map records 051–054.

## Evidence

Focused owner plus Audit build:

`build-logs/shortest_route_20260920_finite_physical_v9.log`

The log reports `Build completed successfully (3481 jobs)`, zero `error:`
lines, and the Audit axiom list
`[propext, Classical.choice, Quot.sound]`.
