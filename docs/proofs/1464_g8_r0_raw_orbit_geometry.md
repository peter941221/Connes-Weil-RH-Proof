# 1464 — G8 R0 raw orbit-geometry export

**Status:** R0 FORMAL; R2/R3 and the same-owner readback remain open. No
semi-local sign or RH result is claimed.

Consumer: the healthy-`CompactLog`, B5-shaped G8 chain for the detector
selected against the same hypothetical right-hand off-line zero. The target
continues to be `0 <= C1SameOwnerWeil.qw g` for that exact detector and its
finite visible-prime family.

## Result

`ConnesWeilRH/Dev/C1G8R0OrbitGeometry.lean` defines
`OrbitG8Geometry rho g` as a lower-data structure. It carries the exact
selected-owner factorization and orbit index, base/correction support,
unscaled target values, minimal interpolation, centered functional-equation
orbit sum, square-zero control, fourth-order square tail, support interval,
and the support-derived finite visible-prime cutoff.

The producer
`exists_orbitG8Geometry_of_sourceNontrivialZero_right` proves that every
right-oriented off-line source zero exports such a package. Its proof calls
the raw-target orbit construction and the dyadic tail-start construction,
then derives the support and prime cutoff on the same selected owner. It does
not call `selectedOwner_healthyDetectorData_of_closedBall_square_zero_control_and_fourthOrderTail`
or `exists_healthyDetectorData_with_pinned_support`. The geometry structure
has no `HealthyYoshidaDetectorData` field and no Weil-sign field, so the G8
readback producer can consume the raw package without assuming the later
detector contradiction.

This completes only the compatibility/package obligation R0 in map 012. It
does not identify the G8 cutoff trace with the finite-S response, prove a
cutoff remainder tends to zero, or read a trace limit back to the same-owner
Weil value. In particular, `G8SameOwnerReadbackData` remains unconstructed.

## Verification

The paired leaf is `C1G8R0OrbitGeometryAudit.lean`. Native WSL2 ext4 build:

```text
lake build ConnesWeilRH.Dev.C1G8R0OrbitGeometry
  ConnesWeilRH.Dev.C1G8R0OrbitGeometryAudit
Build completed successfully (3660 jobs).
error: 0
sorryAx: 0
Quot.sound] audit prints: 1 / #print axioms lines: 1
```

The exported producer audits to exactly
`[propext, Classical.choice, Quot.sound]`. The acceptance log is
`1464_r0_geometry_try4.log`; the Windows and ext4 source MD5 values matched
before the build.
