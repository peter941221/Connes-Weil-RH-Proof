# 2474 - cell-local curvature attachment

Date: 2026-10-02.

The global 2348 remainder has been complemented by
`stripNorm_le_localCurvature2474`.  It accepts one bound for the weighted
second derivative on each grid cell and charges

`Σᵢ curvature(i) · step³ / 12`

instead of `max(curvature) · (2 radius) · step² / 12`.  Node bounds remain
the exact 2471 owner node inputs.  This is the theorem-shaped interface needed
for a panel-local derivative enclosure; it does not itself provide the
numeric `curvature` array.

The declaration is audited on the standard three axioms.  No numerical
certificate, producer gate, GO conclusion, or RH claim follows.
