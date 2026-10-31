3215 Route-A Boundary Cell Support-Crossing Geometry
====================================================

Status
------

PASS_SUPPORT_CROSSING_NEGATIVE_RESULT

Purpose
-------

This record checks the first 40960-cell midpoint against the concrete owner
support radius. It is a geometry boundary, not a positivity or producer
certificate.

Reproduction
------------

    WSL2 ext4 workspace
    LEAN_NUM_THREADS=1 lake build ConnesWeilRH.Dev.C1RouteAConcreteOwnerBoundaryGeometry3215
    lake env lean ConnesWeilRH/Dev/C1RouteAConcreteOwnerBoundaryGeometry3215Audit.lean

Observed result
---------------

Lean proves:

    |record2680Center3212 0| < storedWidth 4 ^ 2

Therefore the first cell midpoint is strictly inside the owner support. The
same file proves the negation of the support-zero condition. The 3204 row's
`value_upper = 0` must consequently be interpreted as a signed one-sided
upper bound at the midpoint, not as an identity saying that the function is
zero there.

Audit
-----

The focused build used `leanprover/lean4:v4.30.0` and Lean 4.30.0. The two
3215 declarations audit to exactly `[propext, Classical.choice, Quot.sound]`.
No JSONL row was imported, no tail was added, and no producer or RH claim was
made.

Next proof boundary
-------------------

The next cell-level theorem must prove a concrete signed midpoint inequality
for the owner, then bound the second and fourth derivatives and use the
sixth-order remainder. The support-zero theorem is not applicable to this
boundary cell.
