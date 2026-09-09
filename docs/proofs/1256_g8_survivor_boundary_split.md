# Proof 1256 — exact G8 survivor/boundary split

Status: FORMAL-SURVIVOR-BOUNDARY-SPLIT (Lean), 2026-09-10.

The same healthy-source G8 compression now has an exact Schur–polar
decomposition through the finite visible-prime metric coframe.  Two owner-local
maps name the terminal survivor and the sum of the genuine rectangular boundary
outputs, and Lean proves

```text
finiteEulerMetricCoframe
  = upperEulerFactor · (survivor + boundarySum)
```

Consequently the compressed G8 operator is exactly

```text
(upperEulerFactor · (survivor + boundarySum))†
  · W_g ·
(upperEulerFactor · (survivor + boundarySum)).
```

This is an exact same-owner operator identity.  It does not assign a sign to
the boundary channels, does not identify the boundary sum with a finite-prime
trace term, and does not prove a healthy-limit `qw` readback.  The L4
projection-limit and A4 aggregate obligations therefore remain open.

The owning module imports the Schur–polar telescope explicitly; the paired
audit prints standard axioms only.

Audit evidence: `/home/peter/rh/build-logs/1256_g8_survivor_boundary_retry7.log`.
The owning module and audit build completed successfully (3922 jobs), with
zero `error:` lines and zero `sorryAx`.

RH is not claimed.
