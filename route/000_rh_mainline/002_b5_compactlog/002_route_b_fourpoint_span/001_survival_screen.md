# 001 — Route B survival screen

Status 2026-09-27: the fixed first probe below was run. Its `n = 4` row was
a `dxi = 0.05` resolution artifact and is withdrawn; the screen now returns
`DEAD` on the strict reading (no certified `n >= 1` row carries the
registered signs) and `SURVIVES_SCREEN` on the `q` margin alone. See
records 2028/2029/2030/2031.

Purpose: decide whether the current Route B branch deserves full interval
certification and Lean investment. This is a triage screen, not a theorem.

Fixed first probe:

```text
rho = 0.55 + 14.134725141734693 i
T = 28
q = 2^(-14)
n = 4
lambda = b_n / C_n
```

Required output per owner:

```text
owner cardinality
minimum node separation
node-product condition estimate
correction mass
C_n, b_n, D_n, det_n, lambda_n
determinant error margin
corrected-base profile maximum
q margin
same-index tail ratio
```

Decision labels:

```text
DEAD:
  det_upper >= 0
  or tail_ratio >= 1
  or profile_upper >= q
  or owner/correction conditioning explodes

SURVIVES_SCREEN:
  det_upper < 0
  tail_ratio < 0.1
  profile_upper < q / 10
  values stable under precision and grid refinement

INCONCLUSIVE:
  anything between the two cases
```

These thresholds are engineering triage thresholds. They do not replace
interval proofs.

After the first rho, use a small height stress set and track degradation:

```text
gamma = 14.13, 21.02, 30.42, 50, 100
```

Watch whether determinant margin collapses, tail ratio grows, q margin shrinks,
or node-product conditioning worsens with height. A trend failure is evidence
against the current parameter family, not automatically against all of Route B.

Do not write new Lean leaves before this screen identifies a surviving margin.