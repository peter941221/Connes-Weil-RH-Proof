# Record 1222 — invalidation of the 1220 entrywise numeric probe

Date: 2026-09-08.

Status: IMPLEMENTATION-INVALID.  This is a diagnostic record, not a numerical
certificate, a route ruling, or an RH claim.

Consumer in scope: the registered 1219 E2--E5 attempt to supply the named
same-parity `hsp` hypothesis consumed by record 1218.  It does not alter the
binding healthy-`CompactLog`, B5-shaped mainline or supply a positivity
producer.

## Evidence

The run-4 log printed, for entry `(0,0)`,

```text
C0 mid = 0.267963860808493
H mid  = 1.298071522386948892749803290624e33
entry  = [1.298071052978789e33, 1.298071991795108e33]
```

The order-one `C0`, `kappa`, and finite-prime integral isolate the blow-up to
the archimedean bracket accumulator `H`.  Inspection of the exact-rational
code gives two independent violations of the intended compact-support
reduction.

### I1 — illegal outside-support point evaluation

Mathematically,

```text
b(u) = exp(-1/(1-u^2))  for |u| < 1,       b(u) = 0  for |u| >= 1.
```

`bump_D_bound` correctly intersects an interval with `(-1,1)`.  In contrast,
`bump_deriv_value_iv(m, u_c)` calls `bump_value_iv(u_c)` without testing the
domain.  For a Taylor centre `u_c = 1 + epsilon`, it evaluates

```text
exp(-1/(1-u_c^2)) = exp(1/(u_c^2-1)),
```

which grows without bound as `epsilon` decreases, whereas every derivative
of the compact smooth bump is zero at that point.  The entry partition bounds
the live `u` range by `ucl0,ucl1` but does not split the leaf at `u = +/-1`;
therefore it admits a support-crossing leaf whose centre lies outside support.
The observed `H` scale is the expected signature of this error.

### I2 — missing signed half-axis substitution

The probe declares two `s` signs, but the loop body uses the same positive
`(a,b)` endpoints for both values:

```python
for sign in (1, -1):
    for (a, b) in bands:
        stack = [..., (a, b)]
```

`sign` has no later use.  Thus the computation duplicates the positive
half-axis and never evaluates the negative `s` half required by the pinned
integral over `(-1,1)`.  Even after I1 is repaired, this is not the stated
integral.

## Consequence and controlled recovery

The run is neither GO nor the registered F1/F2 NO-GO: it did not implement
the preregistered ground truth.  Both running instances were stopped after
the diagnostic readout, so no further invalid output is treated as evidence.

Before another run, a new amendment must pin all of the following:

1. a partition which splits every `u = y/2-s` cell at `u = -1, 1`, with a
   Taylor expansion only on a cell contained in the smooth support interior;
2. the exact mapping of the negative `s` band, including orientation and
   Legendre parity, and an algebraic check that the two signed bands cover
   the original integral once;
3. a small exact semantic test proving that the point and interval bump APIs
   agree outside support and at the two boundary-adjacent cells.

Only then may a replacement exact-Fraction probe be started.  Record 1217's
boxes are unchanged; no Lean E2a generator may consume any 1220 run output.
