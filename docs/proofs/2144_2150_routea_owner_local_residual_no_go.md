# 2144-2150 - Known-owner constraints and complete-owner residual audit

Date: 2026-09-28.

Status: SCOPED NO-GO for the current owner-local residual mechanism.

## Evidence

Record 2144 adds all 21 known source zeros in the formal ball as correction
zero constraints to the 40-profile H1 basis. The 4001-node screen still reads
`C > 0`, `D < 0`, `det < 0`, but the correction pin residual is `9.13e-5`.

Record 2145 recomputes the 29-constraint matrix with 320-point high-precision
quadrature. Its smallest singular value is about `2.74e-35`; exact pin repair
requires coefficient L2 change about `7.98e11`, so the basis cannot support a
stable certified exact-owner interpolation.

Records 2146-2148 test wider, wider-scale, and node-local-width bases. The
minimum-norm rows either lose the healthy gate, retain condition numbers from
`1e18` to `1e46`, or fail the constraints. A green sampled gate with failed
pins is not admissible evidence.

Record 2149 was an instrument failure: direct complex evaluation overflowed
and returned NaN. It is not used as mathematical evidence. Record 2150 fixes
the evaluator with log scaling. On 5000 random points in the formal ball, the
trial-162 residual product reaches log10 magnitude about `1613`, against anchor
model `1`; the 99th percentile is also far above the budget.

## Decision

Close only this mechanism:

```text
40-profile H1 null-fibre residual budget
+ finite known-zero under-approximation
+ attempted complete-ball supremum transfer
```

The 2141 finite-known-zero signed gate remains a numerical candidate, but it
cannot be promoted to the actual closed-ball owner through a uniform residual
bound. This does not close the formal C3' route or other owner-preserving
mechanisms.

Evidence:

```text
scripts/routea_knownzero_constraint_screen_2144.py
scripts/routea_knownzero_mp_repair_2145.py
scripts/routea_wider_basis_knownzero_screen_2146.py
scripts/routea_wide_scale_knownzero_screen_2147.py
scripts/routea_node_local_width_screen_2148.py
scripts/routea_closedball_residual_sup_screen_2149.py
scripts/routea_closedball_log_residual_screen_2150.py
results/2144_routea_knownzero_constraint_screen.json
results/2145_routea_knownzero_mp_repair.json
results/2146_routea_wider_basis_knownzero_screen.json
results/2147_routea_wide_scale_knownzero_screen.json
results/2148_routea_node_local_width_screen.json
results/2149_routea_closedball_residual_sup_screen.json
results/2150_routea_closedball_log_residual_screen.json
```
