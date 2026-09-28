# 2139 - Owner-local omitted-residual screen

Date: 2026-09-28.

Status: SCOPED-NO-GO-FOR-NAIVE-OWNER-LOCAL-CARDINAL-PREFIX. This is a
numerical mechanism screen, not an actual-owner theorem and not an RH result.

## Consumer and setup

The consumer is the 2138 residual-budget contract:

```text
finite exact prefix + omitted low-shell residual + high-shell tail
    < anchor multiplicity
```

The probe uses `rho = 0.945 + 39.25244858548658 i`, `N = 0`, formal radius
`43.2666238038906`, and the same smooth-seed cardinal interpolation formula
used by the Route-A owner probes. The base and correction interpolate the
healthy target/orbit nodes, then a sweep adds known zeta zeros as zero-valued
prefix nodes. The 21 omitted points are a known-zero under-approximation of
the formal owner; no abstract-owner claim is made.

## Result

```text
prefix zeros | interpolation nodes | omitted zeros | abs residual / anchor
0            | 8                  | 21            | 5.92468117481211e4
5            | 13                 | 16            | 1.852410508636541e15
10           | 18                 | 11            | 1.9157305927827673e32
15           | 23                 | 6             | 4.309477489612436e31
21           | 29                 | 0             | 0
```

All nonzero residual rows were positive in this model, so signed cancellation
does not rescue the absolute residual budget. Adding zero pins worsens the
reading because the cardinal interpolation path becomes badly conditioned;
the screen therefore measures both residual leakage and conditioning failure.

## Decision

Close the following scoped mechanism:

```text
fixed smooth-seed cardinal interpolation
    + orbit/healthy targets
    + a finite omitted-zero residual budget
```

It cannot be promoted by simply increasing the prefix: the tested path needs
all 21 known zeros before the residual vanishes, and intermediate prefixes
are numerically much worse. This does not close every owner-local mechanism.
Reopening requires a changed basis/regularization, a signed residual identity,
or a different owner construction with a reproducible margin probe.

Evidence:

```text
scripts/routea_owner_local_residual_screen_2139.py
results/2139_routea_owner_local_residual_screen.json
docs/proofs/2138_routea_residual_budget_consumer.md
scripts/fourpoint_actual_owner_1980.py
```
