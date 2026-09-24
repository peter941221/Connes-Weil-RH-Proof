# 1945 — Explicit-lambda shortcut is a scoped no-go

Date: 2026-09-24

## Decision

The first attack tested whether the four-point gate could use a simple
owner-scale coefficient instead of the owner-specific vertex coefficient.
On the 18 committed-class cases from record 1918, the quadratic gate was
evaluated with

```text
lambda_vertex = B'/(2*C)
lambda_scale  = 0.5 * (3 + ||rho||)^4
```

and with 0.9 and 1.1 multiples of `lambda_scale`.

The vertex was negative on all 18 cases. The fixed scale was negative on only
6/18 cases; its 0.9 and 1.1 multiples were negative on 9/18 and 3/18 cases.
The largest positive value for the fixed scale was approximately `5.91e8`.

## Route impact

This is a numerical, committed-class no-go for the simple fixed coefficient.
It does not disprove the vertex route and does not provide a counterexample to
the analytic theorem. The coefficient must remain owner-specific, or the
proof must establish a sharper owner-dependent selection rule.

The next producer target is therefore the actual vertex determinant with the
same owner and visible-prime set:

```text
B' > 0
D*C - (B'/2)^2 < 0.
```

The four-channel physical expansion from record 1944 is the intended carrier
for this estimate. No absolute-value channel majorant is licensed.

## Reproducibility

Probe: `scripts/fourpoint_explicit_lambda_probe_1945.py`.

Input: `results/1918_fourpoint_diagonal_sign_certified.json`.

Artifact: `results/1945_fourpoint_explicit_lambda_probe.json`.

WSL resource-runner log: the external build-log location for the 1945 probe.

The probe completed with exit code 0. This record is numeric decision evidence
only; no Lean theorem and no RH claim is added.
