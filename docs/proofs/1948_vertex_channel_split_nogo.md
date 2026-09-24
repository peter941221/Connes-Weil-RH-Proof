# 1948 — Separate vertex-channel signs are not a stable target

Date: 2026-09-24

## Result

The vertex channel stress extended the 1918/1919 kernel rig to widths
`c = 1.3, 1.6, 2.0, 2.4, 3.0`, with both committed heights and `delta = 0.05`.
At the owner-specific vertex:

- the full gate was negative on 10/10 cases;
- the finite-prime channel was negative on 10/10 cases;
- the Archimedean channel was negative on only 3/10 cases.

The Archimedean contribution becomes positive from the wider cases, while the
prime contribution supplies the compensating negative mass. The largest
positive Archimedean value in this stress was approximately `5.32e5`; the
full gate remained negative in the same case.

## Decision

The proposal to prove `Q_arch(lambda_vertex) < 0` and
`Q_prime(lambda_vertex) < 0` separately is a scoped no-go as a general
committed-class strategy. It can only be reopened after proving an actual
selected-owner width/shape restriction that excludes the sign reversal.

The live target returns to the summed owner-preserving inequality

```text
Q_arch(lambda_vertex) + Q_prime(lambda_vertex) <= -eta,
```

with the prime/Archimedean cancellation retained exactly and the actual
visible-prime set unchanged.

## Reproducibility

Probe: `scripts/fourpoint_vertex_channel_stress_1948.py`.

Artifact: `results/1948_fourpoint_vertex_channel_stress.json`.

The retry completed with the resource runner and exit code 0. Numerical
identity residuals were at most `1.73e-4` in the widest/highest case; this is
stress evidence and not an analytic gate certificate.
