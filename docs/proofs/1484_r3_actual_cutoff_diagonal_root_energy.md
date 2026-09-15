# 1484 — Actual-cutoff diagonal channels as detector-root energies

Date: 2026-09-15.

Status: formal finite-cutoff factorization and same-basis trace readback.
The cutoff limit for either diagonal channel remains open.

## Consumer and result

The consumer is the healthy-`CompactLog`, detector-selected semi-local B5
readback for one selected owner and its finite visible-prime family. In
[`C1G8R3DiagonalRootLegNormalForm.lean`](../../ConnesWeilRH/Dev/C1G8R3DiagonalRootLegNormalForm.lean),
`g8MetricCutoffDetectorRootLeg` applies the selected detector's convolution
root after a chosen metric coframe and the literal source-compressed cutoff.
Lean proves for every diagonal coframe `L` that

```text
g8MetricCutoffChannel(L,L) = A_n† A_n
trace(g8MetricCutoffChannel(L,L)) = sum_i ||A_n e_i||^2
```

where `A_n` is the detector-root leg on the same named source basis. Thus the
survivor/survivor and boundary/boundary limits require uniform same-basis
Hilbert--Schmidt control and convergence of their respective root-leg columns;
finite-cutoff trace-class proofs alone do not provide that control.

The paired audit covers the root-leg owner, positive-square identity, and
trace-energy identity. Acceptance log:
`build-logs/1503_g8_diagonal_root_try3.log`;
`Build completed successfully (3961 jobs)`, zero `error:` lines, zero
`sorryAx`, and three `Quot.sound]` audit terminators.

## Boundary

This proves the exact finite-cutoff energy representation, not a uniform bound
or limit for the survivor and boundary energies. The detector-root leakage
and common-right square-sum estimates remain open, as do the total G8
trace-to-`qw` identity, signed remainder decay, detector-specific sign, C3,
and RH. The mixed-channel limit from record 1483 is independent and does not
imply either diagonal energy limit.
