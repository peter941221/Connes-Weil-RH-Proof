# 2201 — Route-A weighted-zero solve-enclosure preflight

Date: 2026-09-29

This record advances the active healthy-`CompactLog` B5 consumer:

```text
selected actual source owner -> same-owner qw >= 0 -> SourceRH -> Mathlib RH
```

The owner is the 30-node candidate used by records 2197–2200
(`gamma = 39.25244858548658`, `delta = 0.445`, `scale = 0.8`). The purpose is
to test whether interpolation-solve uncertainty can consume the direct-product
screen's signed-margin headroom.

## Method

Treat the `m=6400` interpolation matrix as `A0` and the measured
`m=3200`-to-`m=6400` matrix difference as a provisional matrix error `E`. For
each right-hand side, use

```text
||c-c0||inf <= ||A0^-1||inf ||E||inf ||c0||inf
                    / (1 - ||A0^-1||inf ||E||inf).
```

The resulting coefficient radii are propagated through the same direct-product
`M0/D2` screen as record 2197. The run was executed with the resource-aware
wrapper; the log is `results/20260929_2201_solve_preflight_pass4.log` and the
JSON artifact is `results/2201_weighted_zero_solve_enclosure_preflight.json`.

## Reading

```text
condition(A0)                         2.653731999607843e5
||A0^-1||inf                          6.770498945019070e17
||E||inf                               9.183896645769796e-25
Neumann factor                         6.217956255134857e-7
base coefficient radius               1.725905221940381e8
correction coefficient radius          3.536472115641207e11
max budget / signed margin             0.002204023875512719
binding sigma                          1.0
```

The corresponding unperturbed direct-product reading was `0.0022031972`, so
the provisional solve radius changes the ratio by about `8.27e-7` absolute.
The correction's large coefficient is visible, but it is not binding in this
screen.

## Status and nonclaims

Status: `SOLVE-ENCLOSURE-PREFLIGHT`; the direct-product branch remains
`GO-CANDIDATE / UNPRICED`.

This is not yet an outward certificate: the matrix difference is a quadrature
comparison, the physical integrals are sampled trapezoids, and the multiplicity
constant and signed-margin anchor are inherited screen inputs. The result only
removes solve instability as the likely local bottleneck. It does not transfer
the candidate to the complete source owner, prove the low-frequency shell, or
prove the producer gate.

Reproducible command:

```text
bash scripts/run_resource_aware_task.sh --workspace /home/peter/rh --class heavy \
  --log /home/peter/rh/results/20260929_2201_solve_preflight_pass4.log -- \
  env PROBE=1 python3 scripts/routea_weighted_zero_solve_enclosure_preflight_2201.py
```

