# 1279 — G8 P1 leakage/source Euler cross owner

Date: 2026-09-10.

Status: FORMAL Lean fact. No cutoff limit, sign, P2 remainder, `qw` readback,
or RH claim is made.

The finite-Euler metric coframe is split into the source inclusion and its
physical leakage,

```text
E = J + L,       L = finiteEulerMetricCoframe − sourceInclusion.
```

Lean identifies `L` exactly with `sourcePhysicalCoframeLeakage`. Consequently
the already existing uncut target response is proved to be

```text
finiteEulerTargetCommutatorResponse = L† W_g J.
```

This is the correct same-owner candidate for the finite-prime Euler cross
term. It does not yet identify the literal cutoff sandwich
`C_n† L† W_g J C_n` with its uncut trace; that remains the analytic P1/P3
cutoff-to-endpoint bridge.

Verification: `1282_g8_p1_leakage_cross_owner_retry3.log`, green owning/Audit
build (3925 jobs), zero `error:`/`sorryAx`, standard three axioms only.
