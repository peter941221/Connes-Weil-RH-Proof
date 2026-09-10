# 1280 — G8 P1 literal-cutoff leakage/source cross

Date: 2026-09-10.

Status: FORMAL Lean fact. No cutoff limit, sign, P2 remainder, `qw` readback,
or RH claim is made.

For the selected owner, scale, finite family, and named source/global bases,
the literal cutoff channel is defined by the same generic metric-channel
owner, with the physical leakage coframe on the left and the source inclusion
on the right:

```text
LeakCross_n = C_n† L† W_g J C_n,
    C_n = J† A_n,
    L = finiteEulerMetricCoframe − J.
```

Lean proves the displayed operator equality by definitional reduction and
supplies a concrete Hilbert–Schmidt pair, hence a
`PositiveTrace.IsTraceClassAlong` certificate on the same source basis.  The
transpose `J† W_g L` channel receives the matching trace-class owner for the
ordinary-trace adjoint ledger.  Together with record 1279, this pins the
literal cutoff channel to the uncut owner `L† W_g J` without replacing the
cutoff by an uncut operator.

The required analytic comparison between the cutoff trace and the uncut
finite-prime response is still open; no P2 remainder or P3 limit is supplied.

Verification: `1284_g8_p1_cutoff_leakage_cross_retry.log`, green owning/Audit
build (3925 jobs), zero `error:`/`sorryAx`, standard three axioms only.
