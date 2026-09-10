# 1282 — G8 P1 literal metric cutoff positivity

Date: 2026-09-10.

Status: FORMAL Lean fact. This proves positivity at each fixed cutoff only;
it does not prove a cutoff limit, finite-prime readback, P2 remainder decay,
or an RH conclusion.

For the fixed selected detector, finite Euler family, source scale, and named
cutoff leg, write

```text
C_n = J† A_n,       E = finiteEulerMetricCoframe.
```

The literal metric operator is definitionally

```text
g8PhysicalMetricCutoffOperator_n
  = (E C_n)† W_g (E C_n).
```

Since the selected convolution detector `W_g` is positive, its adjoint
conjugation gives positivity of the complete cutoff metric operator.  The
proof uses the same owner and cutoff as the P1 channel ledger; no uncut
operator is substituted.

Verification: `1288_g8_p1_metric_positive.log`, green owning/Audit build
(3926 jobs), zero `error:`/`sorryAx`, standard three axioms only.
