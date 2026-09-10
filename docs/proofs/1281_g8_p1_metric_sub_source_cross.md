# 1281 — G8 P1 metric-minus-source cross expansion

Date: 2026-09-10.

Status: FORMAL Lean fact. This is an exact cutoff-level identity only; no
cutoff limit, sign, P2 remainder, `qw` readback, or RH claim is made.

Writing `E = finiteEulerMetricCoframe` and `J = sourceInclusion`, the leakage
cross channel from record 1280 satisfies, for every literal cutoff index,

```text
C_n† (E − J)† W_g J C_n
  = C_n† E† W_g J C_n − C_n† J† W_g J C_n.
```

The proof keeps the same source cutoff leg and detector owner throughout.  The
adjoint of a difference is discharged explicitly by the inner-product
characterization, and the remaining operator equality is closed by module
arithmetic.  Thus the leakage cross is aligned with the metric/source channel
and the source/source channel without introducing external subtraction data.

Verification: `1287_g8_p1_metric_sub_source_retry2.log`, green owning/Audit
build (3925 jobs), zero `error:`/`sorryAx`, standard three axioms only.
