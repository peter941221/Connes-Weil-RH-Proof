# 1859 - Windowed common-index budget

Date: 2026-09-23.

Status: Formally verified in Lean; quantifier reduction.

`exists_nat_windowed_geometric_budget_and_quadratic_tail` proves that any
nonnegative contraction factor `q < 1` can be combined with the independent
quadratic tail limit using one shared orbit index:

```text
2 * (q^n * sBase) * sCorrection <= budget
and
(6*pi)^2 * ((1/2)^(n+1) * C) < epsilon.
```

Together with record 1858, the intended instantiation is
`q = (baseUpper - baseLower) * seminorm(base)`. The theorem is conditional;
it does not prove the finite coefficient budget or detector-specific signed
positivity.

Verification: WSL focused build `window-budget-1859.log`; successful footer,
zero `error:` lines, zero `sorryAx`, and standard three-axiom audit output.
