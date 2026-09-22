# 1852 - Common index for budget and tail

Date: 2026-09-22.

Status: Formally verified in Lean 4; producer-side quantitative reduction.

The theorem `exists_nat_geometric_budget_and_quadratic_tail` proves that,
under nonnegative base/correction factors, strict base contraction, positive
harmonic budget, nonnegative correction tail constant, and positive epsilon,
one natural index simultaneously satisfies

```text
2 * ((2 * sBase)^n * sBase) * sCorrection <= budget
(6*pi)^2 * ((1/2)^(n+1) * C) < epsilon
```

The proof intersects the two eventual-at-infinity neighborhoods. It is the
common-index bridge between record 1851's all-index healthy orbit assembly and
the geometric harmonic-budget reduction. It does not prove strict contraction
or the detector-specific positivity estimate.

Verification: paired Audit target in
`C1P2ConvolutionSeminormBoundAudit`; standard axioms only and no `sorryAx`.
