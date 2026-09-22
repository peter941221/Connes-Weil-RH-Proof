# 1840 - Eventual geometric budget under strict base contraction

Date: 2026-09-22.

Status: Formally verified in Lean 4; producer-side conditional reduction only.

Module: `ConnesWeilRH.Dev.C1P2ConvolutionSeminormBound`.

The theorem `exists_nat_geometric_budget_of_base_contraction` proves:

```text
0 <= sBase
0 <= sCorrection
2 * sBase < 1
0 < budget
```

imply that there exists `n : Nat` with

```text
2 * ((2 * sBase)^n * sBase) * sCorrection <= budget.
```

The proof uses the standard limit `(2 * sBase)^n -> 0` and multiplies it by
the fixed nonnegative correction factor. It supplies the exact quantitative
step needed after the existing `rawFactorSeminorm_le_geometric_bound`
theorem.

This does not prove the RH producer. The selected `OrbitG8Geometry` must
still realize the selected orbit index while preserving interpolation,
square-zero, tail, visible-prime, and Archimedean-margin obligations. The
repository also has not yet proved the required strict inequality
`2 * seminorm(base) < 1` for the constructor-selected base.

Verification: focused Lake build log `1840_convolution_budget_final3.log`,
zero `error:` lines; paired Audit target built; no `sorryAx` claimed.
