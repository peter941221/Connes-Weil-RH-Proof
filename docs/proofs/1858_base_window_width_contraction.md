# 1858 - Retain the base support-window width

Date: 2026-09-23.

Status: Formally verified in Lean; geometric-bound strengthening.

`C1P2ConvolutionSeminormBound.lean` now includes
`rawFactorSeminorm_le_geometric_bound_of_base_window`. The estimate accepts
an explicit support interval `[a,b]` for the selected base and gives the
contraction factor

```text
(b - a) * SchwartzMap.seminorm(base).
```

The correction factor remains on its existing `[-1,1]` owner, so the outer
factor remains `2`. This strictly strengthens the previous hard-coded
`2 * seminorm(base)` interface whenever the base was constructed in a
narrower window. It is a formal bound only; the numerical inequality
`(b-a) * seminorm(base) < 1` remains to be certified for the selected Mellin
coefficients.

Verification: WSL focused build `window-bound-1858.log`; successful footer,
zero `error:` lines, and the new audit declaration has only
`[propext, Classical.choice, Quot.sound]`.
