# 3090 - c3Sigma zero margin

The strict zero-frequency margin is now closed in Lean:

```text
c3Sigma 0 > 0
```

The proof has two exact steps. First, the half-anchored reciprocal series has
nonnegative gap terms

```text
1 / (n + 1/4) - 1 / (n + 1/2)
```

with a strictly positive zeroth term. Summability and the real-part map give
`Re(digamma(1/4)) < Re(digamma(1/2))`. Second, the Mathlib identity
`digamma(1/2) = -2 * log(2) - EulerGamma`, together with `log(pi) > 0`, gives
`Re(digamma(1/2)) < log(pi)`.

The audited theorem `c3Sigma_zero_pos` uses only
`[propext, Classical.choice, Quot.sound]` and no `sorryAx`.
