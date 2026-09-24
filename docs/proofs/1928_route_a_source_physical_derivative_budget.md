# 1928 — Finite-window source derivative budget

## Result

The new leaf
`ConnesWeilRH/Dev/C1P2PhysicalDerivativeSeminormBound.lean` proves, for the
actual finite-window source combination and its exact finite support, the bound

```text
seminorm(deriv (encode (sum c_p p)))
  <= sum_{p in support(c)} ||c_p|| * seminorm(deriv (encode p.test)).
```

The proof is an unconditional finite-sum triangle estimate on the committed
source owner. It does not enlarge the visible-prime set, assume the desired
gate sign, or use `qw >= 0`.

The paired audit builds successfully with the standard axiom set
`[propext, Classical.choice, Quot.sound]` and no `sorryAx`.

The same leaf also proves the log-pullback transport: the first derivative
seminorm of `compactLogTestOfWindow g` is bounded by the source derivative
seminorm with one physical-coordinate weight. The weight is forced by the
chain rule `d/du g(exp u) = exp(u) * g'(exp u)` and is discharged using the
committed `norm_pow_mul_le_seminorm` theorem.

## Route-A impact

This removes the previous opaque physical-derivative-budget premise for the
source combination itself. The exact coefficient support and each source
basis derivative seminorm are now exposed as the only inputs to this bound.
Together with 1927, the variational path has a concrete objective: minimize a
finite-dimensional coefficient cost whose weighted source derivative sum
dominates the actual physical derivative.

## Remaining obligation

The remaining bridge is now only the finite-basis minimization and its
parameter-uniform numerical margin. The source-to-`CompactLogTest` derivative
transport itself is formal. Until the minimizer's explicit bound and its
signed margin are proved, Route A has not entered parameter/margin Round 3 and
no RH conclusion follows.

Evidence level: FORMAL for the source derivative budget; PROJECT CANDIDATE for
the CompactLog transport and signed margin.
