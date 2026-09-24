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

## Route-A impact

This removes the previous opaque physical-derivative-budget premise for the
source combination itself. The exact coefficient support and each source
basis derivative seminorm are now exposed as the only inputs to this bound.
Together with 1927, the variational path has a concrete objective: minimize a
finite-dimensional coefficient cost whose weighted source derivative sum
dominates the actual physical derivative.

## Remaining obligation

The bound is presently on the positive-variable encoded source test. The next
bridge must transport it through `compactLogTestOfWindow` to the selected
`CompactLogTest` derivative cost, then prove an explicit finite-basis cost
bound for the minimizer. Until that bridge and its margin are proved, Route A
has not entered parameter/margin Round 3 and no RH conclusion follows.

Evidence level: FORMAL for the source derivative budget; PROJECT CANDIDATE for
the CompactLog transport and signed margin.
