# 1006 - Gate 2 spectral summability closure

## Verdict

The convergence half of Gate 2 is closed unconditionally for every
`CompactLogTest`. The Riemann-Weil explicit-formula equality is not proved, and
RH is not claimed.

## Dependency reduction

```text
completed-xi kernel moment
  -> exp(O(R log R)) bound on doubled Jensen circles
  -> analytic zero-multiplicity mass <= K * 3^n
  -> compact-log Laplace decay <= C * 4^(-n)
  -> absolute spectral summability because 3 < 4
```

The strict inequality matters. Replacing the multiplicity bound by an
`O(4^n)` estimate would cancel the available quadratic decay and would not
prove convergence.

## Lean ownership

- `C1XiGrowth.completedRiemannXiKernelMoment_le` controls both ends of the
  theta-kernel integral using direct and inverse Gamma moments.
- `C1SpectralWeil.spectralHeightMultiplicity_le_finiteHeightMultiplicity`
  preserves analytic `xiMultiplicity` while embedding one dyadic shell into a
  symmetric-height zero window.
- `C1SpectralSummability.finiteHeightMultiplicity_dyadic_le` combines the
  dyadic xi bound with Jensen's divisor inequality.
- `C1SpectralSummability.spectralSummableProp` proves absolute convergence for
  every compact-log test.
- `C1SpectralSummability.gate2ExplicitFormula_iff` removes convergence from the
  active Gate 2 bottom without assuming the remaining formula equality.

The reduced consumer is exactly

```text
gate2ExplicitFormula F
  <-> C1SameOwnerWeil.psi F = C1SpectralWeil.spectralWeilValue F
```

Both sides use the same `CompactLogTest` owner. The remaining equality is a
genuine explicit-formula/positive-trace theorem, not a definition or a
convergence obligation.

## Verification

The isolated ext4 import-facing build of
`ConnesWeilRH.Dev.C1SpectralSummabilityProbe` completed 3532 jobs. Every audited
declaration depends only on `[propext, Classical.choice, Quot.sound]`; the
changed proof modules contain no `sorry`, `admit`, new `axiom`, or `sorryAx`.
