# 3091 - joint-symbol continuity

Continuity at zero is now fully instantiated for the actual joint symbol.

The finite prime Poisson terms and their owner-specific finite sum are
continuous at zero. The archimedean term `c3Sigma` is continuous because the
existing `hasDerivAt_digamma_criticalQuarterLine` theorem supplies a genuine
derivative of `Complex.digamma` at the quarter-line boundary point. Composing
that continuity with the real-frequency affine map and `Complex.re` gives
`c3Sigma_continuousAt_zero`.

The audit uses only `[propext, Classical.choice, Quot.sound]` and no `sorryAx`.
