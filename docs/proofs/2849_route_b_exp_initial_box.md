# 2849 Route B tight exponential initial box

On cell 4096, the Lean phase bridge gives the phase range `[-3,-2]`. A direct
`Real.exp_bound` calculation proves the rational initial box
`[1/32, 1/4]` contains `transitionExp2731 x` for every point in the cell.

This is a materially tighter sound initial box than the generic `[0,1]` bound.
It is now suitable as the `e0` premise of record 2848. The theorem uses only
the standard axiom trio; it remains a one-cell result and does not by itself
close transition charges or the global ledger.
