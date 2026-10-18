# 2856 Route B sharper exponential initial box

Splitting the exponents into pieces with absolute value at most one allows
Mathlib's `Real.exp_bound` to be applied legally. Taylor order 30 proves the
needed segment estimates, and the cell-4096 phase enclosure then yields the
Lean-certified initial box `[1/16,1/8]` for `transitionExp2731`.

This is the tighter e0 candidate for the next replay reprice.
