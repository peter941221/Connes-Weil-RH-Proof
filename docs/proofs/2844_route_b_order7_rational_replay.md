# 2844 Route B order-7 rational replay

For cell 4096, the Python stage boxes from record 2840 were converted to exact
rational `RationalBox2744` literals. Lean then replayed the order-7 exponential,
replay-owned denominator, reciprocal, and product recurrences.

The theorem `routeB_replay_transition_contained2844` proves that the resulting
transition box is contained in the exported Python transition box. The Linux
build completed 3658 jobs. The paired audit has only
`propext`, `Classical.choice`, and `Quot.sound`.

This closes arithmetic replay containment for orders 4 and 7 at one cell. It
does not yet prove that the phase boxes contain the actual Lean derivatives,
does not cover all 8192 cells, and does not close ledger domination, SourceRH,
or RH.
