# 2845 Route B phase-box bridge

For cell 4096, the direct phase soundness gate now passes for orders 0 through
7: the Python exported phase boxes contain the exact Lean
`phaseJetInterval2734` boxes.

The initial attempt hit Lean's default heartbeat limit while normalizing the
order-2 expression; it was an elaboration resource limit, not a failed
inequality. Exact Fraction diagnosis record 2846 independently confirms
containment. The theorem uses elevated proof heartbeat and recursion limits.

This closes the phase-box membership premise at one cell. It does not yet
prove the exponential seed box, global cell coverage, ledger domination,
SourceRH, or RH.
