# 2834 Route B source cell envelope

This record defines source-side norm and charge slots directly from the exact
2734 interval jet endpoint maximum and the 2833 cell width. It is a genuine
intermediate artifact for the evaluator port.

The charge includes the factor `4` used by the 2804 generator:
`charge = 4 * width * endpointAbsMax`.

It does not prove that these source-side charges are below the 2804 ledger
charges.

The remaining bridge is semantic, not merely arithmetic: 2804 was generated
by the Python `p3.seed_jet` evaluator, while 2834 uses Lean
`seedTransitionJetInterval2734`. A per-cell equality or directed enclosure
between these two evaluators is still required before ledger domination can
be claimed.

Structural audit: both implementations use the same derivative-jet recursion:
`U = x`, `V = 1-x`, phase `1/U - 1/V`, exponential `exp(-phase)`, and the
final quotient `E/(1+E)`. This supports a possible semantic bridge, but is not
yet a Lean equality or directed-rounding theorem.
