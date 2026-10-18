# 2809 Route B seed cell geometry

The 8192-cell grid used by the Route B ledger is represented exactly in Lean
by one dyadic formula. The cells are adjacent, cover `[1/4096, 1/2]`, and
every cell lies inside `(0,1)`. The 2808 complex rectangle bridge therefore
supplies membership for `seedJetComplexRect2808` at every cell index. This is
the seed jet object, not yet the D4/D7 evaluator functions `f4` and `f7` used
by 2807.

The evaluator membership port, per-cell corner-norm comparison, and charge
comparison to the 2804 ledger remain open.
No finite integral, exterior tail, cardinal pin, SourceRH, or RH claim is made.
