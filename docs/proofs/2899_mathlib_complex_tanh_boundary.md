# 2899 Mathlib complex tanh boundary

Mathlib provides `Complex.tanh` as a meromorphic function via
`Complex.meromorphicNFOn_tanh` in
`Analysis/SpecialFunctions/Trigonometric/Meromorphic.lean`. The definition is
the quotient of `sinh` by `cosh`, so the Route B Cauchy proof must establish
that the composed `cosh` denominator has no zeros on the selected disk before
using a holomorphic power-series interface.

This confirms the remaining obligation is a concrete denominator-zero exclusion
for the composed argument, followed by a local holomorphic restriction. It is
not discharged by the global meromorphic theorem.
