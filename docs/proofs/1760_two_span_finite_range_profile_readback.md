# 1760 — Two-span finite-range profile readback

Date: 2026-09-21

The theorem `twoSpan_p2Aggregate_eq_archimedean_plus_rangeProfile` rewrites
the `p2AggregateValue` of the genuine two-span owner
`spanObj [A,B] [1,-lam]` as the Archimedean term plus the exact finite visible
prime-power range obtained from the common support radius `R`. The square has
support in `(-2R,2R)`, so the range is `range (ceil(exp(2R)) + 1)`.

The proof propagates support through the real span and Hermitian convolution
square, then consumes the existing range-profile identity. It introduces no
sign, symmetry, numerical, or RH assumption.

Verification: `shortest_route_20260921_range_readback_v14.log`, build
completed successfully (3784 jobs), zero `error:` lines, zero `sorryAx`, and
standard three-axiom Audit output.
