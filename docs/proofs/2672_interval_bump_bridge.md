# Record 2672 - interval bump and trigonometric bridges

**Verdict: MATHEMATICAL-BUMP-AND-TRIG-HULL-BRIDGES-PASS; evaluator certificate remains open.**

The 2242 evaluator bounds the compact-support bump by first enclosing
`q = 1 - (x / radius)^2`, then enclosing `-30 / q`, and finally applying the
monotone real exponential. This record formalizes that composition in Lean for
the non-singular branch `0 < q`.

The new declarations in
`ConnesWeilRH/Dev/C1RouteAIntervalAlgebra.lean` are:

- `RealInterval2429.mem_invPositive`: a positive interval encloses the
  reciprocal of every point it contains;
- `RealInterval2429.mem_exp`: monotonicity of `Real.exp` preserves interval
  membership;
- `RealInterval2429.mem_expNegThirtyDiv`: the interval expression
  `exp((-30) * q⁻¹)` encloses `exp(-30 / q)`.
- `RealInterval2429.abs_sub_chord_le_widthSq_eighth`: when `|f''| <= 1`,
  the error from the line joining endpoint values is at most `width^2 / 8`;
- `RealInterval2429.mem_sinEndpointHull` and
  `RealInterval2429.mem_cosEndpointHull`: sine and cosine on a real angle
  interval lie between their endpoint minimum and maximum, expanded by
  `width^2 / 8`.

The proof uses only ordered-field reciprocal monotonicity, the existing
outward interval multiplication theorem, `Real.exp_le_exp`, and Mathlib's
convexity criterion from the sign of the second derivative. For the chord
bound, `f + x^2/2` is convex and `f - x^2/2` is concave when `|f''| <= 1`;
the endpoint chord gives the exact `width^2 / 8` allowance. The source
compiles in the active Linux Mathlib v4.30 environment with exit code 0. The
axiom audit reports the project standard trio
`[propext, Classical.choice, Quot.sound]`; no `sorryAx` is introduced.

This closes mathematical bump composition and exact-real trigonometric hull
sub-obligations. It does not prove MPFR directed rounding, binary64 endpoint
conversion, the full 2242 evaluator contract, the live-owner identity,
`chargeRest`, the signed infinite-xi tail, Producer GO, SourceRH, or RH.

Evidence:

- `ConnesWeilRH/Dev/C1RouteAIntervalAlgebra.lean`
- `ConnesWeilRH/Dev/C1RouteAIntervalAlgebraAudit.lean`
- `scripts/routea_weighted_zero_zero_count_certificate_2242.py`
