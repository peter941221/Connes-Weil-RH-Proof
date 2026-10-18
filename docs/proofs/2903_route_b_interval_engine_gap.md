# 2903 Route B interval-engine gap

Status: OPEN engineering/mathematical prerequisite; no Producer GO and no RH
claim.

The 2889 artifact now exports 320 cell rectangles with high-precision
`re_lo/re_hi/im_lo/im_hi` endpoints.  The existing `ComplexRect2427` and
`norm_le_of_rect_mem_2453` infrastructure consumes a proved rectangle
membership, and record 2902 adds the tighter square-norm consumer.

The missing premise is the membership itself for the analytic Route-B
function on one angular cell.  A repository search of the pinned Mathlib
checkout found no reusable outward interval implementation for the required
composition of complex exponential, reciprocal, division, and `tanh`.
Mathlib supplies the analytic functions and maximum-modulus theorem, but not
the numerical interval certificate that turns the Python `mpmath.iv` output
into Lean inequalities.

Decision:

1. Do not generate 319 more Lean wrappers before a single-cell interval engine
   closes.
2. The next Route-B experiment is one formal cell covering the chain
   `t -> 2*t/(1-t^2) -> exp -> quotient -> H` with directed rational bounds.
3. If that cell cannot close with a named margin, reactivate Route A under the
   existing `FROZEN_MAINTENANCE` rule; this record is not itself a Route-B
   failure or a Producer GO.

