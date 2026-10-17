# Record 2745: corrected jet refinement decision probe

The corrected 2743 Fraction recurrence was evaluated over the same registered
representative cell, split into 1, 2, 4 and 8 equal rational subcells. Orders
4 and 7 were checked at each subcell's endpoints and midpoint against an
independent 100-digit mpmath derivative engine (90 sampled checks total).
All samples are contained. This remains diagnostic, not continuum proof.

At 1 versus 8 pieces, maximum order-4 interval width contracts from
112.8452 to 14.1089, and order-7 width from 15853485.65 to 1982668.71.
The sum of width times interval absolute maximum decreases from 0.0536588
to 0.0506468 (order 4) and from 926.2998 to 503.0041 (order 7).
The width loss is approximately linear in cell width at this location.

Decision: the corrected recurrence has a measurable refinement lever on this
cell; the large seven-order width alone is not a no-go. This does not justify
a global rollout: no all-region budget, Lean arithmetic replay, D4/D7 bound,
cardinal pin or RH result is established. Next work must bind rational jet
operations to the semantic recurrence and price the full finite region before
claiming that refinement meets the wired constants.
