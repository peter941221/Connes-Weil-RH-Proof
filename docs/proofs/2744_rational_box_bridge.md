# Record2744: rational box bridge

`RationalBox2744` is a small type-level bridge for outward replay data. It
stores rational lower and upper endpoints with an orderedness proof, embeds to
`RealInterval2429`, and proves membership transfer and rational-box addition.
It is infrastructure only: no generated replay data or D4/D7 integral claim
is included.

The bridge now also proves membership preservation under nonnegative rational
scalar multiplication, which is the coefficient operation required by the
jet recurrence. It remains infrastructure rather than a completed replay.

Rational-box subtraction is now included, with endpoints `a.lo-b.hi` and
`a.hi-b.lo` and a proof that membership is preserved. This covers the phase
recurrence's subtraction operation.

The bridge now proves that rational-box addition and subtraction embed exactly
as the corresponding `RealInterval2429` operations, so replay arithmetic can
be consumed by existing semantic interval theorems.

The bridge now supports recursive finite sums with membership preservation,
matching the existing Lean jet sum interface. This is the aggregation step
needed before a rational recurrence can feed the semantic jet theorem.

The replay bridge now includes rational-box multiplication with exact
compatibility to `RealInterval2429.mul`; membership follows from the existing
interval multiplication theorem.

The bridge now supports positive endpoint inversion, completing the basic
operation set required by denominator reciprocal jet recurrence.
