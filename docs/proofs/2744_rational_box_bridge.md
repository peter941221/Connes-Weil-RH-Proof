# Record2744: rational box bridge

`RationalBox2744` is a small type-level bridge for outward replay data. It
stores rational lower and upper endpoints with an orderedness proof, embeds to
`RealInterval2429`, and proves membership transfer and rational-box addition.
It is infrastructure only: no generated replay data or D4/D7 integral claim
is included.

The bridge now also proves membership preservation under nonnegative rational
scalar multiplication, which is the coefficient operation required by the
jet recurrence. It remains infrastructure rather than a completed replay.
