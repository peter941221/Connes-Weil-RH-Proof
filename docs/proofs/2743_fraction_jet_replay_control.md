# Record2743 corrected Fraction jet replay control

The original PASS is withdrawn. Its coordinate inputs collapsed each cell to
one point, its exponential box used the phase endpoints in reverse order,
and its exponential recurrence used choose(n,j+1) rather than choose(n-1,j).
Orderedness and finiteness alone did not detect these errors.

The corrected replay matches the 2734 definitions: coordinate intervals are
[a,b] and [1-b,1-a]; exp lower uses phase.lo and exp upper uses phase.hi;
reciprocal order n uses choose(n,j+1), while exponential order n uses
choose(n-1,j). Two cells and orders 0..7 remain ordered and finite.
An independent mpmath differentiation engine at 100 decimal digits checks
both endpoints and the midpoint at every order: 48/48 sampled containments.
Sampling is a diagnostic and does not prove continuum containment.

The corrected order-7 widths are about 7.93e6, replacing the invalid 4.1e-10
readings. These widths expose actual interval dependency loss. No Lean replay,
full-region integral, D4/D7, pins or RH certificate follows from this control.
