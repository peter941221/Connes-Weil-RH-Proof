# 2598 interval propagation

`2598` proves the generic logical propagation used by the 2338 certificate:
entry rectangles for a candidate inverse and the analytic moment matrix imply
a rectangle for each entry of `I - X * A`.

The proof uses the previously audited rectangle operations:
complex multiplication, finite summation, and subtraction. It does not assert
that the 2338 rectangles contain the analytic integrals, and it does not assert
that the propagated rectangles satisfy the numerical `2595` bounds.

The same file also proves `norm_le_rectL1Upper2598`, converting a rectangle
enclosure into a complex-norm upper bound using the endpoint maximum of the
real and imaginary coordinates. The remaining 2595 comparison is a separate
finite rational certificate.
