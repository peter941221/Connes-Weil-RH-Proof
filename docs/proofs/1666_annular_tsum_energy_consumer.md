# 1666 — Annular total-energy consumer

The annular root operator introduced in 1665 now has a second consumer form.
For a fixed support radius `N`, assume that every later annulus has a uniform
bound on its complete source-basis square sum:

```text
sum' i, ||Annular(N,n)(sourceBasis i)||^2 <= B.
```

The fixed-annulus summability theorem supplies the nonnegative summands, so
every finite sub-sum is bounded by that total sum.  The earlier annular
criterion then gives square-summability of the limiting source-compressed
root columns.

This is a formal interface change, not an analytic estimate.  The remaining
producer obligation is now explicitly a radius-uniform total annular-energy
bound (equivalently a suitable Hilbert–Schmidt/trace estimate).  No RH claim
is made.
