# 2904 Route B binding-cell refinement probe

The 256-cell interval enclosure is method-limited at its largest rectangle.
Replaying the same `mpmath.iv` construction with uniform angular refinement
gives the following upper bounds:

```text
cells   upper bound
  256   13.779036089117261069...
  512   13.435848468403776750...
 1024   13.280949289178591665...
 2048   13.218166491178113198...
```

This is a design probe, not a formal interval certificate.  It shows that the
gap to the Cauchy budget is enclosure dependency loss, so the next formal
attempt should split the binding angular cell before generating the remaining
Lean wrappers.

