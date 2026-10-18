# 2877 Route B D4 residual endpoint identities

Writing the centred residual as `H(y,z)` with `y = t^2`, exact symbolic
specialisation gives:

```text
H(0,z) = 21 - 4 z
H(1,z) = 128 z (3 z^2 - 2)
H(0,2) = 13
H(1,1) = 128
```

These are the endpoint values on the logistic owner path. They provide exact
positive anchors for the outer regions. The endpoint identities alone do not
prove the interior sign; the remaining obligation is a monotonicity or
interval enclosure for `H(y,z(y))`.
