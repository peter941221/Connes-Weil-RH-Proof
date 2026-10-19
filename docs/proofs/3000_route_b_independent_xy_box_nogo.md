# 3000 Route B independent x/y box no-go

The tightened theta rectangle from record 2996 cannot prove the target doubled-
argument rectangle if its real and imaginary coordinates are treated as
independent variables.

The box is

```text
x in [0.0255, 0.0260]
y in [-0.0430, -0.0425]
```

For

```text
D   = (1 - x^2 + y^2)^2 + (2xy)^2
Nre = 4x(1 - x^2 + y^2) - 8xy^2
Nim = 4y(1 + x^2 + y^2)
```

the four corners give the following argument coordinates:

```text
(x,y) = (0.0255, -0.0430):  Re = 0.10150109, Im = -0.17201639
(x,y) = (0.0255, -0.0425):  Re = 0.10151412, Im = -0.17002348
(x,y) = (0.0260, -0.0430):  Re = 0.10349394, Im = -0.17202962
(x,y) = (0.0260, -0.0425):  Re = 0.10350723, Im = -0.17003657
```

The target rectangle is

```text
Re in [0.1023183624, 0.103]
Im in [-0.1715760949, -0.1712505046]
```

Several corners violate the target. Therefore an independent-coordinate
interval proof is unsound or must widen beyond the committed target and
re-price the downstream budget.

Decision: do not continue with corner-based `nlinarith` bounds. Preserve the
theta correlation by proving the rational inequalities directly from the
shared `sin(theta)` and `cos(theta)` expressions, or use a dependency-aware
Taylor/affine enclosure.
