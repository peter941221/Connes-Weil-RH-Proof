# Proof 782: Complete physical Hardy--prolate boundary kernel

## Result

Proof 781 reduces the literal Gate 3U target to one completed source
commutator:

```text
Target_S = A_S^* Lift(T_S) Z[W,R]J,
Z = (I-E,L),
Z^* Z = I-R.
```

Here `W=C_root^* C_root`, `E` is the radial support projection, `R` is the
source Sonin projection, and `A_S` is the complete left Hardy--prolate row.
The pre-existing physical boundary theorem has the exact orientation

```text
[W,R] = -K_complete.
```

`K_complete` is the one completed physical kernel containing the outer,
reflected second-support, and prolate contributions.  Substitution gives the
literal operator identity

```text
Target_S = -A_S^* Lift(T_S) Z K_complete J.
```

Lean also proves the coefficient and trace-diagonal forms:

```text
<x, Target_S y> = -<A_S x, Lift(T_S) Z K_complete J y>,
Tr(Target_S) = sum_i -<A_S e_i, Lift(T_S) Z K_complete J e_i>.
```

## Why It Matters

The route now reaches the actual three-branch physical boundary object
without reopening the two coordinates eliminated by Proof 781.

```text
compact root W
      |
      v
[W,R] = -K_complete
      |
      v
Z = (I-E,L)
      |
      v
Lift(T_S) and one signed Hardy--prolate pairing.
```

The sign comes from the commutator orientation only.  It is not a positivity
claim and it does not make any branch vanish.

## Scope

This is an exact operator, coefficient, and ordinary trace-diagonal normal
form.  It preserves the cancellation between the outer, reflected
second-support, and prolate contributions.

It does not supply a support-polynomial estimate uniform in the visible finite
set.  In particular, it does not permit separate trace-norm, nuclear-norm,
Hilbert--Schmidt, Cauchy--Schwarz, or triangle-inequality estimates of the
three physical branches.

Proof 782 does not prove Gate 3U, the finite-S sign, Burnol's identity, or
`_root_.RiemannHypothesis`.
