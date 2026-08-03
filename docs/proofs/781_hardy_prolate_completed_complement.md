# Proof 781: Completed Hardy--Prolate complement row

## Result

Proof 780 made compact-root locality explicit in the two coordinates of the
completed Hardy--prolate row:

```text
Y_S W J = (T_S(I-E)[W,E]J, L[W,R]J).
```

Proof 781 proves that these are not two independently owned boundary objects.
Define the complete complement analysis

```text
Z = (I-E, L),
L^*L = E-R,
```

where `E` is the radial support projection and `R` is the source Sonin
projection. Lean proves

```text
Z^* Z = I-R,
Z R = 0.
```

Since `R J=J`, compact-root locality now has one exact source boundary form:

```text
Z W J = Z(W R-R W)J = Z[W,R]J.
```

Let `Lift(T_S)` act as the finite Euler transport on the outer coordinate and
as the identity on the Hardy/prolate coordinate. The complete right row is
therefore exactly

```text
Y_S W J = Lift(T_S) Z[W,R]J.
```

Consequently the literal target is

```text
Target_S = (X_S D_S)^* Lift(T_S) Z[W,R]J.
```

Every target coefficient and every ordinary named-basis trace diagonal is the
same one signed pairing of this expression.

## Why It Matters

The estimate now has one physical boundary input:

```text
compact root W
      |
      v
complete source commutator [W,R]
      |
      v
Z = (outer complement, Hardy/prolate analysis)
      |
      v
Lift(T_S) and one signed row pairing.
```

The existing completed-kernel expansion of `[W,R]` keeps the outer,
reflected second-support, and prolate branches coupled. Proof 781 therefore
gives the correct input object for a compact-root, weighted Toeplitz or
Wiener--Hopf estimate without turning its cancellation into a positive energy
sum.

## Scope

This is an exact operator, coefficient, and trace-diagonal normal form. It
does not prove a support-polynomial bound uniform in the visible finite set.
In particular, it does not authorize Cauchy--Schwarz, trace-norm, nuclear-norm,
or Hilbert--Schmidt bounds on the outer and Sonin coordinates separately.

Proof 781 does not prove Gate 3U, the finite-S sign, Burnol's identity, or
`_root_.RiemannHypothesis`.
