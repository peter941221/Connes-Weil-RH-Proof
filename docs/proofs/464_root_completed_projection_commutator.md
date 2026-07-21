# Proof 464: root-completed projection commutator

## Result

The centered finite-Euler common right leg is rewritten exactly as a
transport/projection commutator:

```text
commonRightLeg
  = C_g P (A_S - I) B
  = C_g P [A_S, B] B.
```

The proof uses only

```text
P B = 0,
B^2 = B.
```

The first equality is Proof 435's centered causal crossing.  The second
equality removes the identity component before any renewal expansion or
absolute value.  This is the correct object for a future compact-support
commutator estimate.

The complete root-homogeneous first-jet owner now reads

```text
sourceRootCompletedFiniteEulerCorner
  = (C_g B)^dagger C_g P [A_S,B] B.
```

Both convolution roots and both band projections remain inside this single
signed pairing.

Because `A_S` is contractive and `B` is an orthogonal projection, Lean also
proves the family-uniform operator-norm bound

```text
norm([A_S,B]) <= 2.
```

This removes the Euler condition number from the commutator norm.  It is not
a Hilbert--Schmidt or trace-norm estimate; the boundary-localized Schatten
factor remains necessary.

## Boundary

Proof 464 is an exact operator bridge.  It does not assert that the
commutator is Hilbert--Schmidt, trace class, uniformly bounded in the visible
prime set, or signed.  Gate 3U, the finite-S sign, Burnol's identity, and
`_root_.RiemannHypothesis` remain open.
