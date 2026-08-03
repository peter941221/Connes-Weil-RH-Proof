# Proof 783: Hermitian completed Hardy--prolate kernel

## Result

Proof 782 gives the literal target in one completed physical boundary form:

```text
Target_S = -A_S^dagger Q_S K_complete J,
K_complete^dagger = -K_complete.
```

Here `A_S` is the complete left Hardy--prolate row, `Q_S` is the lifted
completed-complement analysis, `J` is the source inclusion, and
`K_complete` is the same coupled outer/reflected-second-support/prolate
kernel as in Proof 782.

Proof 783 proves that the actual Hermitian target is exactly

```text
Hermitian(Target_S)
  = (1/2) [
      -A_S^dagger Q_S K_complete J
      + J^dagger K_complete Q_S^dagger A_S
    ].
```

For every source vector `x`, Lean also proves the diagonal readout

```text
<x, Hermitian(Target_S) x>
  = Re(-<A_S x, Q_S K_complete J x>).
```

## Why It Matters

The real Gate scalar is now attached to one directed completed physical
pairing before its real part is taken.

```text
complete physical kernel K_complete
                |
                v
      -A_S^dagger Q_S K_complete J
                |
                v
       Hermitian part / real diagonal
```

This rules out an invalid move in which the two adjoint terms, or the three
physical branches inside `K_complete`, are estimated separately.

## Scope

Skew-adjointness of `K_complete` is an orientation statement. It does not
make the Hermitian target zero, positive, trace bounded, or uniform in the
visible finite prime family.

Proof 783 does not prove the support-polynomial analytic Gate 3U estimate,
the finite-S sign, Burnol's identity, or `_root_.RiemannHypothesis`.
