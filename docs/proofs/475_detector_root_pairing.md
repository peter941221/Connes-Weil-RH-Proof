# Proof 475: Detector root pairing

## Result

Proof 474 assembled the full outer, reflected, second-support, and prolate
response into one trace-class operator. Proof 475 identifies that operator
with the actual source Sonin commutator and factors the completed displacement
atom through the selected compact convolution root.

Write

```text
B = source quotient-band projection,
R = source Sonin projection,
C = selected compact convolution root,
W = C^dagger C,
U_z = translation by -z.
```

Lean first proves

```text
O_complete=[R,W].
```

Because `B R=0`, the opposite commutator orientation in the completed atom
has the exact factorization

```text
B[W,R]U_zB
  =(C B)^dagger (C R U_z B).
```

Consequently every completed diagonal coefficient is the single signed
root pairing

```text
<C B e_i,C R U_z B e_i>,
```

and the displacement trace is one `tsum` of these coefficients.

## Verification

The Windows source was copied one way into the Ubuntu 24.04 ext4 verification
mirror. The acceptance batch passed:

```text
+------------------------------------------------------+-------+--------+
| target                                               | jobs  | result |
+------------------------------------------------------+-------+--------+
| Proof 475 source plus focused audit                  |  3271 | PASS   |
| CCM25Concrete aggregate                              |  3750 | PASS   |
| full repository                                      |  3831 | PASS   |
+------------------------------------------------------+-------+--------+
```

The five audited theorems depend exactly on

```text
[propext, Classical.choice, Quot.sound]
```

The Proof 475 source and audit contain no `sorry`, `admit`, or new `axiom`.
The build emitted only existing repository linter warnings and the local WSL
proxy notice; the new Proof 475 module emitted no linter warning.

## Boundary

This factorization does not say that either raw whole-line leg `C B` or
`C R U_z B` is Hilbert--Schmidt. In particular, it must not be converted into
a two-leg Hilbert--Schmidt norm bound. Its purpose is to place the same compact
root on both sides of the complete signed response before any absolute value.

The next analytic producer must use the real-line support geometry of this
root pairing to control its complete scalar probability average uniformly in
the visible finite prime set. Renewal trace exchange, Gate 3U, the finite-S
sign, negative-owner integration, Burnol identity, and
`_root_.RiemannHypothesis` remain open.
