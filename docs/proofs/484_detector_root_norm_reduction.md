# Proof 484: detector norm reduction to the convolution root

## Result

The result is good: the homogeneous finite-Euler corner estimate now exposes
the actual selected convolution root instead of treating the detector norm as
an independent quantity.

For

```text
D_g = C_g^dagger C_g,
H   = sum_i norm(A_lambda e_i)^2,
P   = (c-a)^2 seminorm_0,0(g)^2,
```

Lean proves

```text
norm(D_g) <= norm(C_g)^2
norm(trace(completeCorner_S))
  <= 6 P + 2 norm(C_g)^2 H.
```

The first inequality is the operator-norm submultiplicativity bound applied
to the exact positive factorization `D_g = C_g^dagger C_g`.  The second keeps
Proof 483's homogeneous prolate term intact and substitutes the first bound
only after the complete trace estimate has been formed.

## Verification

The WSL2 Ubuntu 24.04 ext4 verification batch passed:

```text
+------------------------------------------------------+-------+--------+
| target                                               | jobs  | result |
+------------------------------------------------------+-------+--------+
| Proof 484 source plus axiom audit                    |  3279 | PASS   |
| CCM25Concrete aggregate                              |  3758 | PASS   |
| full repository                                      |  3839 | PASS   |
+------------------------------------------------------+-------+--------+
```

All three audited theorems depend exactly on
`[propext, Classical.choice, Quot.sound]`.  No `sorry`, `admit`, or new axiom
was added.

This is not yet the Gate 3U bound: the selected convolution root still needs
an explicit support/Sobolev estimate, and the finite-S sign, negative-owner
integration, Burnol identity, and `_root_.RiemannHypothesis` remain open.
