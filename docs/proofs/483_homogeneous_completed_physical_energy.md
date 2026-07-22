# Proof 483: homogeneous completed physical energy

## Result

The result is good: Proof 482's homogeneous prolate commutator estimate is now
consumed by the actual completed finite-Euler corner.

Write

```text
P = (c-a)^2 * seminorm_0,0(g)^2
H = sum_i norm(A e_i)^2
D = detectorOperator(owner).
```

The new axiom-clean theorem proves

```text
norm(trace(completeCorner_S)) <= 6 * P + 2 * norm(D) * H.
```

The three compact boundary branches each contribute `2 * P`.  The prolate
branch is expanded as the bounded sandwich
`B [K_prol,D] R`, then Proof 482 supplies `2 * norm(D) * H`.  The trace is
decomposed only after the complete pair has been formed, and every summand
has an explicit trace-class owner.

## Verification

The final WSL2 ext4 acceptance batch passed:

```text
+------------------------------------------------------+-------+--------+
| target                                               | jobs  | result |
+------------------------------------------------------+-------+--------+
| Proof 483 source plus axiom audit                    |  3279 | PASS   |
| CCM25Concrete aggregate                              |  3758 | PASS   |
| full repository                                      |  3839 | PASS   |
+------------------------------------------------------+-------+--------+
```

The audit reports exactly `[propext, Classical.choice, Quot.sound]`.  The
source and audit introduce no `sorry`, `admit`, or new axiom declaration.

The theorem is not a Gate 3U proof: reducing `norm(D)` and `H` to the required
uniform support/Sobolev polynomial, proving the finite-S sign, Burnol's
identity, and `_root_.RiemannHypothesis` remain open.
