# Proof 482: homogeneous prolate commutator trace bound

## Result

The result is good: the fixed prolate commutator now has the detector
homogeneity required by the next physical-energy consumer.

Let

```text
A = sourceProlateHilbertSchmidtFactor(lambda)
K_prol = A^dagger A
D = detectorOperator(owner)
H = sum_i norm(A e_i)^2.
```

The new axiom-clean Lean owners prove

```text
abs(trace([K_prol,D])) <= 2 * norm(D) * H.
```

The transported form also proves the same estimate after any two bounded
finite-S sandwiches:

```text
abs(trace(L [K_prol,D] R)) <= 2 * norm(D) * H

norm(L) <= 1,  norm(R) <= 1.
```

This is the form required by the actual finite-Euler corner.  Its intended
instantiation is `L = radialSupportProjection lambda` and
`R = radialSupportProjection lambda`; the surrounding outer and second-support
branches remain in the same trace decomposition.

The proof expands the commutator into the two genuine trace products
`A^dagger D A` and `A^dagger D^dagger A`. Each product is bounded by the
geometric Hilbert--Schmidt estimate `sqrt(H) * sqrt(norm(D)^2 H)`, and the
two orientations are added only after their trace products have been formed.

This is the source of the factor `norm(D)`. Splitting the two orientations
into an orthogonal `L2` pair and applying `2ab <= a^2+b^2` loses that factor and
produces the spurious `(1 + norm(D)^2) H` term from Proof 481.

## Verification

```text
+------------------------------------------------------+-------+--------+
| target                                               | jobs  | result |
+------------------------------------------------------+-------+--------+
| Proof 482 source plus axiom audit                   |  3278 | PASS   |
| CCM25Concrete aggregate                              |  3757 | PASS   |
| full repository                                      |  3838 | PASS   |
+------------------------------------------------------+-------+--------+
```

The audit reports exactly

```text
[propext, Classical.choice, Quot.sound]
```

The source and audit contain no `sorry`, `admit`, or new `axiom`.

## Boundary

The bounded-sandwich owner is still only a component estimate. The next
consumer must expand the complete physical pair into its three compact
boundary branches plus this transported prolate branch, yielding the intended
`6P + 2 * norm(D) * H` trace majorant. This does not yet prove the canonical
Gate 3U bound, the finite-S sign, Burnol's identity, or
`_root_.RiemannHypothesis`.
