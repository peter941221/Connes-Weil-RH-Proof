# Proof 485: root convolution support norm

## Result

The result is good: the remaining selected-root norm in Proof 484 is now
bounded by the same compact-support polynomial as the three physical boundary
branches.

For a source test supported in `[a,c]`, Lean proves

```text
norm(rootConvolution(owner))
  <= (c-a) * seminorm_0,0(owner.sourceTest).
```

Write

```text
P        = (c-a)^2 * seminorm_0,0(owner.sourceTest)^2,
H_lambda = sum_i norm(sourceProlateHilbertSchmidtFactor(lambda)(e_i))^2.
```

Consuming Proof 484 on the exact same owner, finite prime-power family, and
fixed-quotient corner gives

```text
norm(trace(completeCorner_S)) <= (6 + 2 H_lambda) * P.
```

The right side contains no `FinitePrimePowerFamily`.  Thus this completed
fixed-quotient corner is uniformly bounded over the visible finite set once
the existing summable prolate-factor witness is fixed.

## Proof mechanism

The root estimate follows the actual Plancherel multiplier definition:

```text
root convolution
  = inverse Fourier * multiplication by Fourier(g*) * Fourier
                         |
                         v
operator norm <= Fourier(g*) L-infinity norm
              <= g* L1 norm
              <= (c-a) seminorm_0,0(g*)
              =  (c-a) seminorm_0,0(g).
```

The first step uses Mathlib's exact operator-norm preservation lemmas for
precomposition by a linear isometric equivalence and postcomposition by a
linear isometry.  The support step rewrites the whole-line integral as an
integral over `[a,c]`; the CCM25 involution reflects the interval and
preserves the order-zero Schwartz seminorm.

## Verification

Commands were run in the Ubuntu 24.04 ext4 verification environment using the
existing Lake cache.

```text
+------------------------------------------------------+-------+--------+
| target                                               | jobs  | result |
+------------------------------------------------------+-------+--------+
| Proof 485 source plus axiom audit                    |  3280 | PASS   |
| CCM25Concrete aggregate                              |  3759 | PASS   |
| full repository                                      |  3840 | PASS   |
+------------------------------------------------------+-------+--------+
```

All eight audited Proof 485 theorems depend exactly on
`[propext, Classical.choice, Quot.sound]`.  The source and audit add no
`sorry`, `admit`, or new axiom declaration.  The only non-repository notice
was the existing WSL localhost-proxy warning; replayed repository warnings
are unchanged, and the new Proof 485 source emits no linter warning.

## Boundary

This is not yet Gate 3U.  The bounded object is the one-sided
`sourceRootCompletedFixedQuotientCorner`, not the canonical endpoint response
used by the final route.  A same-object endpoint identification or complete
endpoint assembly is still required before this uniform corner estimate can
be consumed as Gate 3U.  The finite-S sign, negative-owner integration,
Burnol identity, and `_root_.RiemannHypothesis` remain open.
