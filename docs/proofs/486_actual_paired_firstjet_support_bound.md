# Proof 486: actual paired first-jet support bound

## Result

The result is good but still strictly below Gate 3U.  Proof 486 upgrades the
one-sided fixed-quotient estimate from Proof 485 to the actual paired
finite-Euler first jet on the global logarithmic carrier.

Write

```text
P        = (c-a)^2 * seminorm_0,0(owner.sourceTest)^2,
H_lambda = sum_i norm(sourceProlateHilbertSchmidtFactor(lambda)(e_i))^2.
```

For every visible finite prime-power family, Lean proves

```text
norm(trace(actualPairedFirstJet_S)) <= (12 + 4 H_lambda) * P.
```

The right side is independent of the finite family.

## Proof mechanism

Let `F` be the fixed physical commutator, `B` the source band projection,
`R` the source Sonin projection, and `A` the normalized causal finite-Euler
inverse.  The actual paired first jet is kept in its two genuine causal
orientations:

```text
actual paired first jet
  = -(R F B A R)
    + (R A^dagger B F R).
```

Every projection and `A` is contractive, while the adjoint satisfies

```text
norm(A^dagger) = norm(A) <= 1.
```

Proof 486 first makes the complete homogeneous physical bound stable under
arbitrary contractive left and right sandwiches.  It then applies that same
bound separately to the forward and reverse causal orientations and uses the
triangle inequality only after both orientations are complete trace-class
objects.

This separation is semantically necessary.  The causal inverse is not known
to be self-adjoint:

```text
A^dagger != A
```

so the proof does not replace the paired trace by twice the real part of one
orientation, and it does not use an unproved infinite-dimensional trace
cycle.

## Verification

The acceptance commands ran in the Ubuntu 24.04 ext4 verification environment
using the existing Lake cache.

```text
+------------------------------------------------------+-------+--------+
| target                                               | jobs  | result |
+------------------------------------------------------+-------+--------+
| Proof 486 source plus axiom audit                    |  3284 | PASS   |
| CCM25Concrete aggregate                              |  3760 | PASS   |
| full repository                                      |  3841 | PASS   |
+------------------------------------------------------+-------+--------+
```

All four audited Proof 486 theorems depend exactly on
`[propext, Classical.choice, Quot.sound]`.  The source and audit contain no
`sorry`, `admit`, or new axiom declaration.  The only non-repository notice
was the existing WSL localhost-proxy warning; replayed repository warnings
are unchanged, and the new Proof 486 source emits no linter warning.

## Boundary

This is not yet Gate 3U.  The theorem controls the actual paired first jet on
the global logarithmic carrier.  The final route still needs:

```text
global paired first jet
  -> exact source Sonin carrier transport
  -> quadratic Gram remainder bound
  -> canonical endpoint response
  -> Gate 3U.
```

In particular, no basis-independence slogan may replace the carrier proof.
The source inclusion must be shown to satisfy

```text
sourceInclusion sourceInclusion^dagger = sourceSoninProjection,
```

and the response must be absorbed by that projection on both sides before a
legal trace transport is used.  The finite-S sign, negative-owner integration,
Burnol identity, and `_root_.RiemannHypothesis` remain open.
