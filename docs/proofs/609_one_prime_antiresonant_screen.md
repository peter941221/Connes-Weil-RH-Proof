# Proof 609: one-prime antiresonant screen

## Result

The result is good for eliminating one obstruction branch, but it does not
prove the quotient required by Bone 1.

For the empty suffix,

```text
reducedRow(p, []) * newFrame([])
  = -transition(p, [])^dagger * onePrimeBoundaryMomentColumn(p).
```

If `p` is prime and `q_p = p^(-1/2)`, then

```text
||reducedRow(p, []) * newFrame([])||
  <= 196 q_p ||detector||.
```

The operator norm therefore tends to zero along the arithmetic primes.  The
same is true after evaluation on every uniformly bounded moving source
sequence.

## Why it matters

Proof 608 turns Bone 1 into a numerator-versus-denominator question.  Proof
609 shows that the one-prime numerator is `O(q_p)`, while the scalar part of
the denominator is `O(sqrt(q_p))`.  The scalar power is favorable.

The unresolved issue is geometric:

```text
ambientLoss(p)^dagger
  = sqrt(q_p) / (1 + q_p) * (I + U_(log p)).
```

The factor `I + U_(log p)` has an approximate antiresonant kernel.  Its norm
can be much smaller than its scalar prefactor, so numerator decay alone does
not imply a bounded quotient.

## Boundary

This excludes the nondecaying-numerator obstruction on the `S = []`
new-frame column only.  It does not prove denominator comparability, a
factorization, Bone 1, Gate 3U, the finite-S sign, Burnol's identity, or RH.

## Verification

```text
focused source build: 3380 jobs, PASS
import-facing audit:  PASS
audited declarations: 4
axioms: [propext, Classical.choice, Quot.sound]
```
