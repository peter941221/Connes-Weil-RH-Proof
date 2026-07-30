# Proof 632: complete one-prime numerator bound

## Result

For the empty suffix and every arithmetic visible prime, Proof 632 proves

```text
||A_(p,[])|| <= 24 ||detector||,

A_(p,S) = signedCompressedInteriorOwner_(p,S).
```

It follows along the genuine arithmetic-prime sequence that

```text
sqrt(q_p) ||A_(p,[])|| -> 0,
q_p ||A_(p,[])||^2 -> 0.
```

This is a bound for the complete numerator operator, not only for one chosen
column.

## Proof mechanism

The empty-suffix telescope has the exact form

```text
A_(p,[]) = -T_(p,[])^dagger M_[p] R_(p,[])^dagger.
```

The existing one-prime moment theorem gives

```text
||M_[p]|| <= 24 ||detector||,
```

and both Schur--Markov transition factors are contractions.  A generic
three-factor contraction lemma therefore preserves the constant `24`.
Finally `q_p -> 0` along the arithmetic primes, so the two weighted limits
follow by squeezing.

## Boundary

The result rules out growth of the complete numerator as the explanation for
an empty-suffix failure.  It does not compare the numerator with

```text
L_p^dagger N_p^dagger newFrame_(p,[]).
```

That denominator can still decay faster on approximate antiresonant vectors.
No Bone 1 quotient, Gate 3U sign, or RH conclusion follows.

## Lean owners

```text
ConnesWeilRH/Source/CCM25Concrete/
  ...AntiresonantInteriorOnePrimeNumeratorBound.lean
ConnesWeilRH/Dev/
  ...AntiresonantInteriorOnePrimeNumeratorBoundAudit.lean
```

## Verification

```text
+--------------------------------------+-------+--------+
| target                               | jobs  | result |
+--------------------------------------+-------+--------+
| one-prime numerator source           |  3399 | PASS   |
| focused three-declaration audit      |     - | PASS   |
| CCM25Concrete aggregate              |  3909 | PASS   |
| full repository                      |  3990 | PASS   |
+--------------------------------------+-------+--------+
```

All three audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.
