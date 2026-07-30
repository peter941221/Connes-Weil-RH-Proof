# Proof 636: single-channel right co-defect

## Result

Let

```text
C_(p,S) = L_p^dagger newFrame_(p,S),
T_(p,S) = suffixEulerFrameTransition_(p,S).
```

Lean proves

```text
C_(p,S)^dagger C_(p,S) = I - T_(p,S)^dagger T_(p,S),

||C_(p,S)x||^2
  = Re <(I - T_(p,S)^dagger T_(p,S))x,x>.
```

Combining this Gram identity with Proof 634 gives an exact restatement of
Bone 1:

```text
exists C >= 0, forall route-valid (p,S), forall x,
  ||signedInterior_(p,S)x||^2
    <= C^2 Re <(I-T_(p,S)^dagger T_(p,S))x,x>.
```

## Derivation

The normalized Euler transport is normal.  Its two orientations are
polynomials in commuting translations by `log p` and `-log p`.  The existing
ambient co-defect factorization therefore gives

```text
L_p L_p^dagger = I - F_p^dagger F_p.
```

The generic rectangular right-defect identity contains an old-range boundary
square.  The actual Schur owner stores

```text
F_p newFrame_(p,S) = oldFrame_(p,S) T_(p,S),
```

so that boundary term is zero.  Compression by the new frame yields the Gram
identity.

```text
 ambient right defect I-F_p^dagger F_p
                    |
                    v  compress by newFrame
 transition defect I-T_(p,S)^dagger T_(p,S)
                    ^
                    |  exact Gram identity
 raw loss column C_(p,S)^dagger C_(p,S)
```

## Boundary

The right co-defect is a positive denominator.  Positivity does not control
the signed numerator.  Proof 636 names the missing inequality; it does not
prove it.

Proof 569's orientation guard remains active.  The right co-defect does not
cancel transition skew, endpoint residual, or row skew without a new source
identity.

## Verification

```text
+--------------------------------------+-------+--------+
| target                               | jobs  | result |
+--------------------------------------+-------+--------+
| single-channel right co-defect       |  3407 | PASS   |
| focused six-declaration audit        |     - | PASS   |
| CCM25Concrete aggregate              |  3911 | PASS   |
| full repository                      |  3992 | PASS   |
+--------------------------------------+-------+--------+
```

All six audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.

## Lean owners

```text
ConnesWeilRH/Source/CCM25Concrete/
  ...AntiresonantInteriorSingleChannelRightCoDefect.lean
ConnesWeilRH/Dev/
  ...AntiresonantInteriorSingleChannelRightCoDefectAudit.lean
```
