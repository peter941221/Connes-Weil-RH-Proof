# Proof 625: ambient physical factorization

## Result

The actual Schur step stores the source identity

```text
transport * newFrame = oldFrame * Transition.
```

Proof 625 applies it to the complete physical cofactor and proves

```text
(transport * newFrame) * K_(p,S)^dagger * Transition
  = oldFrame * Transition * K_(p,S)^dagger * Transition.
```

Consequently every Proof 624 factor satisfies the actual ambient-carrier
equation

```text
(transport * newFrame) * K_(p,S)^dagger * Transition
  = rho_p * oldCarrierAnalysis_(p,S)^dagger * factor_(p,S).
```

Here `transport` is the genuine normalized one-prime Euler transport from the
actual Schur owner, not an abstract replacement.

## Active bottom

The remaining Bone 1 task is now a family-uniform source factorization of this
same ambient physical owner.  Transition covariance, suffix dressing, local
raw cofactor order, and carrier alignment are no longer separate obligations.

No factor, norm bound, Gate 3U estimate, finite-S sign, Burnol identity, or RH
proof is inferred.
