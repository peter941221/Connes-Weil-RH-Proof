# Proof 468: Detector displacement trace owner

## Result

Proof 467 reduced the complete finite-Euler corner to the probability average
of the fixed displacement response

```text
B[W,P]U_(-z)B.
```

The existing `sourceThreeBranchPairData` owns `[P,W]` as one genuine
Hilbert--Schmidt pair containing the outer, reflected second-support, and
prolate branches.  Proof 468 applies the bounded sandwich

```text
left  = B,
right = U_(-z)B
```

and keeps the sign inside the right Hilbert--Schmidt leg.  Its trace product is

```text
-B[P,W]U_(-z)B = B[W,P]U_(-z)B.
```

Therefore every displacement atom in the Proof 467 probability law is trace
class along the named global basis, using only the existing compact-root
support witness and the existing prolate Hilbert--Schmidt factor.

## Boundary

This result proves trace legality for each fixed displacement.  It does not
prove trace-norm summability over the renewal law, exchange ordinary trace
with the infinite probability sum, identify the signed scalar trace, or prove
a uniform compact-support estimate.  Gate 3U, the finite-S sign, Burnol's
identity, and `_root_.RiemannHypothesis` remain open.
