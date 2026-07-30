# Proof 675: radial interior physical expansion

Proof 675 closes the exact algebraic readback of the compressed radial
interior channel. It does not estimate the channel and does not claim the
Gate 3U sign.

## Exact objects

Let

```text
E   = radialSupportProjection unitSoninScale
Q_S = parameterizedFourierSupportProjection unitSoninScale 1 S
K_S = parameterizedProlateRemainder unitSoninScale 1 S
P_S = newSuffixRangeProjection unitSoninScale S
W_p = radialCompressedPositiveTranslation p
```

The source proves the endpoint identity

```text
P_S = E Q_S E - K_S.
```

The repository commutator convention is `[A,W] = A W - W A`. Therefore the
existing three-branch ledger, which expands `[P_S,W_p]`, gives the reversed
orientation as

```text
[W_p,P_S]
  = -cc20ThreeBranchCommutator E Q_S K_S W_p.
```

All four physical branches remain in the signed owner. No branchwise norm,
positivity, or cancellation statement is introduced.

## Verification

The focused source and audit use the Ubuntu-24.04 WSL2 ext4 mirror and the
shared Lake lock. The audit is expected to report only
`[propext, Classical.choice, Quot.sound]`.

The result is a source expansion only. Gate 3U, the finite-S sign, Burnol's
identity, and `_root_.RiemannHypothesis` remain open.
