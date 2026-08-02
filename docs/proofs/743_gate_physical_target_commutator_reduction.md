# Proof 743: Gate Physical Target-Commutator Reduction

## Result

The result is structurally useful but does not close Gate 3U.  Proof 743
connects Proof 742's complete physical leakage directly to the existing actual
target-commutator owner from Proofs 428--429.

Write

```text
J   = sourceInclusion,
T_S = finiteEulerTransportOperator_S,
A_S = T_S^(-1),
P_S = targetSoninProjection_S,
W   = detectorOperator.
```

The actual target product is

```text
Target_S
  = -J^dagger A_S (I-P_S) [W,P_S] T_S J.              (TC.1)
```

Lean proves the operator identity

```text
PhysicalLeakage_S^dagger = Target_S.                  (TC.2)
```

This is the correct orientation.  It follows from the exact chain

```text
PhysicalLeakage_S = -sourceBandGramResponse_S,
leftOrderedSourceBandGramResponse_S
  = sourceBandGramResponse_S^dagger,
leftOrderedSourceBandGramResponse_S = -Target_S.
```

No infinite-dimensional trace cycle is used.

## Trace Consequences

For every source Hilbert basis, adjoint passage gives

```text
Tr(Target_S) = conjugate(Tr(PhysicalLeakage_S)),
|Tr(Target_S)| = |Tr(PhysicalLeakage_S)|.              (TC.3)
```

Fixed-family trace legality transfers to `Target_S`.  Combining `(TC.3)` with
Proof 742 yields the route-facing equivalence

```text
(exists C, forall S, |Tr(Gate_S)| <= C)
  <->
(exists C, forall S, |Tr(Target_S)| <= C).             (TC.4)
```

Thus the active ordinary-trace owner contains no explicit
`finiteEulerGramInv`.  Its finite-S dependence is confined to one complete
inverse-transport / target-commutator / forward-transport product.

## Orientation Guard

Proof 256's formula

```text
D = T E T^(-1) B
```

is a nested-band coframe on the band carrier.  It is not a direct formula for
Proof 742's source-Sonin leakage.  In the current Lean orientation, `T_S` and
`T_S^(-1)` preserve the radial support `E`; Proof 256 writes the causal
invariance on the complementary half-line in the opposite transport
orientation.  Substituting that formula into `(TC.1)` without a carrier and
adjoint conversion would be invalid.

The target commutator itself has the existing nearly-invariant
Hilbert--Schmidt control, but the estimate

```text
||J^dagger A_S|| * ||[W,P_S]||_2 * ||T_S J||
```

is forbidden: it restores the Euler condition number.  The compact-root
support must be applied to the complete signed scalar in `(TC.1)` before any
factorwise norm or absolute value.

## Literature Check

The source check found structural results, not the missing estimate:

```text
Camara--Carteiro--Ross,
Multipliers and equivalence of functions, spaces, and operators:
https://arxiv.org/abs/2307.05453

Gerard--Pushnitski,
Weighted model spaces and Schmidt subspaces of Hankel operators:
https://arxiv.org/abs/1803.04295
```

The first paper gives multiplier-based equivalence of generalized Toeplitz
operators.  The second identifies weighted model-space structure through
isometric multipliers.  Neither states a family-uniform trace bound for the
Euler product `(TC.1)`.  They therefore do not replace the source-specific
compact-support argument still required here.

## Verification

The Windows source of truth was copied one way to the Ubuntu-24.04 WSL2 ext4
mirror.  The accepted builds were

```text
+----------------------------------+-------+--------+
| target                           | jobs  | result |
+----------------------------------+-------+--------+
| focused source + axiom audit     |  3387 | PASS   |
| CCM25Concrete aggregate          |  4011 | PASS   |
| full repository                  |  4092 | PASS   |
+----------------------------------+-------+--------+
```

All six audited theorems use exactly
`[propext, Classical.choice, Quot.sound]`.  The new source and audit contain no
`sorry`, `admit`, user axiom, heartbeat increase, recursion-limit increase,
unsafe declaration, or line over 100 characters.

Gate 3U, the finite-S sign, the arithmetic same-object identity, Burnol's
identity, and `_root_.RiemannHypothesis` remain open.
