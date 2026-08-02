# Proof 744: Gate Physical Pulled-Oblique Reduction

## Result

The result is structurally useful but does not close Gate 3U.  Proof 744
pulls Proof 743's actual target projection back to the fixed source ambient
carrier and places every detector-dependent factor inside the existing source
Sonin commutator.

Write

```text
J   = sourceInclusion,
R   = sourceSoninProjection,
T_S = finiteEulerTransportOperator_S,
A_S = T_S^(-1),
P_S = targetSoninProjection_S,
W   = detectorOperator,
Q_S = A_S P_S T_S.
```

The new operator `Q_S` is an oblique projection.  Lean proves

```text
Q_S^2 = Q_S,
Q_S J  = J,
Q_S R  = R.                                             (PO.1)
```

The last identity follows from `R=J J^dagger`; it does not identify `Q_S`
with `R`.

## Operator Reduction

Proof 743's active owner is

```text
Target_S
  = -J^dagger A_S (I-P_S) [W,P_S] T_S J.               (PO.2)
```

The exact operator calculation is

```text
(I-P_S)[W,P_S]T_SJ = (I-P_S)WT_SJ,
WT_S = T_SW,
A_ST_S = I.
```

Using these three identities in `(PO.2)` gives the first pulled form

```text
Target_S = J^dagger (Q_S-I) W J.                       (PO.3)
```

Now use `RJ=J`, `Q_SR=R`, and `J^dagger R=J^dagger`:

```text
J^dagger Q_S[W,R]J
  = J^dagger Q_S(W R-R W)J
  = J^dagger(Q_S-I)WJ.
```

Therefore Lean proves the fixed-source commutator form

```text
Target_S = J^dagger Q_S [W,R] J.                       (PO.4)
```

The theorem carrying `(PO.4)` is
`finiteEulerTargetCommutatorResponse_eq_pulledSourceCommutator` in
`CCM24FiniteSGatePhysicalPulledObliqueReduction.lean`.

## Why This Is Stronger

Proof 743 still displayed the moving commutator `[W,P_S]` on the target
carrier.  Formula `(PO.4)` separates the two kinds of dependence:

```text
fixed source geometry                 finite-S geometry
---------------------                 -----------------
[W,R]                                 Q_S=A_SP_ST_S
compact-root / three-branch owner     pulled oblique projection
```

This aligns the active ordinary-trace target with Proof 262's source-boundary
view.  At the family quantifier level, Lean now proves

```text
(exists C, forall S, |Tr(Gate_S)| <= C)
  <->
(exists C, forall S, |Tr(J^dagger Q_S[W,R]J)| <= C).   (PO.5)
```

No infinite-dimensional trace cycle is used in deriving `(PO.3)`--`(PO.5)`.

## Guard

`Q_S` is idempotent but is not proved self-adjoint.  It is therefore not an
orthogonal projection, and no estimate such as

```text
||Q_S|| <= 1
```

is available.  Likewise, estimating

```text
||J^dagger Q_S|| * ||[W,R]||_1 * ||J||
```

would replace the required signed compact-support estimate by a
total-variation bound and can reintroduce the Euler condition number.  The
next producer must apply the compact-root support of the complete
three-branch commutator before taking an absolute value.

## Verification

The Windows source of truth was copied one way to the Ubuntu-24.04 WSL2 ext4
verification tree.  The accepted builds were

```text
+----------------------------------+-------+--------+
| target                           | jobs  | result |
+----------------------------------+-------+--------+
| focused source + axiom audit     |  3388 | PASS   |
| CCM25Concrete aggregate          |  4012 | PASS   |
| full repository                  |  4093 | PASS   |
+----------------------------------+-------+--------+
```

All nine audited theorems use exactly
`[propext, Classical.choice, Quot.sound]`.  The new source and audit contain
no `sorry`, `admit`, user axiom, heartbeat increase, recursion-limit
increase, unsafe declaration, new linter warning, or line over 100
characters.

Gate 3U, the finite-S sign, the arithmetic same-object identity, Burnol's
identity, and `_root_.RiemannHypothesis` remain open.
