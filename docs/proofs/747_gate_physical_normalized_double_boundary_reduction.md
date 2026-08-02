# Proof 747: Gate Physical Normalized Double-Boundary Reduction

## Result

The result is structurally useful but does not close Gate 3U.  Proof 747
opens Proof 746's physical coframe leakage as a second boundary commutator.
It then applies the exact finite-Euler lower-factor gauge so that the inverse
source Gram factor is a family-uniform contraction.

Write

```text
J   = sourceInclusion,
R   = sourceSoninProjection=J J^dagger,
C   = I-R,
W   = detectorOperator,
H_S = finiteEulerAmbientGram=T_S^dagger T_S,
G_S = J^dagger H_S J,
c_S = finiteEulerLowerFactor(S)>0.
```

The two source boundary orientations used by the module are

```text
MetricBoundary_S  =[R,H_S]=R H_S-H_S R,
DetectorBoundary =[W,R]  =W R-R W.                  (OK.1)
```

Lean proves that the metric boundary is skew-adjoint:

```text
MetricBoundary_S^dagger=-MetricBoundary_S.          (OK.2)
```

## Double-Boundary Identity

Proof 746 writes the active target as `L_S^dagger WJ`, where

```text
L_S=C H_S J G_S^(-1).
```

Taking the adjoint and using the two orthogonal-projection identities
`R C=0` and `J^dagger R=J^dagger` gives the exact metric crossing

```text
L_S^dagger=G_S^(-1) J^dagger [R,H_S] C.             (OK.3)
```

The detector complement is independently exact:

```text
C W J=[W,R]J.                                       (OK.4)
```

Substituting `(OK.3)` and `(OK.4)` into the same operator, without a trace
cycle, yields

```text
Target_S
  =G_S^(-1) J^dagger [R,H_S] [W,R] J.               (OK.5)
```

Both scalar ambient components disappear inside commutators.  This is an
algebraic cancellation on one complete signed operator; it is not a bound on
either commutator.

## Lower-Factor Gauge

Let `B_S` be the exact restricted inverse from the transported Sonin carrier
to the source Sonin carrier.  The existing Gram identity is

```text
G_S^(-1)=B_S B_S^dagger.
```

Proof 747 defines

```text
NormalizedGramInv_S
  =c_S^2 G_S^(-1)
  =(c_S B_S)(c_S B_S)^dagger.                        (OK.6)
```

The previously proved restricted-inverse estimate now gives the new theorem

```text
norm(NormalizedGramInv_S)<=1                         (OK.7)
```

for every finite prime-power family `S`.

The ambient metric and its boundary receive the reciprocal gauge:

```text
NormalizedAmbientGram_S=c_S^(-2) H_S,
NormalizedMetricBoundary_S
  =[R,NormalizedAmbientGram_S]
  =c_S^(-2)[R,H_S].                                  (OK.8)
```

Since `c_S` is nonzero, the two scalar factors cancel exactly.  Lean proves
the operator identity

```text
Target_S
  =NormalizedGramInv_S J^dagger
     NormalizedMetricBoundary_S [W,R]J.              (OK.9)
```

Consequently, for every named source Hilbert basis,

```text
Tr(Target_S)=Tr(NormalizedDoubleBoundary_S).         (OK.10)
```

At the route quantifier level this gives

```text
(exists C, forall S, |Tr(Gate_S)| <= C)
  <->
(exists C, forall S,
  |Tr(NormalizedDoubleBoundary_S)| <= C).            (OK.11)
```

## What Changed

```text
+----------------------+---------------------------------------------------+
| owner                | exact readout                                     |
+----------------------+---------------------------------------------------+
| Proof 746 leakage    | L_S^dagger [W,R]J                                |
| Proof 747 raw        | G_S^-1 J^dagger [R,H_S][W,R]J                    |
| Proof 747 normalized | (c_S^2 G_S^-1)J^dagger(c_S^-2[R,H_S])[W,R]J      |
+----------------------+---------------------------------------------------+
```

The gain is precise: the first finite-S factor in the normalized row has
operator norm at most one.  The complete finite-S dependence that still
needs analysis is exposed in the normalized metric boundary.

## Guard

Do not infer a uniform target bound from `(OK.7)`.  No uniform norm, trace
norm, sign, or compact-support estimate is proved for
`NormalizedMetricBoundary_S`.  A separate norm estimate of that factor can
recover the same rejected finite-Euler condition growth in a different
place.

Keep `[R,H_S]`, `[W,R]`, and all compact-root/second-support/prolate branches
inside one signed scalar before taking an absolute value.  Skew-adjointness
in `(OK.2)` does not imply positivity or cancellation after multiplication by
the other factors.  The gauge identity is exact algebra, not Gate 3U.

Proof 747 proves neither the uniform bound in `(OK.11)` nor the finite-S sign,
arithmetic same-object identity, Burnol identity, or RH.

## Verification

The Windows source of truth was copied one way to the Ubuntu-24.04 WSL2 ext4
verification tree.  Matching SHA-256 hashes were checked before building.
The accepted builds were

```text
+----------------------------------+-------+--------+
| target                           | jobs  | result |
+----------------------------------+-------+--------+
| focused source + axiom audit     |  3391 | PASS   |
| CCM25Concrete aggregate          |  4015 | PASS   |
| full repository                  |  4096 | PASS   |
+----------------------------------+-------+--------+
```

All sixteen audited theorems use exactly
`[propext, Classical.choice, Quot.sound]`.  The new source and audit contain
no `sorry`, `admit`, user axiom, heartbeat increase, recursion-limit increase,
unsafe declaration, new linter warning, or line over 100 characters.

Gate 3U, the finite-S sign, the arithmetic same-object identity, Burnol's
identity, and `_root_.RiemannHypothesis` remain open.
