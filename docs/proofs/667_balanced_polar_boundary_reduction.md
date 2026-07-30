# Proof 667: balanced polar-boundary reduction

## Result

The result is good as a strict channel elimination, but it does **not**
close Bone 1A. The detector intertwinement inside Proof 666's recurrence is
identified with the actual left Julia co-defect (left Julia co-defect), and
its genuinely route-scaled norm is uniformly controlled by `6 ||W||`.

Write

```text
H_(p,S) = L_(p::S) R_S,
D_S     = U_S^dagger W U_S,
F_S     = FirstJetPhysical_S,
B_0     = J^dagger W J,
E_S     = B_0-F_S.
```

Proof 666's recurrence is

```text
H_(p,S)(B_0+D_S-F_S)
  -(B_0+D_(p::S)-F_(p::S))H_(p,S)
  +L_(p::S)(D_(p::S)-D_S)R_S.
```

The new reduction extracts exactly the two terms containing the detector
compression in the transition orientation.

## Controlled polar channel

The complete old-carrier transition gauge satisfies

```text
H_(p,S)=(1+q_p)T_(p,S).
```

The existing physical detector intertwinement then gives the operator
identity

```text
H_(p,S)D_S-D_(p::S)H_(p,S)
  =(1+q_p) BoundaryDefect_(p,S).
```

The boundary defect has the actual Julia factorization

```text
BoundaryDefect_(p,S)
  =-LeftCoDefect_(p,S) RightFactor_(p,S),

RightFactor_(p,S)
  =BoundaryFactor_(p,S)^dagger W U_S.
```

Every factor in `RightFactor` except the detector is contractive. Combined
with the proved left-co-defect estimate, Lean obtains

```text
||RightFactor_(p,S)|| <= ||W||,

||BoundaryDefect_(p,S)||
  <=6 s_p ||W||,
```

where

```text
s_p=sqrt(q_p)/(1+q_p).
```

The route normalization is exact:

```text
q_p^(-1/2)(1+q_p)=s_p^(-1).
```

Therefore

```text
||q_p^(-1/2)(1+q_p) BoundaryDefect_(p,S)||
  <=6 ||W||
```

uniformly in the prime and the route-valid suffix.

```text
 +--------------------------+
 | polar detector covariance|
 | H D_S-D_new H            |
 +------------+-------------+
              |
              v
    (1+q_p) BoundaryDefect
              |
              v
  -LeftCoDefect * RightFactor
              |
              v
       scaled norm <= 6||W||
```

## Survivor residual

After removing that controlled channel, define the signed residual

```text
Residual_(p,S)
  =H_(p,S)E_S-E_(p::S)H_(p,S)
    +L_(p::S)(D_(p::S)-D_S)R_S.
```

The proof keeps the base/first-jet covariance and metric detector increment
inside one operator. They are not separately estimated. The exact split is

```text
PolarFirstJetRecurrence_(p,S)
  =ControlledPolarBoundary_(p,S)+Residual_(p,S).
```

Consequently

```text
Bone 1A route-uniform bound exists
  <->
sup_(route-valid p,S) q_p^(-1/2)||Residual_(p,S)|| < infinity.
```

Converting either direction adds only the explicit constant `6 ||W||`.
This is an existence equivalence, not a proof that the residual is bounded.
Its two displayed terms must remain coupled until a source theorem identifies
their common producer.

Proof 656's two-step factor remains a separate Bone 1 requirement. Gate 3U,
the finite-S sign, Burnol's identity, and RH also remain open.

## Lean artifacts

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrier
  AntiresonantInteriorBalancedPolarBoundaryReduction.lean

ConnesWeilRH/Dev/
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrier
  AntiresonantInteriorBalancedPolarBoundaryReductionAudit.lean
```

## Verification

The Windows truth source was copied to the Ubuntu-24.04 WSL2 ext4 mirror and
built under the shared Lake lock.

```text
+--------------------------------------+-------+--------+
| target                               | jobs  | result |
+--------------------------------------+-------+--------+
| Proof 667 focused source + audit     |  3455 | PASS   |
| CCM25Concrete aggregate              |  3942 | PASS   |
| full repository                      |  4023 | PASS   |
+--------------------------------------+-------+--------+
```

All twelve audited theorems use exactly
`[propext, Classical.choice, Quot.sound]`. No `sorry`, `admit`, user axiom,
heartbeat increase, or new source linter warning was added.
