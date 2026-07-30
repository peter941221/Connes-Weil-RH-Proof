# Proof 662: ambient metric/first-jet residual

## Result

Let `U_S` be the actual suffix polar frame, `P_S=U_S U_S^*` its ambient
range projection, and `W` the selected detector. Proof 662 identifies the
ambient lift of the polar detector compression exactly:

```text
U_S (U_S^* W U_S) U_S^* = P_S W P_S.
```

This is the adjacent projection channel controlled by Proofs 658--660. Its
covariance has the exact old-frame readback and bound

```text
PolarProjectionCovariance_(p,S)
  = oldFrame_(p,S) PolarIntertwining_(p,S),

||s_p^(-1) PolarProjectionCovariance_(p,S)||
  <= 6 ||W||.
```

The remaining polar/raw mismatch is not split into independently estimated
metric and first-jet pieces. Proof 662 records its exact same-object form:

```text
MismatchResponse_S
  = RoutePolarKernel_S - FirstJetResponse_S.
```

Its complete adjacent ambient covariance is named
`MetricFirstJetResidual_(p,S)`. Lean proves the exact split

```text
RawCovariance_(p,S)
  = PolarProjectionCovariance_(p,S)
    - MetricFirstJetResidual_(p,S).
```

Hence the fixed-bound conversions are

```text
raw ambient bound B
  -> metric/first-jet residual bound 6 ||W|| + B,

metric/first-jet residual bound B
  -> raw ambient bound 6 ||W|| + B.
```

At existence level this gives the new Bone 1A reduction

```text
exists a route-uniform scaled complete-target bound
  <->
exists a route-uniform scaled metric/first-jet residual bound.
```

## Recursive Decomposition

```text
Bone 1A complete target
          |
          | Proof 660
          v
raw source intertwinement
          |
          | Proof 661, isometric lift
          v
raw ambient covariance
          |
          | Proof 662, exact subtraction
          +-------------------------------+
          |                               |
          v                               v
P_S W P_S adjacent channel       RoutePolarKernel - FirstJet
controlled by 6 ||W||            active unresolved covariance
```

## Boundary

This is a reduction, not the missing uniform estimate. The active Bone 1A
bottom is now the complete covariance of
`RoutePolarKernel_S - FirstJetResponse_S`. The two summands must remain
recombined: the existing `rho_(p::S)`-weighted metric estimate cannot be
converted to the required `s_p` scale because the suffix scalar can collapse.

Full Bone 1 separately still requires Proof 656's route-uniform two-step
coboundary factor. Gate 3U, the finite-S sign, Burnol's identity, and RH remain
open.

## Lean Owners

```text
ConnesWeilRH/Source/CCM25Concrete/
  ...AntiresonantInteriorAmbientMetricFirstJetResidual.lean
ConnesWeilRH/Dev/
  ...AntiresonantInteriorAmbientMetricFirstJetResidualAudit.lean
```

Verification in the Ubuntu-24.04 WSL2 ext4 mirror used the shared Lake lock:

```text
+--------------------------------------+-------+--------+
| target                               | jobs  | result |
+--------------------------------------+-------+--------+
| Proof 662 focused audit              |  3449 | PASS   |
| Proof 661--662 combined audits       |  3450 | PASS   |
| CCM25Concrete aggregate              |  3937 | PASS   |
| full repository                      |  4018 | PASS   |
+--------------------------------------+-------+--------+
```

All thirteen Proof 662 audited theorems use exactly
`[propext, Classical.choice, Quot.sound]`. No `sorry`, `admit`, or user axiom
was added.
