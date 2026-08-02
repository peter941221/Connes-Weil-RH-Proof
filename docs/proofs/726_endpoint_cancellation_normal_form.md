# Proof 726: Endpoint Cancellation Normal Form

## Result

Proof 725 already identifies the two endpoint channels with the complete
off-Sonin leakage. Proof 726 gives that object a stable name:

```text
sourceEndpointCancellationResidual
  = sourceOuterCoframeLeakage
    + sourceBandProjection o sourceActualBandForwardEndpointCoframe.
```

The new Lean module proves the following exact normal forms:

```text
residual
  = (I - sourceSoninProjection) o endpoint
  = endpoint - sourceInclusion
  = sourceActualBandForwardCoframe + sourcePhysicalCoframeLeakage.
```

It also proves the pure projection identity

```text
(I - radialSupportProjection) + sourceBandProjection
  = I - sourceSoninProjection.
```

The source projection and inclusion adjoint both annihilate the residual. The
zero theorem is deliberately exposed only as an equivalence:

```text
residual = 0
  <-> endpoint = sourceInclusion.
```

No cancellation, norm estimate, Gate 3U bound, finite-S sign, Burnol identity,
or RH theorem is asserted. The next producer must now identify this named
residual with a genuine physical boundary cocycle and prove its cancellation
or signed control before applying norms or traces.

## Verification

The Windows source of truth was synchronized to the Ubuntu-24.04 WSL2 ext4
mirror. The focused source, audit, and aggregate were built together under the
shared Lake lock, followed by the full repository build:

```text
lake build ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSPhysicalCancellationEndpointNormalForm
lake build ConnesWeilRH.Dev.CCM24FiniteSPhysicalCancellationEndpointNormalFormAudit
lake build ConnesWeilRH.Source.CCM25Concrete
lake build
```

```text
+----------------------------------+-------+--------+
| target                           | jobs  | result |
+----------------------------------+-------+--------+
| source + audit + aggregate batch | 3995  | PASS   |
| full repository                  | 4075  | PASS   |
+----------------------------------+-------+--------+
```

All nine audited theorems use exactly:

```text
[propext, Classical.choice, Quot.sound]
```

No `sorry`, `admit`, user axiom, heartbeat increase, or recursion-limit
increase was added.
