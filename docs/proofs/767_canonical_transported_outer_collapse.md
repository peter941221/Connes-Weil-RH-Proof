# Proof 767: Canonical Transported-Outer Collapse

## Result

The projection-level result is good: the apparent outer-projection anomaly
isolated by Proof 766 vanishes for the actual finite Euler transport.  It
survives in an arbitrary or periodic transport model, but not in the
source-specific causal geometry already formalized in this repository.

Let `E` be the radial-support projection and `T_alpha` the synchronized finite
Euler equivalence.  The existing source theorem proves both directions of
radial-support invariance:

```text
T_alpha Ran(E) subset Ran(E),
T_alpha^-1 Ran(E) subset Ran(E).
```

Evidence:

```text
parameterizedFiniteEulerEquiv_maps_radialSupport
ccm24FiniteEulerTransport_maps_logRadialSupport
```

The second inclusion upgrades invariance to equality:

```text
T_alpha Ran(E) = Ran(E).                              (767.1)
```

The orthogonal projection onto a closed range is unique.  Therefore the
Gram-corrected transported projection satisfies

```text
P(T_alpha Ran(E)) = E.                                (767.2)
```

Lean proves `(767.2)` for every `|alpha| <= 1`, not only at the endpoint.

## Why The Periodic Probe Differed

Proof 262's finite certificate uses cyclic translation matrices.  A finite
periodic carrier has no one-sided invariant half-line, so its transported
outer projection can move.  That probe correctly guards abstract projection
algebra, but it cannot override the real-line causal theorem `(767.1)`.

```text
periodic finite section                 actual real-line source
        |                                         |
        v                                         v
no invariant half-line                 T and T^-1 preserve Ran(E)
        |                                         |
        v                                         v
P(T E) may differ from E               P(T E) = E
```

This is the same modeling limitation already recorded in Proofs 256 and 257:
periodic finite sections lose the one-sided invariant subspace.

## Projection-Level Band Consequence

Let `R_alpha=P(T_alpha Ran(R_0))` be the canonical moving Sonin projection.
The formal transported projection difference is

```text
B_alpha^transport=P(T_alpha Ran(E))-R_alpha.
```

Using `(767.2)`, Lean obtains

```text
B_alpha^transport=E-R_alpha=B_alpha^route.            (767.3)
```

At the endpoints,

```text
B_0^transport=E-R_0,
B_1^transport=E-R_S.
```

Thus Proof 766's arbitrary ledger specializes to

```text
outerProjectionDifference=0,
movingOuterBandDifference=soninBandDifference.        (767.4)
```

Root smoothing preserves both identities.  The zero outer response is
trace-legal in every named global Hilbert basis and has ordinary trace zero.
Consequently the corrected boundary cycle becomes

```text
Re Tr_boundary(CompletedBoundaryCycle_S)
  =-Re Tr_global(TransportedBandResponse_S).           (767.5)
```

Equation `(767.5)` is conditional on the displayed source-to-ambient ordinary
trace cycle.  It proves projection-level candidate alignment, not the missing
Proof 262 dual-coframe/nested-band carrier identity.  Proof 743's opposite
causal-orientation guard therefore remains active.

## Lean Declarations

```text
parameterizedTransportedOuterProjection
parameterizedTransportedOuterProjection_isStarProjection
parameterizedTransportedOuterProjection_range
parameterizedTransportedOuterProjection_eq_fixed
finiteEulerTransportedOuterProjection
finiteEulerTransportedOuterProjection_eq_fixed
parameterizedTransportedBandProjection
parameterizedTransportedBandProjection_eq_soninBand
parameterizedTransportedBandProjection_zero
parameterizedTransportedBandProjection_one
actualOuterProjectionDifference_eq_zero
actualMovingOuterBandDifference_eq_fixed
actualRootSandwichedOuterProjectionDifference_eq_zero
actualRootSandwichedMovingOuterBandResponse_eq_fixed
actualRootSandwichedOuterProjectionDifference_isTraceClassAlong
ordinaryTraceAlong_actualRootSandwichedOuterProjectionDifference_eq_zero
ordinaryTraceAlong_completedBoundaryCycle_re_eq_neg_actualMoving
```

## Status

```text
+------------------------------------------------+----------+
| statement                                      | status   |
+------------------------------------------------+----------+
| actual transported outer projection            | BUILT    |
| transported outer equals fixed radial support  | PROVED   |
| outer endpoint anomaly                         | ZERO     |
| transported band equals route band             | PROVED   |
| projection-level band candidate alignment      | PROVED   |
| source/ambient ordinary-trace cycle             | PREMISE  |
| Proof 262 dual-coframe operator identity        | OPEN     |
| uniform shorted Sonin estimate                  | OPEN     |
| Gate 3U                                         | OPEN     |
| Riemann Hypothesis                              | UNPROVED |
+------------------------------------------------+----------+
```

Proof 767 is an exact projection-level correction.  It does not prove the
dual-coframe carrier identification, the source/ambient ordinary-trace cycle,
the uniform signed estimate, the finite-S sign, Burnol's identity, or RH.
