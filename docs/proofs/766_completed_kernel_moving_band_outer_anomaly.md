# Proof 766: Completed-Kernel Moving-Band Outer Anomaly

## Result

Proof 766 rejects a direct identification between Proof 765's canonical
completed-boundary cycle and Proof 262's transported-band dual-coframe owner.
The two endpoints move different projection pairs.

The current Lean route uses

```text
fixed band endpoint
  =(E-R_S)-(E-R_0),                                   (766.1)
```

where the radial support projection `E` is fixed.  Proof 262's finite-matrix
certificate instead defines

```text
transported band endpoint
  =(E_S-R_S)-(E-R_0).                                 (766.2)
```

The script evidence is literal:

```python
transported_band = transported_outer - transported_inner
direct_band = np.trace(detector @ (transported_band - band))
```

Source: `docs/proofs/262_endpoint_two_commutator_gate_probe.py`, lines 103--151.

Subtracting `(766.1)` from `(766.2)` gives the exact outer endpoint anomaly

```text
(E_S-R_S)-(E-R_0)
  =(E_S-E)+[(E-R_S)-(E-R_0)].                         (766.3)
```

Lean now proves `(766.3)` for an arbitrary supplied moving outer projection.
It also proves

```text
moving band difference = fixed band difference
  iff
moving outer projection = E.                         (766.4)
```

Thus the two bands cannot be identified by cancelling only the common Sonin
endpoint.

## Root-Smoothed Ledger

Let `C_g` be the selected convolution root.  Root smoothing preserves the
same three-term ledger:

```text
C_g MovingBand C_g^dagger
  =C_g(E_S-E)C_g^dagger
   +C_g FixedBand C_g^dagger.                         (766.5)
```

If the two right-hand operators are trace-legal, ordinary trace additivity
gives the corresponding scalar equality.  Proof 766 does not infer trace
legality from boundedness.

Combining `(766.5)` with Proof 765 and an explicit source-to-ambient endpoint
cycle yields

```text
Re Tr_boundary(CompletedBoundaryCycle_S)
  =Re Tr(C_g(E_S-E)C_g^dagger)
   -Re Tr(C_g MovingBand_S C_g^dagger).                (766.6)
```

Equation `(766.6)` is the corrected Proof 765/262 bridge.  The first term is
the genuine outer anomaly; the second is the transported-band response which
Proof 262 rewrites using its contractive dual coframe and Sonin graph.

```text
                 moving outer E_S
                         |
                         v
transported band = outer anomaly + fixed-outer band
                         |                 |
                         |                 +--> current Lean route
                         |
                         +--> Proof 262 dual-coframe endpoint

completed boundary scalar = outer anomaly - transported-band scalar
```

## Analytic Consequence

Proof 254 already derives the correct estimate for a legally smoothed ambient
half-line Markov response:

```text
abs integral z F(-z) dmu(z) <= 2 B_root ||g||_2^2.    (766.7)
```

Therefore the outer term in `(766.6)` is the structurally easier channel once
the actual moving outer projection and its trace cycle are constructed.  The
hard term remains Proof 262's shorted Sonin response.  Proof 766 does not turn
the mathematical estimate `(766.7)` into a Lean theorem and does not identify
an arbitrary `movingOuter` with the actual metric projection.

The correct next producer has three parts:

```text
1. construct the actual transported outer projection on finiteSCarrier;
2. identify its moving-band trace with Proof 262's dual-coframe formula;
3. combine the ambient Markov bound with the shorted Sonin bound.
```

## Lean Declarations

```text
outerProjectionDifference
movingOuterBandDifference
movingOuterBandDifference_eq_outer_add_fixed
movingOuterBandDifference_eq_fixed_iff
rootSandwichedMovingOuterBandResponse
rootSandwichedOuterProjectionDifference
rootSandwichedMovingOuterBandResponse_eq_outer_add_fixed
ordinaryTraceAlong_movingOuterBandResponse_eq_add
ordinaryTraceAlong_completedBoundaryCycle_re_eq_outer_sub_moving
```

## Status

```text
+---------------------------------------------+----------+
| statement                                   | status   |
+---------------------------------------------+----------+
| fixed/moving outer operator ledger          | PROVED   |
| root-smoothed response ledger               | PROVED   |
| corrected completed-boundary trace bridge   | PROVED   |
| actual moving-outer construction            | OPEN     |
| Proof 262 dual-coframe Lean identification  | OPEN     |
| uniform shorted Sonin estimate              | OPEN     |
| Gate 3U                                     | OPEN     |
| Riemann Hypothesis                          | UNPROVED |
+---------------------------------------------+----------+
```

No claim is made that Gate 3U, the finite-S sign, Burnol's identity, or RH is
proved.
