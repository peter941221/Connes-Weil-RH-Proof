# Record 2533 — signed grid refinement feasibility

Date: 2026-10-03

## Decision

The record-2532 signed midpoint-second plus sampled familywise-third
architecture remains numerically viable on a refined grid. The 5120 and
10240 cell replays both remain below the existing endpoint pin for both signs;
the 10240 replay leaves the larger positive margin after the finer node sum is
recomputed.

This record selects a certificate grid and narrows the next proof obligation
to a whole-cell curvature enclosure. It does not close the producer.

## Fixed owner and representation

The selected healthy `CompactLog` detector, support radius, visible-prime
family, 2338 coefficient-box source, coefficient midpoint/radius split, and
signed owner modulation are unchanged. The pointwise quantity is assembled as
follows:

```text
30 signed family terms
    -> complex sum at the node
    -> norm after cancellation
    -> scalar sum of coefficient-box radii
    -> exponential endpoint weight
```

For the derivative ladder, the modulation is signed in both the phase and the
complex derivative parameter. Absolute values occur only when a magnitude
bound is formed. This distinction matters because changing the sign of the
modulation changes the odd imaginary derivative channels.

## Diagnostic replay

The replay priced the midpoint weighted second derivative and added
`cell_width / 2` times a familywise third-derivative maximum sampled at 17
points in each cell.

```text
+--------+--------+----------------------+----------------------+----------------------+----------------------+
| cells  | sigma  | node sum             | curvature remainder  | total                | base margin          |
+--------+--------+----------------------+----------------------+----------------------+----------------------+
| 2560   | -1/2   | 2.686887376406491    | 0.051151164747867    | 2.738038541154359    |  0.041055837045641   |
| 2560   | +1/2   | 2.675211462945179    | 0.050884273382568    | 2.726095736327746    |  0.052998641872254   |
| 5120   | -1/2   | 2.686801577875378    | 0.008733079904682    | 2.695534657780060    |  0.083559720419940   |
| 5120   | +1/2   | 2.675102292521271    | 0.008666314662117    | 2.683768607183388    |  0.095325771016612   |
| 10240  | -1/2   | 2.686700019845782    | 0.001678452697860    | 2.688378472543641    |  0.090715905656359   |
| 10240  | +1/2   | 2.675007889593528    | 0.001661761513858    | 2.676669651107386    |  0.102424727092614   |
+--------+--------+----------------------+----------------------+----------------------+----------------------+
```

The table is evidence for a routing decision, not an inequality accepted by
Lean. A sampled maximum does not bound every point in a cell.

## Why the grid change helps

The composite-trapezoid remainder has cubic dependence on the cell width when
the second derivative is bounded by a midpoint value plus a third variation
term. Halving the cell width sharply reduces the variation price. The node
sum is recomputed on every grid, so the result includes the small change from
the refined trapezoid nodes instead of treating it as a fixed input.

The 10240 grid is the preferred first certificate target. Its diagnostic
margin is positive for both endpoint signs, and its sampled variation term is
smaller than the 5120 term. This is an engineering choice inside the same
mathematical owner; it does not change the consumer target.

## Next proof gate

The missing object is a whole-cell upper bound for the familywise third
derivative. The intended route is:

```text
sampled third derivative
    + certified fourth-derivative Lipschitz allowance
    -> directed third-derivative cell bound
    -> upward rational curvature cell payload
    -> segmented finite-sum Lean import
    -> endpoint pin comparison
```

The fourth-derivative ladder must be derived from the existing bump derivative
ladder and checked with the same signed modulation convention. Any bound that
uses only the 17 samples remains diagnostic.

## Nonclaims

This record does not establish the exact midpoint-to-2338-owner identity, the
complete selected-owner signed C3-prime margin, Producer GO, `SourceRH`, or the
Riemann Hypothesis.

Evidence:

- `scripts/routea_owner_signed_grid_refinement_2533.py`
- `results/2533_signed_grid_refinement_probe.json`
- `route/002_route_a_signed_kernel/002_c3p_selected_owner/002_remainder_certificate_terminal/004_signed_grid_refinement_2533/README.md`
- `docs/proofs/2532_signed_curvature_center_third.md`

## Conservative session replay retained separately

The completed 2533 session also evaluated a more conservative local endpoint
third-derivative envelope. It is retained as raw session evidence because the
original command was not an imported Lean payload. Its gating result is useful:
2560 is rejected by the conservative envelope, while 5120 and 10240 remain
below the endpoint pin.

```text
+--------+--------+----------------------+----------------------+----------------------+
| cells  | sigma  | conservative total  | conservative margin | routing              |
+--------+--------+----------------------+----------------------+----------------------+
| 2560   | -1/2   | 2.804271452106082    | -0.025177073906082   | reject this grid     |
| 2560   | +1/2   | 2.792328647279470    | -0.013234269079470   | reject this grid     |
| 5120   | -1/2   | 2.703778797379185    |  0.075315580820815   | viable               |
| 5120   | +1/2   | 2.692012746782513    |  0.087081631417487   | viable               |
| 10240  | -1/2   | 2.689406808984803    |  0.089687569215197   | preferred            |
| 10240  | +1/2   | 2.677697987548548    |  0.101396390651452   | preferred            |
+--------+--------+----------------------+----------------------+----------------------+
```

The reproducible `2533_signed_grid_refinement_probe.json` is the tighter
record-2532 center-third replay. The conservative session evidence is stored
in `results/2533_signed_grid_endpoint_envelope_session46970.{json,txt}` and is
used only to keep the grid choice honest under a looser envelope.
