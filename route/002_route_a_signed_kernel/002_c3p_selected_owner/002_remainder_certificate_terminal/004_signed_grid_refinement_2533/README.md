# 004 — signed grid refinement for the whole-cell remainder

Status: `VIABLE DIAGNOSTIC; WHOLE-CELL CERTIFICATE OPEN`.

This terminal subtask extends the record-2532 signed midpoint-second plus
sampled familywise-third architecture to a grid ladder. The selected detector,
exact owner, support radius, visible-prime family, coefficient source, and
signed owner modulation are unchanged. The named change is the production
grid used to price the midpoint-to-cell variation.

```text
2338 exact coefficient boxes
    -> midpoint complex coefficient plus scalar Euclidean radius charge
    -> signed 30-family complex sum at each node
    -> norm after the signed sum
    -> midpoint weighted second derivative
    -> sampled familywise third-derivative variation on each cell
```

The 2533 replay uses 2560, 5120, and 10240 cells. The third-derivative
supremum is sampled on a 17-point subgrid, so this remains feasibility evidence
and is not a whole-cell enclosure.

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

The endpoint pin is `baseNormUpper2343 = 2.7790943782`. Every row in this
same-architecture replay is below the pin. The 10240 grid is the preferred
first target for a whole-cell payload because it retains positive margin while
reducing the sampled variation term by about a factor of five relative to
5120.

What this changes:

```text
previous diagnostic: 003_signed_pointwise_cancellation_2560/
current grid terminal: 004_signed_grid_refinement_2533/
```

This is a grid refinement inside the existing signed-cancellation
representation, not a new RH route. The next proof obligation is to replace
the sampled third-derivative maximum with a directed whole-cell enclosure.
The enclosure must be exported as upward rational cell bounds and imported
through segmented `Finset.sum_le_sum` lemmas.

The route is still open on all of the following:

```text
node transcendental enclosure
exact midpoint-to-2338-owner identity
whole-cell curvature certificate
complete selected-owner signed C3' margin
Producer GO
SourceRH
Riemann Hypothesis
```

Evidence: `docs/proofs/2533_signed_grid_refinement.md`,
`scripts/routea_owner_signed_grid_refinement_2533.py`, and
`results/2533_signed_grid_refinement_probe.json`.

Record 2534 closes the generic whole-cell Lipschitz transport interface in
Lean under the next terminal `005_whole_cell_lipschitz_interface_2534/`.
The owner-specific fourth-derivative envelope is still the active proof gate.

A conservative endpoint-envelope replay from the completed 2533 session is
also retained in `results/2533_signed_grid_endpoint_envelope_session46970.json`
and `.txt`. It rejects 2560 but leaves positive margins at 5120 and 10240,
which confirms 10240 as the preferred first certificate grid under a looser
price. The formal JSON replay in `results/2533_signed_grid_refinement_probe.json`
uses the tighter record-2532 center-third architecture and remains diagnostic.
