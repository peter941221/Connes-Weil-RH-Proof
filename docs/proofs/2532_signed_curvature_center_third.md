# Record 2532 — signed curvature center/third-variation feasibility

Date: 2026-10-03.

The active 2530 node payload still needs a whole-cell bound for the weighted
second derivative. Record 2532 tests a named enclosure architecture:

```text
cell center:
  keep the 30-family signed F'' sum intact
  add the coefficient-box scalar error at the center

cell variation:
  add (cell width / 2) * a familywise upper for |F'''|
```

The third-derivative term includes the coefficient magnitude
`|c_mid| + coefficient_error`; omitting this factor was caught in the first
script run and corrected before accepting the result.

The familywise third-derivative supremum is sampled on 17 points inside each
cell, so the result is a feasibility probe rather than a certified supremum.
The 2560-cell prices are:

```text
+----------+----------------------+----------------------+----------------------+
| sigma    | center/third rem     | total with node      | base margin          |
+----------+----------------------+----------------------+----------------------+
| -1/2     | 0.0511511647478674   | 2.738038541154359    | 0.0410558370456406   |
| +1/2     | 0.0508842733825677   | 2.726095736327747    | 0.0529986418722533   |
+----------+----------------------+----------------------+----------------------+
```

The result fits `baseNormUpper2343 = 2.7790943782` with useful sampled
headroom. It therefore selects this architecture for the next proof attempt:
replace the sampled familywise third-derivative maximum with a directed,
whole-cell enclosure. No Lean curvature payload has been imported yet.

Evidence:

- `scripts/routea_owner_signed_curvature_center_third_2532.py`
- `results/2532_signed_curvature_center_third_probe.json`
- `docs/proofs/2530_center_error_node_payload.md`
- `ConnesWeilRH/Dev/C1RouteASignedCenterError2531.lean`

Nonclaims: no Producer GO, no SourceRH, no RH.
