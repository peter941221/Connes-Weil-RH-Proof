# 2525 - current owner node-box budget obstruction

Date: 2026-10-03.

The directed MPFR replay of the 640-cell actual-owner node formula gives:

```text
sigma = -1/2      89.16808640598855...
sigma = +1/2      89.16865278044224...
```

The replay uses the 2338 exact coefficient-ball endpoints, the exact 2460
radii and modulations, the 2471 half-step panels, directed MPFR endpoint
arithmetic, and the 30-family sum before the final rectangle norm. The result
is consistent with the 2524 high-precision diagnostic.

The value cannot be imported into the current endpoint-strip budget: the
consumer constants are `baseNormUpper2343 = 2.7790943782` and
`correctionNormUpper2343 = 231.2642026141`, while the current node-box route
adds a base-side node term of about 89 before the 415 remainder. The total
therefore cannot satisfy the existing 2343 endpoint pin.

This is a scoped obstruction to the current wide rectangle node representation.
It does not reject Route A, the 2338 exact owner, or the signed C3' mechanism.
A valid reopen must change a named hypothesis or representation, for example:
exact-point node evaluation with preserved family cancellation, a tighter panel
box, or a revised endpoint budget proved from the same consumer.

The 2525 script initially exposed and fixed three interval-arithmetic defects:
scalar/range radius mixing, rectangle-shape nesting, and interval subtraction
using endpoint subtraction. The final run uses directed subtraction and matches
the 2524 diagnostic within about 1e-8 relative.

Evidence:

- `scripts/routea_owner_panel_node_mpfr_2525.py`
- `results/2525_owner_panel_node_mpfr.json`
- `docs/proofs/2524_owner_node_sum_diagnostic.md`
- `ConnesWeilRH/Dev/C1RouteAOwnerPanelNodeUpper2471.lean`
- `ConnesWeilRH/Dev/C1RouteAEndpointStrip.lean`
