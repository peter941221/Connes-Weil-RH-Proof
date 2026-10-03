# 002 — 640-cell node-sum certificate

Status: `BLOCKED BY CURRENT VALUE BOX / REOPEN REQUIRED`. This subtask converts the actual-owner node
upper `ownerPanelNodeUpper2471` into a certified value for
`compositeNodeUpper2347` at the production grid
`cells = 640`, `step = stripRadius2303 / 320`.

The diagnostic record 2524 evaluates the same exact-owner coefficient balls,
panel geometry, and weighted node formula as the Lean definition:

```text
sigma = -1/2      composite node upper = 89.1680855402758...
sigma = +1/2      composite node upper = 89.1686519152897...
```

The directed MPFR replay in record 2525 gives 89.16808640598855... and
89.16865278044224... for the two signs. These values are still not a Lean
certificate, but they are high enough to expose the current budget mismatch.

## Execution order

```text
1. Freeze the 2338 and 2275 source hashes used by the owner arrays.
2. Re-evaluate every node with directed MPFR RNDD/RNDU arithmetic.
3. Preserve the finite-family sum before the final rectangle norm.
4. Store each node upper as an outward binary64/rational payload.
5. Sum the payload through a segmented Finset.sum_le_sum proof.
6. Compare both signs with the exact downstream endpoint pin.
```

The implementation must not reuse the 2453/2454 node certificate: those
constants belong to the excluded 2275 capture vectors. The owner is the 2338
repair family already instantiated by records 2460-2466.

Acceptance gates:

```text
directed MPFR node enclosure for all 641 nodes       PASS
independent replay of the 2524 diagnostic             PASS
outward payload and source hashes                     PASS
segmented Lean sum                                    PASS
both sigma signs below the frozen pin                 PASS
```

The current endpoint constants in `C1RouteAEndpointStrip.lean` are
`baseNormUpper2343 = 2.7790943782` and
`correctionNormUpper2343 = 231.2642026141`. The present node-box route adds
roughly 89 to the base-side node term before the 415 remainder, so it cannot
feed those endpoint pins. This is a scoped obstruction to the current
rectangle-node construction, not a no-go for the owner or Route A. Reopen only
with a named change: exact-point node evaluation preserving family cancellation,
a tighter panel representation, or a different endpoint budget.

Evidence:

- `docs/proofs/2524_owner_node_sum_diagnostic.md`
- `results/2524_owner_panel_node_price.json`
- `scripts/routea_owner_panel_node_price_2524.py`
- `ConnesWeilRH/Dev/C1RouteAOwnerPanelNodeUpper2471.lean`
- `docs/proofs/2471_owner_panel_node_upper.md`
