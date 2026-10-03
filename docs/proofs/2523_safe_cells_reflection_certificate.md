# Record 2523 — discharge the 248 safe cell premises and bound the full remainder

Target: for `sigma = -1/2` or `sigma = 1/2`, prove all 640 per-cell
premises of `ownerPanelStripNorm_le_productionTable2521` with no numerical
hypothesis, and close the explicit gate

```text
localCurvatureRemainder2474 productionTable2523 (stripRadius2303 / 320) 640 ≤ 415.
```

Records 2514-2522 proved the exponential safe-cell estimate and the 392
fallback cells; this record closes the remaining 248 safe cells and the
640-cell total.

Grid provenance first. The certificate prices on the actual Lean grid
literal `stripRadius2303 = 65536001/10000000`. The 2517 capture price used
the float-derived radius
`2076918743413931858457251756481/316912650057057350374175801344`
(about 6.553600000000003); the two are not equal, so the old table could
not be reused directly as a Lean-side bound. Reassembled on the old radius
the table reads `414.5754133864649`; on the true grid the total is
`414.5754350875391` — the radius repair costs about `2.2e-5` of budget.

## Safe-cell scalar machinery (C1RouteASafeScalar2523)

The safe cell bound has the shape

```text
safeFamily2523 index i
  = exp(r_i / 2) * ownerProductionExpUpper2514 index i
      * safeFactor2523 (|Re c_i| + |Im c_i|) m_i r_i t_i,
```

where `t = ownerProductionT2516 index i` is the cell endpoint ratio and
the factor collects the second-derivative terms inherited from the 2514
production panel. Three doors reduce each family bound to rational
arithmetic:

- `exp_weight_rational2523` reuses Mathlib's `Real.exp_bound` (degree 20
  Taylor on `|r/10| ≤ 1`) raised to the fifth power, giving
  `exp(r_i/2) ≤ W` for each of the 30 exact owner radii.
- `split_upper_rational2523` splits `z = 30/(1 - a²)` into floor `n` and a
  remainder in `[0,1]`, and bounds
  `expNegOneUpper2498^n * (Taylor20(rem) + err) ≤ U`.
- `safeFamily_le_rational2523` multiplies the three nonneg pieces and
  lands each family on the `1/1024` grid.

The grid is `|x|`-symmetric, so cell `639 - index` has the same endpoint
ratio and the same exponential upper as `index`:
`production_t_reflect2523`, `production_a_reflect2523`,
`safeFamily_reflect2523` and `safeSum_reflect2523` prove it exactly. This
halves the work: only the 124 right-half cells 320..443 carry generated
proofs; the left half follows by reflection.

## Generated witnesses

`scripts/routea_safe_certificate_2523.py` computes every witness with
exact `Fraction` arithmetic and emits:

- `C1RouteASafeConstants2523`: 30 weight bounds, the exact `e^-1` power
  chain, and the 30-term sum chain.
- `C1RouteASafeCells2523Part00..15`: 8 cells per module, 30 family bounds
  plus a cell sum each (3880 theorems total).
- `C1RouteASafeCertificate2523`: the table, reflection glue, and the
  640-cell gate.

Lean re-proves each inequality by `norm_num`; no floating-point assertion
is imported anywhere. The generator's `--check` mode re-derives the grid
parse, all rational witnesses, and all source and module hashes.

## The 640-entry total without a monolithic evaluation

The first build let a single `norm_num` unfold all 640 entries of
`productionTable2523` (124-arm match plus two `if` reductions each): whnf
timeout at `maxHeartbeats 8000000`. A single explicit 640-leaf addition
chain also timed out at 1M heartbeats during statement elaboration. The
accepted shape keeps every declaration small:

- nine `remainder_peel` lemmas split `Finset.range` through an explicit
  literal rewrite `640 = 64 + 576` and `Finset.sum_range_add`,
- ten `remainder_segment` lemmas each unfold exactly 64 entries inside
  one bounded `norm_num`,
- the gate compares ten exact rationals against 415.

The failed attempts stay in the build log; regeneration follows every
generator edit, and the accepted build elaborates the current file.

## What is now unconditional

- `safe_hcell2523`: all 248 safe cells, both signs, only the sign
  hypothesis.
- `production_hcell2523`: all 640 cells, both signs.
- `productionTable_remainder_le_415_2523`: the table total is at most 415;
  exactly `41732529736545736515534300074794459/100663296000000000000000000000000`
  = `414.5754350875391`, margin `0.4246`.
- `ownerPanelStripNorm_le_nodes_add_415_2523`:
  `stripNorm sigma ownerPanelSumValue_2467 ≤ compositeNodeUpper2347
  (ownerPanelNodeUpper2471 sigma stripRadius2303 (stripRadius2303/320))
  (stripRadius2303/320) 640 + 415`.

## What remains open

This is the remainder half of the strip budget only. Still open: the node
sum itself (`compositeNodeUpper2347 (ownerPanelNodeUpper2471 ...)` is
consumed, not certified), the identification of the 2463 midpoint
coefficients with the exact interpolation-repair solution (a midpoint in
the box is not a certified box point), the selected-detector signed
budget, and RH. Nothing here claims any of them.

Evidence and reproduction:

```sh
python3 scripts/routea_safe_certificate_2523.py --full
python3 scripts/routea_safe_certificate_2523.py --check
lake build ConnesWeilRH.Dev.C1RouteASafeCertificate2523Audit
python3 scripts/validate_safe_build_2523.py --mirror BUILD_MIRROR --log BUILD_LOG
```

Run the build under `scripts/run_resource_aware_task.sh`, retaining the
log. `results/2523_safe_certificate.json` pins the witnesses and sources
with status `EXACT_WITNESSES_BUILD_REQUIRED`; the build/audit acceptance
is recorded separately in `results/2523_safe_build_validation.json`.

Accepted validation: the resource-managed Linux build completed
successfully (3918 jobs; 3919 with the audit target). All seven audited
declarations — `safeSum_reflect2523`, `safeCell320_2523`, `safeCell443_2523`,
`safeRight_hcell2523`, `production_hcell2523`,
`productionTable_remainder_le_415_2523`,
`ownerPanelStripNorm_le_nodes_add_415_2523` — depend on exactly
`[propext, Classical.choice, Quot.sound]`. All 206 project-source files in
the import cone match the authoritative working tree byte for byte, the
mathlib checkout matches the pin, and the generator/fallback artifacts
chain-hash to the built tree. Initial failures retained in local logs: the
monolithic 640-entry `norm_num` (whnf timeout) and the 640-leaf chain
(elaboration timeout) above, plus one silent shape bug where an
unparenthesized offset parsed as `(productionTable2523 64) + i`.
