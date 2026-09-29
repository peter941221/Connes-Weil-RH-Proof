# 2244 — Transfer and obligation ledger at the 2243 standing

Date: 2026-09-30

Consumer: the healthy `CompactLog` B5 selected detector, actual
`sourceNontrivialZeroSet` owner, same-owner `qw >= 0` producer.

Verdict: **status record, no new numeric claims**. Two of the six ladder
items closed in the 2242-2243 batch (the certified zero count and the
composite-EM panel landing), so the 2119 coarse transfer product now sits
inside the margin (`0.3317529367828551`); the remaining obligations are the
2157 near-pin separation input and the strict signed margin (item 5), plus
the formal complete-owner transfer itself, which the coarse product reads
but does not prove.

## The ladder at the 2243 standing

```text
item                              status at 2243            number
1. all-30-node outward envelope   executed (2229)           binding node 2 charge (2229)
2a. operand construction ledger   paid at the rounding     c-radius 1.12e-05 rel; w 9.2e-14
                                  level (2233/2237/2239);  (2233); generation certified
                                  node-position exactness  (2237, delta_max 9.49e-29);
                                  booked to the 2119 item  x over all 30 nodes (2239)
2b. finite-sum accumulation       closed per-term; stitch  zero deficits (2232); all-node
                                  priced                   bitwise ledger (2239)
3. uniform charge vs budget       priced (2231)            1.4068690278731986e-04 of 6.2550323e-05
4. complete-owner transfer        OPEN; 2119 reading now   ratio 48.428313652912905
                                  inside (see below); 2157  x 0.006850392090059914
                                  open; 2134 bypassed;     = 0.3317529367828551
                                  2197 enclosure executed
5. strict signed margin           OPEN (this record)       anchor 1675397327895.099
```

## 2119: the coarse product closes

The formal owner-cardinality bound `3002.5554464806` against the 62-node
screened family gives the unchanged ratio `48.428313652912905`. Read as a
linear count transfer against the high-shell budget:

```text
2236 standing  48.428313652912905 x 0.07743395177596035  = 3.750x over
2238 standing  48.428313652912905 x 0.03553548732728288  = 1.720923726094767x over
2243 standing  48.428313652912905 x 0.006850392090059914 = 0.3317529367828551x (inside)
```

The registered count-refinement lever (sharpen the bound by `>= 1.721x`)
is moot at this reading. The reading is not a proof of the transfer: it
charges the owner set linearly at the formal count ratio, and the actual
transfer argument (what the ratio must multiply, and why) remains item 4's
open content. What changed is that the numerical side no longer forces it.

## 2157: unchanged and open

The near-pin derivative-cost floor stands: an exact paper no-go for
separation-free support-only uniform derivative budgets
(`derivativeCost >= 4 exp(-X S)/(delta X L^2)` diverges as the pin-target
distance `delta -> 0`). The remaining admissible inputs are a separation
bound on the nonzero orbit targets (research-grade) or a signed estimate
avoiding the derivative seminorm; the detector target `t = rho + 1/2` has
automatic separation, the orbit target `rho` does not. The 2242-2243 batch
does not touch this channel (it is the correction's derivative seminorm,
not the low-shell budget).

## 2134: bypassed

Unchanged from 2241: the current lane never extrapolates a sampled tail —
the high-shell tail is the Lean geometric assembly `4 * mult * B` over the
certified outward `B`, which is exactly the "independently certified rule"
2134 listed as the admissible replacement. 2134 stays a no-go for its own
mechanism and is off the critical path.

## 2197: the outward enclosure is executed

The 2230 inventory recorded the low-shell item as "the outward enclosure of
the base/correction functions, their second derivatives, and the
coefficient solve is still unpaid". That enclosure now exists: certified
generation radii (2237), outward direct-product envelope (2234-2236),
zero-count certificate for the four channels (2242), and the composite-EM
repricing (2243), landing at `C_upper = 240796.76135588222`,
`tail/margin = 0.006850392090059914` — `3.109295925568858x` the 2197 screen.
The 2197 screen itself is superseded as the budget carrier by this
envelope; the sampled lower screen (2195) remains a screen, not a bound.

## Item 5: the strict signed margin

Still open, and now the terminal analytic obligation: the producer needs
the strict sign of

```text
archimedeanTerm + integral(actualAggregate) <= -epsilon
```

with its own certified margin, not the candidate anchor. The numerical side
is inside: the high-shell budget upper sits at `0.006850392090059914` of
the anchor (`146.0x` headroom), so no further numeric sharpening is
required to make room for the margin — what remains is the sign-side
argument on the actual owner, which is Lean/analytic work, not numerics.

## What this closes and what it does not

Closed: the status inventory — every ladder item is either executed,
priced, or explicitly open with its required input named.

Not closed:

- the formal complete-owner transfer (item 4) — read inside, not proved;
- the 2157 near-pin separation input;
- the strict signed margin (item 5);
- no producer GO, no gate sign change, no RH claim.

## Provenance

- prior ladder: `docs/proofs/2230_routea_weighted_zero_operand_provenance_and_owner_transfer_preflight.md`
  (items 1, 2a, 2b, 3, 4, 5);
- 2119 ratio and reading convention: `docs/proofs/2241_routea_weighted_zero_owner_transfer_recheck.md`;
- 2157/2134: `docs/proofs/2157_near_pin_derivative_cost_floor.md`,
  `docs/proofs/2134_routea_evaluator_horizon_no_go.md`;
- current margin reading: `results/2243_panel_cem_reprice.json`
  (`tail_upper_over_margin 0.006850392090059914`,
  `transfer_2119.over_margin_at_2243 0.3317529367828551`);
- arithmetic: `48.428313652912905 x {0.07743395177596035,
  0.03553548732728288, 0.006850392090059914} = {3.750, 1.721,
  0.332}`.