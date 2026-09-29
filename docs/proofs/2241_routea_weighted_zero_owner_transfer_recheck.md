# 2241 — Owner-transfer re-check at the 2238 standing

Date: 2026-09-30

Consumer: the healthy `CompactLog` B5 selected detector, actual
`sourceNontrivialZeroSet` owner, same-owner `qw >= 0` producer.

Verdict: **the binding owner-transfer gap is the 2119 cardinality ratio,
and it now reads `1.721x` over the margin at the coarse product reading**
(`48.43 x 0.03553548732728288`). The registered composite-EM panel lever
(projected `0.010940194125321153`) would flip it to `0.530x` under the
same reading. The other two transfer records are either unchanged (2157)
or bypassed by the current certified lane (2134).

## The three transfer items at the 2238 standing

```text
item   verdict at re-check
2119   formal owner-cardinality bound 3002.5554464806 vs the 62-node
       screened family = 48.43x; the transfer enters the high-shell
       budget linearly with the count ratio (the B_zm aggregate sums
       over owner nodes), so
           2236 standing  48.43 x 0.07743395177596035 = 3.750x over margin
           2238 standing  48.43 x 0.03553548732728288 = 1.721x over margin
           + composite-EM 48.43 x 0.010940194125321153 = 0.530x (projected)
       alone, the 2238 standing needs the count bound sharpened by
       1.721x (3002.5554464806 -> at most 1744.8) to clear
2157   near-pin derivative-cost floor: an exact paper no-go for
       support-only uniform derivative budgets; the remaining input is a
       separation bound on the nonzero orbit targets. This channel is
       the correction's derivative seminorm, not the low-shell budget;
       2236-2238 do not touch it. Status unchanged.
2134   m=6400 sampled-tail extrapolation: scoped no-go (the 500..550
       alias cliff 2.2280960477922288e30). The current lane does not
       extrapolate a sampled tail at all: the high-shell tail is the
       Lean geometric assembly 4 * mult * B over the 2197-screen B, and
       B is certified by the 2234-2238 outward envelope. The decision in
       2134 listed exactly such an independently certified rule as the
       admissible replacement; the lane satisfies that role. 2134 stays
       a no-go for its own mechanism and is off the critical path.
```

The `1.721x` product is the coarse reading: it charges the owner set at
the full formal count ratio against a budget screened on the 62-node
family. Both directions of movement are registered: the 2119 count
refinement (needs `>= 1.721x` on its own) and the composite-EM panel
(projected `3.248x`, which alone flips the transfer inside the margin).

## What this closes and what it does not

Closed: an explicit, current-numbered re-check of the three transfer
records against the 2238 envelope, with the binding item isolated and the
required factor stated.

Not closed:

- the 2119 count ratio is still the binding transfer gap (1.721x over);
- the near-pin separation input (2157) is unchanged and open;
- the composite-EM projection is an estimate, not a certificate;
- no producer or RH claim.

## Provenance

- inputs: `docs/proofs/2119_routea_formal_owner_cardinality_bound.md`,
  `docs/proofs/2134_routea_evaluator_horizon_no_go.md`,
  `docs/proofs/2157_near_pin_derivative_cost_floor.md`,
  `results/2238_panel_dx2_reprice.json` (`tail_upper_over_margin
  0.03553548732728288`), projected reading from
  `docs/proofs/2238_routea_weighted_zero_panel_dx2.md`
- arithmetic: 48.43 x {0.07743395177596035, 0.03553548732728288,
  0.010940194125321153} = {3.750, 1.721, 0.530}