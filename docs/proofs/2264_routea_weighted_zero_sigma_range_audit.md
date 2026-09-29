# 2264 — Sigma-range audit: frozen direct-product constant vs centered strip

Date: 2026-09-30

Consumer: 2260 pinned the producer side to one Lean lemma, whose numeric
envelope is the frozen screen constant
`bUpper2243 = 9506275.102584327` (the rounded-up `(2π)² · C` with
`C = 240796.76135588222`, relative tie `1.18e-15` at 2260). The 2265
producer brick makes the chain interface
exact: the hypothesis must hold for the strip norms at every
`σ ∈ (-1/2, 1/2)` (the chain evaluates `laplaceAt F` at
`centeredXiCoordinate ρ = (ρ.re - 1/2) + i·ρ.im`). The committed 2197 /
2234 / 2243 envelope however tabulates `σ ∈ [0, 1]` with certified row
`σ = 1`. This record audits whether the frozen constant already dominates
the centered range at screen grade.

Verdict: **COVERED at screen grade, margin 3.3071×. The raw min-product
over `[-1/2, 1/2]` peaks at `2874525.124523096` (binding channel b, at the
strip edge `σ = -1/2`), which is `0.302382` of the frozen constant; the
raw maximum over the whole sampled window `[-0.6, 1.1]` is the `σ = 1`
value `3057372.2573045553` (the raw-2197 number, anchor reproduced
bitwise). The producer may therefore consume the frozen number at screen
grade; the certified envelope on `[-1/2, 1]` (2234-style panel /
coefficient / Lipschitz re-run) remains the registered numeric obligation
before the tie holds at certified grade.**

## Method

For `F = base ⋆ corr` the product law of
`CC20YoshidaConvolution.laplaceAt_convolution` and two integrations by
parts give, with `σ = Re s`,

```text
t² · ‖L(base)(s) · L(corr)(s)‖  <=  min( D2_b(σ) · M_c(σ), D2_c(σ) · M_b(σ) ),
M_f(σ)  = ∫ e^{σx} |f|,        D2_f(σ) = ∫ e^{σx} |f''|,
```

i.e. the min of the two product channels of the committed strip-weighted
norms (`b` = `corr''·base`, `c` = `base''·corr`). The audit recomputes
`M` and `D2` for all four row pieces from
`results/2234_build_cache.npz` on the committed grid
(`NX = 240001`, `a_max` from the cache) over `σ ∈ [-0.6, 1.1]` (341
points) and inverts out `C = min-product / (2π)²`. Anchors: at `σ = 1.0`
the four recomputed norms must reproduce the committed 2197 binding row.

Screening artifact: no producer GO, no gate sign change, no RH claim.

## Results

```text
range          argmax σ   max min-product       vs frozen  margin    channel
[0, 1]            1.0     3057372.2573045553    0.321616   3.109296  b
[-1/2, 1/2]      -0.5     2874525.124523096     0.302382   3.307077  b
[-1/2, 1]         1.0     3057372.2573045553    0.321616   3.109296  b
[-0.6, 0]        -0.6     2901133.1486646286    0.305181   3.276746  b
```

Anchor check at `σ = 1.0`: relative deviation `0.0` for all four row
norms (`base_M0 2.0033357887456087`, `corr_M0 913.4469710803505`,
`base_D2 6688.576604759935`, `corr_D2 1526140.687188009`), i.e. the audit
reproduces the committed 2197 binding row bitwise.

## Interpretation

- The min-product is *largest* at the positive edge `σ = 1` (the certified
  screen row) and decays toward the center: at `σ = -1/2` it is `0.94` of
  the `σ = 1` value. The frozen constant was frozen at the `σ = 1` repriced
  value, so it carries roughly the full 3.31× margin over the centered
  strip — the convention gap between the screen's `[0, 1]` table and the
  chain's `(-1/2, 1/2)` requirement is not merely covered, it is covered
  with the same headroom the screen already had.
- The maximum over `[-0.6, 0]` sits at the sampled edge `σ = -0.6` and is
  still below the frozen constant (0.305 of it), so the negative half is
  dominated throughout the sampled window; the risk is not in the sampled
  values but in the absence of a certified envelope there.
- The sup over the open strip `(-1/2, 1/2)` equals the max over the closed
  strip by continuity of the raw values; the boundary row `σ = -1/2`
  itself is the binding row reported above.

## What this closes and what it does not

Closed: the screen-grade dominance question — the frozen `bUpper2243`
dominates the raw centered-strip min-product by 3.3071×, with the 2197
anchor reproduced bitwise. The 2265 producer brick's hypothesis
(`min(D2_b·M_c, D2_c·M_b) ≤ B` on `[-1/2, 1/2]`) is satisfied
numerically by `B = bUpper2243` at screen grade.

Not closed: the certified envelope on `[-1/2, 1]`. The committed certified
re-run (2234-style panels / coefficients / Lipschitz) covers `[0, 1]`
only; the negative half has no certified enclosure, so the
`B = bUpper2243` consumption is screen-grade until that re-run lands. The
producer gate stays closed. No producer GO, no gate sign change, no RH
claim.

## Nonclaims

- binary64 trapezoid measurements on the committed grid; not outward
  interval enclosures;
- single candidate construction (2234 build cache); the 2103 stress
  candidates are not re-measured;
- the leaning on the frozen constant is the 2260-tie at screen grade;
  certified-grade consumption needs the negative-half envelope.

## Provenance

- script: `scripts/routea_weighted_zero_sigma_range_audit_2264.py`;
- artifact: `results/2264_sigma_range_audit.json`
  (md5 `02a5deeaf3b7f73a5db752a697c941b4`);
- frozen constant: `results/2243_panel_cem_reprice.json`
  (`bUpper2243 = 9506275.102584327`);
- construction cache: `results/2234_build_cache.npz`;
- chain interface: `ConnesWeilRH/Dev/C1SpectralWeil.lean:275`
  (`centeredXiCoordinate`), producer brick
  `ConnesWeilRH/Dev/C1RouteADirectProductDecay.lean` (2265);
- predecessor: `docs/proofs/2260_routea_weighted_zero_producer_assembly_recon.md`.