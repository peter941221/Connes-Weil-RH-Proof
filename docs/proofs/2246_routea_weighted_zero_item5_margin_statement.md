# 2246 — Strict signed-margin statement at the 2243/2245/2248 standing

Date: 2026-09-30

Consumer: the weighted-zero-measure C3' producer gate
`B_zm(rho, N) < epsilon(rho, N)` (records 2185/2186), ladder item 5: the
terminal analytic obligation of route `A.005.1`.

Verdict: **statement fixed, not proved**. The exact inequality and its
ledger are pinned; the missing brick is a certified downward enclosure of
the finite-window functional (the anchor is a binary64 sample).

## The statement

At the candidate `rho = 0.945 + 39.25244858548658 i`, `N = 0` (support
`5.12`, scale `0.80`, the 2103 direct known-prefix construction; anchor
`q_step_002 = -1675397327895.099`):

```text
there is eps0 > 0 and a certified downward enclosure q_lo with

    (-q_lo) - ( 4 * mult * B_upper * (owner/screen transfer)
                + known_error_sum )  >=  eps0,

where 4 * mult * B_upper is the Lean high-shell tail and the transfer is
the 2245 count brick times the per-node uniformity lemma.
```

## The ledger at the current standing

```text
anchor margin (sampled)                 1675397327895.099
known error sum  (2109)                 74601530.30234718    (4.452766460841471e-5 of margin)

high-shell budget, 2243 standing        11477128602.720102
high-shell budget, 2248 standing         4894093747.764274   (mult 301.83032993648527 -> 128.70692502980964)

count ratio, unconditional              0.41935483870967744  (<= 26 / 62)
count ratio, imported                   0.3387096774193548   (= 21 / 62)
transferred charge, unconditional       2052361894.223729
transferred charge, imported            1657676914.5653195

total charge, unconditional              2126963424.5260766  reading 0.0012695277646158757
total charge, imported                   1732278444.8676672  reading 0.0010339508223067488
slack, unconditional                    0.9987304722353841
slack, imported                         0.9989660491776933
```

## The three bricks

```text
L1  downward enclosure of |Q|     OPEN
    (direct finite-window functional; trapezoid / solve / quadrature
     outward; the 2109 known-error ledger prices the evaluation errors
     but is charged against the sampled margin, not an interval of it)

L2  complete-owner transfer       COUNT-SIDE-DONE / PER-NODE-OPEN
    (owner <= 26 unconditional, = 21 imported, at the stress point (2245);
     the per-node uniformity of the screen charges remains open, so the
     transferred-charge number is a reading)

L3  strict arithmetic             STATEMENT-FIXED
    (q_lo > total charge with positive slack; current slack ~0.9987)
```

`L1` is the load-bearing brick: the anchor `1675397327895.099` is a
single binary64 sample of the direct construction without an error bar.
Its enclosure is a finite numerical-analytic task (outward arithmetic on
the m=6400 grid, the solve, and the trapezoid quadrature), not a new
mechanism.

## What this closes and what it does not

Closed: the never-formally-written item-5 inequality now exists as an
artifact with its full ledger, against the tightened 2248 multiplicity
constant and the 2245 count brick; the numeric slack is `~0.9987` (was
`146x` headroom in the coarser bookkeeping).

Not closed: `L1` and the per-node half of `L2`; the strict inequality is
not established; no producer GO, no gate sign change, no RH claim.

## Provenance

- script: `scripts/routea_weighted_zero_item5_margin_statement_2246.py`;
- artifact: `results/2246_signed_margin_statement.json`;
- inputs: `results/2103_full_known_prefix_direct_owner_grid_m6400.json`,
  `results/2109_known_prefix_margin_ledger.json`,
  `results/2243_panel_cem_reprice.json`,
  `results/2245_owner_count_brick.json`,
  `results/2248_multiplicity_tightening.json`.