Record 2663 (part 1): the (0,3) entry tiling brick and its exact ledger
Date: 2026-10-11

Result

Positive.  The two bricks the (0,3) membership assembly consumes are
proven and priced: the hand tiling module `C1RouteAEntryTiling2663.lean`
(green build) and the exact-rational 190-panel ledger with all four
strict-coordinate barriers holding
(`scripts/recon_2663_budget.py` v3).

1. Tiling module `ConnesWeilRH/Dev/C1RouteAEntryTiling2663.lean`

   - Entry geometry: `entryF2663 = normalizedMomentIntegrand2618 theta_3
     (r3^2) node_0` on the full interval (-1, 1); 190 panels
     `entryA2663 k = -(19/20) + k/100` tiling [-19/20, 19/20] with
     centers `entryCenter2663 k = -(19/20) + (2k+1)/200`, halfwidth
     1/200.
   - Edge decay (base-2 device): with `|Re(node_0)| * r3^2` bounded by
     `51923/10000`, the exponent real part on `19/20 <= |x| <= 1` is at
     most `-4000/13 + 51923/10000 <= -605/2`, and
     `e^(-605/2) <= 2^(-302)` follows from `2 < e` by
     `(e^1)^302 <= e^302` (`Real.exp_nat_mul`).  Each edge slice is
     bounded by `(1/20) * 2^(-302)` (`intervalIntegral.
     norm_integral_le_of_norm_le_const`), and `edgeBar2663_total` sums
     the two slices to the rational banner `2*(1/20)*2^(-302)`.
   - Tiling: `entryTilingAbs2663` (adjacent-intervals Ico sum,
     hint over `Set.Ico`), `entryShift2663` (per-panel substitution to
     the centered halfwidth-1/200 form,
     `integral_comp_add_left`), and `entryTilingBall2663` (sum
     congruence + endpoint evaluations `entryA2663 0 = -19/20`,
     `entryA2663 190 = 19/20`).
   - Coordinate glue for the generated assembly: `finset_sum_re2663` /
     `finset_sum_im2663`, the norm triangle through the L1 split
     (`norm_sum_le_abs_re_add_abs_im2663` and its `of_le` form),
     `rat_cast_sum2663`, and the `RatPair2542` embedding sum
     `embedPair2542_sum2663`.

   Build: direct `lean` in the WSL mirror, green -- 0 errors, 0
   warnings, 0 "uses sorry"; 23/23 `#print axioms` records exactly
   `[propext, Classical.choice, Quot.sound]`; olean written
   (`results/build_2663_tiling.log` on disk; `*.log` is repo-ignored).
   The module is frozen at md5 `8f85469c5251d6d1b6c4c61a815ea249`.

2. Ledger `scripts/recon_2663_budget.py` (v3, exact rationals only)

   Parsed from committed Lean literals: `r3sq` (`widthEntry3_2661`
   squared), `beta` (tied to `Re(node_0) * r3^2`), per panel the amp
   value/radius (2657), phase value/radius (2658), table integral and
   residual upper (2648/2655), and the 2656/2649 deficit.  Per-panel
   charge and residual mirror the 2662 proof chain; the ledger is

       total = r3sq * sum_k (charge_k + res_k) + 2*(1/20)*2^(-302).

   Readings: sum charge+res = 6.084522e-68, total = 3.274933e-67;
   `|r3sq * sum centers - rect center|` = 6.25e-69 (re) / 1.70e-69 (im)
   against rectangle halfwidth 4.324e-65 -- margin/total = 132.0216 (re)
   and 132.0354 (im).  The four strict-coordinate barrier facts the
   assembly replays (at 60-significant-digit per-panel floor/ceil bars,
   frozen sums LO/HI/CBAR in `results/2663_bars.json`):

       reBarLo = r3sq*(LO_re - (CBAR + EBAR)) >= reLo,
       reBarHi = r3sq*(HI_re + (CBAR + EBAR)) <= reHi,

   plus the im analogues (`EBAR = edgeBar`); all four hold exactly and
   are frozen in `results/2663_budget_recon.json` under `barriers`.
   VERDICT: LEDGER PASSES BOTH AXES.

Remaining to the (0,3) membership

- the DATA module (190-arm dispatchers + decide+kernel sum theorems for
  the bar literals and charge bars),
- the per-panel generated consumer facts (`entryBallAt2663P{tag}`, the
  `entryCenterFact2663P{tag}` four-conjunct rational bounds),
- the assembly sandwich (per-panel coordinate bars + CBAR through
  `norm_sum_le`, the edge terms through `entryEdgeRight2663` /
  `entryEdgeLeft2663` and `edgeBar2663_total`, the r3^2 tie, and the
  final barrier inequalities), concluding membership of the actual entry
  in `analyticMomentInterval2597_row_00` element 3.

No producer, `SourceRH`, or RH claim is made or implied by this record.
The captured modulation/node convention and the 2597 interval naming are
as fixed by records 2597/2584/2661.