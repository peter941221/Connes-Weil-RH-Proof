Record 2663 (part 2): the first unconditional off-diagonal membership
Date: 2026-10-11

Result

Positive.  The owner moment-matrix entry (0,3) lies in its committed home
rectangle, with every leaf on exactly `[propext, Classical.choice,
Quot.sound]`:

    theorem entry03Mem2663 :
        (analyticMomentInterval2597 0 3).Mem
          (ownerMomentMatrix2351 capturedModulations2584 capturedNodes2584 0 3)

(`ConnesWeilRH/Dev/C1RouteAEntryAssembly2663.lean`).  This is the first
unconditional membership of the 870 off-diagonal entries; the 30 diagonal
entries were closed by record 2644.  No producer, `SourceRH`, or RH claim
is made or implied.

1. The assembly chain (hand module, 19 audited declarations)

   For each coordinate X in {Re, Im} the chain is:

   - `ownerMomentMatrix2351 ... 0 3 = momentEntry2351 theta_3 node_0`
     (rfl), then `momentEntry2351_eq_normalizedIntegral2618`, the real
     scalar pull-out (`Complex.real_smul`, `Complex.re_ofReal_mul` /
     `im_ofReal_mul`), the definitional `entryF2663` rewrite, and the
     `storedWidth_sq_eq2663` tie, giving
     `Re(entry) = r3^2 * Re(∫_{-1}^{1} entryF2663)` (normalization 2618);
   - three-piece split (`entrySplit2663`, adjacent intervals at
     `-19/20`, `19/20`; `entrySplitRe2663`/`Im2663` through
     `Complex.add_re/im`);
   - center slice: `entryCentralDecompRe2663`/`Im2663` decompose
     `∫ = ∑_k Z_k` (the frozen tiling `entryTilingBall2663`) into
     `embedPair2542 (∑ c_k) + ∑ (Z_k - c_k)`
     (`embedPair2542_sum2663`, `Finset.sum_add_distrib`), and the
     deviation is bounded by `‖∑ diff‖ <= ∑ (|re| + |im|) <= CBAR`
     (`norm_sum_le_abs_re_add_abs_im_of_le2663` with `entryPanelsBall2663`,
     summed through `rat_cast_sum2663` and `sum_CBAR2663`);
   - the per-panel centers are bracketed by the bar sums through
     `entryPanelsCenterFstLo/FstHi/SndLo/SndHi2663` and the exactly
     replayed `sum_LOre/HIre/LOim/HIim2663` (`decide +kernel`), giving
     `LO - CBAR <= center coordinate <= HI + CBAR`
     (`entryCentralRe/Im{Le,Ge}2663`);
   - each edge slice is bounded by `(1/20) * 2^(-302)` from
     `entryEdgeLeft2663` / `entryEdgeRight2663` through
     `Complex.abs_re_le_norm` / `abs_im_le_norm` and `neg_abs_le`
     (`entryEdgePairRe/Im{Le,Ge}2663`);
   - the four coordinate bounds `entryRe/Im{Le,Ge}2663` combine the
     pieces by `linarith` under the nonnegative weight r3^2
     (`mul_le_mul_of_nonneg_left`) and close against the barrier
     inequalities `rectRe/Im{Lo,Hi}2663_{le,ge}2663`, whose literals are
     tied back to the row fields by `rect*2663_tie2663` (rfl + norm_num).

   `entry03Mem2663` is then the four-conjunct `ComplexRect2427.Mem`
   chain.  All bars and barriers are exact rationals; no float64 text
   enters any module.

2. Generated support modules (deterministic generator)

   `scripts/gen_2663_assembly.py` emits 13 modules from committed
   artifacts only (`results/2663_bars.json`, `results/2663_budget_recon.json`,
   the 2597 row literals):

   - `C1RouteAEntryBars2663.lean`: 60-significant-digit bar literals,
     190-arm dispatchers (`reLoBar2663` ... `chBar2663`), the frozen bar
     sums, and their `decide +kernel` replay theorems;
   - `C1RouteAEntryRect2663.lean`: the rectangle literals, the four row
     ties, and the four strict-coordinate barriers;
   - `C1RouteAEntryPanel2663B{00..09}.lean`: the per-panel consumer facts
     `entryCenterTie2663P{tag}` ... `entryBallAt2663P{tag}` (the
     `panelTrueBall2662` panels re-tied to `entryPanel2663` terms);
   - `C1RouteAEntryPanels2663.lean`: the five `forall k ∈ Ico 0 190`
     statements (`entryPanelsCenterFstLo/FstHi/SndLo/SndHi2663`,
     `entryPanelsBall2663`) by `interval_cases`.

   Determinism gate: after the one generator defect below was fixed, a
   re-run reproduced 12 of 13 modules byte-identically (the fixed module
   grew by exactly 3800 bytes = 190 x 5 bullets x the 4-char `show `);
   the 12 unchanged md5s keep their oleans valid.

3. Build evidence

   - Panels module green inside the combined run
     (`results/build_2663_membership_panels_assembly.log` on disk;
     `*.log` is repo-ignored); the same run failed only in the assembly.
   - Final run (`results/build_2663_membership_final.log`): footer
     `Build completed successfully (4882 jobs).`, `[4882/4882] Built
     ConnesWeilRH.Dev.C1RouteAEntryAssembly2663 (61s)`, 0 `error:` lines,
     0 warnings and 0 `uses sorry` in both new modules, and 19/19
     `#print axioms` records in the assembly exactly
     `[propext, Classical.choice, Quot.sound]` (plus 5/5 in Panels and
     12/12 in Rect from the cached replay).  Both oleans verified on
     disk by direct file test.
   - Freeze md5s: `C1RouteAEntryPanels2663.lean`
     `4be904729b115f8e12e82779d9e26891`, `C1RouteAEntryAssembly2663.lean`
     `ffcd37e18fab7e292efd837a637d6f31` (both md5-identical between the
     Windows tree and the building workspace).

4. Instrument lessons (fixed between the two assembly runs)

   - Interval-impact trap, statement form: `∫ x in a..b, f x + ∫ ...`
     parsed the second integral into the first integral's body (the
     documented swallowing law); the error surfaced as a bogus
     `Complex.add_re` pattern failure on a goal containing an integral
     of `f x + ∫ ...`.  Fix: parenthesize every summed integral in the
     statement.
   - `rw [← Real.exp_zero]` rewrote the FIRST `1` occurrence, inside
     `(1 - x ^ 2)`, not the goal's `0`; the type mismatch named
     `Real.exp 0 - x ^ 2` explicitly.  Fix: `have ... := Real.exp_le_exp.mpr`
     plus `simpa only [Real.exp_zero] using`.
   - The generator's `forall` bullets emitted the first `simpa` bracket
     item as `show X = Y from rfl` and the second without its `show`
     (parse error `unexpected token 'from'; expected ']'`); only the
     compiler caught it.  Fixed at the generator, then regenerated.
   - `measurableSet_lt continuous_abs.measurable measurable_const` is the
     resolving form for `{|x| < 1}` (precedented by
     `C1G8R3ConcreteWingMajorant.lean`); `measurable_id.abs.measurable`
     does not resolve.
   - `<` vs `≤` at a `Set.Ioc` membership split:
     `lt_of_le_of_lt hmin hx.1` yields `<`, the `Set.Icc` goal wants
     `≤`; use `le_trans hmin (le_of_lt hx.1)`.
   - The `(1/2)^302` literal in the two edge-pair lower bounds needs the
     scoped `set_option exponentiation.threshold 400 in` wrapper (with
     the explanatory comment) as in the Rect module.

Remaining off the diagonal

- 869 further off-diagonal memberships of the 870; the (0,3) chain is
  now the template (same tiling, same bars, per-entry rectangles).

The captured modulation/node convention and the 2597 interval naming are
as fixed by records 2597/2584/2661.