Record 2656: full 190-panel analytic-containment cover of entry (0, 3) — 189 modules GREEN
Date: 2026-10-10

Result

Positive.  `scripts/generate_panel_analytic_all_2656.py` parameterized
the committed record-2649 pilot certificate (panel 109) over the whole
record-2624 panel cover — 189 modules
`C1RouteAComplexPanelAnalytic2656P{TAG}.lean` (panel 109 stays the
committed 2649 pilot) plus the umbrella
`C1RouteAPanelAnalytics2656.lean` — and the batch built green
(0 error, 0 `uses sorry`, 0 module warning from the 2656/2655 modules;
the 80 replayed warnings are pre-existing Yoshida/Mellin-era modules;
verified from the build log, not the exit code).  Build:
`✔ [4107/4107] Built ConnesWeilRH.Dev.C1RouteAPanelAnalytics2656` +
`Build completed successfully (4107 jobs)`.  Each module ends in
`complexPanelAnalyticCertificate2656P{TAG}`, the per-panel containment
of the complex residual integral, 18 theorems deep (all module-local
names TAG-suffixed).

Sign-agnostic branches

The 2649 pilot had center 29/200 > 0 and may use `abs_of_pos` at every
sign site.  The cover centers span [-19/20, 19/20], so the template
branches on the center sign:

    site                     pos center         neg center
    |2c| strip (BETASIGN)    abs_of_pos 2c>0    abs_of_neg 2c<0
    |c + position| (ABSSIGN) abs_of_pos         abs_of_neg
    hnum outer calc          |2c+position| form (unified)

The `hnum` numerator bound is sign-agnostic: after `rw [abs_mul]` the
goal is `|2c+position| * |position|`, and the inner
`have h1 : |2c+position| <= 2|c|+1/200` is proved once via
`abs_add_le` + the BETASIGN strip, so both branches share the same
outer calc.

VAR landscape (VAR = 1/25 + 30*(2|c|+1/200)/200 / (1-B^2)^2, B = |c|+1/200)

    cohort            panels   VAR
    tightest          94/95    0.04225   (center +-1/200)
    median            all      0.28186
    vacuous (VAR>=1)  46       up to 29.9414 at panels 0/189

The 46 cut-adjacent panels carry TRUE but VACUOUS variation bounds
(VAR >= 1): the per-panel certificate holds, but it is useless as a
bound.  The partition brick (next record) must route those panels
through monotone edge bounds instead of the VAR budget.

Generator debug trail (four error classes)

1. Token pass: bare QQT/RR/CC tokens needed a word-boundary regex pass
   after the @@-dict replacement.
2. Def prefix: the 2648 emitter hardcodes `2648` inside def names
   (`complexPanel*2648P{TAG}`) while the file/module names carry 2655 —
   the template needs @@DPRE@@="2648" for defs and 2655 for imports.
3. Literal shapes: (a) rational literals must be emitted bare
   `(num / den)` so the site ascription decides the type —
   `((171 : ℚ) / 200 : ℝ)` elaborates `↑171 / 200` which does not match
   `(171 / 200 : ℝ)` in `rw [abs_of_pos ...]`; (b) the hnum outer calc
   must start at the ABS form `|2c+position| * |position|` (the
   post-`abs_mul` goal), not the bare form; (c) norm_num sites
   `(0 : ℝ) <= ((X : ℚ) : ℝ)` fail to unify against an ℝ-literal goal —
   the ℚ round-trip is only valid for cast-of-DEF sites
   (`((complexPanel... : ℚ) : ℝ)`), never for literals.

Scope

Analytic containment certificates per panel only.  No partition
theorem, no (0,3) entry containment against the committed 2597
rectangle, no off-diagonal claim, no Producer GO, no SourceRH, no RH.

4. Cross-module name collision: the template's @@R@@ suffix must expand
   to `2656P{TAG}`, not bare `2656` — per-record names build fine as
   separate oleans but collide the moment the umbrella merges 189
   environments (failure surfaces as an auxiliary `._proof_1_1` clash
   at the SECOND import).  The 2655 batch avoided this only because the
   2648 emitter already carries `P{TAG}` in def names.

Next obligations

1. Partition theorem over the 190 panel integrals, routing the 46
   vacuous-VAR cut-adjacent panels through monotone edge bounds.
2. (0,3) entry containment against `analyticMomentInterval2597_row_03`
   in the committed 2597 rectangle.
3. Parallel lanes: live change-integral enclosure (2653 seam premise);
   continued grid scale-out toward the full 20480 cells.
