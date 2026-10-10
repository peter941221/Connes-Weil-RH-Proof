Record 2655: full 190-panel table cover of entry (0,3) — 189 modules GREEN
Date: 2026-10-10

Result

Positive: `scripts/generate_panel_tables_all_2655.py` emitted the
record-2648 pilot emitter over the whole panel cover — 189 modules
`C1RouteAComplexPanelTable2655P{TAG}.lean` (panel 109 stays the
committed 2648 pilot) plus the umbrella
`C1RouteAPanelTables2655.lean` — and the batch built green
(`✔ [3919/3919] Built ConnesWeilRH.Dev.C1RouteAPanelTables2655` +
`Build completed successfully (3919 jobs)`; 0 error, 0 `uses sorry`,
0 module warning).

Panel lattice (record-2624 pricing, verbatim):

    panels   190, indices 0..189
    center   panel_center(k) = -19/20 + (2k+1)/200
    width    half width 1/200 (cut 19/20)
    degree   55, complex numerator N = (beta + i*psi)*D - 60*(center + t)

Regression: EVERY panel re-runs the 2624 pipeline's
`build_complex_panel` and asserts byte-equality of the residual upper
and the panel integral against the emitted tables (189/189 passed) —
the same check the 2648 pilot ran on panel 109, now per panel.

Edge behavior (the two cut-adjacent panels behave as priced):

    panel   residual upper (float)
    0       4.00e-1     (edge)
    1       8.22e-10
    2       8.97e-17
    ...     interior panels ~1e-16 .. 1e-10
    187     7.55e-17
    188     6.15e-10
    189     3.30e-1     (edge)

Mechanism

The 2648 emitter is reused verbatim via monkey-patched TAG/RECORD
globals — zero divergence between the pilot data path and the batch
path by construction.  Each module carries the same eight
`decide +kernel` replays (primitive derivative, residual identity
with take/drop zero-slot checks, |re|+|im| modulus upper, integral
components) under the 2621 heartbeat ceiling.

Scope

Data layer only: no analytic containment (record 2656), no
off-diagonal claim, no Producer GO, no SourceRH, no RH.

Next obligations

1. Record 2656: per-panel analytic containment (the 2649 template
   parameterized over centers, with sign-agnostic absolute-value
   branches for the negative-center panels).
2. Partition theorem over the 190 panel integrals + monotone edge
   bounds; (0,3) containment against the committed 2597 row_03
   rectangle.
