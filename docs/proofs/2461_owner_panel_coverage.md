# 2461 - exact-radius owner panel coverage probe

Date: 2026-10-02.

Verdict: `OWNER-PANEL-COVERAGE-PASS`. The 2459 box arithmetic was replayed
with the exact owner radius from 2342/2351 on 19 distinct production-grid
panels. Every family box and the composed 30-family sum contained five
exact-mpf sample values on every panel.

The panel set covers:

- negative and positive interior panels;
- the panel containing zero;
- both sides of every family support edge, with duplicates removed;
- the two global endpoint panels.

This is a coverage diagnostic, not a Lean certificate. It uses the same
2338 coefficient balls, frozen 2275 family parameters, exact rational panel
coordinates, composed complex rectangles, and 90-digit mpf-to-dyadic truth
replay as 2460. The formal gap remains the generic indexed Lean theorem and
the full weighted trapezoid/zeta attachment.

Evidence:

- `scripts/routea_owner_panel_coverage_2461.py`
- `results/2461_owner_panel_coverage.json`
