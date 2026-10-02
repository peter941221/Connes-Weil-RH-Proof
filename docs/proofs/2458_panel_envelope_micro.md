# 2458 - W-C panel envelope shape probed at production grid spacing

Date: 2026-10-02.

Verdict in one line: the analytic per-family panel envelope - the
2455 W-C architecture - has a valid, tight, and cheap shape: on three
panels of the production grid spacing h = 2R/(N-1) with N = 120001
drawn from the 2275 capture, all 15 exact sample points are contained,
and the full-grid producer cost extrapolates to about 0.93 hours, so
the 10^5-scale attachment is bounded by Lean-side design, not by
computation.

## Setup

Same outward semantics as 2454 (dps 90, DELTA = 2^-200, complex sum
composed before the modulus).  Per panel [x0, x1]:

- bump box by monotonicity in |x| inside the family support, clamped
  to zero outside and to the inside endpoint on edge-straddling panels
  (the bump tends to 0 at the support edge);
- phase boxes by the certified Lipschitz shape
  cos t in [cos c - rho, cos c + rho], sin likewise, with c the
  midpoint argument and rho the half-width plus DELTA - exactly the
  shape a single Mathlib Lipschitz lemma can certify once;
- composed 2454 hull arithmetic per family, summed across the 30
  families.

Panels: interior x = 1/4, family 15 support edge, and the global
support edge (x near R - 3h/2).

## Readings

```
+--------------+------------------+------------+-----------------+
| panel        | max hull width   | containment | sec/panel      |
+--------------+------------------+------------+-----------------+
| interior     | 2.854283e-01     | 5/5        | 0.007          |
| family edge  | 2.813029e-09     | 5/5        |                |
| global edge  | 7.421255e-46     | 5/5        |                |
+--------------+------------------+------------+-----------------+
```

The widths track the function magnitude (the interior panel carries
O(0.1-1) values; the edge panels are astronomically small because the
bump is), i.e. the envelope is tight relative to what it bounds.
Full-grid estimate: 0.007 s x 120001 x 2 endpoints x 2 channels ~=
0.93 hours of exact-rational arithmetic.

## What this validates and what stays open

Validated: the envelope SHAPE (monotone bump box + Lipschitz phase
box + composed hull) contains the truth at production spacing, and its
producer cost is trivial.  The Lean-side commitments this sets up, all
still open: the two range lemmas (bump monotonicity, cos/sin Lipschitz
on rational panels) proved once; one generic panel-containment theorem
over array indexing (no per-panel theorems); the node-value attachment
for the trapezoidal sum of 2457; the zeta attachment (global m_j sups
or per-panel envelopes feeding panelQuadrature_le_2457); and the
support glue from interval integrals to the full-line stripNorm.  Per
the 2456 ruling the producer, when written, targets the 2338
coefficient balls, not the 2275 capture vectors used here.

Scope: mechanism probe on capture data, diagnostic only.  No Lean
module, no certificate, no strip norm discharged, no producer GO, no
RH claim.

Evidence:

- `scripts/routea_panel_envelope_micro_2458.py`
- `results/2458_panel_envelope_micro.json`
