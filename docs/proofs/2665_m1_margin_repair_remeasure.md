# Record 2665 — M1: certified margins re-measured on the repaired coefficients

**Verdict: M1-CLOSED-ALL-MARGINS-SURVIVE-REPAIR (measurement grade).**
The 2338 ideal-interpolation repair moves every certified Route-A margin by
at most 3.5e-8 relative (L1 detector value) and 4.5e-9 relative (window
charge); all verdicts stay green with 1e9..1e12 absolute headroom. This
removes uncertainty source #1 from the 2026-10-11 strategy review ("margins
never re-measured on the repaired owner"). No producer GO, no gate lambda,
no Lean transfer discharged, no RH claim.

## Preregistration

- **consumer**: healthy selected detector producer margin — the gap pair is
  Lean-closed (2310 `hgap_of_certified_split`: window + tail <= 1e7, margin
  20.953x) but on the CAPTURED coefficients, which record 2337 excluded from
  the mandatory targets; the strip side was re-measured by 2340.
- **owner**: the same 30-family corrected a^2 basis (2275 capture: nodes,
  widths, modulations) with the 2338 ideal coefficient pair (exact
  interpolation repair), float64 realization of the exact balls, cast
  charged explicitly.
- **premise to remove**: "the certified margins survive the repair".
- **failure criterion**: any leg failing => a named no-go
  (`WINDOW-MARGIN-REPAIR-FAIL` / `L1-MARGIN-REPAIR-FAIL`) on this owner.

## Leg 1 — strip (already measured): record 2340

`results/2340_recomposed_point_panel_transfer.json`:
`all_nodes_fit_existing_pin = true`, 101/101 sigma nodes, worst node -50,
`status = RECOMPOSED_POINT_PANEL_TRANSFER_ENCLOSED_ONLY` (artifact grade;
the explicit transfer proof stays open in the A4 inventory).

## Leg 2 — window charge: `results/2665_window_margin_repair.json`

Instrument: the committed 2309 rig (`routea_hgap_transform_cert_2309.py`)
run at STEP_DENOM = 256 in one process, control (captured coefficients,
unpatched loader) then treatment (repaired pair injected through
`routea_direct_functional_difference_screen_2295.filon.load_owner`).

```
+--------------------------+---------------------------+------------------+
| quantity                 | value                     | note             |
+--------------------------+---------------------------+------------------+
| control charge_hi        | 477248.9858117574         | drift 0.0 vs     |
|                          |                           | committed 2309   |
| treatment charge_hi      | 477248.98791684554        | +4.410880280e-09 |
|                          |                           | vs control       |
| eps_cast (exact Frac)    | 9.081052295664025e-17     | charged: x(1+e)  |
| treatment_inflated       | 477248.9879168456         |                  |
| ratio_budget             | 0.04772489879168456       | of 1e7           |
| margin                   | 9522751.012083154         | committed was    |
|                          |                           | 9522751.01418824 |
| verdict                  | WINDOW-MARGIN-SURVIVES-   |                  |
|                          | REPAIR                    |                  |
+--------------------------+---------------------------+------------------+
```

Controls: C1 same-run reproduction of the committed denom-256 charge
(bitwise, drift exactly 0.0, gate `< committed` and `drift <= 1e-6` both
enforced); C2 the rig's own order-0 bitwise + sandwich controls; C3 cast
multiplier computed in exact Fractions from the 2338 balls. The coefficient
magnitudes moved at most 1.4e-11 (base) and 7.6e-4 (correction) relative
(rmax screen in the artifact). `inputs['radii']` stay the captured-owner
2302 object radii (over-cover; the storage slot prices a stored float this
run does not use — disclosed in the artifact notes). Wall 1883 s.

## Leg 3 — hmargin / 2109 ledger: `results/2665_l1_margin_repair.json`

Instrument: the 2249 L1 numeric chain re-executed verbatim from the rig's
own functions (`routea_weighted_zero_l1_enclosure_2249.py`), coefficients
injected at the two `np.linalg.solve` sites; control + treatment in one
process. A monotone-inflation screen is INVALID here (q is a signed
cancellation sum), so the value itself is re-measured — per the lane law.

Order faithfulness gate: the rig's own solved base/corr are BITWISE the
capture's stored hex arrays (`order_base_ok = order_corr_ok = true`), so the
2338 coefficient_rows inject positionally.

```
+--------------------------+---------------------------+------------------+
| quantity                 | value                     | note             |
+--------------------------+---------------------------+------------------+
| control q                | -1675397327923.575        | drift 0.0 vs     |
|                          |                           | committed 2249   |
| treatment q              | -1675397268663.944        | +3.54e-08 rel    |
| delta_q_cast (triangle)  | 8.54194960134819          | absolute, sound  |
| treatment margin_lo      | 1675395987120.101         | committed        |
|                          |                           | 1675396046388.27 |
| margin ratio             | 0.9999999646243808        |                  |
| charge_import (2109)     | 1732278444.8676655        |                  |
| verdict_import           | +1673663708675.2334       | > 0              |
| verdict_uncond           | +1673269023695.575        | > 0              |
| verdict                  | L1-MARGIN-SURVIVES-REPAIR |                  |
+--------------------------+---------------------------+------------------+
```

The cast perturbation is charged as the exact multiplicative pointwise
difference `(B+b)^2 (C+c)^2 - B^2 C^2` with `b = (eps/(1-eps)) * Lambda_b`
(triangle: `|c_exact| <= |c_run|/(1-eps)`), summed against `|kern*p2|`
because the physical kernel is SIGNED (a signed sum is not a bound; the
first treatment run's negative delta exposed this and was re-run). The
2109 known-error ledger is netted inside both verdict channels. Wall 533 s.

## Instrument laws (new, AGENTS section 2ap-adjacent)

1. **Loader-reentry law**: a rig's `grid_inputs()` re-invokes the owner
   loader internally; control-vs-capture guards must compare VALUES, not
   object identity (`is not` fails on the fresh parse).
2. **Signed-kernel perturbation law**: a coefficient perturbation charge
   through a signed kernel must be summed against the ABSOLUTE multiplier
   (`|kern*p2|`); the signed sum is not a bound — the tell is a control-arm
   "charge" at ulp scale and a negative treatment "charge".
3. **Multi-arm probe budgeting**: control + treatment interval arms in one
   process can exceed the 30-minute background default; pass an explicit
   long timeout (this run: 2 h) and, after a task kill, check whether the
   WSL-side python survived before relaunching (here the process tree died
   with the handle).

## Nonclaims

Measurement grade only. Not discharged by this record: the explicit Lean
transfer of 2340 (A4 inventory), the producer composition, gate lambda,
detector health at the repaired owner beyond these margins, producer GO,
SourceRH, RH.

## Erratum (same day): the A4 "first brick" already exists

The next-steps list of this record proposed writing the 2340 grid-to-strip
transfer into Lean as the first A4 brick. Starting that brick surfaced that
it was already committed, in three records:

+----------------------------------------------------------------------+
| brick                                   | record | module             |
+-----------------------------------------+--------+--------------------+
| exponential transfer law + grid         | 2312   | C1RouteAStrip-     |
| consumer (min-product transfer)         |        | Transfer.lean      |
| floor sampling + concrete 101-node      | 2313   | C1RouteAGrid-      |
| node consumer                           |        | Sampling.lean      |
| owner support at the pin                | 2314   | C1RouteAOwner-     |
| (tsupport correctedPhysical subset      |        | Support.lean       |
| [-stripRadius2303, stripRadius2303])    |        |                    |
+----------------------------------------------------------------------+

The 2340 grid max 706456.176 fits the 2313 consumer's node bound
`stripGridMax2303 = 2644542.8515` with 3.74x margin, so the measured side
is compatible with the committed consumer shape. The remaining A4 bricks
are NOT the transfer shape; they are (i) the 101-node min-product
certificates on the actual owner (the membership brick: consumes the
2560-2571 correction-second pricing, the 2455-2459 quadrature import and
the 2514-2523 remainder gate), and (ii) the owner identification of the
producer wiring's b/c with the correctedPhysical model (AGENTS 2am). A
draft module written against the mis-scoped reading
(`C1RouteAGridTransport2666.lean`) was deleted before any build; it was
strictly dominated by the 2312/2313 theorems (weaker hypotheses shape,
no new content).
