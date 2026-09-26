# Record 1994 — Opposite-gates height audit: pre-registration

Date: 2026-09-26.

Status: PRE-REGISTRATION. No run has been executed. This document fixes the
registered cases, the verdict rules, and the falsifiable predictions before
the rig runs.

## Why this measurement (re-targeted Route A audit)

This record replaces the withdrawn 1801 "wide owner" plan as the Route A
viability measurement. Three committed results made that plan obsolete:

- Record 1802 withdrew the 1801b tailStart cap (quantifier substitution); the
  window side of the "gate narrow vs window wide" tension no longer exists.
- Record 1904 proved the universal window-contraction lower bound, killing
  base-window widening as a route.
- Records 1809/1931 force `0 < ICgate g.convolutionSquare` for every healthy
  detector owner, so the live Route A assembly is the 1902 two-span
  opposite-gates certificate (`carrierTwoSpanDeterminantCertificate_of_
opposite_gates`: `ICgate(u) <= 0 < ICgate(v)`), not the owner's own gate.

The route topology's `004_common_bottleneck_audit` recommendation 2 asks for
exactly this audit on the Route B owner class.

## Committed-data re-read (no new run; results/1983_rh_reach_probe.json, 50 rows)

Reading the committed (C, B01, D) rows through the 1902 lens:

- `det = C*D - B01^2 < 0` on 50/50 rows.
- Opposite gates (`C > 0` and `D < 0`) hold on 5 of the 6 probed ordinates,
  33/50 rows, at `sc = 1.00` or on the `sc = 0.90` band, with certified
  `spread_D` from 3.6e-5 to 1.1e-3.
- gamma_5 = 30.424876... is the unique hole: all 8 committed gamma_5 rows
  read `C > 0, D > 0` at `sc = 1.00` (vertex-branch face; `det < 0` via
  cross domination), and the only non-primary knobs tried there (`sc in
  {0.90, 1.10}` at delta = 0.45) read `C < 0`.
- gamma_6 = 32.935061... is the strongest height in the set: opposite gates
  at `sc = 1.00` for every probed delta, `|D|` up to 3.2e12, `spread_D`
  down to 3.6e-5.

The two unmeasured, decision-relevant gaps:

(A) Is the gamma_5 hole a rescue-band artifact? 1983 tried `sc != 1.00`
    only at `delta = 0.45` on that ordinate.
(B) Does the opposite-gates pattern survive the next two ordinates
    (gamma_7, gamma_8, beyond the committed 6-ordinate list)?

## Registered run (fixed)

Instrument: the 1981/1983 machinery verbatim (imports
`fourpoint_owner_density_1959` and `fourpoint_owner_completion_1980`;
`k = 30`, `dxi = 0.004`, `xi_max = 40.0`, certified Ap/B prime-route pair,
laws F80/F81 respected, `n = 0` throughout, witness/contraction diagnostics
mirrored from 1981). Only the node/width layer is height-generalized, and
only where the registered case requires it:

- gamma_5 rescue scan: EXACTLY the committed 1983 convention (6-ordinate
  kill list, 13-node owner) so the scan is comparable with the committed
  gamma_5 column; only the scale knob moves.
  Registered cases (15):
  `gamma = 30.424876125859513210`, `delta in {0.10, 0.20, 0.30}`,
  `sc in {0.86, 0.88, 0.90, 0.92, 0.94}`.

- Height extension: kill list extended to the 10 ordinates gamma_1..gamma_10
  (known-zeros under-approximation, same caveat class as records 1980/1981;
  owner size grows to 17 nodes). Width pools extended to keep same-height
  rows distinct. Registered cases (4):
  `gamma_7 = 37.586178158825671`, `gamma_8 = 40.918719012147495`,
  `delta = 0.10`, `sc in {0.90, 1.00}`.

## Verdict rules (fixed before execution)

```text
OPPOSITE_GATES_HOLD : at least one gamma_5 rescue cell with
                      C > 0, D < 0, spread_D < 1/3,
                      AND at least one opposite-gates cell at EACH of
                      gamma_7 and gamma_8 with spread_D < 1/3.

GAMMA5_HOLE_STRUCTURAL : no gamma_5 rescue cell with
                      C > 0, D < 0, spread_D < 1/3.

HEIGHT_COLLAPSE     : no opposite-gates cell at gamma_7 or at gamma_8
                      (whichever fails is named).

DEAD row            : non-finite gate entries or interpolation
                      conditioning explosion (cond > 1e8); recorded,
                      counted toward neither side.
```

The uniform-face expectation `det < 0` is registered as P3: any finite row
with `det >= 0` is reported as a face anomaly.

## Falsifiable predictions

- P1: the gamma_5 hole is a band artifact — at least one rescue cell reads
  opposite gates (mechanism: the scale-knot D-sign flip structure measured
  at the other five ordinates).
- P2: gamma_7 and gamma_8 each host an opposite-gates cell at
  `sc in {0.90, 1.00}`.
- P3: `det < 0` on all finite rows.

Any of P1-P3 may fail; failure semantics are fixed above.

## Boundary

Proxy owner (known zeros only; the height extension's kill list is an
under-approximation), grid instrument with certified route spread, no Lean
brick, no gate-sign theorem, no determinant theorem, no RH claim. This is a
survival screen in the sense of
`route/000_rh_mainline/002_b5_compactlog/002_route_b_fourpoint_span/
001_survival_screen.md`: it informs the Route A 1902-shape assembly
question and the Route B height-degradation watch simultaneously, and it
promotes nothing to a producer theorem.
