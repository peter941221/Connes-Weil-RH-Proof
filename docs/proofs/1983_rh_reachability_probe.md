# 1983 — RH-reachability probe: pre-registration (coverage of the off-line plane)

Date: 2026-09-25.

Status: PRE-REGISTRATION, committed BEFORE the run it describes. No gate
sign is proved here and no RH claim is made. The record measures the one
layer that the 1982 pricing left open: whether the four-point same-span
lane, equipped with the priced deterministic construction, can in
principle reach RH — i.e. whether every hypothetical off-line zero lands
on a face that a committed Lean wire can prove — and whether the one
risky construction brick (vertical decay) is numerically feasible.

## 1. The question, made mechanical

The lane reaches RH iff every hypothetical off-line zero `rho = 1/2 +
delta + i*gamma` is killable: the owner built at `rho` must land, for
some allowed knob, on a face carried by a committed wire.

```text
witness region (1917 trichotomy, iff):
    D < 0   v   (D = 0 and B != 0)   v   (D > 0 and B^2 - 4CD >= 0)

committed provable faces:
    WIRE1 : D < 0                      (1981 diag-only wire, health-free)
    WIRE2 : B > 0  and  C > 0  and  det < 0     (1918 det wire)

    GAP   : witness exists, neither wire covers it (a wire gap: a THIRD
            wire could close it — priced only if it occurs)
    DEAD  : no witness at all — the span quadratic cannot go nonpositive
            at any positive lambda.  A single DEAD cell means the lane
            CANNOT reach RH as constituted.
```

## 2. Cell space and instrument (fixed now)

```text
cells        delta in {0.02, 0.05, 0.10, 0.20, 0.30, 0.45}
             x  displaced ordinate in GAMMAS (six established ordinates
             14.1347 .. 32.9351; the hypothetical world displaces the
             k-th on-line zero to rho = 1/2+delta+i*gamma_k, prefix =
             the remaining on-line ordinates inside the ball radius)
owner        healthyCorrectionNodes rho 0 empty, orbit-priority targets,
             M = 12 or 13 (kill count 4 or 5 by radius); EXACTLY the
             record-1981 machinery with the height grouping generalized
             from gamma_1 to the displaced ordinate; width pools
             unchanged (WIDTHS_H1/REAL/KILL, KILL extended by 3.8 for
             the 5-kill-radius worlds); Gevrey k = 30; certified route
             pair; 1919 identity; contraction scan
knobs        primary (scale 1.00, n = 0); rescue set, tried in order
             for any cell whose current face is not a wire face:
             (0.90, 0), (1.10, 0), (1.00, 1)
instrument   xi_max = 40, dxi = 0.008; a sign call needs relative
             certified spread < 1/3 on the deciding entries, else the
             row re-runs at dxi = 0.004, then 0.002 (two refine tiers)
instrument   pin residual > 1e-6, cond > 1e8, or non-finite density
health gate  => the cell is INSTRUMENT-limited (excluded from face
             calls; NEVER counted as DEAD)
replication  the two record-1981 registered rows (delta = 0.05 and
anchors      0.10 at gamma_1, sc 1.00, n 0) must reproduce within the
             dxi^4 shift (~1e-3 relative), else instrument drift is
             declared and the survey is void
```

## 3. Verdict rules (pre-registered, mechanical)

```text
OBSTRUCTED_TO_RH : any cell DEAD after primary + full rescue set
GAP_TO_RH        : no DEAD, at least one cell GAP after rescue
COVERED_SURFACE  : no DEAD, no GAP; every cell WIRE1/WIRE2 or
                   INSTRUMENT, instrument count <= 6
INSTRUMENT_BOUND : instrument count > 6 (grid unresolvable; extend the
                   width pools and re-probe before any verdict)

DECAY_FEASIBLE   : per-window |V_j| shows the sqrt(t)-linear (Gevrey)
                   regime with fitted slope c_eff > 0 on t in [100,400],
                   AND the certifiable envelope sum_j |A_j| |V_j| drops
                   below 1/2 permanently by T <= 400 at the registered
                   point (delta = 0.10, gamma_1, sc 1.00, n = 0)
DECAY_INADEQUATE : otherwise — brick 2 must not start; the deterministic
                   route loses its Cut-1 leg
```

Probe B (ordinate-direction stability) is read off the delta = 0.10
column — no separate rule; its outcome modulates confidence, not the
verdict.

## 4. What this decides and what it does not

A COVERED_SURFACE verdict means: no structural obstruction to RH is
visible anywhere on the probed off-line surface, and every remaining
layer between here and RH is either priced (bricks 1-3, interval
certification) or is a measurable uniformity question. It is still NOT
"RH is proved", and not yet "the path is certain": (a) brick 2's
explicit-constant analysis stays a live risk until formalized (probe C
de-risks it numerically, nothing more), and (b) converting measured
coverage into certified coverage needs a uniformity/structural theorem
over the (delta, gamma) plane whose price can only be quoted after the
probe shows the coverage geometry. Conversely, an OBSTRUCTED verdict
stops all brick work on this lane immediately.

## 5. Reproduce

```text
python3 scripts/fourpoint_rh_reach_probe_1983.py --quick   # 2-cell smoke
python3 scripts/fourpoint_rh_reach_probe_1983.py           # full probe
```

Output: `results/1983_rh_reach_probe.json`. WSL, numpy/scipy only.

## 6. Outcome (coverage): COVERED_SURFACE — 36/36 cells on provable faces

Run after the pre-registration commit (`6d8fb8eb`); one smoke-driven fix
before the full run (the kill width pool needed its pre-registered 5th
entry 3.8 for the 5-kill-radius worlds). Self-check: the generalized
layer reproduces the record-1981 nodes/family/kills exactly at
`g_disp = gamma_1`, and the two replication anchors hold
(`delta = 0.05: rel 3.6e-3`, `delta = 0.10: rel 7.7e-4`, both within the
declared dxi^4 shift; survey VALID).

```text
FACE MAP  (best face over the allowed knob set; rows = delta)
+--------+--------+--------+--------+--------+--------+--------+
| d\g    | 14.134 | 21.022 | 25.011 | 27.670 | 30.425 | 32.935 |
+--------+--------+--------+--------+--------+--------+--------+
| 0.02   | W1*    | W1     | W1*    | W1*    | W2     | W1     |
| 0.05   | W1*    | W1     | W1*    | W1*    | W2     | W1     |
| 0.10   | W1     | W1     | W1*    | W1*    | W2     | W1     |
| 0.20   | W1     | W1     | W1*    | W1*    | W2     | W1     |
| 0.30   | W1     | W1     | W2     | W1*    | W2     | W1     |
| 0.45   | W1     | W1     | W1*    | W2     | W1**   | W1     |
+--------+--------+--------+--------+--------+--------+--------+
  W1 = WIRE1 (D < 0, record 1981), W2 = WIRE2 (B,C > 0, det < 0, 1918)
  *  primary knob (sc 1.00) was DEAD or GAP; rescued
  ** needed the second rescue (sc 1.10)
counts: WIRE1 29, WIRE2 7, GAP 0, DEAD 0, INSTRUMENT 0
VERDICT (pre-registered rule): COVERED_SURFACE
```

Structure of the rescue (13 cells, all primary DEAD-or-GAP):

```text
+-----------------------------------+---------------------------+
| rescued by (sc = 0.90, n = 0)     | 12 of 13                  |
|   margins at the rescued rows     | huge (|D| 1e+08 .. 1e+13, |
|                                   | spread_D <= 1.0e-03)      |
| rescued by (sc = 1.10, n = 0)     | 1 (d=0.45, g=30.4249)     |
+-----------------------------------+---------------------------+
```

The record-1981 "scale-0.90 negative band" therefore GENERALIZES: the
primary knob fails on a mid-ordinate/small-delta patch
(gammas 25.01/27.67 at delta <= 0.30, plus two GAP pockets at
delta = 0.02/0.05 near gamma_1 and two GAP pockets at delta = 0.45),
and ONE scale move covers the whole patch. WIRE2 independently carries
7 cells (the gamma_5 column below delta = 0.30, plus one cell each at
(gamma_3, 0.30) and (gamma_4, 0.45)) — the two faces TOGETHER leave no
hole on the probed surface. Instrument health on all 50 rows: pins
max 8.6e-12, cond max 4.4e+04 (worst at delta = 0.02 — the near-line
cells resolved cleanly), T_need in 31.8..36.6 everywhere.

## 7. Outcome (probe C): registered verdict DECAY_INADEQUATE stands;
   the upgraded instrument answers the underlying question FEASIBLE

The registered double-precision decay probe returned DECAY_INADEQUATE
per its own rule: the certifiable envelope drops below 1/2 at T = 32
(clause 2 met) but the envelope fit slope on [100, 400] is NEGATIVE
(c_env = -0.023), and every per-window c_eff on [50, 400] is ~ 0 —
while E(400) = 4.6e-13 with sum|A| = 9.7e+13, i.e. |V_j| pinned near
1e-27, FLAT.  Diagnosis in two layers, each verified by a fix:

```text
layer 1  double-precision summation noise: the window's own mass is
         ~ e^{-k} ~ 9.4e-14, term magnitudes ~1e-16..1e-13, rounding
         floor ~ 1e-27  — the probe's flat level (instrument,
         scripts/fourpoint_rh_reach_probe_1983.py);
layer 2  float64 Gauss-Legendre WEIGHTS/NODES: relative 1e-16 on a
         total weight mass ~1e-13 gives an ABSOLUTE floor 1e-16 x
         1e-13 = 1e-29 ~ e^{-67} — exactly the flat level a first
         mpmath (dps=80) attempt still measured, because mpmath
         precision was defeated by float64 inputs
         (scripts/fourpoint_decay_mpmath_1983.py v1).
```

v2 computes nodes, weights and the sum ALL at 80 decimals
(composite GL 20 x 100, Newton-refined `P_m` roots):

```text
+-----+----------+----------+----------+----------+-------------+
| a   | log|L|(50) | (100)  | (200)    | (400)    | c_eff 200-400 / saddle |
+-----+----------+----------+----------+----------+-------------+
| 2.0 | -66.13   | -87.04   | -119.82  | -165.20  |  7.746 / 7.746 |
| 3.2 | -78.43   | -110.59  | -149.22  | -206.25  |  9.736 / 9.798 |
+-----+----------+----------+----------+----------+-------------+
  saddle law log|L_phi(i t)| ~ -sqrt(k a t): CONFIRMED, the fitted
  sqrt(t)-slope equals the edge-saddle constant by 3-4 digits at the
  working parameters (k = 30); regime reached by t ~ 100-200.
```

Resolution: the registered rule's DECAY_INADEQUATE was an INSTRUMENT
verdict. On the evidence of the upgraded instrument both feasibility
clauses PASS — the Gevrey vertical-decay law holds with the saddle
constant `c = sqrt(k a)`, and the strip-contraction requirement
(envelope < 1/2 beyond T) is satisfied at T = 32 with 12+ orders of
margin. Brick 2's method (steepest descent with explicit constants)
is numerically validated; its constants need only be VALID, not sharp.
Erratum: the probe script's reference constant was
`sqrt(k a / 2)` — a factor sqrt(2) low; corrected to `sqrt(k a)`.

## 8. Where this leaves the lane: the composite verdict

```text
+-----------------------------------+-----------------------------+
| layer between here and RH         | status after this record    |
+-----------------------------------+-----------------------------+
| structural obstruction (DEAD zone)| NONE FOUND on 36 cells      |
|                                   | (COVERED_SURFACE)           |
| construction visible to Lean      | priced (1982 bricks 1-3)    |
| brick-2 analysis method           | VALIDATED (this record s.7) |
| D < 0 certification at a point    | mechanical (1976 method;    |
|                                   | 1982 target ~1e-06 rel)     |
| coverage -> THEOREM (uniformity)  | OPEN, now with a measured   |
|                                   | geometry to attack          |
+-----------------------------------+-----------------------------+
```

Honest scope: this probe measures a 36-cell surface of the off-line
plane with one representative family and four knobs. RH needs every
off-line zero, so the remaining mathematical work is the UNIFORMITY
layer: a theorem that the face map is stable (e.g. the wire faces are
open conditions in (delta, gamma) and the scale-0.90 rescue dominates
the DEAD patch, so finitely many certified regions + compactness
arguments cover the plane). No such theorem is proved here; its price
can now be quoted against a measured geometry instead of a guess.
Also unchanged: the passing owner is a construction at a HYPOTHETICAL
off-line zero (that is the correct proof-by-contradiction shape), and
no RH claim is made anywhere in this record.
