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
