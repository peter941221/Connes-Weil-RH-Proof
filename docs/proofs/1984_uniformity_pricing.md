# 1984 — Uniformity-layer pricing: pre-registration (gamma-scaling, face stability, rescue dominance)

Date: 2026-09-25.

Status: PRE-REGISTRATION, committed BEFORE the run. No gate sign is proved
and no RH claim is made. Record 1983 left exactly one mathematical unknown
between the priced bricks and RH: the UNIFORMITY layer — promoting the
measured 36/36 face coverage to a theorem over the whole off-line plane.
This record pre-registers the three measurements that price that layer.

## 1. What the uniformity theorem must look like

The gate entries (C, B01, D) are finite sums of terms of the form
`integral of (analytic kernel) x |L(s)|^2 x dxi`, where `L` is a fixed
finite linear combination of fixed windows whose parameters (widths, node
list, weights from one 12x14 solve) depend REAL-ANALYTICALLY on
(delta, gamma, scale).  Hence each face of the 1917 trichotomy is an OPEN
condition (strict sign), and face membership can only change across the
zero hypersurfaces of C, B01, D, det.  The theorem shape is therefore:

```text
T1 (analytic dependence)   D (and B, C) are real-analytic in the family
                           parameters on the admissible set;
T2 (box certification)     interval arithmetic on a finite (delta, gamma)
                           mesh, with analyticity giving the covering;
T3 (rescue dominance)      the scale-0.90 knob keeps D < 0 by an explicit
                           margin on the patch where the primary knob dies.
```

T2/T3 are measurable NOW; T1 is a Lean-side analyticity brick.  This probe
measures what T2 and T3 must certify.

## 2. Scans (fixed now)

```text
gamma-scaling   gamma in {50, 80, 120, 200, 400}  x delta in {0.10, 0.30}
                x scale in {1.00, 0.90}            (20 rows)
delta-fine g1   delta in {0.02, 0.03, 0.04, 0.05, 0.06, 0.08},
                gamma = gamma_1, scale 1.00         (6 rows)
dead-patch edge delta in {0.22, 0.24, 0.26, 0.28, 0.30, 0.32},
                gamma = gamma_3, scale in {1.00, 0.90}  (12 rows)
large-delta     delta in {0.40, 0.45, 0.48}, gamma = gamma_2,
                scale 1.00                          (3 rows)
world model     exactly record-1983 (displaced ordinate, remaining
                established ordinates in the ball radius); width pools as
                record-1983 with the kill pool extended to six entries
                [2.2, 2.6, 3.0, 3.4, 3.8, 4.2] (large gamma puts all six
                established ordinates inside the radius; M = 14);
                contraction scan tmax = max(100, 1.5 gamma).
instrument      xi_max 40, dxi 0.008, spread bar 1/3, refine tiers 0.004
                then 0.002, health gate as record-1983.
```

## 3. Verdict rules (mechanical)

```text
UNIFORMITY_SUPPORTED : every row lands WIRE1/WIRE2; AND the sc = 0.90
                       rows keep |D| >= 1e+06 at every scanned gamma
                       (dominance persists); AND neither fine-delta block
                       contains a sign flip at instrument resolution.
UNIFORMITY_WEAK      : all covered, but |D| at sc = 0.90 < 1e+06 for some
                       gamma (dominance not uniform in gamma).
UNIFORMITY_BROKEN    : some cell DEAD after both scale knobs — the 1983
                       coverage does not extend and the lane stops.
```

Deliverable either way: the PRICE LIST of the uniformity layer — the
explicit statements T1/T2/T3 must carry, each with its measured evidence
and its Lean-side difficulty class.

## 4. Reproduce

```text
python3 scripts/fourpoint_uniformity_probe_1984.py
```

Output: `results/1984_uniformity_probe.json`. WSL, numpy/scipy only.
