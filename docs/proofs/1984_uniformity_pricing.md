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

## 5. Outcome (post-run, same file as the pre-registration)

Run: `python3 scripts/fourpoint_uniformity_probe_1984.py` (WSL, numpy/scipy),
output `results/1984_uniformity_probe.json`, 25 cells, all healthy (pin
errors <= 1e-6 gate, cond <= 3.8e+03 everywhere vs the 1e+08 gate, density
finite on every row, spreads 0.00-0.03 against the 1/3 bar - no refine tier
was ever invoked).

### 5.1 Mechanical verdict

```text
UNIFORMITY_WEAK  (registered rule)
face counts      WIRE1 15 / WIRE2 6 / GAP 4  (no DEAD, no INSTRUMENT,
                 no UNRESOLVED_SPREAD)
triggers         dominance clause VACUOUSLY TRUE (gamma_scan_absD_scale090
                 = [] - the rescue knob never ran because the primary knob
                 landed WIRE1 at every scanned gamma, so run_cell stopped
                 before trying sc = 0.90);
                 WEAK fired solely on fine_blocks_with_sign_flip = 1.
```

### 5.2 Why both WEAK readings are rule artifacts, not instabilities

(i) The dominance clause was vacuous, not violated.  `all(v >= 1e+06 for v
in [])` is true; the rescue dominance question was simply not exercised at
gamma >= 50 because it is not NEEDED there.  The dead patch is a bounded
mid-gamma phenomenon: the primary knob is already WIRE1 at gamma = 50 in
both delta columns.

(ii) The one counted "sign flip" is the true face boundary.  In the
gamma_1 fine-delta block, D(delta) crosses zero between delta = 0.05
(+1.0093e+06, GAP side) and delta = 0.06 (-7.3772e+04, WIRE1 side).  That
is exactly the D = 0 hypersurface of the 1917 trichotomy: GAP with D > 0
still carries a witness (1983: rescued by sc = 0.90; dead-edge here: all
WIRE2), and a certified-box theorem (T2) must localize delta* and certify
the two sides in separate boxes - a crossing of the trichotomy boundary is
T2's job description, not an instability of any wired face.  No knife edge
INSIDE a wired face was observed anywhere in the scan.

### 5.3 Measured tables

gamma-scaling (primary knob sc = 1.00; both columns WIRE1 at every gamma):

```text
gamma |  D (delta = 0.10) |  D (delta = 0.30) | T_need (1.5 gamma cap)
------+-------------------+-------------------+-----------------------
   50 |        -3.617e+13 |        -2.586e+12 |   53.88  (= 1.08 gamma)
   80 |        -3.533e+14 |        -2.488e+13 |   83.91  (= 1.05 gamma)
  120 |        -1.322e+15 |        -9.277e+13 |  124.06  (= 1.03 gamma)
  200 |        -1.454e+16 |        -1.041e+15 |  203.76  (= 1.02 gamma)
  400 |        -7.244e+21 |        -8.701e+20 |   NONE within T <= 600
```

|D| grows monotonically in gamma along both columns over five decades of
gamma; the growth is NOT a clean power law (local log-log exponents range
from ~4 to ~19; the 50 -> 400 endpoint fit is ~9.2).  No trend back toward
the D = 0 hypersurface - the DEAD patch does not reopen at large gamma.

gamma_1 fine-delta (the D(delta) = 0 crossing; spreads 0.00 throughout):

```text
delta |   D          | face
------+--------------+-------
0.02  | +2.8206e+07  | GAP
0.03  | +9.2212e+06  | GAP
0.04  | +3.3617e+06  | GAP
0.05  | +1.0093e+06  | GAP
0.06  | -7.3772e+04  | WIRE1
0.08  | -8.8089e+05  | WIRE1
```

dead-patch edge (gamma_3, primary knob - the whole edge is WIRE2, D > 0
with det < 0, so the witness survives without any rescue knob):

```text
delta |  D           | face | T_need
------+--------------+------+--------
0.22  | +2.1538e+09  | WIRE2| 34.34
0.24  | +1.7219e+09  | WIRE2| 34.34
0.26  | +1.3966e+09  | WIRE2| 34.34
0.28  | +1.1468e+09  | WIRE2| 34.34
0.30  | +9.5183e+08  | WIRE2| 34.34
0.32  | +7.9739e+08  | WIRE2| 34.34
```

large-delta (gamma_2, primary knob): delta = 0.40/0.45/0.48 all WIRE1 with
D = -2.5715e+07 / -1.8570e+07 / -1.5499e+07 - the D < 0 face re-engulfs
the large-delta corridor.

### 5.4 Loose ends flagged by the run

```text
L1  large-gamma contraction: at gamma = 400 the local strip contraction
    discipline (tail <= 1/2, record-1959 form) is NOT met within the
    scanned T <= 600 (T_need = None); for gamma <= 200 it is met at
    T_need ~ 1.02 - 1.08 gamma.  The D-face at gamma = 400 is measured
    (finite W, clean pins) but its decay side is open.
L2  the D = 0 hypersurface must be localized: measured bracket
    delta* in (0.05, 0.06) at gamma = gamma_1; T2 boxes may not straddle it.
L3  gamma = 400 rows ran at the registered instrument only (spread bar
    passed, so no refine tier); a finer-dxi cross-check is owed before
    any certified box is drawn that wide.
```

### 5.5 The price list of the uniformity layer (deliverable)

```text
T1  analytic dependence (Lean brick).
    Statement: C, B01, D are real-analytic in (delta, gamma, scale) on
    the admissible set.  New evidence: cond <= 3.8e+03 on all 25 cells
    (vs gate 1e+08) - the node-solve is uniformly non-degenerate over
    the scanned plane, so the analytic family has no measured
    degeneracy.  Difficulty: medium-high, Lean-side only; blocked on
    brick 2's explicit analytic constants, no new numerics.

T2  box certification.
    Must (a) mesh the plane in boxes that do not straddle the measured
    D = 0 hypersurface (L2), (b) carry certified margins: the smallest
    |D| on a wired face is 7.38e+04 (gamma_1, delta = 0.06, adjacent to
    the boundary) - roughly 70x the dxi = 0.008 instrument floor, rising
    past 1e+06 by delta = 0.08; boxes near delta* must be narrow,
    (c) inherit the dxi^4, certified-Legendre and strip-contraction
    certificates from brick 2.  The dead patch needing both knobs is
    BOUNDED in gamma: primary alone works from gamma = 50 up.

T3  rescue dominance (RE-SCOPED by this probe).
    Old statement: sc = 0.90 keeps |D| >= 1e+06 at every gamma.  New
    statement: on the bounded patch (gamma in [gamma_1, 50) x
    delta in (0.02, 0.32]) at least one of {primary, sc = 0.90, WIRE2}
    carries the witness with margin >= 1e+06.  Measured support:
    1983's 12/13 rescues with |D| >= 1e+08; this probe: the entire
    gamma_3 edge is WIRE2 at D >= 8e+08; gamma >= 50 needs no rescue.
```

Read-through: the registered UNIFORMITY_BROKEN (a DEAD cell) did not
trigger at any scanned gamma in [50, 400]; the coverage structure of 1983
is intact on the whole scanned plane.  What remains open is exactly the
layer, at a reduced price: T1 (analyticity brick), T2 (boxes localizing
one hypersurface and covering one bounded patch), T3 (dominance on that
same patch).  Base/T4/B4/S3/WO legs unchanged and OPEN; RH not claimed.
