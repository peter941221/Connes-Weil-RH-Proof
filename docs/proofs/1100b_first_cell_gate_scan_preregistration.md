# 1100b - first-cell-corrected orbit gate scan (pre-registration)

Date: 2026-09-02.

Status: PRE-REGISTRATION, committed BEFORE the run.  This record executes
the probe named in record 1100 section 5: resolve the sign of the
`orbitWindowSemiLocalGate` top over the triple-vanishing subspace by
correcting the arch body's missing first cell.  Consumer (map `004`
section 2): `sourceRH_of_orbitWindowSemiLocalGate`.  RH is not claimed;
GATE 1 untouched; evidence level NUMERICAL.  The probe is
`1100b_first_cell_gate_scan_probe.py`.

## 1. The corrected quantity

The record-1100 scan measured every total top at
`-(0.94..1.00) x step/2` (law 37): the certified 1020 arch body starts its
trapezoid at the first correlation lag (`positive = lags > 1e-12` in
`1020_lane_r_prime_free_spectrum.py`), missing the `[0, step]` cell of the
body integrand.  The corrected arch used by this scan is

```text
arch_corr(f) = [C F(0) + trapezoid of I over [step, 2a] + F(0) log tanh a]
             + step * (I(0) + I(step)) / 2
```

with `I(y) = (expm1(y/2) F(y) + (F(y) - F(0))) / sinh(y)` (the rig's own
numerator form), `I(0) = F(0)/2` (the removable limit; the numerator is
`y F(0)/2 + O(y^2)` against denominator `y + O(y^3)`), and `F(k)` the k-th
lag of the same fft autocorrelation array the rig uses.  The added cell is
the trapezoid completion consistent with the body's own rule:

```text
step (I(0) + I(step))/2 = step F(0)/2 + step^2 (F''(0)/4 + F(0)/16)
                          + O(step^3),
F''(0) = -integral (f')^2 <= 0   (f compactly supported)
```

so the correction is at most `step F(0)/2 x (1 + step/(8 F(0)))` - it
explains why the measured record-1100 offsets sat in `(0.94..1.00) x
step/2` rather than at exactly `step/2`.

Honest residual after the correction: the body trapezoid over
`[step, 2a]` still carries its second-order error
`~ (2a) step^2 / 12 x <I''>`, which at `a = 4`, grid 8001 reaches the
same `1e-5` scale as the corrected residual.  The scan grid is therefore
moved 8001 -> 32001 (step / 4, that error / 16, worst `~4e-6` at `a = 4`),
and the sign of the top direction is arbitrated by an INDEPENDENT
construction with no sliver and no step-grid body error (gate G-cell-3).

## 2. What the sign would mean, and what this probe cannot do

The gate functional on the vanishing subspace is the repo's model of the
Weil quadratic form restricted to `V` (triple-vanishing, compact
support): `qw = -Q` there, so `Q <= 0` on all of `V` at every orbit radius
is the all-of-V form of Weil positivity - RH-strength mathematics.  The
verdict branches therefore carry sharp meanings, both stated BEFORE the
run:

- If the corrected top is certified POSITIVE at some radius, the
  all-of-V sign statement is numerically false there and any C3 sign
  proof must restrict to the detector subclass (the record-1100 section-2
  pre-named consequence).  This is NOT and will NOT be labeled evidence
  against RH: a Weil-violation claim would require certified interval
  arithmetic on an explicit witness, not a float64 rig, and that
  escalation is named as the only honest next step in that branch.
- If the corrected top is certified NEGATIVE at every radius, the gate is
  numerically alive on `V` (law 34: evidence-only until a certified
  spectral-gap upper bound exists).

The scan still imposes NO detection constraint and NO normalization:
both branches concern the sign theorem on all of `V`, not the detector
subclass.  `F(0) = 1` on the orthonormal null rows (used by G-cell-2).

## 3. Gates (pre-registered; abort discipline as in 1097/1100)

```text
+----------+----------------------------------------------------+---------+
| Gate     | Criterion                                          | Class   |
+----------+----------------------------------------------------+---------+
| G-arch-1 | Environment drift of the imported rig vs the nine  | MEASURE |
|          | committed 1087 legendre anchors, recorded, <= 1e-4 |         |
|          | abs (grid 6001, correction off).                   |         |
| G-arch-2 | Adapted class (correction off) vs imported rig on  | ABORT   |
|          | the nine anchors <= 1e-12 abs (same interpreter).  |         |
| G-recon  | The probe's own re-implementation of the full      | ABORT   |
|          | body+tail+C F(0) pipeline equals the imported      |         |
|          | `_arch_of_function` value <= 1e-15 rel on the nine |         |
|          | anchor rows and every G-cell-3 function.           |         |
| G-repro  | Uncorrected scan at grid 8001 reproduces all 32    | ABORT   |
|          | logged run6 top_total values (31 valid rows plus   |         |
|          | the discarded a=4 K=32 row, value pre-discard)     |         |
|          | <= 2e-6 abs (same environment + 6-decimal print    |         |
|          | rounding 5e-7).                                    |         |
| G-cell-2 | Sliver mechanism readback on the G-repro rows: the | ABORT   |
|          | measured first cell over (step F(0)/2) in          |         |
|          | [0.30, 1.005].  Band set from the section-1        |         |
|          | expansion `ratio = 1 - step |f'|^2 / (2 F(0)) +    |         |
|          | step / 8`: small-window high-K rows carry large    |         |
|          | derivative mass, and a PRE-RUN calibration on five |         |
|          | representative rows measured ratios in             |         |
|          | [0.4171, 0.9989] (a=1 K=32 is the extreme; the     |         |
|          | formula predicts it).  O(1) sign or structure      |         |
|          | errors land at ~2, ~0.5, or > 1 and cannot reach   |         |
|          | this band.                                         |         |
| G-count  | Sieve anchors: a=1 -> 5 visible prime powers;      | ABORT   |
|          | a=2 -> 24.                                         |         |
| G-sym-t  | Prime matrices from shifts {+log q} vs {-log q}    | ABORT   |
|          | transpose-equal <= 5e-6 abs (grid 32001).          |         |
| G-closed | Sine closed-form overlaps vs analytic-shift route, | ABORT   |
|          | a=2 K=8, t=log 2 and log 3: fine grid 32001        |         |
|          | <= 5e-6 abs, coarse 16001 diff 3x-6x larger, null  |         |
|          | level <= 5e-6 abs.                                 |         |
| G-cell-3 | DECIDER: independent direct construction (GL in u, | ABORT   |
|          | Simpson in y from 0, analytic evaluator, no fft,   |         |
|          | no polarization, includes the first cell exactly)  |         |
|          | of arch for explicit functions vs the corrected    |         |
|          | rig <= 5e-6 abs on: first legendre x bump at a=2   |         |
|          | and a=4; third sine at a=2; and the corrected      |         |
|          | arch-matrix Rayleigh value at the top eigenvector  |         |
|          | of (a=2 leg K=16), (a=4 leg K=24), (a=2 sine       |         |
|          | K=20) - the decision-relevant directions.          |         |
| G-cell-4 | Direct construction internal y-refinement (4001    | ABORT   |
|          | vs 8001 y-nodes) <= 1e-7 abs on every G-cell-3     |         |
|          | function.                                          |         |
| G-row    | Per row: moment residual <= 1e-10 AND orthonorm.   | DISCARD |
|          | error <= 1e-10; identical to 1100.                 |         |
+----------+----------------------------------------------------+---------+
```

The corrected-scan fidelity stack: per-call arch certified 5e-6 by
G-cell-3 (worst-case top error `K x 5e-6`, realistically the smooth-bias
scale `~2e-6`), body trapezoid `<= ~4e-6` at `a = 4`, grid 32001.  The
verdict threshold 1e-5 sits above both.  G-basis (analytic evaluator ==
sampled basis on the grid, <= 1e-12) is retained inside the class as in
1100; it is what licenses the off-grid GL evaluations of G-cell-3.

Deviations from the record-1100 scan plan, all decided BEFORE the run and
listed here: scan grid 8001 -> 32001; first-cell correction on; new
G-recon/G-repro/G-cell-2/G-cell-3/G-cell-4; verdict thresholds moved from
the 1e-3 row-level threshold (set an order above the OLD 5.6e-05
fidelity) to the 1e-5 extrapolated threshold (an order above the NEW
fidelity).  No gate is weakened relative to 1100: every 1100 gate is
either retained verbatim (G-arch-1/2, G-count, G-sym-t, G-closed,
G-row) or subsumed by a stronger one (G-recon + G-repro + G-cell-2
replace the old same-environment anchor role with a run6 replay).

## 4. Verdict mapping (pre-registered)

```text
any ABORT-class gate fails -> ABORT: no verdict, no repo change.

T(family, radius) := geometric-increment extrapolation of the corrected
top_total K-sequence over its valid rows (same extrapolator as 1100).

H1b GATE-FAILS-ON-V (numerical, law 34): some T >= +1e-5
   -> a triple-vanishing direction carries a certified positive gate
      price at that radius: the all-of-V sign statement is false there;
      any C3 sign proof must restrict to the detector subclass.  Map 004
      P2/C3 rows updated (sign shape restricted).  No RH-direction claim;
      interval-arithmetic escalation named, not run.

H2b GATE-ALIVE-EVIDENCE (numerical): every T <= -1e-5
   -> the gate is numerically alive on V at every scanned radius; the
      named formal target is the certified spectral-gap upper bound
      (law 34 machinery).

else SPLIT2: tops pinned at zero within +-1e-5 at the 4x grid / ~50x
   fidelity upgrade; the per-radius sign table is recorded and the
   certified-upper-bound machinery is the next target regardless of
   branch.
```

No repo change is keyed to any branch except this record's verdict
section and, for H1b/H2b, the map 004 status rows (labeled NUMERICAL).
The README is not touched (README change guard).

## 5. Verdict (appended after the run)

PENDING.
