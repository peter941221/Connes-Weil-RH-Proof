# 1982 — Deterministic-route scout: the cardinal岔路 is dead, the Gevrey-formalization cost is the path

Date: 2026-09-25.

Status: SCOUTING. One rig, `scripts/fourpoint_cardinal_rscan_1982.py`,
results `results/1982_cardinal_rscan.json`. No gate sign is proved and no RH
claim is made. The record is a negative result plus a costed route map for
the deterministic construction — the answer to "which path can be made
certain".

## 1. What "certain" requires, precisely

The record-1981 GO_CANDIDATE lives on an explicit Gevrey-window family. For
the four-point same-span lane to produce a THEOREM, the object whose gate is
certified must be an admissible construction available to Lean, i.e. a
`CompactLogTest` (= Mathlib `TestFunction`, Schwartz/C-infinity, plus compact
support) satisfying the three base hypotheses: support in `Ioo baseLower
baseUpper`, `laplaceAt base w = 1` on every owner node, and the strip
contraction `||laplaceAt base (sigma + i t)|| <= 1/2` for `T <= |t|`.
Numerical signs on a family that Lean cannot see are not certifiable. The
deterministic route therefore has exactly two candidate shapes:

```text
beta  reuse the COMMITTED cardinal construction (record-1958 formulas,
      explicitSeed; pins already formal 1962-63, L1 budget formal 1977-78)
      at a better parameter r;
alpha formalize the Gevrey-window family itself (the family the certified
      rigs measure).
```

## 2. Beta is dead: the cardinal r-scan fails at every r

At the record-1981 registered point (`delta = 0.10`, `N = 0`, `M = 12`,
`n = 0`), scanning the seed width `r` (`= 1, 2, 3, 4`; the `r = 6` row was
cut by the session time budget after the pattern was already unambiguous):

```text
+-----+-------------+-------------+------------+--------------------------+
| r   | peak |xi|   | max|L_base| | T_need     | tail>4                   |
+-----+-------------+-------------+------------+--------------------------+
| 1   | 33.4        | 4.6e+05     | none       | 100%                     |
| 2   | 17.8        | 7.9e+04     | none       | 100%                     |
| 3   | 39.7        | 5.7e+05     | none       | 100%                     |
| 4   | 39.7        | 2.5e+06     | none       | 100%                     |
+-----+-------------+-------------+------------+--------------------------+
  pins exact (<= 6.7e-16, by construction); W(0) = 0 exact;
  gate entries 1e+13..1e+43 (meaningless: truncation-dominated);
  peak abscissa does NOT scale like 1/r and contraction does NOT improve.
```

Mechanism: by Fourier duality a WIDER window concentrates ITS OWN transform,
but the cardinal base is not a window — it is a 12-term interpolation
combination whose coefficients `y_z / (nodeProduct z z * L_seed 0)` grow
with the node count and control the transform. The failure is structural at
`M = 12` nodes, not a knob setting: record 1959 section 1.3 saw it at
`r = 1` on 8 nodes, and this scan confirms it does not go away on wider
seeds or on the 12-node owner. **The committed cardinal construction cannot
carry the registered owner. Beta is closed.**

## 3. Alpha is the deterministic path: its full cost list

The Gevrey-window family the certified rigs measure is
`f_j(x) = A_j exp(-k/(1 - (x/a_j)^2)) e^{i theta_j x}` on `|x| < a_j`, with
the coefficient vector `A` determined by the `M x M` interpolation system.
To make it a Lean object whose gate is certifiable, three bricks are needed:

```text
+----+-------------------------------------------------+-------------------+
| #  | brick                                           | size/risk         |
+----+-------------------------------------------------+-------------------+
| 1  | C-infinity of the flat window: exp(-k/(1-u^2))  | medium; Mathlib   |
|    | extended by 0 is C-infinity (flatness at the    | has the smooth    |
|    | boundary); a computable definition (exp + div)  | transition glue;  |
|    | with ContDiffinfinity proofs                    | one brick family  |
+----+-------------------------------------------------+-------------------+
| 2  | vertical decay of its Laplace transform:        | large; steepest-  |
|    | ||L_phi(a(sigma + i t))|| <= C exp(-c sqrt(k    | descent style     |
|    | |t|)) with EXPLICIT C, c — the strip            | estimates; the    |
|    | contraction and hence Cut 1 stand on this       | one real analysis |
|    |                                                 | brick             |
+----+-------------------------------------------------+-------------------+
| 3  | the interpolation system: det M != 0 (interval  | small/mechanical; |
|    | certified; measured cond 2.5e+03..1.3e+04) and  | interval          |
|    | explicit bounds on A = M^{-1} 1                 | arithmetic        |
+----+-------------------------------------------------+-------------------+
```

On top of these, the gate certification itself (record 1981 program) is
unchanged: interval-certify `D` (and `C`) at the registered point, the
seed-ladder rungs `4 <= j < M - 1` for `C_base4, C_corr2`, and the Cut-1
joint margin.

## 4. Where this leaves the lane

```text
+-----------------------------------+------------------------------------+
| question                          | answer after this record           |
+-----------------------------------+------------------------------------+
| is there a deterministic path?    | yes, exactly one: alpha (bricks    |
|                                   | 1-3 above), beta is closed by      |
|                                   | measurement                        |
| is the path finite?               | the brick list is finite and each  |
|                                   | brick has a known method; brick 2  |
|                                   | carries the only real analysis     |
|                                   | risk                               |
| is the path short?                | no. bricks 1-2 are weeks-scale     |
|                                   | formalization work; this record    |
|                                   | does not shorten them, it prices   |
|                                   | them                               |
+-----------------------------------+------------------------------------+
```

Honest scope: this record closes one fork and prices the other. Nothing
here shortens brick 2, and a failure of brick 2 (no explicit-enough decay
constant) would push the deterministic route back to the drawing board —
that risk is now localized to one brick instead of spread over the lane.

## 5. Reproduce

```text
python3 scripts/fourpoint_cardinal_rscan_1982.py --quick   # r=1 smoke
python3 scripts/fourpoint_cardinal_rscan_1982.py           # r scan
```

Output: `results/1982_cardinal_rscan.json`. WSL, numpy/scipy only.

## 6. Interval-certification target measured (refinement of the 1981 point)

The certified pair converges at the exact `dxi^4` rate (successive
differences shrink by ~16 per halving); extrapolated limit
`D* ~ -1.0737429e+06`:

```text
+----------+---------------------+-------------+
| dxi      | D                   | spread_D    |
+----------+---------------------+-------------+
| 0.0080   | -1.0728693974e+06   | 8.1e-04     |
| 0.0040   | -1.0736882705e+06   | 5.1e-05     |
| 0.0020   | -1.0737394423e+06   | 3.2e-06     |
| 0.0010   | -1.0737426406e+06   | 2.0e-07     |
| 0.0005   | -1.0737428404e+06   | 1.2e-08     |
+----------+---------------------+-------------+
```

The interval bracket worth cutting in Lean is therefore a ~1e-06 relative
window around `D*` (six to seven certified digits) — brick 3 of section 3's
cost list inherits this target. Instrument:
`scripts/fourpoint_refine_1982.py`, `results/1982_refine_target.json`.

## 7. Reproduce (addendum)

```text
python3 scripts/fourpoint_refine_1982.py
```
