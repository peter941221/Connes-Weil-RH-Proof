# 1980 — Face census on the committed owner data, pre-registered real-owner falsification run: PARK at the registered point

Date: 2026-09-25.

Status: RUN EXECUTED. Sections 1-4 are the pre-registration, committed
**before** the run (commit history is the witness: pre-registration
`09d1f539`, results in the same record's section 5, committed after).
Section 5 reports the outcome. No gate sign is proved and no RH claim is
made; the registered verdict at the registered point is **PARK**.

## 1. Result: the branch selection is refuted by the committed data

Record 1918 selected the map-106 §2 target (the vertex branch, `C > 0`,
`b > 0`, `det < 0`) from a probe on a bump surrogate family (`D > 0` on
18/18 cases). The committed-owner JSONs of record 1959 — the real owner
shape, `W = |L_base(1/2-2*pi*i*xi)|^(2(n+1)) |L_corr(1/2-2*pi*i*xi)|^2` —
never supported that selection. Census over the 36 committed rows
(27-row grid `results/1959_fourpoint_owner_density.json` + 9-point scale scan
`results/1959_scale_scan.json`):

```text
+--------------------------------+--------+-----------------------------+
| sign class                     |  rows  | note                        |
+--------------------------------+--------+-----------------------------+
| D < 0                          | 30/36  | robust across every knob    |
| D > 0                          |  6/36  | one corner only             |
| C > 0 (healthiness)            | 11/36  | knife-edge in the knob      |
| b > 0                          |  7/36  | flips between knots         |
| VERTEX (C>0, b>0, det<0)       |  2/36  | isolated points             |
| DOOR-A (C>0, D<0)              |  8/36  | adjacent-knot stable (5/9   |
|                                |        | of the scale scan)          |
+--------------------------------+--------+-----------------------------+
```

`D < 0` is not a numerical accident: on the 26-row JSON the certified
`Ap`-vs-`B` relative spread on the `D` entry is `1e-13 .. 1e-29` (worst
absolute spread `3.7e-05` against `|D| = 5.5e+14`), i.e. the sign carries
twelve or more certified digits on every row.

## 2. The Face-A reframe

The committed trichotomy (record 1917,
`exists_nonzero_lambda_quadratic_nonpos_iff`) gives a Cut-2 witness from
`D < 0` **alone**, with the closed-form positive coefficient `gatePlusRoot`
(`exists_pos_lambda_quadratic_nonpos`, no cross-term condition). The wires to
the committed consumer
(`exists_pos_lambda_gate_and_prefix_of_annihilator_gate_neg`) carry the gate
and the finite-prefix bound at that coefficient on a healthy detector, whose
only sign hypothesis is the pivot `C > 0`. Therefore on the owner the
binding obligations are

```text
    C > 0     and     D < 0,
```

and nothing else: `b` is not needed, and `det = C*D - b^2 < 0` is automatic
once `C > 0, D < 0`. The witness coefficient may be taken at the positive
root

```text
    lam+ = (B' + sqrt(B'^2 - 4*C*D)) / (2*C)  > 0        (C > 0, D < 0),
```

where `Q(lam) <= 0` holds on the whole interval `[lam-, lam+]`. On the
committed DOOR-A rows this choice makes the Cut-1 window factor
`(K^4 + lam)^2 / lam^2` (`K = 3 + |rho|`, `K^4 = 8.6e+04` at `rho` near
`gamma_1`) an O(1)..O(50) number, not a growing one:

```text
+------------------+-------------+-------------+------------+------------+
| committed row    | C           | D           | lam+       | window     |
+------------------+-------------+-------------+------------+------------+
| sc=1.10 g1 n=0   | +4.7487e+00 | -5.5255e+14 | 1.08e+07   | 1.02       |
| g2 d=.05 n=0     | +8.0080e-01 | -3.6362e+09 | 2.65e+04   | 18.2       |
| sc=0.86 g1 n=0   | +3.7233e+00 | -3.1005e+08 | 9.4e+03    | ~1.0e+02   |
+------------------+-------------+-------------+------------+------------+
```

This does not change any route ruling of map 106; it replaces the §2 sign
target (`C > 0, b > 0, det < 0`, three signs, two of them knife-edge) by the
formal fallback branch of §2 (`C > 0, D < 0`, two signs, one of which is
certified at 1e-13 on every committed row). The formal fallback is already
wired (record 1917); nothing new needs to be proved to consume it.

## 3. Pre-registered run (registered before execution)

One owner, one measurement, no free knobs at classification time.

Owner: `healthyCorrectionNodes rho 0 routeNodes` with `rho = 1/2 + i*gamma_1`
(`gamma_1 = 14.134725141734693...`, the accepted first ordinate, on-line to
classical precision), `N = 0`, `routeNodes = empty`
(the minimal instantiation; the ball radius is `2^(N+1) + 2 + dist 2 rho =
18.2140...`, so the closed-ball zero prefix is the ordinates
`gamma_2 = 21.022039638771555`, `gamma_3 = 25.010857580145689`,
`gamma_4 = 27.670321930357...`, `gamma_5 = 30.424876125859513`;
`gamma_6 = 32.935...` lies outside at distance `18.80`). With the
critical-line collapse of the orbit (`{rho, 1 - conj rho}` distinct) the
owner has `M = 10` nodes:

```text
0.5 +- 14.1347i (orbit, targets +1 / -1), 1.0 + 14.1347i (target -1),
0.5, 1, 1.5 (targets 0), 0.5 + 21.0220i, 0.5 + 25.0109i,
0.5 + 27.6703i, 0.5 + 30.4249i (kill targets 0)
```

The kill-set ordinates are external classical numerics (first five zeta
ordinates), used as node positions; this is a scoped instantiation of the
formal `sourceNontrivialZerosInClosedBallFinset`, which stays abstract.

Classification (fixed now):

```text
GO_CANDIDATE : C > 0 and D < 0 on the completed owner (default window
               xi_max = 40, dxi = 0.004, certified pair), with each sign
               margin exceeding 3x its certified spread
               (spread_C < C/3 and spread_D < |D|/3).
PARK         : C <= 0, or D >= 0, or any sign margin below 3x its spread.
```

On `GO_CANDIDATE` the next bricks are the interval certification of `C` and
`D` on this owner and the seed-ladder rungs `4 <= j < M - 1` feeding
`C_base4, C_corr2` (bounded mechanical work, method of record 1976).
On `PARK` the four-point same-span lane is frozen with a scoped no-go note
and the project returns to the map-043 O-programs; no further determinant
Lean work is started (per the decision gate of record 1979).

Reported either way, without classification force: pins, contraction
`T_need`, mass confinement, the 1919 variance-identity check, the `n = 0, 1`
and window-scale `{0.9, 1.0, 1.1}` robustness census (informational only —
classification uses the default point only), and the required tail budget

```text
    M_n^2 < xiMult * lam^2 /
            (4 * smc * (3/4)^shellStart * K^4 * (K^4 + lam)^2 * (2*pi)^12)
```

at `smc = 1`, i.e. the number the future `((1/2)^n * C_base4 * C_corr2)`
must beat on this owner.

Instrument: new rig `scripts/fourpoint_owner_completion_1980.py`, reusing the
certified machinery of `scripts/fourpoint_owner_density_1959.py`
(`phi` quadrature, dual-grid phase convention of law F80, measure weights of
law F81, certified pair `Ap`/`B`, 1919 variance check, contraction scan).
Runs in WSL on the current tree.

## 4. Provenance correction

The vertex-branch selection of record 1918 was made on a surrogate family and
never re-audited when the instrument moved to the committed owner shape
(record 1959). The rule this record adds to the lane discipline: **a branch
selection is attached to the family it was measured on; when the family
changes, the selection is re-audited before further work is planned on it.**

## 5. Outcome (run executed after the pre-registration commit)

Instrument health on every row: pins `max |L_base - 1| <= 2.2e-15`,
`max |L_corr - y| <= 9.7e-15`, interpolation condition number
`3.9e+02 .. 1.05e+03`, `W(0) <= 3.5e-40` (the committed double zero),
mass beyond `|xi| > 4 <= 9.9e-07`, certified pair `A`/`Ap`/`B` relative
spread `<= 3.6e-08` on `C` and `<= 1.0e-05` on `D`, 1919 variance identity
`<= 6.6e-05` relative (coarse-grid level; refinement study of record 1959
section 2.3 applies unchanged), strip contraction exists with
`T_need ~= 31.8` (`= 2.26 gamma_1`).

Registered point (window scale 1.00, convolution count `n = 0`):

```text
C  = -1.007020   (spread 1.0e-08)
b  = +1.5366e+01 (spread 5.7e-06)
D  = +7.5961e+04 (spread 8.1e-07)
det = C*D - b^2 = -7.6730e+04
```

`C > 0` FAILS with a margin of thirteen certified digits. Verdict per the
pre-registered rule: **PARK**.

Informational knobs (no classification force, recorded as registered):

```text
+-------+---+-------------+-------------+-------------+-------------+
| scale | n | C           | b           | D           | det         |
+-------+---+-------------+-------------+-------------+-------------+
| 0.90  | 0 | -0.998565   | -1.3473e+01 | +2.4067e+04 | -2.4214e+04 |
| 1.10  | 0 | -0.997313   | +1.7298e+01 | -7.0033e+04 | +6.9546e+04 |
| 1.00  | 1 | -1.000044   | +1.4232e-01 | -3.2292e+02 | +3.2291e+02 |
+-------+---+-------------+-------------+-------------+-------------+
```

`C` stays within `0.7 %` of `-1` on every knob — a flat, structural reading,
in contrast with the design-family `C`, which flipped sign between adjacent
knobs (record 1959 section 6). The default-point branch is `RAY`
(`C < 0, D > 0, det < 0`): a Cut-2 witness exists by the trichotomy, but the
committed consumer wiring requires the healthiness pivot `C > 0`
(`pinned_orbit_positive_pivot`), so the witness cannot be carried into the
prefix margin on this owner.

Mechanism (reading, not theorem): the committed owner forces `W(0) = 0`
exactly (the raw node `1/2` pins `L_base(1/2) = 1` and `L_corr(1/2) = 0`),
and the `N = 0` kill set places correction zeros at
`xi ~= -2.25, -3.34, -3.98, -4.41` while the surviving density peaks at
`xi ~= -2.0` — entirely inside the sigma-negative zone `|xi| > 1.0011`
(record 1920, probe A). With the `xi ~ 0` mass gone, the Archimedean
channel integral sits on the negative part of the sigma symbol and the pivot
reads `C ~ -1` steadily. The design family could place its mass closer to
the origin (its knob-fragile `C` signs came from that freedom); the real
owner cannot.

Consequence, as registered: the four-point same-span lane is **frozen with a
scoped no-go note**. Scope: this is a falsification at the registered point
of ONE admissible representative family (Gevrey windows, distinct widths,
`k = 30`) of the committed hypotheses at `rho = gamma_1`, `N = 0`,
`routeNodes = empty` — not an all-owner theorem; the committed construction
itself remains noncomputable and untouched. Per the registered consequence,
no further determinant Lean work is started in this lane and the project's
priority returns to the map-043 O-programs (`O1` FIO/shear position
estimate, `O2` uniformity, `O3` kernel forcing), which do not pass through
this gate.

## 6. Reproduce

```text
python3 scripts/fourpoint_owner_completion_1980.py            # registered run
python3 scripts/fourpoint_owner_completion_1980.py --quick    # coarse smoke
```

Runs in WSL on the current tree; numpy/scipy only. Output:
`results/1980_owner_completion.json`.
