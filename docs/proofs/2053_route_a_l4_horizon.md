# 2053 — Route A link L2: L4 full-line tail outcome + the φ-quadrature resolution horizon of the committed evaluator

Verdict: **L4-PRICE-FAIL + PHI-HORIZON-DOMINANT** at the registered owner
(one-copy G8-H, ρ = 0.6 + 40.9187190121475i, scale 0.88, K = 30, support
9.504).  Two measured statements, both against frozen pre-run rules:

1. **L4-PRICE-FAIL** — the registered 2041 kill fires: the tail bound
   assembled from the LANDED Gevrey rung constants (records 1986/1987/1988)
   is `T_bnd(40) = 6.515715e+41`, i.e. `6.5e22` x the `1e19` L2 bar and
   `5.9e21` x `|Q| = 1.1111e20`, and it GROWS with the window
   (`4.053658e+42` at X = 200) — no window widening converges it.

2. **PHI-HORIZON-DOMINANT** — the committed φ-quadrature rule's own error
   DOMINATES the committed functional's value at this owner.  The committed
   rule (m = 400) reads `Q_400(40) = -1.1111757839943646e+20`; the same
   pipeline at m = 1600 and m = 6400 reads `-3.4060498718812666e+12` /
   `-3.4060498718959634e+12` (mutual rel `4.3e-12`); the difference
   `|dQ| = 1.1111757e+20` is 3.3e7 x the (m-converged) window integral.

Probe: `scripts/routea_l4_horizon_2053.py` (md5
`b287cb2efbaf6e9bd034a3aa6aac76c8`, WSL ext4 mirror run, 1183.0 s),
artifact `results/2053_l4_horizon.json` (md5
`275a4e07aa4453b4ae661275d90f3743`).  Supporting diagnostic (per-unit-bin
localization of the window mass): `scripts/diag_2053_loc.py`, readings in
section 4.

## 1. Frozen rules and controls

Header-frozen rules (script lines 21-38, verbatim in substance):

- C0a truth-vs-committed soft control at (a = 1.76, t = 2): rel <= 1e-3.
- C0b window control: probe `Q_{m=400}(40)` vs the committed record-2037
  `q_h1 = -1.11119e20` (`|Q| = 1.1111e20`; cross-read `-1.11126e20` at
  record 2041): `|Q_400|` rel <= 2e-2 AND the sign must be negative.
- C1 truth pinning: G with two-level stability (npts vs npts+20 at fixed
  dps; dps vs dps+40), rel <= 1e-20.
- C2 rule status at (family, t): OK iff `|v_rule - v_true| <= 1e-3 |v_true|`;
  UNRESOLVED iff the difference exceeds `1e-3 max(|v_true|, Gerr)` and
  `|v_rule| > 3 max(...)`; horizon `H_j` = smallest sampled
  t in {5, 10, 20, 40, 80, 160} with UNRESOLVED.
- C3 cliff: `t*_j = 4800/a_j^2`; the m = 400 value must jump >= 1e6 between
  0.9 t* and 1.1 t* while the m = 6400 value does not.
- C4: PHI-HORIZON-DOMINANT iff `|Q_1600(40)| <= 0.5 |Q_400(40)|` and
  `|Q_400(40) - Q_1600(40)| >= 1e19`.
- C5: L4-PRICE-FAIL iff `T_bnd(40) > 1e19`.

Controls read:

```
+----+--------------------------------------------------------------+
| C0a| truth 6.957388e-14 vs committed float 6.957388e-14, rel      |
|    | 8.527e-15  -> PASS                                           |
| C0b| Q_400 = -1.1111757840e+20 vs q_h1(2037) = -1.11119e20,       |
|    | |Q| rel 6.821e-05, sign_ok = True  -> PASS                   |
+----+--------------------------------------------------------------+
```

## 2. Method: truth by G, and the two error regimes of the committed rule

The committed family evaluator is `r59.phi_weights(a, panels=6, m=400)`
(2400 nodes/family) fed through `exp(z X) @ (phi W)` with
`z = a (0.5 + i t)`, `t = theta_j - 2 pi xi`; the committed per-family value
is `v_j = a * phi_laplace = a^2 * int_{-1}^{1} phi(u) e^{w a u} du`.
GL exactness on one panel is governed by `omega_tilde = a^2 |t| / 6 <= 2m`,
i.e. the **cliff** `t*_j = 4800/a_j^2` at m = 400.

Truth: **G** — composite GL on phase-π panels of the u-integral, at working
dps, with the a-priori budget `Gerr = (pi/2)^{2n}/(2n)! * Sabs`.  Twelve
pinning points pass two-level stability with worst rel `1.06e-28`
(dps 200-260, npts 60-80; the deepest, `(4.752, 268)`, budget `4.4e-478`):

```
+--------+-----------+---------------+-----------+-----------+
| a      | t         | G             | rel_npts  | rel_dps   |
+--------+-----------+---------------+-----------+-----------+
| 1.760  |     2.00  | 2.246057e-14  | 6.94e-46  | 1.59e-201 |
| 1.760  |    30.00  | 8.774027e-28  | 3.45e-57  | 6.86e-188 |
| 2.288  |    40.00  | 5.459778e-39  | 9.79e-57  | 9.72e-177 |
| 2.992  |    40.24  | 4.457682e-49  | 7.03e-57  | 9.35e-168 |
| 3.696  |    60.00  | 3.357323e-71  | 9.34e-57  | 2.23e-143 |
| 4.752  |    79.42  | 3.886385e-102 | 9.34e-57  | 9.21e-112 |
| 4.752  |   213.00  | 1.574262e-166 | 1.56e-48  | 1.25e-47  |
| 4.752  |   268.00  | 1.182381e-186 | 1.06e-28  | 2.85e-28  |
+--------+-----------+---------------+-----------+-----------+
```

**The rule has TWO error regimes, both measured** (C2/C3):

- **Floor regime** (`|t| < t*`): the rule is quadrature-exact but its
  absolute error is a **flat, t-independent floor** (the integrating weight
  array against Gevrey-30 φ), scale `~e^{-2K}` = `8.8e-27`.  Measured for
  a = 1.76 (`|v_400 - v_true|`): `1.19e-27 / 2.35e-27 / 2.49e-27 / 2.34e-27`
  at t = 20/40/80/160, and `5.9e-28` at t = 2 — flat within a factor ~4 over
  a 80x t-range.  Family scaling at ξ = 35 (m = 400 values): `2.29e-27`
  (a = 1.76) .. `7.27e-27` (a = 2.82), i.e. order `(int phi)^2` /
  `e^{-2K}` scale.  The stored-float re-summation (`rule_exact`, dps 70)
  agrees with the float value to ~1e-2 relative (`2.314e-27` vs `2.293e-27`
  for fam 1 at ξ = 35), so the floor is the rule's own mathematical output,
  not float64 summation noise.
- **Alias regime** (`|t| > t*`): the rule value jumps to `~e^{-K}`-scale
  alias error, `1e12x` the floor.  C3, all 17 families: at 0.9 t* the m = 400
  value is at the floor (`1.9e-26` .. `1.5e-24`), at 1.0-1.1 t* it is
  `7.5e-15` .. `2.7e-13`; the jump ratio `1.3e11` .. `4.7e11`, while the
  m = 6400 value at 1.1 t* stays at `~e^{-2K}`-scale noise
  (`5.4e-26` .. `7.1e-25`).  Example rows:

```
+-----+-------+-----------+-----------+------------+-------------+
| fam | a     | t*        | v(0.9 t*) | v(1.0 t*)  | jump400     |
+-----+-------+-----------+-----------+------------+-------------+
|   1 | 1.760 |  1549.59  | 1.856e-26 | 7.484e-15  | 4.73e+11    |
|  13 | 3.344 |   429.25  | 2.521e-25 | 5.003e-14  | 1.71e+11    |
|  16 | 4.400 |   247.93  | 9.776e-25 | 1.743e-13  | 1.31e+11    |
|  17 | 4.752 |   212.56  | 1.518e-24 | 2.670e-13  | 1.28e+11    |
+-----+-------+-----------+-----------+------------+-------------+
```

**Horizon table** (C2; status at t = 5/10/20/40/80/160, O = OK,
G = GRAY, U = UNRESOLVED):

```
+-----+-------+-----------+---------+----+---------------------+
| fam | a     | theta     | t*      | H  | O O O U U U (t=5..) |
+-----+-------+-----------+---------+----+---------------------+
|   1 | 1.760 |  -40.919  | 1549.6  | 40 | O O O U U U         |
|   2 | 2.024 |  -40.919  | 1171.7  | 40 | O O G U U U         |
|   3 | 2.288 |  +40.919  |  916.9  | 20 | O O U U U U         |
|   4 | 2.552 |  +40.919  |  737.0  | 20 | O O U U U U         |
|   5 | 2.816 |  -40.919  |  605.3  | 20 | O G U U U U         |
|   6 | 1.848 |   -0.000  | 1405.5  | 40 | O O O U U U         |
|   7 | 2.200 |   -0.000  |  991.7  | 40 | O O G U U U         |
|   8 | 2.552 |   -0.000  |  737.0  | 20 | O O U U U U         |
|   9 | 1.936 |  -14.135  | 1280.7  | 40 | O O G U U U         |
|  10 | 2.288 |  -21.022  |  916.9  | 20 | O O U U U U         |
|  11 | 2.640 |  -25.011  |  688.7  | 20 | O O U U U U         |
|  12 | 2.992 |  -27.670  |  536.2  | 20 | O G U U U U         |
|  13 | 3.344 |  -30.425  |  429.2  | 10 | O U U U U U         |
|  14 | 3.696 |  -32.935  |  351.4  | 10 | O U U U U U         |
|  15 | 4.048 |  -37.586  |  292.9  | 10 | O U U U U U         |
|  16 | 4.400 |  -43.327  |  247.9  | 10 | O U U U U U         |
|  17 | 4.752 |  -48.005  |  212.6  | 10 | G U U U U U         |
+-----+-------+-----------+---------+----+---------------------+
```

The horizon is where `1e-3 x truth` crosses the flat floor — a resolution
horizon of the committed evaluator, not a truth statement.  At the boundary
the failure is already total: fam 1 at t = 40 reads `v_true = 7.67e-31`,
`v_400 = 2.35e-27` (rel `3.1e3`); by t = 160 the rule's floor sits `1e30`
above truth.

## 3. What the committed Q actually is (the window collapse)

C4 runs the committed 2037 path at m in {400, 1600, 6400} over [-40, 40]
(h = 0.01, h = 0.01, h = 0.02):

```
+--------+---------------------+-------------+-----------------+
| m      | Q_full(40)          | Q_sym(10)   | |C|_max         |
+--------+---------------------+-------------+-----------------+
| 400    | -1.111175783994e+20 | -3.406e+12  | 6.153298316e+09 |
| 1600   | -3.406049871881e+12 | -3.406e+12  | 1.598561633e+07 |
| 6400   | -3.406049871896e+12 | -3.406e+12  | 1.598561633e+07 |
+--------+---------------------+-------------+-----------------+
```

`Q_sym(X)` (cumulative, m = 400 vs 1600): identical to 5+ digits at
X = 5..20 (`-3.406049871883e+12` vs `-3.406049871881e+12`), then diverging
only on the positive side: at X = 30/35/40 the m = 400 reads
`-1.351e+18 / -5.386e+19 / -1.111e+20` while the m = 1600 value is FLAT at
`-3.406049871881e+12`.  Readings:

- **The whole alias mass enters on the positive side, xi in (26, 40]** —
  exactly the two families with `t* < |t|` inside the window: fam 17
  crosses `|t| = 212.6` at xi = 26.2, fam 16 crosses `|t| = 247.9` at
  xi = 32.5 (fam 15's `t* = 292.9` is crossed only at the edge, xi = 39.8).
  At ξ = 35 the two aliased families read `v_400 = 1.236e-13` (fam 16) and
  `8.449e-14` (fam 17) against truths `9.09e-171` / `2.85e-185` — and their
  exact re-summations agree with their floats to all 10 stored digits
  (`v400_exact = v400_float` bitwise in the artifact), so the alias value is
  the rule's deterministic mathematical output.  Amplified by the raw
  interpolation coefficients (`sum|base| = 1.36e+14`, `sum|corr| = 2.52e+16`)
  these two families alone carry the committed `|lb| ~ 0.046` at ξ = 35.
- **At m = 1600 every family is quadrature-exact across the whole window**
  (`t*_min = 19200/a^2 = 850.3` at fam 17 vs window max `|t| = 299.3`), so
  `Q_1600 = -3.406049871881e+12` is the TRUE window integral (floors enter
  g only squared, at < 1e-25 relative); the m = 6400 agreement at `4.3e-12`
  relative corroborates.
- **The committed Q's sign is inherited, its magnitude is not**: the true
  window integral is NEGATIVE (`-3.40605e+12`), so the sign claim
  (`qw < 0`) survives idealization at this owner; the committed magnitude
  is `3.3e7 x` the true value.

## 4. Where the true window integral lives (diagnostic)

`scripts/diag_2053_loc.py` rebuilds the m = 400 / m = 1600 profiles at
h = 0.005 over [-12, 12] and reports per-unit-bin trapezoid integrals of
`ker * g` (per-bin values undercount by their boundary intervals; the
full-range trapezoid and the fine scan are the exact readings).  Both m
give IDENTICAL structure:

```
+----------+-----------+---------------+---------------------------+
| bin      | Q         | max|fx|       | argmax reading            |
+----------+-----------+---------------+---------------------------+
| [-8,-7)  | -3.13e+13 | 1.521e+15     | xi=-7.03: |lb|=0.69,      |
|          |           |               | |cc|=228, p=1.02e+05,     |
|          |           |               | ker=0.54                  |
| [-7,-6)  | +2.72e+13 | 1.096e+15     | xi=-7.00: |cc|=238        |
| [-6,-5)  | +1.77e+12 | 1.473e+15     | xi=-5.87: |cc|=210        |
| [-5,-4)  | +1.69e+07 | 6.26e+09      | |cc|~0.1                  |
| [+5,+8]  | ~-1e-13   | 6.7e-12       | |cc|~1e-11 (cancellation) |
+----------+-----------+---------------+---------------------------+
```

Fine scan of [-8, -7] at h = 0.0005: `Q = -3.191286e+13`,
`max|fx| = 1.531e+15` at xi = -7.028 — the feature is smooth and resolved.
The asymmetry is the story: at |xi| ~ 6-8 the NEGATIVE side carries a real
`|cc| ~ 230` mass hump while the positive side sits at `|cc| ~ 1e-11`
(cancellation floors).  The m = 400 vs m = 1600 agreement to 5+ digits in
these bins (both families' t are far inside the exact regime there:
`|t| <= 85 < t*_min = 212.6`) certifies the mass is real signal.  So:

```
true window integral  -3.40605e+12
  =  negative-side mass hump   xi in [-8, -5]   (|cc| up to 230)
  +  everything else           < 1e+07
committed Q_400       -1.11118e+20
  =  true                  -3.406e+12
  +  fam-16/17 alias       -1.111e+20        (xi in (26, 40])
```

## 5. L4: the full-line tail from the landed rungs

Assembly (C5): per family, the bound is the MINIMUM over the three landed
rungs of `|v_j| <= e^{0.5 a_j^2} N_r / (a_j^{2r-2} |0.5 + i t|^r)`
(u-integral rungs converted to the committed `a^2`-convention with the
correct `a^{2r-2}` bookkeeping); `lb_bnd`, `cc_bnd` are the coefficient-norm
sums over families; the kernel envelope is
`env = C_book + sig_peak + 2 = 458.0476 + 5.9915 + 2 = 466.0391`; the tail
integral `T_bnd(X) = int_X^{21X} env p^2 lb_bnd^2 cc_bnd^2 dxi`:

```
+--------+---------------+----------------+----------------+
| X      | T_bnd(X)      | / 1e19 budget  | / 1.1111e20    |
+--------+---------------+----------------+----------------+
|  40    | 6.515715e+41  | 6.52e+22       | 5.87e+21       |
|  60    | 1.072337e+42  | 1.07e+23       | 9.65e+21       |
| 100    | 1.921392e+42  | 1.92e+23       | 1.73e+22       |
| 200    | 4.053658e+42  | 4.05e+23       | 3.65e+22       |
+--------+---------------+----------------+----------------+
```

The kill fires by **22.5 orders of magnitude**, and the bound GROWS with X.
Structural reason (from the rung constants `N1 = 4.990741e-12`,
`N2 = 4.592160e-08`, `N3 = 3.416204`):

- rung 1 vs rung 2 crossover at `|w| = N2/(N1 a^2) = 9201.4/a^2`
  (hw = 407.5 for a = 4.752);
- rung 2 vs rung 3 crossover at `|w| = N3 a^2/N2 = 7.44e+07 a^2`
  (hw = 1.68e+09, i.e. xi ~ 2.7e8, for a = 4.752).

So over the ENTIRE tail window the sharpest landed rung is the WEAKEST-decay
one (rung 1: `|w|^{-1}`, then rung 2: `|w|^{-2}`); combined with the
degree-8 weight `p^2 ~ xi^8` and the raw `sum|base| sum|corr|` norms
squared twice, the bound-integrand does not decay on any practical range.
This is exactly the registered kill's reading: a price error in the
1986-1988 rung constants FOR THIS family class (a re-derivation wave, not a
patch, would be needed to price this tail).

## 6. Consequences and registrations

1. **Records 2048-2052 remain internally valid**: they bound the committed
   m = 400 DAG evaluation against the stored-floats-exact object O, and
   `6.330553e+17 = 0.0633 x budget` stands as the price of that (correct)
   claim.  This batch does not disturb them.
2. **The object they priced is φ-rule-contaminated in its outer window.**
   The L2 link's certified object and the IDEAL functional differ, at this
   owner, by `1.1111757e+20` — the committed Q is 3.3e7 x the true window
   integral.  L5's registered "phi quadrature" piece is thus MEASURED, not
   merely registered: it is the dominant term of the committed functional's
   value at this owner.
3. **Registered follow-up — the reduced evaluator.**  Re-run the L2 chain
   (2048-2052 machinery, unchanged in structure) at m = 1600, where every
   family is exact across the window and the floors price out below any
   budget.  Direction of the re-price, NOT measured here: the object's
   `|C|_max` drops from `6.153e+09` (m = 400, alias peak) to `1.599e+07`
   (m = 1600, the xi in [-8, -5] mass hump), and the outer-window g mass
   drops by 3e7.  Note the tightened bar: if the ideal object is the
   certificate's target, its budget is `|Q_ideal| = 3.4e12` (10% bar:
   `3.4e11`) — 6 orders tighter than the 1e19 bar the current charges were
   measured against.
4. **The sign survives**: `Q_ideal = -3.40605e+12 < 0` at this owner, so
   the detector-side sign claim is not an artifact of the φ-rule; only the
   magnitude is.
5. **The alias is deterministic and grid-reproducible** — which is why the
   1996 (dxi = 0.004) and 2037 (dxi = 0.004, direct quadratic form)
   pipelines agreed at rel 6e-5 on `-1.111e20`: the alias error is a smooth,
   adequately-resolved function of xi (period ~0.27 at fam 17's phase
   rate), not sampling noise.  Reproducibility across pipelines is NOT
   evidence of signal here.

## 7. Incident chain (all caught before any verdict was licensed)

1. **The C0b sign defect and the CONTROL-FAIL run.**  Run 1 produced
   `VERDICT: CONTROL-FAIL` with NO verdict licensed.  Cause: `Q_COMMITTED`
   was entered unsigned (`+1.1111e20`) and the frozen rule's rel formula
   `abs(qv400 - Q_COMMITTED)/Q_COMMITTED` is meaningless on a signed
   reference — it read `2.000068`.  Adjudication against the committed
   record: `q_h1 = -1.11119e20` (record 2037, quoted in 2041; cross-read
   `-1.11126e20` at 1996).  The failing side was the INSTRUMENT, not the
   physics (seventh instance of the gate-at-the-design's-floor law).  Fix:
   magnitude comparison against `|Q|` plus an explicit negative-sign
   anchor; run 2 then read C0b PASS (`rel 6.821e-05`, `sign_ok = True`).
2. **Determinism cross-read of the two runs**: 1772 fields compared, 8
   differing — all in the C0b block plus `elapsed_s` (1184.1 s vs 1183.0 s).
   Every measured quantity (C1 pins, C2 rows, C3 rows, C4 headline rows,
   profiles, C5) is bitwise identical across runs.
3. **Pre-run instrument fixes** (the earlier arc, all disclosed):
   the truth normalization factor `a` (committed convention is `a^2 x`
   u-integral; the first draft returned `a x`, caught by C0a at exactly
   ratio 1.760 = a); the `rule_exact` exponent (stored X are physical, so
   the argument is `w`, not `w a`; 0.44 -> 3.8e-16 after the fix); the
   `v_bound` u-integral bookkeeping (`a^{2r-2}`); and the build-location
   discipline (the first run was killed on the Windows-side tree and re-run
   in the WSL ext4 mirror).
4. **The Taylor-series truth route was RETIRED.**  The first draft's ODE
   `(1-u^2) y' + 2 k u y = 0` sums `(1-u^2)^k`, not the Gevrey φ; the
   correct `(1-u^2)^2 y' + 2 k u y = 0` gives a three-term recurrence
   `b_{j+1} = [2(2j-K) b_j - (2j-2) b_{j-1}]/(2j+2)` whose series converges
   only like `e^{-c sqrt j}` (impractical at depth 400), and the `K_n`
   recurrence `K_n = (e^w - (-1)^n e^{-w})/w - (n/w) K_{n-1}` destroys all
   digits for `n >> |w|` (the draft sum reached 1e+15285).  G is the truth
   method; the retired route is recorded so it is not re-attempted.
5. **Ops**: the probe needs the harness background-task pattern (a nohup'd
   WSL job dies with the session), and `pkill -f` self-kills its own
   command line unless the kill and launch are in separate `wsl.exe` calls
   (bracket pattern).

## 8. Scope and non-claims

- Measured statements about the committed evaluator at ONE owner (one-copy
  G8-H), the committed 2037 path, and the landed rung constants; no
  uniformity over owners, no producer theorem, not RH.
- The horizon/floor/alias laws are measured here on 17 families at K = 30;
  the `e^{-K}` / `e^{-2K}` scales are observed orders of magnitude, not
  proven statements.
- The L4 tail bound is assembled from the rungs as landed; the kill means
  these constants cannot price this family's tail, not that no such bound
  exists.
- The reduced evaluator is registered, NOT executed; its costs are a
  direction, not a measurement.