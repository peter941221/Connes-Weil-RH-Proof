# 2058 — Route A link L5, solve channel: the KKT-floor charge replaced by the direct functional difference at the m = 1600 reduced evaluator

Verdict: **IDEAL-L2-VIABLE** at the registered owner (one-copy G8-H,
ρ = 0.6 + 40.9187190121475i, scale 0.88, K = 30, support 9.504).  Record
2057 priced L5 at 1.842946e+09 with the SOLVE channel binding at 95.38% of
∫e_g — its KKT certificate sits in the uniform-floor regime and its charge
was carried by the floor correction INS_S |c_KKT − c_minnorm| and the
stored-vs-KKT deviation through a POINTWISE envelope of the coefficient
perturbation, multiplied by the crude kernel bound (SIG_MAX + C_book).
2057 §3 registered the min-H1/floor-side tightening of that channel; this
record executes it — not by a tighter bound, but by a different charge.
Q = ∫ K p² |lb|² |cc|² is QUADRATIC in each coefficient vector, so the
channel (a coefficient perturbation c_stored → c_mn, the exact min-norm
interpolant of the stored matrices, i.e. the uniform-floor clamped-rule
twin) is priced by the DIRECT same-grid difference

```
dQ = Q(c_mn) - Q(c_stored) = trapz( W (g1 - g0) ),  W = ker p^2
```

and the deviation envelope — with its derivative slots and K4 tail — is
not needed for the channel at all; only the two chains' OWN arithmetic
envelopes enter.  The triangle is 2055's, with the second term repriced:

```
|ladder - Q(O*)|  <=  TOTAL_2055 + |Q(O) - Q(O*)|
                  <=  4.401166e+10 (2055) + 1.104942e+08 (L5, this record)
                  =   4.412216e+10
                  =   0.01295 x budget3 (3.4060498718812666e+12)
                  =   0.1295 x the 10% bar (3.4060498718812666e+11)
```

so the ideal-twin window survives at **7.72x under the 10% bar** (2057:
7.43x; 2056: 4.32x).  charge_L5 = charge_value 1.104582e+08 + charge_kernel
3.607399e+04; charge_value = (SIG_MAX + C_book) ∫e_g^{ns} + charge_solve
with ∫e_g^{ns} = 2.380518e+05 — the SAME value in both records, since the
F/X/(P) envelope at the 0.001 grid is untouched — and the solve channel
now added as a computed price instead of riding through the 463.42x
kernel multiplication.  The same-grid decomposition is exact (the 0.001
split of ∫e_g^{full} = 3.976762e+06 is 3.738711e+06 solve +
2.380518e+05 ns, D4):

```
charge_L5                       2057              2058
--------------------------------+-----------------+-----------------
solve channel                   1.732593e+09      1.402572e+05  12353x
  (2057: 463.4198 x the solve    (463.4198 x       (in-run dQ +
   part of int e_g; 2058: the     3.738711e+06)     qe_grid + arith)
   direct difference, no kernel)
F/X/(P) envelope part           1.103179e+08      1.103179e+08  unchanged
charge_kernel                   3.607399e+04      3.607399e+04  unchanged
--------------------------------+-----------------+-----------------
charge_L5                       1.842946e+09      1.104942e+08  16.679x
```

solve channel internals: charge_solve = |dQ| 2.595018e+04 + qe_grid
1.240688e-01 + qe_arith 1.143069e+05 = 1.402572e+05.  Against the 2057
decomp reading of the same channel (3.793124e+06 at dxi = 0.004) the
measured envelope-to-price gain is 27.044x; the D4 same-grid marginal
reading (int_eg^{full} − int_eg^{ns} = 3.738711e+06) agrees with it at
0.98565x.

Probe: `scripts/routea_l5_solve_2058.py` (md5
`662c70d22618850b02d135982d9fc58f`, WSL ext4 mirror run, 848.4 s),
artifact `results/2058_l5_solve.json` (md5
`9d1512ee6033bc80d36d3b7c679d2233`).  Companion diagnostic:
`scripts/diag_2058_collapse.py` (md5 `c9bfc409164bbe721118eb96f73a3c69`),
artifact `results/diag_2058.json` (md5
`58baefc99fd2ac91efa1cdb9362fdeab`) — it sizes the FAILED route (the
linear/quadratic split) and the construction deviation, both quoted below.
It is record 2057's probe with ONE channel replaced and the B2 gate retired
(D1/D3 replace it); the R57 gate reproduces the 2057 price IN THIS RUN,
bitwise (rel 0.0 on ∫e_g, charge_value, charge_L5), so the gain above is a
same-run difference.  L4 (record 2053) stands and the Gram rule / a_mat
idealisation gaps stay REGISTERED (S8, S3b) as in 2056/2057.

## 1. The mechanism (what changed, and why it is valid)

**Quadraticity.**  With lb = base @ v, cc = corr @ v the functional is
quadratic in each coefficient vector, so the exact channel difference is
dQ = Q(c_mn) − Q(c_stored), a single float computation per grid node:
dg = W·(g1 − g0) is a DIFFERENCE of two sums evaluated at the SAME nodes,
so it inherits the grid's own resolution, unlike the derivative split.
The split route was measured and REJECTED (diagnostic):

```
grid       dQ            lin           linbound      env1        env1/dQ
---------+-------------+-------------+-------------+-----------+--------
0.008    | 2.289397e+04| 2.861744e+06| 1.284787e+07| 9.271857e+06| 405.0
0.004    | 2.289395e+04| 5.723488e+06| 2.569575e+07| 9.290721e+06| 405.8
0.002    | 2.289397e+04| 1.144698e+07| 5.139150e+07| 9.287676e+06| 405.7
---------+-------------+-------------+-------------+-----------+--------
```

dQ is stable to 6 digits while the linear term lin = 2 Re[Σ db_j Ab_j +
Σ dc_j Cc_j] and the residual sec = dQ − lin BOTH scale as 1/h exactly
(lin ≈ dQ/h), because the individual integrals Ab_j = ∫ K p² |cc|²conj(lb)
v_j alias at these grids (the family values' xi-oscillation reaches
2π a X ~ 283 rad/unit at the largest families) while the pointwise
difference does not.  The bare pointwise-envelope analog of the same
deviation reads env1 = 9.28e+06 = 405x dQ (stable across grids), and the
2057 charge — with the derivative and K4 slots on top — read 3.79e+06 at
0.004 = 146x the direct price.  The split is therefore not a pricing
route; the difference is.

**Construction.**  c_mn is the EXACT min-norm solve of the stored
matrices computed in mp (50 digits), cast to float; the cast entry is
INS U |c_mn| (cast_max_b 3.362e-03, cast_max_c 1.522) and is charged
through jet_cm's l5_cast envelope.  The probe's S4 reproduces the KKT
certificate's d-sums (d_base_meas 4.514320e+04, d_corr_meas 2.490374e+07;
an mp recompute in batch reproduces both to all printed digits), and the
floor correction stays as in 2057 (floor_corr_base 1.408e-03,
floor_corr_corr 2.380e-01).  The diagnostic's float solve of the SAME
equations (cond(S) = 3.766e+08) deviates from the mp-exact interpolant by
5.511e+03 (b) / 3.040e+06 (c) — 1.9e-10 / 2.3e-10 relative, i.e. at the
d-sum scale itself — which is why its dQ reads 2.289397e+04, 12% below
the probe's 2.595018e+04: dQ is a difference of two 3.406e+12-scale
integrals (dQ/Q0 = 7.6e−09), so coefficient-path perturbations at the
1e-10 level move it by percents.  The priced object must therefore BE the
mp-exact interpolant cast to float, with the cast charged — never a float
solve.

**Charge.**  charge_solve = |dQ| + qe_grid + qe_arith:

* |dQ| = 2.595018e+04 on the 0.001 grid (80001 nodes).
* qe_grid = 4 max(|dQ(.001) − dQ(.004)|, |dQ(.001) − dQ_phi(.001)|) =
  4 x 0.031017 = 1.240688e-01; the controls are rel 1.195e-06 (grid) and
  6.388e-07 (golden-ratio shift 0.61803...).  This is a CONTROL, not a
  certified enclosure (nonclaim).
* qe_arith = INS (int_e0 + int_ecm) + 32 U trapz|W dg| =
  1.05 x 108863.7 + 9.965e-09 = 1.143069e+05: the two chains' OWN
  forward-rounding envelopes — jet0 (c_stored, no channels) and jet_cm
  (c_mn_f, ONLY the cast envelope) — integrated by the same
  corrected-trapezoid convention.  int_e0 5.443122e+04 (err0_c0 max
  8.396e+04, med 8.673e-19), int_ecm 5.443251e+04: the cast moves the
  envelope by 2.4e-05 relative, i.e. the routing, not the cast, carries
  the arithmetic channel.  The post-chain constant is 32U (the 2056/2057
  20U proved tight: log2 80001 = 16.3 U of trapezoid accumulation plus
  per-term operations).
* charge_solve/dQ = 5.405: the arithmetic channel now dominates the
  channel's own price, and charge_solve (1.402572e+05) lands at 1.032x
  the KKT certificate's own deviation bound dc_base = 1.359110e+05 — the
  direct difference has reached the analytic bound's scale.

**Invariants.**  The (P) bridge, the F/X channels, the ladder, the KKT
certificate and every 2051–2057 object are untouched; the R57 bitwise
reproduction proves it in-run.  The zeroing of dbase/dcorr removes
EXACTLY the solve channel's envelope (B7): the value slots are bitwise
untouched, while k4/ek4 and the int_g regress term move with the error
channel BY DESIGN — k4 is the solve channel's own K4 entry, so B7 gates
property only the value-only pieces.

The mechanics above are frozen as instrument laws (AGENTS.md section 2i):
the direct-difference law for quadratic-function channels (never the
derivative split — its integrals alias); the ideal-interpolant
construction law (mp-exact min-norm cast to float, cast charged — never a
float solve); the computed-vs-bounded channel law (a computed difference
enters the charge additively, not through the crude kernel constant); the
pointwise-reference convention law (each object's own s-convention; lift
the float weight); the error-slot zeroing law (gate the value slots); the
smoke-grid comparison law (compare the h-independent trapz); and the
post-chain accumulation constant 32U on trapz|W dg|.

## 2. Controls (all green; 29/29 gates)

```
R57  2057 price, same run, solve channel restored: int_eg
     3.976762498008143e+06 (rel 0.0), err0_trapz 3.976762e+06,
     charge_value 1.8429103599871004e+09 (rel 0.0), charge_L5
     1.8429464339779341e+09 (rel 0.0) -- BITWISE; total_ideal_57
     4.585461e+10
B6   JetL5B(bridge off) vs JetL5 at 4 nodes: all bundles + K4 dev 0.0
B7   zeroing dbase/dcorr: val0/val1 arrays bitwise True, tr_v/em_v
     bitwise True (val_trapz 1.235172e+14 both); int_g 1.235172e+14 both
     (rel 1e-16: only the K4 entry moves)
D1   float vs mp pointwise difference, xi in {-39.9375, -6.68, 39.9375}:
     worst ratio 4.955e-06 (xi = -6.68: D -435.568157746857 vs mp
     -435.567565636131, dev 5.921e-04 over allow 1.195e+02); end nodes
     ratio 2.53e-19 / 7.75e-20 (D ~ 1e-33 scale there, W -2.642e+20)
D2   grid controls: rel_coarse 1.195e-06, rel_phi 6.388e-07 (TOL 1e-3);
     qe_grid 1.240688e-01
D3   envelope monotonicity at the three nodes: err0(c_mn_f with cast) >=
     err0(c_mn_f without) and err0(ns) <= err0(full), all True; at
     xi = -6.68 err0_full 2.895099e+04 vs err0_ns 2.460653e+02 (the solve
     channel carries 99.15% of the full envelope at that node), err0_cm
     5.690824e+01 vs err0_cm0 5.690092e+01
D4   same-grid marginal reading: int_eg(full) - int_eg(ns) =
     3.738710733697e+06 = 0.9856546388901983x the 2057 decomp
     3.793124474011112e+06
A12a bridged bound >= mp.quad truth (worst ratio 4.415e-02); A12b
     extreme-node arithmetic (4 rows); A13 bridge <= elementary; P7
     piece-ellipse 0 bad, clear_min 0.0021, rightmost_gap 0.0026
P2   0.0 (bitwise), P6 9.906e-06 (TOL 1.0)
C1/C2 Q400 -1.111176e+20, Q1600 -3.406050e+12; C4 tier-B d_base
     2.1507e-09 / d_corr 2.4812e-09
P3   0 bad, ellipse clear_min 0.0079; P4 dxi_max 3.010e-16 (m = 1600),
     A10 oracle dev 2.039e-53, A11 rel 0.0
P5   KKT theta 8.942e-28 / 8.942e-28, weyl_relative 7.586e-07, lmin
     2.888e-29, lmax 3.807e-23, floor/lmax 2.627e+04 (uniform-floor),
     invnorm 1.339e+16, dc_base 1.359110e+05
A7   worst sigma ratio 0.007 (TOL 0.2); A8 worst book ratio 0.573;
     SIGMAX 5.372183; A9 worst rule-bound/truth ratio 2.570e-05
B3   F-channel truth ratios (3 rows); B5 r51.selftest passes;
     S8 gram d12 1.423e-13, d13 2.286e-13 (registered)
```

S7 details (0.001 grid, 80001 nodes, ns pass): err0_max 3.680363e+05
(2057: 7.884e+06 — the solve channel's node spikes are out), err0_med
2.787e-16, trapz 2.380518e+05, EM error slots 3.741e-20, regress
1.189e-02; err1_ends 2.245e-13 / 2.243e-13; value channel trapz
1.235172e+14 + EM 4.033e-32 + regress 4.514e+05 (same as 2057);
sig_loc_max 2.0; k4_trapz 3.250e+20, ek4_trapz 8.561e+12 (2057:
1.208e+14 — the solve channel's K4 entry is out of the ns pass); epsK
2.921e-10 (unchanged).  Decomp at 0.004 (single-channel jets, indicative
shares): F 5.442840e+04, X 9.738743e+04, rule_bridge 1.950806e+05 (the
2056 elementary form 7.128255e+07); channel margins (S3) FC_k
7.426e-40 ... 1.723e-37, XC_k 1.669e-23 ... 6.603e-21, el_max
9.880e-20, epsF_max 7.602e-08 — all identical to 2056/2057.

## 3. What this buys, and the registered lever

The solve channel leaves the binding position and the F/X/(P) envelope
takes it back: 463.4198 x 2.380518e+05 = 1.103179e+08 = 99.87% of
charge_L5, of which the rule_bridge channel is the largest single piece
(1.950806e+05, 81.9%; indicative from the 0.004 decomp).  The solve
channel itself now reads 1.402572e+05 = 0.127% of charge_L5, and its own
price is dominated by its arithmetic envelope (qe_arith 1.143069e+05 =
81.5% of charge_solve; int_e0 and int_ecm agree to 1.000024 relative, so
the routing — not the cast — carries it).  Registered levers for the next
record, in order:

* the rule_bridge channel's computed-difference accumulation allowance
  (2057's allow0_max 1.214e-23 binds the bridged bound for the large-a
  families): a cancellation-aware accumulation of the two sums, as
  registered in 2057 §3;
* the solve-side arithmetic channel: int_e0 + int_ecm are U|c|-scale
  envelopes of the SAME routing structure and agree to 2.4e-05 relative,
  so a shared/cancellation-aware arithmetic chain could cut charge_solve
  toward |dQ| (gain bounded by the channel's 0.127% share of charge_L5);
* the kernel constant (SIG_MAX + C_book) = 463.4198 multiplies the whole
  F/X/(P) envelope.

## 4. Nonclaims

Registered in the artifact (11 items); in short (2056's and 2057's, plus
this record's): the sigma_loc K4 tail is a MODELLING bound, not a proven
enclosure of |E''''|; the envelope integrals (including the two arithmetic
envelopes int_e0/int_ecm) are a resolved-grid convention — the refinement
control is the 0.1-grid smoke (same trapz comparison as 2056/2057), and
the 7.72x margin absorbs it; dQ's grid allowance qe_grid is a CONTROL
(0.001 vs 0.004 vs phi-shifted grids), not a certified enclosure of the
grid truncation; the cast envelope INS U |c_mn| is a crude relative-U
bound on the mp→float cast of the exact interpolant; c_mn is the exact
min-norm solve of the STORED matrices, so the a_mat idealisation gap
(m = 400 rule vs true Laplace integral at the owner-node arguments) stays
REGISTERED and MEASURED (S3b), not enclosed, exactly as the solve channel
certifies the stored matrices only; the Gram rule is REGISTERED and
MEASURED (S8), not enclosed; the P3/A9 selftests validate the rule-bound
structure at small m and small |Im s'|; the exp/sqrt/cos constants (8U,
6U) are op-count constants, not libm proofs; the 2057 bridge's own
allowance and A12a/A12b nonclaims stand unchanged; the D1 truth check
runs at three nodes (two window-edge, one hump), not a continuum; L4
(2053) stands, evaluator-independent; COVER open; not a producer theorem;
not RH.