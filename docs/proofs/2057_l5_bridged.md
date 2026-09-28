# 2057 — Route A link L5, bridged: the split-rule (P) channel at the m = 1600 reduced evaluator

Verdict: **IDEAL-L2-VIABLE** at the registered owner (one-copy G8-H,
ρ = 0.6 + 40.9187190121475i, scale 0.88, K = 30, support 9.504).  Record
2056 priced L5 at 3.478788e+10 with 94.96% of ∫e_g carried by the (P)
rule-residual channel — and within it by the outer-panel elementary bound
on the two panels that reach |u| = 1.  That bound is a bound on the SUM
|I| + |GL|, oscillatory-unaware and m-independent, so it saturates at the
e^{−K/(1−(2/3)²)} = e^{−54} family-panel scale however many nodes the rule
carries.  2056 §5 registered the SPLIT-RULE BRIDGING as the lever; this
record executes it.  The triangle is 2056's, with the second term repriced:

```
|ladder - Q(O*)|  <=  TOTAL_2055 + |Q(O) - Q(O*)|
                  <=  4.401166e+10 (2055) + 1.842946e+09 (L5, this record)
                  =   4.585461e+10
                  =   0.0135 x budget3 (3.4060498718812666e+12)
                  =   0.1346 x the 10% bar (3.4060498718812666e+11)
```

so the ideal-twin window survives at **7.43x under the 10% bar** (2056:
4.32x).  charge_L5 = charge_value 1.842910e+09 + charge_kernel 3.607399e+04;
charge_value = (SIG_MAX + C_book) ∫e_g with ∫e_g = 3.976762e+06 — 5.30% of
the 2056 value — and the (P) channel LEAVES the binding position:

```
channel (S7 decomp, dxi = 0.004)   reading        share of int e_g
---------------------------------+--------------+----------------
(S) solve channel  (KKT floors)   | 3.793124e+06 | 95.38%   <- binds now
(P) rule residual, bridged        | 1.950806e+05 |  4.91%
(X) phi-chain rounding            | 9.738e+04    |  2.45e-03
(F) node/weight certification     | 5.443e+04    |  1.37e-03
---------------------------------+--------------+----------------
(P) the same channel at 2056      | 7.128255e+07 |  (365x higher)
int e_g (0.001 grid, 80001 pts)   | 3.976762e+06 |  (2056: 7.506767e+07)
int g (same grid)                 | 1.235172e+14 |  (2056: 1.235172e+14,
                                  |              |   rel 4.8e-13: the K4
                                  |              |   bundle entry now carries
                                  |              |   the bridged k = 4 bound)
charge_value = 463.4198 * int e_g | 1.842910e+09 |
charge_kernel = epsK (int g+e_g)  | 3.607399e+04 |
charge_L5 = value + kernel        | 1.842946e+09 |  gain 18.876x on 2056
```

(shares: each channel over the 0.001-grid ∫e_g; the decomp itself runs at
dxi = 0.004 as single-channel jets, so the shares need not sum to 1.)

Probe: `scripts/routea_l5_bridged_2057.py` (md5
`d093b7d643a80b9a1e67c6b4d3bd3a3e`, WSL ext4 mirror run, 234.3 s),
artifact `results/2057_l5_bridged.json` (md5
`28966087fc928cbc5202364c64e3aeed`).  It is record 2056's probe with ONE
channel replaced; the R56 gate reproduces the 2056 price IN THIS RUN,
bitwise (rel 0.0 on ∫e_g, charge_value, charge_L5), so the gain above is a
same-run difference and not a quoted one.  L4 (record 2053) stands and the
Gram rule / a_mat idealisation gaps stay REGISTERED (S8, S3b) as in 2056.

## 1. The bridge (what changed, and why it is valid)

For the outer panel P = [2a/3, a] (right; the left panel [−a, −2a/3] is
mirrored), cut at |u| = 1 − delta with DELTA_SPLIT = 0.05 into
P1 = [2a/3, a(1−delta)] and the edge slice P2 = [a(1−delta), a], and S1 the
SAME composite GL rule (m = 1600) on P1:

```
|GL_c - I|  <=  |GL_c - S1|  +  |S1 - I_P1|  +  |I_P2|
```

* **|GL_c − S1| is COMPUTED**, per node and per slot, as one complex
  difference of two sums — no bound on either rule's own residual is
  needed; this is the whole point of the bridge.  Both outer panels are
  combined into ONE difference before the modulus (tighter than summing
  moduli), and slot k carries the moment (−2πia x)^k directly (no
  transport: |D_k| is evaluated at slot k).
* **|S1 − I_P1|** carries the Trefethen ellipse bound of the P1 geometry
  (uc = 0.85833, hu = 0.14167, rho_max = 2.26508, rho = 2.21895,
  chm = 1.33497): rho^{−2m} = e^{−2552}, floored at 1e-300 — dead at
  m = 1600 for any admissible family.  The ellipse's rightmost real point
  is uc + hu·chm = 0.99743 < 1: it misses the singular point u = 1 by
  0.00257 (P7 rightmost_gap), so the integrand is analytic inside and the
  bound formula applies with the same M(rho) as the inner panels.
* **|I_P2|** carries the elementary slice bound delta·a·exp(h_out over
  P2): the slice's integrand is bounded by e^{−K/(2 delta) + a²/2} scale —
  measured B2sum 9.478e−135 (a = 1.76) to 2.542e−130 (a = 4.752).
* Per node the (P) bound is min(elementary, bridged) + the four floored
  inner panels; both are valid bounds on the same residual, so the min is
  valid.  In practice the bridge wins at every profile node (gain below).
* The computed difference is carried with an allowance on the
  absolute-sum scale (the P6 lesson): allow_k = INS ((EPS_TERM +
  (2k + 4m) U + amp)(Ac_k + Ap_k) + dp_k), where m = 1600,
  Ac_k = Σ|F| e^{aX/2} (2πa|X|)^k over the committed outer panels,
  Ap_k the same over the piece rule, and dp_k the piece rule's own
  construction deviation against the IDEAL piece rule the ellipse bound
  applies to (the fx_channels op-count formulas on the certified
  dxi/wlo/whi tables of the SAME numpy root array P4 certifies, plus the
  two map slots — dxi_proxy = false in this run).  Measured:
  abs_c0_max 1.718e−12, abs_p0_max 1.186e−21, epsF_piece_max 7.603e−08,
  dp0_max 1.422e−32, allow0_max 1.214e−23 (covers_2056_el 5.84e−04).

Measured per-family gain of the bridged bound over the 2056 elementary one
at the window-edge node (S3 el_node_profile, all 17 families):

```
a        1.760    1.848   ...   3.080    3.432    4.048    4.400    4.752
el_2056  2.308e-23 2.866e-23 ... 2.651e-22 4.996e-22 1.356e-21 2.626e-21 9.880e-20
bridge   2.616e-25 3.113e-25 ... 2.939e-24 5.323e-24 1.113e-23 2.141e-23 5.767e-23
gain_end 88.2x    92.1x     ... 90.2x    93.9x    121.8x   122.7x   1713.3x
```

(the largest-a families carry the smallest bridge bound: the allowance,
which is A-independent per term, becomes the binding part of the bridge
for them — 1.214e−23 of the 5.767e−23 v-scale reading).

The mechanics above are frozen as instrument laws (AGENTS.md section 2h):
the split-rule bridge itself; the ellipse-clearance rule (gate
rightmost_gap > 0 plus a separate clearance check — an absolute clearance
threshold rejects valid geometry near the singularity); the
computed-difference allowance rule (absolute-sum scale, including the
piece's own construction deviation dp_k from the certified dxi/wlo/whi
tables, never a proxy); the min-of-bounds rule (a run must gate that the
replacement actually wins); and the same-run reprice rule (the parent's
price is re-derived in-run, bitwise, rather than quoted across records).

## 2. Controls (all green; 25/25 gates)

```
R56  2056 price, same run, bridge off: int_eg 7.506767205930778e+07
     (rel 0.0), err0_trapz 7.506767e+07 (2056 smoke quote 7.771e+07 at
     the 0.1 grid), charge_value 3.478784327892473e+10 (rel 0.0),
     charge_L5 3.4787879352936325e+10 (rel 0.0) -- BITWISE
B6   JetL5B(bridge off) vs JetL5 at 4 nodes: all bundles + K4 dev 0.0
A12a bridged bound >= mp.quad truth, 4 families x u0 in {0, 24}
     (|Im s'| <= 24): worst ratio 4.415e-02 (fam 16: true 7.647e-27,
     bound 1.274e-23, elem_2056 2.079e-20)
A12b extreme nodes (fam 16, xi = +-40), slots 0 and 2: |D_float - D_mp|
     over allow 8.4e-13 ... 5.4e-11 (D ~ 5e-34 at k = 0, 5e-30 at k = 2;
     allow 1.214e-23 / 9.756e-21)
A13  bridge <= elementary at every family, both profile nodes
P7   piece-ellipse selftest, m in {6, 10, 20}: 0 bad; bound/err
     1e+31 ... 1e+33 (valid, loose at small m -- the P3 pattern);
     clear_min 0.00208, rightmost_gap 0.00257
P2   0.0 (bitwise), P6 9.906e-06 (TOL 1.0)
C1/C2 Q400 -1.1111757839943652e+20, Q1600 -3406049871881.275 (rel 2.4e-15)
C4   tier-B d_base 2.1507e-09 / d_corr 2.4812e-09 (2054 values)
P3   0 bad, ellipse clear_min 0.0079; P4 dxi_max 3.010e-16 (m = 1600),
     A10 oracle dev 2.039e-53 over all 1600 roots; A11 rel 0.0
P5   KKT theta 8.94e-28, weyl_relative 7.586e-07, lmin 2.888e-29,
     lmax 3.807e-23, floor/lmax 2.63e+04 (uniform-floor regime)
A7   worst sigma ratio 0.199; A8 worst book ratio 0.573; SIGMAX 5.372183
A9   worst rule-bound/truth ratio 2.570e-05
B2   solve-channel truth ratios 1.58e-14 / 4.65e-03 / 3.09e-18
B3   F-channel truth ratios 1.88e-08 / 1.34e-07 / 6.28e-12
B5   r51.selftest passes
S8   gram d12 1.423e-13, d13 2.286e-13 (registered)
```

S7 details (0.001 grid, 80001 nodes): err0_max 7.883735e+06 (2056:
1.161924e+08), err0_med 2.787e−16 (2056: 1.485e−06), trapz 3.976762e+06,
EM error slots 3.741e−20, regress 1.677e−01; value channel trapz
1.235172e+14 + EM 4.033e−32 + regress 4.514e+05; sig_loc_max 2.0;
k4_trapz 3.250e+20, ek4_trapz 1.208e+14 (2056: 2.608e+15 — the K4 entry
now carries the bridged bound's k = 4 form); epsK 2.920565e−10 (unchanged);
err1_ends 2.245e−13 / 2.243e−13; val1_ends −4.748e−25 / −9.147e−27.

Channel margins (S3): FC_k max 7.426e−40 ... 1.723e−37, XC_k max
1.669e−23 ... 6.603e−21, el_max 9.880e−20, epsF_max 7.602e−08,
dX_max 3.332e−15, dWrel_max 3.801e−08 — all identical to 2056 (the F/X
channels are untouched by the bridge).

## 3. What this buys, and the registered lever

The (P) channel is no longer the price of the ideal-twin window: it falls
365x (7.128e7 → 1.951e5) and the SOLVE channel takes the binding position
at 95.38% of ∫e_g (3.793124e+06, unchanged from 2056 — the bridge touches
nothing else).  The registered lever for the next record is therefore the
solve channel: the KKT certificate is in the uniform-floor regime
(floor/lmax 2.63e+04) and its measured d-sums read d_base_tot
4.514e+04 and d_corr_tot 2.491e+07 (v-scale max-abs), so the channel's
charge is carried by the floor correction INS_S |c_KKT − c_minnorm| and
the stored-vs-KKT deviation — a min-H1/floor-side tightening, not a
(P)-side one.  The bridge's own next lever would be the accumulation
allowance itself (allow0 1.214e−23 is the binding part of the bridged
bound for the large-a families, covers_2056_el 5.84e−04): a
cancellation-aware accumulation of the two sums would drop it, but the
gain is bounded by the solve channel now.

## 4. Nonclaims

Registered in the artifact; in short (2056's, plus the bridge's): the
sigma_loc K4 tail is a MODELLING bound, not a proven enclosure of
|E''''|; the envelope integrals are a resolved-grid convention (the 2056
refinement control, 3.5% between the 0.1 and 0.001 grids, is absorbed by
the 7.43x margin; the R56 same-run trapz both fixes and localises that
control); the Gram rule and the a_mat idealisation gap are REGISTERED and
MEASURED, not enclosed (S8, S3b: (n0,f0) stored 9.402e−14 vs true
9.402e−14 to 1e−28; (n7,f16) stored 3.335e−23 is the rule's alias floor,
true 2.424e−69; the analytic incumbent da_abs = rule_a_max = 3.410e−13);
the bridged bound's computed difference carries the accumulation allowance
of the two sums plus the piece construction deviation dp_k on the
absolute-sum scale; the piece's truth is validated at small m (P7) and at
the A12a points, and at extreme nodes (A12b) only the ARITHMETIC of the
two sums is checked against mp — the true residual at the window edge is
bounded, never computed; the exp/sqrt/cos constants are op-count
constants, not libm proofs; L4 (2053) stands, evaluator-independent;
COVER open; not a producer theorem; not RH.