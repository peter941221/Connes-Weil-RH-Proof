# 2056 — Route A link L5, priced: the ideal twin O* at the m = 1600 reduced evaluator

Verdict: **IDEAL-L2-VIABLE** at the registered owner (one-copy G8-H,
ρ = 0.6 + 40.9187190121475i, scale 0.88, K = 30, support 9.504).  Records
2048–2055 price the committed 2037-class float pipeline with the STORED
FLOATS TAKEN AS EXACT; L5 — the pipeline's own ideal-vs-stored distinction
— stood as a registered, unpriced gap (2051 sec. 5, 2052, 2054 sec. 7,
2055 sec. 7).  This record prices it.  With O the stored-float object and
O* its ideal-construction twin (true Gauss–Legendre nodes/weights and
exact panel map, exact phi values and F products, the TRUE Laplace
integral in place of the m = 1600 composite rule, the exact min-H1 solve
of the exactly-constructed stored matrices, the true sigma, the exact
book), the triangle

```
|ladder - Q(O*)|  <=  TOTAL_2055 + |Q(O) - Q(O*)|
                  <=  4.401166e+10 (2055) + 3.478788e+10 (L5, this record)
                  =   7.879954e+10
                  =   0.0231 x budget3 (3.4060498718812666e+12)
                  =   0.2314 x the 10% bar (3.4060498718812666e+11)
```

so the window node survives the idealisation with a **4.32x margin under
the 10% bar**.  The price is dominated by ONE channel and the gap's
anatomy is the record's content:

```
channel                          reading          share of int e_g
--------------------------------+----------------+----------------
(P) rule residual  (GL vs true)  | 7.128255e+07   | 94.96%
(S) solve channel  (KKT floors)  | 3.793124e+06   |  5.05%
(F) node/weight certification    | 5.443e+04      |  0.07%
(X) phi-chain rounding           | 9.738e+04      |  0.13%
--------------------------------+----------------+----------------
int e_g (0.001 grid, 80001 pts)  | 7.506767e+07   | (dxi = 0.004 for the
charge_value = 463.4198 * int e_g| 3.478784e+10   |  channel shares)
int g (same grid)                | 1.235172e+14   |
charge_kernel                    | 3.607401e+04   |
charge_L5 = value + kernel       | 3.478788e+10   |
```

The (A) sigma and (B) book channels do not enter int e_g: they are the
kernel-side factors of charge_kernel (epsK = max(sigma_eps(0), max
delta_book) = 2.920565e-10; the charge is epsK (int g + int e_g) =
3.6074e+04, six orders below charge_value).

Probe: `scripts/routea_l5_priced_2056.py` (md5
`2c4fada8e4a27020bf8eabde8c3ca643`, WSL ext4 mirror run, 167.4 s),
artifact `results/2056_l5_priced.json` (md5
`75e2ccd41140e44a55faa63a9929772e`).  L4 (record 2053) is standing and
evaluator-independent; the Gram rule and the a_mat idealisation gap stay
REGISTERED, not enclosed (S8, S3b).

## 1. Object, scope, and the frozen assembly

Object: the committed 2037-class float pipeline at the m = 1600
phi-quadrature rule (`xw1600 = phi_weights(a, panels = 6, m = 1600)`,
9600 nodes/fam), committed base/corr and kernel; window [-40, 40]; budget3
= |Q_1600| = 3.4060498718812666e+12 and bar10 = its tenth (both 2053
frozen values; C2 reproduces the frozen Q1600 to rel 2.4e-15, C1 the 2051
Q400 to the printed digits).

The assembly is frozen in the probe header before the run: with
E = g_O - g_O* the L5 input-perturbation envelope of g,

```
|Q(O) - Q(O*)|  <= int |K| |E|  +  int |K - K*| |g*|
                <= (SIG_MAX + C_book) * int e_g^L5
                   + max_xi(eps_sigma + delta_book) * (int g + int e_g^L5),
```

with SIG_MAX + C_book = 5.372183419225665 + 458.0475860314685 =
463.419769 (a valid kernel bound: the p^2 factor lives inside g, not in
K), epsK = max(sigma_eps(0), max delta_book) = 2.920565e-10, and int g =
1.235172e+14 (+ 4.5e+05 of quadrature charges).  Verdict rules (frozen):
IDEAL-L2-VIABLE if all gates pass and total < bar10; GRAY if < budget3;
FAIL otherwise; ANCHOR-FAIL on any gate miss.

The five L5 input channels (each frozen before the run; full formulas in
the probe header), all built as error BUNDLES on the committed jet
(`JetL5`, extending r51's Model):

```
(F/X)  per-node leggauss root and weight certification (mean-value
       certificate; weights w = 2/((1-x^2) P_n'^2)); phi-chain rounding
       (eps_phi, eps_phi,X, eps_F <= [...] INS_F, INS_F = 2); slots
       FC_k = a sum_i deltaF_i e^{0.5aX_i} |2 pi X_i|^k,
       XC_k = a sum_i |F_i| e^{0.5aX_i} deltaX_i (|2 pi X_i|^k zmax
              + k 2pi |2 pi X_i|^{k-1}), zmax = a(0.5 + 2 pi XI_MAX + |th|)
(P)    rule residual per family: the m = 1600 six-panel composite GL of
       f = phi(x) e^{s'x} against the true integral
(S)    KKT certificate: c* = exact min-H1 solve of the stored matrices;
       floor regime (floor/lmax = 2.6e4); dbase = |c_KKT - c_stored|
       + INS_S |c_KKT - c_mn|
(A)    eps_sigma(u) = INS_S (|T0| + 20U), T0 from the exact Gauss
       representation, M13 = 1/24
(B)    delta_book(u) from the exact book sum
```

S7 integrates the envelope on the 0.001 grid (80001 nodes) by the
EULER–MACLAURIN CORRECTED TRAPEZOID: for f in C^4,

```
int f = T_h(f) - (h^2/12)(f'(b) - f'(a)) + R,
|R| <= (2 zeta(4)/(2 pi)^4) h^4 int |f''''|  =  (h^4/720) int |f''''|,
```

so the certified bound is T_h(f) + (h^2/12)(|f'(a)| + |f'(b)|) +
(h^4/720) int |f''''|.  Error channel: |E'(±40)| <= the k = 1 error slot
at the ends (measured 0.0243 both ends), |E''''| <= sigma_loc K4 with
sigma_loc = min(2, 2 err0/(|g| + err0)).  Value channel: the k = 1 slot
carries the exact g' (checked against a central difference at the one
node where the FD is resolvable: xi = -6.68, rel 4.1e-08; at the wings
g ~ 1e-25 and the FD itself is noise), |g''''| <= K4.

## 2. The three levers this record needed (all three were defects)

The gap was NOT cheap: the first smoke carrying the corrected
error-slot channel priced L5 at 1.336e+18 = 3.9e6 x bar10.  Three
separate defects, each measured and each now an instrument law
(AGENTS.md section 2g):

**(1) The outer-panel elementary bound must take the max of the PRODUCT.**
The (P) channel's outer panels (|u| >= 1 - 1/6, i.e. the panels reaching
u = ±1, where no Trefethen ellipse exists) use the elementary bound
|I| + |GL| <= 2 (a/3) max_panel |phi(x) e^{s'x}|.  The first drafts
computed phi_max(panel) times max_panel |e^{s'x}| — the max of each factor
at a DIFFERENT point, valid but loose.  The exact maximum is available in
closed form repeatedly: h(u) = -K/(1-u^2) + a Re(s) u has h''(u) =
-2K(1+3u^2)/(1-u^2)^3 < 0 on (-1, 1), so h is strictly concave and its
panel maximum is the clip of the unique root of h', found by 80
bisections of a strictly decreasing h' (`h_out`).  Measured gain per
family: 1.49x at a = 1.76, 43.1x at a = 4.752 — and it is the
large-a families that dominate the chain.  el_max: 4.2586e-18 ->
9.8802e-20.  The same tightening moved the registered a_mat incumbent
(S3b a-side) from 2.73e-08 to 3.410e-13.

**(2) The quadrature correction must be the EM endpoint form, not a
sup-over-cells charge through the error slots.**  The drafts charged
int E <= trapz(err0) + (h^2/12) int sup_cell |E''| with sup_cell |E''|
from the error slots err2 + rho err3 + (rho^2/2) E4.  The error slots are
|·|-sums and carry NO cancellation: at the cancellation nodes the mean
err2 reads 3.7e+16 against a mean err0 of 0.73 (smoke, 801 nodes) — a
ratio of 5e+16 — so the charge read 3e+07 x the trapz term (corr
2.4712e+15 against tr 7.7707e+07 at dxi = 0.1) and the price 1.336e+18.
The EM form depends on E's OWN derivative at TWO points, which
cancellation cannot inflate: at the 0.001 grid the charge is EM
4.05e-09 + regress 3.62 against the trapz 7.5068e+07.  The regress term
is small exactly because sigma_loc damps it (sig_loc_max = 2.0 at a few
nodes but the integral of sigma_loc K4 collapses; k4_trapz 3.25e+20,
ek4_trapz 2.61e+15 — the 4.3x margin absorbs the modelling-bound status,
disclosed in NONCLAIMS).  The same EM form is used for the value channel:
EM 4.03e-32, regress 4.51e+05 against tr 1.2352e+14 — negligible.

**(3) Consistency gates between two float evaluators scale by their own
allowances.**  P6 compares the jet's value slot with
r52.committed_and_bound at 16 shared nodes.  Both chains evaluate the
same expression in different accumulation orders, so the honest scale is
the SUM of the two certified forward-rounding allowances: |dev| <=
EG_r52 + jet err0.  The drafts gated against the safe-magnitude product
S6 = |p|_safe^2 (sum |base||v|)^2 (sum |corr||v|)^2 and read 2.265e-07 —
S6 bounds the chain's VALUE magnitudes, not the two accumulators'
rounding, whose scale is the per-family absolute sum sum_i |F_i|
e^{0.5 a X_i} ~ 1.7e-12 (measured).  Measured with the allowance form:
worst dev/(EG_r52 + err0) = 9.906e-06 over the 16 nodes (TOL 1.0 — the
statement itself), with the S6 ratio retained as a control
(P2P6.p6_rows[].dev_over_S6).  P2 (jet vs r51's Model on four nodes)
stays bitwise, 0.0.

## 3. Controls (all green)

```
C1/C2    Q400 -1.1111757839943652e+20 (2051 frozen), Q1600
         -3406049871881.275 (2053 frozen, rel 2.4e-15)
C4       tier-B d_base 2.1507e-09 / d_corr 2.4812e-09
P4/A10   leggauss certificate dxi_max 3.010e-16 (m = 1600) /
         2.841e-16 (m = 400); oracle dev 2.04e-53 at dps 120 over all
         1600 legendre roots
P3       rule-bound selftest: 0 bad, ellipse clear_min 0.0079; worst
         bound/err 1e+36 (a valid but loose check at small m)
A11      rule_bound_vec vs rule_residual_lnE: worst rel 0.00e+00
         (3 families x 5 |Im s'| up to a(2 pi 40 + |th|))
P5       KKT theta 8.94e-28, wrel 7.59e-07, lmin 2.888e-29,
         lmax 3.807e-23, floor/lmax 2.63e+04 -> uniform-floor regime
A7/A8    sigma containment worst ratio 0.199 (u = 0); book ratios
         0.007 / 0.000 / 0.573 / 0.000 / 0.007; eps_sig(0) 5.815e-14
A9       rule bound >= true residual at all sampled (a, th, xi):
         worst ratio 2.57e-05
B2/B3    solve channel 1.58e-14 / 4.65e-03 / 3.09e-18; F channel
         1.88e-08 / 1.34e-07 / 6.28e-12 (all <= 1)
B5       jet selftest pass: T1 1.48e-15, T2 K4 24.000000000000007 >= 24,
         T3 0.09150625000000023 vs sampled 0.09150625000000004
S8       gram cross-read d12 1.423e-13, d13 2.286e-13 (registered)
```

Channel margins (S3): FC_k max 7.426e-40 ... 1.723e-37, XC_k max
1.669e-23 ... 6.603e-21, el_max 9.880e-20, epsF_max 7.602e-08,
dX_max 3.332e-15, dWrel_max 3.801e-08.

## 4. The measured structure of the (P) channel

The panel decomposition (smoke diagnostics, reproduced in S3 as
`el_node_profile`): the elementary outer-panel bound is
|Im s'|-INDEPENDENT and dominates at EVERY node, while every inner
Trefethen panel is floored at 1e-300 (at m = 1600 the rho^{-2m} factor is
e^{-5575} for uc = 0.5, e^{-7000}-scale elsewhere).  Hence el_end ==
el_hump for all 17 families (u_end 464–822, u_hump 1.85–212) and the
node-dependence of the (P) envelope is vacuous in practice: the
decomposition reads rule 7.128255e+07 against rule_wsup 7.128255e+07.
The node-dependent machinery (a * rule_bound_vec at every node, the
(2 pi a^2)^k derivative transport, A11) is kept because it is the honest
evaluation of the same formula and would bind if the outer-panel bound
were ever tightened below the inner floor.

## 5. What this buys, and the registered lever

The L5 gap is now priced at 3.478788e+10 = 0.1021 x bar10, and the
window node of the L2 architecture on the ideal twin lands at
7.879954e+10 = 0.2314 x bar10 (4.32x margin) — the certificate's own
object now has a priced window, not just its stored-float shadow.

The binding term is the (P) channel at 94.96% of int e_g, and within it
the elementary outer-panel bound — a bound on |I| + |GL| (the SUM of the
integral and its quadrature, not their difference) that is
oscillatory-unaware and independent of m.  Registered lever for the next
record: the SPLIT-RULE BRIDGING
|GL_committed - I| <= |GL_committed - GL_split| + |GL_split - I|, where
GL_split is the same composite rule on a partition whose outer panels are
subdivided at |u| = 1 - delta: every piece of GL_split is then either
ellipse-bounded (sub-geometric, floored) or a thin edge slice whose
elementary bound carries exp(-K/(2 delta)) instead of exp(-K/(1 - (2/3)^2))
(delta = 0.05: e^{-308} against e^{-54}); the bridging difference is a
computable sum difference (the 2053 alias measurements put that scale at
~1e-12 relative).  Expected gain >= 1e+03, i.e. the (P) channel leaves the
binding position; a sub-geometric enclosure of the flat-singularity
residual would do the same with analysis rather than computation.

## 6. Nonclaims

Registered in the artifact; in short: the sigma_loc K4 tail is a
MODELLING bound (not a proven enclosure of |E''''|; the regress it bounds
is measured); the envelope integrals are a resolved-grid convention
(refinement control 3.5% between the 0.1 and 0.001 grids, absorbed by the
4.32x margin); the Gram rule and the a_mat idealisation gap are
REGISTERED and MEASURED, not enclosed (S8, S3b — the solve channel
certifies the stored matrices, O* = exact solve OF THE STORED MATRICES);
P3/A9 validate the rule-bound structure at small m and small |Im s'|;
the exp/sqrt/cos constants are op-count, not libm proofs; L4 stands,
evaluator-independent; COVER open; not a producer theorem; not RH.