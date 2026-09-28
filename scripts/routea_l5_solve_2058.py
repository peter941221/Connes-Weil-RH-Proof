#!/usr/bin/env python3
# routea_l5_solve_2058.py — record 2058 (probe; verdict rules frozen
# before the run)
#
# LINK L5, SOLVE SIDE: the SOLVE-channel tightening registered by record
# 2057 sec. 3, executed.  Everything below is record 2057 (routea_l5_
# bridged_2057.py, md5 d093b7d643a80b9a1e67c6b4d3bd3a3e, artifact md5
# 28966087fc928cbc5202364c64e3aeed) with ONE channel repriced: the solve
# channel LEAVES the pointwise input-perturbation envelope and is charged
# by the DIRECT FUNCTIONAL DIFFERENCE.  The R57 gate re-derives the 2057
# price in this same run, so the whole change is a same-run difference.
#
# 2057 (the split-rule bridge, retained verbatim below) left the solve
# channel BINDING: 3.793124e+06 of the 3.976762e+06 int e_g, i.e.
# 1.758e+09 of the 1.843e+09 charge_L5 -- the stored-vs-KKT deviation
# d_base_tot 4.514e+04 / d_corr_tot 2.491e+07 plus the floor correction
# INS_S |c_KKT - c_minnorm|, all carried POINTWISE: |delta_j| scales the
# family jet (value + derivative slots + K4) through the bundle algebra,
# the envelope is integrated positively, and the integral is multiplied
# by the crude kernel sup (SIG_MAX + C_book) = 463.42.
#
# THE SOLVE CHANNEL IS QUADRATIC IN THE COEFFICIENTS.  The functional is
#   Q(c) = int K p^2 |lb(c)|^2 |cc(c)|^2,  lb = base @ v, cc = corr @ v,
# so the solve channel's content is ONE NUMBER,
#   dQ = Q(c_mn) - Q(c_stored),
#  (c_stored = the committed float min-H1 solve; c_mn = the exact
# min-norm interpolant of the stored matrices, the exact-arithmetic twin
# of the committed clamped-inverse rule in its uniform-floor regime) and
# it can be COMPUTED on the committed grid instead of enveloped.  The
# pointwise-envelope route is not merely loose here, it is numerically
# UNAVAILABLE: the sensitivity-collapse integral A_j = int W |cc0|^2
# conj(lb0) v_j (fold the perturbation into the two quadratic factors)
# does not converge under the trapezoid -- the diagnostic (diag_2058_
# collapse, artifact md5 e140e44ec2bce93d9e9ed1934621ba10) measures
# |A_b0| = 12.82 / 25.64 / 51.27 at dxi = .008/.004/.002, an exact
# factor-2 growth per grid halving (the 4-fold product in the integrand
# has ~568 rad/unit bandwidth against a ~1e+01-sized integral), while
# dQ itself reads 2.289397e+04 stable to 5 digits on the same grids and
# Q0 = -3.40604987188e+12 reproduces the frozen Q1600 to 2e-11 rel.
# The difference CANCELS the shared quadrature error; the tripled
# integrand cannot.  This is the 2057 computed-difference allowance law
# (record 2057 sec. 2h) applied at the functional level: charge the
# difference, carry an allowance for the arithmetic and the grid.
#
# SO:  |dQ| <= |dQ_float| + qe_grid + qe_arith, with
#   qe_grid  = 4 max(|dQ(.001) - dQ(.004)|, |dQ(.001) - dQ_phi(.001)|):
#              the nested-coarse and incommensurate (phi-shifted, same
#              density) controls; both estimate the main grid's own
#              difference-quadrature error (the coarse reading is an
#              upper proxy, the phi reading a same-scale one),
#   qe_arith = INS (trapz err0(none, at c_stored) + trapz err0(cast, at
#              c_mn)) + 32U trapz |W (g1 - g0)|: the two chains' own
#              certified forward-rounding envelopes (the null-channel
#              bundle at each coefficient vector; the c_mn jet carries
#              the coefficient-cast envelope INS U |c_mn| on top, so its
#              err0 covers the cast of the exact min-norm solve into the
#              float chain) plus the post-chain ops (W multiply,
#              subtraction, trapezoid accumulation).
# Within the channel, W = K p^2 is NOMINAL on both sides: the kernel and
# p chains price their own input deviations in the (sigma/book) and F/X
# channels, so no qe_K term belongs here (their float rounding cancels
# in the difference like the quadrature).
#
# The solve channel is ZEROED OUT of the envelope for the main pass
# (l5["dbase"]/["dcorr"] = 0 -> int e_g^{ns}, the F/X/(P) channels
# only); the full 2057 configuration is re-run on the same grid in the
# same process (gate R57: int e_g, charge_value, charge_L5 bitwise-class
# agreement with the frozen 2057 figures), and the value slots are
# gated to be untouched by the zeroing (gate B7: int g bitwise equal,
# so the zeroing moved the error channel only).
#
# THE BRIDGE (the 2056-registered lever, now executed).  For an outer
# panel P = [2a/3, a] (right; mirrored on the left) cut at |u| = 1-delta
# (DELTA_SPLIT = 0.05) into P1 = [2a/3, a(1-delta)] and the edge slice
# P2 = [a(1-delta), a], with S1 the SAME composite GL rule (m = 1600) on
# P1:
#   |GL_c - I| <= |GL_c - S1| + |S1 - I_P1| + |I_P2|,
#   * |GL_c - S1| is a COMPUTED complex sum difference: no bound is
#     needed on either rule's own residual.  The floated difference is
#     carried with the accumulation allowance of both sums, on the
#     absolute-sum scale (the P6 lesson), plus the piece rule's own
#     construction deviation against the IDEAL piece rule the ellipse
#     bound applies to (dp_k: fx_channels op-count formulas on the
#     certified tables of the SAME root array, + 2 map slots),
#   * |S1 - I_P1| <= Trefethen ellipse bound of P1: rho_max = 2.2651,
#     rho = max(2, 0.98 rho_max) = 2.2196 -> rho^{-2m} = e^{-2552}
#     (floored at 1e-300, dead), same M(rho) formula as the inner panels
#     (validated on the piece geometry by gate P7 at small m),
#   * |I_P2| <= delta a exp(h_out(1-delta, 1)): the slice carries
#     phi <= e^{-K/(2 delta)} = e^{-300} at delta = 0.05, against the
#     e^{-54}-scale of the touching panel.
# Per node the (P) bound is the MIN of the elementary and bridged forms
# plus the four floored inner panels; per slot k it carries the computed
# difference at slot k (moment (2 pi a |x|)^k, direct -- no transport),
# while the K4 entry transports the k = 0 bound by (2 pi a^2)^4 as in
# 2056.  Gate A12 checks the bridged bound against (a) mp.quad truth at
# modest |Im s'| and (b) exact-arithmetic mp reproductions of the two
# sums at extreme nodes (where no quadrature can run).
#
# Records 2048-2055 price the committed 2037-class float pipeline with
# STORED FLOATS TAKEN AS EXACT.  Write O for that object (stored floats
# evaluated in exact arithmetic; committed kernel floats kept) and O* for
# its ideal-construction twin: true Gauss-Legendre nodes/weights and exact
# panel map, exact phi values and F products, the TRUE Laplace integral in
# place of the m = 1600 composite rule, the exact min-H1 solution of the
# (exactly-constructed) stored matrices, the true sigma, and the exact
# book.  L5 is the registered gap |Q(O) - Q(O*)| (2051 sec. 5, 2052,
# 2054, 2055 sec. 7).
#
# THE ASSEMBLY IS A TRIANGLE, WITH THE SOLVE CHANNEL SPLIT OFF.  TOTAL_2055
# bounds |ladder - Q(O)|.  Hence
#   |ladder - Q(O*)| <= TOTAL_2055 + |Q(O) - Q(O*)|,
#   |Q(O) - Q(O*)| <= int |K| |g_O - g*| + int |K - K*| |g*|
#                   <= (SIG_MAX + C_book) * int e_g^{L5,ns} + charge_solve
#                      + max_xi(eps_sigma + delta_book) * (int g + int e_g^{L5,ns}),
# where e_g^{L5,ns} is the L5 input-perturbation envelope of g with the
# SOLVE CHANNEL ZEROED (F/X/(P) channels only; the committed jet with
# l5["dbase"] = l5["dcorr"] = 0) and charge_solve = |dQ_float| +
# qe_grid + qe_arith (the channel whose content was split off, priced by
# the direct difference of sec. header above).  QUADRATURE (S7): the error
# function E = g_O - g_O* is integrated by the EULER-MACLAURIN CORRECTED
# TRAPEZOID.  For f in C^4 on the window,
#   int f = T_h(f) - (h^2/12)(f'(b) - f'(a)) + R,
#   |R| <= (2 zeta(4)/(2 pi)^4) h^4 int |f''''| = (h^4/720) int |f''''|
# (the classical zeta-form EM remainder), hence the certified bound
#   int f <= T_h(f) + (h^2/12)(|f'(a)| + |f'(b)|) + (h^4/720) int|f''''|.
# Error channel: |E'(+-40)| <= the k=1 error slot at the ends, and
#   E4 = |E''''| <= sigma_loc K4,   sigma_loc = min(2, 2 err0/(|g| + err0)):
# the perturbation is multiplicative with local relative size err0/|g|,
# so |E^(4)| <= sigma_loc K4 (path integral along the O -> O* line, the
# payload split per factor; the cap 2 is the crude |E^(4)| <= 2 sup|g^(4)|
# fallback -- a modelling bound, disclosed in NONCLAIMS).  Value channel:
# the k=1 slot carries the exact g', so |g'| at the ends is known, and
# |g''''| <= K4.  The first drafts charged (h^2/12) int sup_cell |E''|
# through the error slots; the |.|-sum inflation at cancellation nodes
# (smoke means err2 3.7e16 against err0 0.73) made that charge 3e+07x
# the trapz term and the price read 1.3e+18.  The EM endpoint form
# depends on E's own derivative at TWO points, which cancellation cannot
# inflate.  No ladder-side (Coef1) channel exists for L5: the ladder
# value is fixed at O and the triangle absorbs the rest.  All channels
# are disjoint from 2048-2055 by construction (those bound
# |ladder - Q(O)|; these bound |Q(O) - Q(O*)|).
#
# CHANNELS (each frozen before the run)
#
# (F/X)  Node/weight certification: for each numpy leggauss root xi_i the
#   true root satisfies |xi_true - xi_i| <= delta_i by the mean-value
#   certificate delta = sup_box|P_n| / inf_box|P_n'| with the box radius
#   solved to fixed point from the P_n / P_n' / P_n'' values at xi_i;
#   values from mpmath.hyp2f1(-n, n+1, 1, (1-x)/2) at the ambient dps 50,
#   with the validated absolute value error E_VAL = 1e-28 (A10: dps
#   doubling to 120 changes every certified value by <= 1e-28 at 21
#   sampled nodes; the forward interval recurrence was rejected after
#   measurement -- its widths grow past 1e178 at n = 1600 outside the
#   central region, and the float recurrence itself is wrong by 2x at
#   x = 0.5; mpmath agrees with it to 12 digits only where its widths
#   stay <= 1e-20).  P_n' = n(P_{n-1} - x P_n)/(1-x^2); P_n'' from the
#   Legendre ODE.  Weights: w = 2/((1-x^2) P_n'(x)^2) with a relative
#   interval 2(|P_n''/P_n'| delta + 1e-24) + 1e-15.  Panel-map rounding:
#   delta_X <= a delta_xi + 3U (a + |X|); delta_W/W relative + 3U (map).
#   Phi chain (float count, delta = 1-u^2, u = |X|/a):
#     eps_phi   <= |K/d| U (3u^2/d + 2) + 8U          (exp constant 8U)
#     eps_phi,X <= 2|K||X|/(a^2 d^2) delta_X
#     eps_F     <= [eps_phi + eps_phi,X + delta_W/W + 3U] INS_F, INS_F=2
#   Per family j, v-derivative slots k = 0..4 (EXACT v units):
#     FC_k = a sum_i deltaF_i e^{0.5aX_i} |2 pi X_i|^k
#     XC_k = a sum_i |F_i| e^{0.5aX_i} deltaX_i *
#              ( |2 pi X_i|^k zmax + k 2pi |2 pi X_i|^{k-1} ),
#     zmax = a (0.5 + 2 pi XI_MAX + |theta|),  deltaF_i = |F_i| eps_F,i.
#   a-side (m = 400 at the 17 owner nodes): rule residual at the node
#   arguments times a, plus the same F-construction data bound summed
#   directly over the 400 caps at each node's exponent weight.
#   REGISTERED, NOT ENCLOSED: the a_mat idealisation gap (the m = 400
#   rule vs the true Laplace integral at the owner-node arguments).
#   Measured (S3b): matched pairs agree with mp.quad dps 60 to 12+
#   digits; mismatched family-node pairs carry |Im s'| up to 228 and the
#   stored entry is the rule's own alias floor (entry (7,16): stored
#   3.3154e-23 vs exact rule 3.3186e-23 vs true integral 1.53e-69);
#   the analytic incumbent (worst pair, outer-panel elementary bound,
#   oscillatory-unaware) was 2.73e-08 and reads 3.41e-13 after the
#   h_out concave-max tightening -- still vacuous against the 1e-12
#   entry scale, so no enclosure is claimed.  The solve
#   channel therefore certifies the stored matrices (O* = exact solve
#   OF THE STORED MATRICES, per the frozen O* definition).
#
# (P)  Rule residual per family: six-panel composite GL(m = 1600) of
#   f = phi(x) e^{s'x}.  Outer panels (reaching |u| = 1): elementary
#   |I| + |GL| <= 2 (a/3) max_panel |phi(x) e^{s'x}| -- the max of the
#   PRODUCT, via h_out: h(u) = -K/(1-u^2) + a Re(s) u is strictly concave
#   on (-1, 1) (h'' = -2K(1+3u^2)/(1-u^2)^3 < 0), so its panel maximum is
#   the clip of the unique root of h' (80 bisections of a strictly
#   decreasing h').  The first drafts multiplied phi_max(panel) by
#   max_panel |e^{s'x}| at a DIFFERENT point -- a valid but loose bound
#   (measured 1.7x for a = 1.76, 45x for a = 4.75), and it was the
#   binding term of the whole L5 price.  Inner
#   panels: E <= C_T M(rho) rho^{-2m}/(1 - rho^{-2}) (Trefethen ellipse
#   bound; C_T = 1e6 generous, structure validated by the P3 selftest),
#   rho = 0.98 rho_max, cosh(mu_lim) = (1-|uc|)/hu, rho_max =
#   chm + sqrt(chm^2 - 1);
#     M(rho) = exp(-K c_phi + a Re(s) uRe_max + |Im s'| ymax),
#     c_phi = (1-|u|^2max)/(1+|u|^2max)^2, uRe_max = uc + hu chm (Re s >= 0)
#     else uc - hu chm, ymax = hu shm (u-units times a).  log space;
#   every exp floored at 1e-300 (underflow must not understate a bound).
#   NODE-DEPENDENT ENVELOPE.  The bound depends on the node ONLY through
#   |Im s'| = a|theta - 2 pi xi|; El_j(xi) is evaluated at every node
#   (a * rule_bound_vec, the vectorized twin of rule_residual_lnE, gated
#   by A11).  The residual's xi-derivative slots follow from the SAME
#   bound: d^k/dxi^k of the residual is the rule residual of the
#   integrand phi(x) (2 pi a x)^k e^{s'x} (the phase (-2 pi i)^k factors
#   out of the absolute value), whose panel bound multiplies by the
#   ellipse moment (2 pi a |x|)^k <= (2 pi a^2)^k (|x| <= a on the used
#   ellipses), so slot k carries (2 pi a^2)^k El_j(xi) (k = 0..4; the
#   K4 entry is node-dependent).  The window-sup El_j of the earlier
#   drafts is retained only as a control (S3).  MEASURED STRUCTURE (the
#   panel decomposition of the smoke): the elementary outer-panel bound
#   is |Im s'|-INDEPENDENT and dominates at EVERY node, while every
#   inner Trefethen panel is floored at 1e-300 (lnE -1840 ... -7250 at
#   m = 1600, si = 0: the rho^{-2m} factor is e^{-5575} for uc = 0.5),
#   so El_j is node-independent in practice and el_node == el_wsup; the
#   node-dependence is kept because it is the honest evaluation of the
#   same formula (and would matter if the outer bound were ever
#   tightened below the inner floor).
#
# (P') 2057 BRIDGE: the outer panels no longer use the elementary bound
#   alone.  Bound per outer panel P:
#     B_P = min(2 (a/3) exp(h_out),
#               |GL_c,P - S1_P| + allow + ell(P1)
#               + delta a exp(h_out over P2))
#   ell(P1) is the ellipse bound above with the P1 geometry
#   (uc' = (2/3 + 1 - delta)/2, hu' = (1 - delta - 2/3)/2 on the right,
#   mirrored on the left); allow_k = INS ((EPS_TERM + (2k + 4m) U + amp)
#   (Ac_k + Ap_k) + dp_k), Ac_k / Ap_k the committed-outer and piece
#   absolute sums at moment k (node-independent: Re z = a/2), dp_k the
#   piece's construction deviation against the IDEAL piece rule the
#   ellipse bound applies to (the fx_channels op-count formulas on the
#   certified dxi / wlo / whi tables of the SAME numpy root array, plus
#   the two map slots); and
#   |GL_c - S1| per slot as |acc_outer[:,k] - accR[:,k] - accL[:,k]|
#   (complex difference, no modulus of the parts).  The two outer panels
#   are combined into ONE difference before the modulus (tighter).  The
#   inner panels keep rule_bound_vec's floored terms, with the two
#   elementary outer terms subtracted off it (same expression, same
#   floats -- rule_bound_vec is called and reused, not re-derived).
#
# (S)  KKT certificate: c* = the exact min-H1 solution of the stored
#   (gram, a_mat) is the c-part of K^{-1} b, K = [[gram, a^H],[a, 0]],
#   b = [0; y].  X = K^{-1} at dps 50; E = I - X K in iv (float entries
#   thin); theta = ||E||_inf < 1 certifies invertibility and
#   ||K^{-1}||_inf <= ||X||_inf/(1-theta).  Residual r = K[c_stored;
#   lambda*] - b in iv; ||c_stored - c*||_inf <= ||K^{-1}||_inf ||r||_inf.
#   Floor regime: the committed rule inverts with max(ew, floor),
#   floor = max(eigmax 1e-12, 1e-18).  Measured here: floor/lmax =
#   2.6e4 >= 1 (uniform-floor regime), so the exact-arithmetic rule
#   value is inv = ev/floor @ ev^T = I/floor and the rule's exact twin
#   is the min-norm interpolant A^H (A A^H)^{-1} y, independent of the
#   eigenbasis; it agrees with the exact KKT solve of the same matrices
#   to |c_KKT - c_mn| (measured in mp, booked with INS_S).  The solve
#   channel is dbase = |c_KKT - c_stored| + INS_S |c_KKT - c_mn|.
#   The Gram construction rule (GAUSS_POINTS single-panel GL, sub-
#   geometric flat-singularity residual) is REGISTERED and MEASURED
#   (S8), not enclosed.
#
# (S') 2058 SOLVE CHANNEL: charged by the DIRECT FUNCTIONAL DIFFERENCE.
#   dQ = Q(c_mn^f) - Q(c_stored), Q(c) = int K p^2 |c @ v|^2 ... as in
#   the header; c_mn^f = the float cast of the exact min-norm solve of
#   the stored matrices (uniform-floor regime twin of the committed
#   clamped rule).  Grid set: main dxi = 0.001 on the S7 window
#   [-40, 40] (80001 nodes -- the same grid as the envelope pass),
#   coarse control dxi = 0.004 (nested), phi control: the same dxi with
#   an incommensurate phase shift (offset 0.6180339887498949 dxi, last
#   cell completed to +40) so a grid-locked aliasing error cannot hide
#   in the nested pair.  charge_solve = |dQ| + 4 max(dev_coarse, dev_phi)
#   + INS (trapz err0_c0 + trapz err0_cm) + 32U trapz |W (g1 - g0)|,
#   err0_c0 = the null-channel jet at (base, corr) [pure forward
#   rounding of the committed chain], err0_cm = the null-channel jet at
#   (c_mn^f, c_mn^f) TOGETHER WITH the cast envelope INS U |c_mn| (one
#   pass; the bundle adds the two channels, so its err0 covers
#   rounding(c_mn) + cast(c_mn)).  Its own truth checks: gate D1
#   (pointwise difference vs mpmath at sample nodes, incl. full-chain mp
#   at hump/edge nodes), D2 (the two grid controls), D3 (the envelopes'
#   monotonicity under zeroing), D4 (the same-grid marginal difference
#   int e_g(full) - int e_g(ns) vs the 2057 single-channel reading).
#   dQ is computed with W NOMINAL on both sides (see header): the
#   kernel's own input deviation is the (A)/(B) channel's business.
#
# (A)  eps_sigma(u) = INS_S (|T0| + 20 U), INS_S = 4; T0 from the exact
#   Gauss representation with |T0| <= 2 M13/(|w|^12 Dmin), M13 = 1/24,
#   w = 8.25 - i u/2 (u = omega = 2 pi xi), Dmin = x^2+y^2 if |y| <= x
#   else 2x|y|; 20 U = the op-count chain of r59.rig.sigma_vec.
#
# (B)  delta_book(xi) = sum_k c_k (3U |2 pi xi log n_k| + 6U),
#   c_k = 2 Lambda(n_k)/sqrt(n_k).
#
# |K| <= SIG_MAX + C_book; SIG_MAX = 5.372183419225665 = sigma(0) =
# log pi - psi(1/4); sigma decreasing on u > 0 by Im psi'(z) =
# sum_n 2(1/4+n)(u/2)/|z+n|^4 > 0 (series representation).
#
# FROZEN VERDICT RULES
#   charge_L5 := charge_value + charge_kernel
#   total_ideal := TOTAL_2055 + charge_L5
#   IDEAL-L2-VIABLE : all gates pass AND total_ideal <  BAR10
#   IDEAL-L2-GRAY   : all gates pass AND BAR10 <= total_ideal < BUDGET3
#   IDEAL-L2-FAIL   : all gates pass AND total_ideal >= BUDGET3
#   ANCHOR-FAIL     : any gate misses
#   TOTAL_2055 = 4.401166144143504e+10 (2055 artifact md5
#   b5c1a9c914d7499e1a06780b4797eeed), BUDGET3 = 3.4060498718812666e12,
#   BAR10 = 3.40604987188126656e11.
#   SAME rules as 2056/2057 (the object and the triangle are unchanged;
#   only the solve channel's price tightens).  The 2057 figures this
#   record is compared against, frozen from the committed artifact
#   (28966087fc928cbc5202364c64e3aeed): CHARGE_L5_2057 =
#   1842946433.9779341, CHARGE_VALUE_2057 = 1842910359.9871004,
#   INT_EG_2057 = 3976762.498008143, TOTAL_IDEAL_2057 =
#   45854607875.41298, SOLVE_DECOMP_2057 = 3793124.474011112 (the S7
#   single-channel reading, dxi = 0.004).
#
# GATES (frozen)
#   P2  zeroed-L5 jet vs r51.Model.g_jet on 4 sample nodes: all bundles
#       + K4 slots max rel <= 1e-12
#   P3  rule-bound selftest: m in {6, 10, 20}, random (a, theta, xi),
#       mpmath quad dps 40 references: bound >= true error in >= 8 cases;
#       ellipse clearance: min sampled distance to u = +/-1 > 0.005 for
#       every used inner ellipse
#   P4  leggauss certification: n = 1600 and n = 400: all nodes certified
#       (nonzero slope, delta_i <= 1e-9), max delta_i <= 1e-10
#   A10 dps-doubling validation: at 21 sampled nodes of the n = 1600
#       table, |P(x; dps 120) - P(x; dps 50)| <= 1e-28 for both P_n and
#       P_{n-1} (validates E_VAL = 1e-28)
#   P5  KKT: theta <= 1e-3 both sides; relative Weyl margin
#       (lmin - 17 U lmax)/lmax > 1e-9; floor regime clean
#       (floor >= lmax uniform-floor OR floor <= lmin floor-free)
#   P6  jet value slot vs r52.committed_and_bound value at 16 shared
#       nodes: |dev| <= EG_r52 + jet err0, the SUM of the two calculi's
#       own certified forward-rounding allowances (both chains evaluate
#       the same expression, in different accumulation orders).  Drafts
#       gated against the safe-magnitude product S (|p|_safe^2
#       (sum|base||v|)^2 (sum|corr||v|)^2) and read 2.3e-07: S is a bound
#       on the chain's VALUE magnitudes, not on the two accumulators'
#       rounding, whose scale is the per-family absolute sum
#       sum_i |F_i| e^{0.5 a X_i} (~1.7e-12 measured).  S is kept as a
#       recorded control (dev_over_S6 in the rows).
#   A11 rule_bound_vec (the vectorized node-dependent rule bound) vs
#       rule_residual_lnE at 3 families x 5 |Im s'| values, rel <= 1e-12
#   C1  Q_400 vs -1.1111757839943646e+20 rel <= 1e-6, sign < 0
#   C2  Q_1600 vs -3.4060498718812666e+12 rel <= 1e-6, sign < 0
#   C3  setup: families 17, book 1647, support 9.504, C_book
#       458.0475860314685, C1_book 21898.85724574201 rel <= 1e-9
#   C4  tier-B recompute vs 2054: d_base 2.151e-09, d_corr 2.481e-09
#       rel <= 1e-2
#   A7  sigma float vs mpmath digamma dps 40 at 13 u-points:
#       |dev| <= eps_sigma(u), all ratios < 1
#   A8  book float vs mpmath dps 40 at 5 xi: |dev| <= delta_book, ratio < 1
#   A9  rule: mpmath quad dps 40 at 6 (family, xi = theta/2pi) with
#       |Im s'| <= 12: |GLsum_float - integral| <= El_j/a (v-units), < 1
#   B2  solve channel truth (2057's pointwise-envelope form): RETIRED in
#       2058 -- the solve channel no longer has a pointwise envelope.
#       Its replacements are D1-D4 below (the direct difference's own
#       truth/controls); the pointwise envelope machinery itself stays
#       validated by B3 (F channel) and P2/P6.
#   D1  direct-difference truth: at 3 sample nodes (one hump xi = -6.68,
#       two window-edge xi = +-39.9375), |D_float - D_mp| <=
#       INS (err0_c0 + err0_cm) + 32U |W(g1-g0)| at the node, ratio <= 1,
#       D = W (g1 - g0) pointwise; D at one hump node additionally with
#       the FULL chain in mp (exact v, not lifted), same criterion
#   D2  grid controls: dev_coarse = |dQ(.001) - dQ(.004)|, dev_phi =
#       |dQ(.001) - dQ(phi-shifted .001)|; charge carries 4 max(...);
#       gate: max(...) / max(|dQ|, 1) <= 1e-3 (smoke: 0.2)
#   D3  envelope monotonicity at sample nodes: err0(ns) <= err0(full)
#       and err0(cast-jet) >= err0(cast-off jet at the same coefficients)
#   D4  same-grid marginal solve reading: int e_g(full) - int e_g(ns)
#       > 0 and within [0.2, 5] x SOLVE_DECOMP_2057 (3.793124e+06)
#   B7  zeroing control: int g and the val0/val1 arrays BITWISE equal
#       between the ns and full passes (the zeroing moved the error
#       channel only) and the ns envelopes <= full pointwise is NOT
#       required (channel removal acts through the bundle, gated
#       pointwise at sample nodes by D3)
#   B3  F channel truth: at 3 sample nodes, |g(F_mp at stored XW) -
#       g(F_stored)| <= e_g^{F-only}(node), ratio <= 1
#   B4  all charges finite, >= 0
#   B5  r51.selftest passes
#   SIGMAX: max |sigma_float| on the grid <= SIG_MAX
#   A12a bridge truth: at 6 (family, xi) points with |Im s'| <= 64,
#       mp.quad dps 40 truth: a * |GL_c - I| <= the jet's own (P) channel
#       bound at that node (v-units, the A9 shape, on the BRIDGED bound)
#   A12b bridge arithmetic: at 4 extreme nodes (|Im s'| up to the window
#       edge, where no quadrature resolves the rule), the mpmath dps 50
#       reproduction of BOTH sums (repr-lifted stored floats) satisfies
#       |D_float - D_mp| <= allow; |D_mp| is recorded
#   A13 bridge gain: at the S3 profile nodes (every family: hump and
#       window-edge |Im s'|), the bridged bound <= the 2056 elementary
#       bound at every family, and the ratio is recorded per family
#   A14 bridge tightness at truth points: bound <= the 2056 elementary
#       bound at the A12a points (the bridged form is not allowed to be
#       looser where truth is measurable)
#   B6 no-bridge regression: JetL5B with bridge off vs JetL5 (r56's
#       channel) on 16 nodes: err0/k4/max-slot BITWISE 0.0
#   R57 2057 price reproduction IN THIS RUN: the same S7 pass with the
#       FULL 2057 l5 configuration (bridge + dbase/dcorr) vs the frozen
#       2057 figures (int_eg, charge_value, charge_l5) rel <= 1e-9
#       (2057's R56 is not re-run: its role -- same-run reprice of the
#       parent record -- is R57's, and the 2056 figures are two records
#       back; B6 still pins the bridge-off bitwise identity)
#   P7 piece-ellipse selftest: m in {6, 10, 20} on the P1 geometry,
#       random (a, theta, xi): the ellipse bound >= the true piece error
#       (mp.quad dps 40) in >= 8 cases; piece ellipse clearance > 0.005
#
# NON-CLAIMS: the Gram rule gap is registered (S8), not enclosed; the
# exp/sqrt/cos constants are op-count constants, not libm proofs; L4
# (2053) stands, evaluator-independent; COVER open; not a producer
# theorem; not RH.  2057-specific: the bridged bound's computed
# difference carries the accumulation allowance of the two sums plus the
# piece rule's construction deviation (the 64 U slot), all on the
# absolute-sum scale; the piece-rule truth is validated at small m (P7)
# and at the A12 points, not at m = 1600 (the ellipse term there is
# floored at 1e-300 and the difference is at the rounding scale, so the
# bridge cannot fail there for any reason a larger m could expose).
# 2058-specific: the direct difference's grid allowances are CONTROLS,
# not certified enclosures: the coarse and phi-shifted readings (D2)
# size the difference-quadrature error and the charge takes 4x their
# max, the same resolved-grid convention as the envelope integrals; the
# arithmetic allowance rides on the two null-channel jet envelopes
# (whose own truth is the P2/P6/B3 pattern), and the coefficient
# vectors are the stored matrices' exact solve and the committed floats
# (no other input moves inside the channel: W = K p^2 is nominal on
# both sides by the channel decomposition).
#
# CLI: --smoke | --workers N | --chunk N
#
import json
import math
import os
import sys
import time

import numpy as np
import mpmath as mp
from multiprocessing import get_context

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, "scripts"))

import fourpoint_owner_completion_1980 as r80  # noqa: E402
import fourpoint_owner_density_1959 as r59     # noqa: E402
import routea_g8h_basis_comparison_2037 as r37  # noqa: E402
import routea_health_cone_2006 as r06          # noqa: E402
import routea_l3_aggregate_2051 as r51         # noqa: E402
import routea_l1_nodal_enclosure_2052 as r52   # noqa: E402
import routea_reduced_evaluator_2054 as r54    # noqa: E402

mp.mp.dps = 50
mp.iv.dps = 30

U = 2.0 ** -53
INS = 1.05
INS_PHI = 4.0
INS_F = 2.0
INS_S = 4.0
XI_MAX = 40.0
K = r37.K
M_RED = 1600
N_A = 400
GAUSS_POINTS = r06.GAUSS_POINTS
SIG_MAX = 5.372183419225665
M13 = mp.mpf(1) / 24
C_T = 1e6
RHO_SAFE = 0.98
MIN_BOUND = 1e-300

# 2057 bridge
DELTA_SPLIT = 0.05

# 2058 solve-direct machinery
PHI_SHIFT = 0.6180339887498949        # golden-ratio conjugate
DXI_MAIN = 0.001
DXI_COARSE = 0.004
D1_NODES = (-39.9375, -6.68, 39.9375)
D1_FULL_MP = (-6.68, 39.9375)         # nodes checked with the exact v chain
TOL_R57 = 1e-9
TOL_D2 = 1e-3
D4_LO = 0.2
D4_HI = 5.0

# frozen 2057 comparison figures (committed artifact
# 28966087fc928cbc5202364c64e3aeed, quoted in the 2057 record)
CHARGE_L5_2057 = 1842946433.9779341
CHARGE_VALUE_2057 = 1842910359.9871004
INT_EG_2057 = 3976762.498008143
TOTAL_IDEAL_2057 = 45854607875.41298
SOLVE_DECOMP_2057 = 3793124.474011112

# frozen references
TOTAL_2055 = 44011661441.43504
BEST_MIN_2055 = 43391367261.73455
ARCH3_2055 = 607213702.8791345
TIERB_DBASE = 2.151e-09
TIERB_DCORR = 2.481e-09
Q400_FROZEN = -1.1111757839943646e+20
Q1600_FROZEN = -3406049871881.2666
BUDGET3 = abs(Q1600_FROZEN)
BAR10 = 0.1 * BUDGET3
C_BOOK_2051 = 458.0475860314685
C1_BOOK_2051 = 21898.85724574201
SUPPORT_2051 = 9.504
BOOK_2051 = 1647
NFAM_2051 = 17

TOL_P2 = 1e-12
TOL_P6 = 1.0        # dev <= (EG_r52 + jet err0), the certified statement
TOL_C3 = 1e-9
TOL_C4 = 1e-2
TOL_CERT = 1e-10
TOL_Q = 1e-6
TOL_A12 = 1.0

T0 = time.time()
_POOL = None
_CERT = {}


def log(msg):
    print("[%7.1fs] %s" % (time.time() - T0, msg), flush=True)


def phase_pool(workers):
    global _POOL
    if _POOL is not None:
        _POOL.terminate()
        _POOL.join()
        _POOL = None
    if workers > 1:
        _POOL = get_context("fork").Pool(workers)
    return _POOL


def pmap(fn, args):
    if _POOL is None:
        return [fn(a) for a in args]
    return _POOL.map(fn, args)


# ------------------------------------------------------- S1: leggauss cert
# Oracle: P_n(x) = hyp2f1(-n, n+1, 1, (1-x)/2), a terminating (n+1)-term
# series, evaluated by mpmath at the ambient dps 50; value error validated
# absolutely by A10 (dps doubling) and cross-read against scipy elsewhere.
E_VAL = mp.mpf("1e-28")
REL_W_FLOOR = mp.mpf("1e-24")     # slope relative-error allowance
REL_W_STORE = mp.mpf("1e-15")     # float storage of x and w


def mp_legendre(n, xm):
    return mp.hyp2f1(-n, n + 1, 1, (1 - xm) / 2)


def _cert_one(n, xf):
    """Mean-value root certificate for one numpy node xf of P_n.

    Returns (dxi, w_lo, w_hi, v, c, s_rel): |x* - xf| <= dxi for the true
    root x*, an interval around the true weight 2/((1-x^2) P_n'(x*)^2),
    and diagnostics.  Fixed point d = sup_box|P|/inf_box|P'| around xf.
    """
    xm = mp.mpf(float(xf))
    pn = mp_legendre(n, xm)
    pnm1 = mp_legendre(n - 1, xm)
    one_m = 1 - xm * xm
    sl = n * (pnm1 - xm * pn) / one_m              # P_n'(xf)
    pnn = (2 * xm * sl - n * (n + 1) * pn) / one_m  # P_n'' via the ODE
    v = abs(pn)
    c = abs(sl)
    if c == 0 or not mp.isfinite(c):
        return float("inf"), float("-inf"), float("inf"), float(v), 0.0, \
            float("inf")
    d = (v + E_VAL) / c
    for _ in range(4):
        den = c - abs(pnn) * d
        if den <= 0:
            return float("inf"), float("-inf"), float("inf"), float(v), \
                float(c), float("inf")
        num = v + E_VAL + (c + abs(pnn) * d) * d + abs(pnn) * d * d / 2
        d = num / den
    w = 2 / (one_m * sl * sl)
    s_rel = n * (1 + abs(xm)) * E_VAL / (abs(one_m) * c)
    relw = 2 * (abs(xm) / abs(one_m) + abs(pnn) / c) * d \
        + 2 * (s_rel + REL_W_FLOOR) + REL_W_STORE
    return float(d), float(w * (1 - relw)), float(w * (1 + relw)), \
        float(v), float(c), float(s_rel)


def _cert_task(args):
    n, lo, hi = args
    xs = _CERT["nodes"]
    out = [_cert_one(n, xs[i]) for i in range(lo, hi)]
    return lo, [o[0] for o in out], [o[1] for o in out], [o[2] for o in out], \
        [o[3] for o in out], [o[4] for o in out], [o[5] for o in out]


def certify_leggauss(n, workers=1):
    xs, ws = np.polynomial.legendre.leggauss(n)
    global _CERT
    _CERT = {"nodes": xs}
    phase_pool(workers)
    spans = [(n, lo, min(lo + 20, n)) for lo in range(0, n, 20)]
    res = pmap(_cert_task, spans)
    dxi = np.full(n, np.inf)
    v = np.zeros(n)
    c = np.zeros(n)
    wlo = np.full(n, np.inf)
    whi = np.full(n, -np.inf)
    srel = np.zeros(n)
    for lo, od, ol, oh, ov, oc, osr in res:
        for i in range(len(od)):
            dxi[lo + i] = od[i]
            wlo[lo + i] = ol[i]
            whi[lo + i] = oh[i]
            v[lo + i] = ov[i]
            c[lo + i] = oc[i]
            srel[lo + i] = osr[i]
    good = np.isfinite(dxi) & (c > 0)
    dW = 0.5 * (whi - wlo)
    stats = {"n": n, "nodes": int(n), "zero_slope": int(np.sum(~good)),
             "v_max": float(np.max(v, initial=0.0)),
             "v_med": float(np.median(v)),
             "slope_min": float(np.min(c)) if np.all(c > 0) else 0.0,
             "dxi_max": float(np.max(dxi)) if np.all(np.isfinite(dxi))
             else float("inf"),
             "dxi_med": float(np.median(dxi[np.isfinite(dxi)])) if np.any(
                 np.isfinite(dxi)) else float("inf"),
             "s_rel_max": float(np.max(srel)),
             "dWrel_max": float(np.max(dW / np.maximum(np.abs(ws),
                                                       1e-300)))}
    return xs, ws, dxi, wlo, whi, stats


def validate_oracle(n, n_sample=21):
    """A10: dps-doubling validation of the oracle at sampled nodes of the
    leggauss(n) table.  Returns the max dps-doubling deviation of P_n and
    P_{n-1} over the sample (gate: <= 1e-28)."""
    xs, _ = np.polynomial.legendre.leggauss(n)
    idx = np.unique(np.linspace(0, n - 1, n_sample).astype(int))
    pts = [mp.mpf(float(xs[i])) for i in idx]
    ref = [(mp_legendre(n, xm), mp_legendre(n - 1, xm)) for xm in pts]
    save = mp.mp.dps
    mp.mp.dps = 120
    hi = [(mp_legendre(n, xm), mp_legendre(n - 1, xm)) for xm in pts]
    mp.mp.dps = save
    dev = max(max(abs(a[0] - b[0]), abs(a[1] - b[1]))
              for a, b in zip(ref, hi))
    return float(dev), [float(xs[i]) for i in idx]


# ------------------------------------------------- S2: rule residual bound
def _chm(rho):
    return 0.5 * (rho + 1.0 / rho), 0.5 * (rho - 1.0 / rho)


def ellipse_clear(uc, hu, rho, npts=2000):
    chm, shm = _chm(rho)
    th = np.linspace(0, 2 * np.pi, npts, endpoint=False)
    ur = uc + hu * chm * np.cos(th)
    ui = hu * shm * np.sin(th)
    d = np.minimum(np.hypot(ur - 1, ui), np.hypot(ur + 1, ui))
    lip = hu * (chm + shm) * (np.pi / npts)
    return float(d.min() - lip)


def umax2(uc, hu, rho):
    chm, shm = _chm(rho)
    base = uc * uc + (hu * shm) ** 2
    lin = max(2 * uc * hu * chm, -2 * uc * hu * chm) + hu * hu
    return base + lin


def rho_of_panel(uc, hu):
    chm_lim = (1.0 - abs(uc)) / hu
    if chm_lim <= 1.0:
        return 1.0
    return chm_lim + math.sqrt(chm_lim * chm_lim - 1.0)


def h_out(a, u_lo, u_hi, sr):
    """Rigorous max of h(u) = -K/(1-u^2) + sr a u on the outer panel.

    The elementary panel bound needs max_x |phi(x) e^{s'x}| over the
    panel, i.e. exp(max of h) -- NOT phi_max(panel) times
    max(e^{s'x}) at a DIFFERENT point, which is what the first draft used
    (it overstates by e^{sr a (x_max - x_argmax)}: 1.7x for a = 1.76,
    45x for a = 4.75).  h''(u) = -2K(1+3u^2)/(1-u^2)^3 < 0 on (-1, 1):
    h is strictly concave there, so the maximizer is the clip of the
    unique root of h'(u) = -2K u/(1-u^2)^2 + sr a to the panel, found by
    80 bisections of a strictly decreasing h'.
    """
    def hval(u):
        return -K / max(1.0 - u * u, 1e-150) + sr * a * u

    def hp(u):
        d = max(1.0 - u * u, 1e-150)
        return -K * 2.0 * u / (d * d) + sr * a

    lo, hi = (u_lo, u_hi) if u_lo <= u_hi else (u_hi, u_lo)
    if hp(lo) <= 0.0:
        return hval(lo)
    if hp(hi) >= 0.0:
        return hval(hi)
    for _ in range(80):
        m = 0.5 * (lo + hi)
        if hp(m) > 0.0:
            lo = m
        else:
            hi = m
    return max(hval(lo), hval(hi))


def rule_residual_lnE(a, sarr, m, want_clear=False):
    """ln of the per-panel bound for |GL_m(panel) f - int_panel f| with
    f = phi(x) exp(s' x).  Returns (per-s results in L-units, clear)."""
    hu = 1.0 / 6.0
    centers = [-5.0 / 6.0, -0.5, -1.0 / 6.0, 1.0 / 6.0, 0.5, 5.0 / 6.0]
    out = []
    clear = 999.0
    for s in np.atleast_1d(sarr):
        sr, si = float(np.real(s)), float(np.imag(s))
        tot = 0.0
        pans = []
        for p, uc in enumerate(centers):
            outer = abs(uc) + hu >= 1.0 - 1e-12
            if outer:
                lnE = (math.log(2.0 * (2.0 * a * hu))
                       + h_out(a, uc - hu, uc + hu, sr))
            else:
                rho = max(2.0, RHO_SAFE * rho_of_panel(uc, hu))
                if want_clear:
                    clear = min(clear, ellipse_clear(uc, hu, rho))
                chm, shm = _chm(rho)
                um2 = umax2(uc, hu, rho)
                cphi = ((1.0 - um2) / (1.0 + um2) ** 2) if um2 < 1.0 else 0.0
                uRe = (uc + hu * chm) if sr >= 0 else (uc - hu * chm)
                Mln = -K * cphi + sr * a * uRe + abs(si) * hu * shm * a
                lnE = (math.log(C_T) + Mln - 2.0 * m * math.log(rho)
                       - math.log(1.0 - rho ** -2))
            val = math.exp(lnE) if lnE > -700 else MIN_BOUND
            tot += val
            pans.append({"panel": p, "lnE": lnE, "bound": val})
        out.append({"lnE_total": math.log(tot) if tot > 0 else -700.0,
                    "bound": tot, "panels": pans})
    if want_clear:
        return out, clear
    return out


def rule_bound_vec(a, si_abs, m):
    """Vectorized twin of rule_residual_lnE's panel sum as a function of
    |Im s'| alone (sr = a/2 > 0 fixed).  Same constants, same 1e-300
    floor on each panel term.  Gated against rule_residual_lnE by A11."""
    hu = 1.0 / 6.0
    sr = 0.5 * a
    si_abs = np.asarray(si_abs, dtype=float)
    tot = np.zeros_like(si_abs)
    for uc in (-5.0 / 6.0, -0.5, -1.0 / 6.0, 1.0 / 6.0, 0.5, 5.0 / 6.0):
        if abs(uc) + hu >= 1.0 - 1e-12:
            lnE = np.full_like(
                si_abs,
                math.log(2.0 * (2.0 * a * hu)) + h_out(a, uc - hu, uc + hu, sr))
        else:
            rho = max(2.0, RHO_SAFE * rho_of_panel(uc, hu))
            chm, shm = _chm(rho)
            um2 = umax2(uc, hu, rho)
            cphi = ((1.0 - um2) / (1.0 + um2) ** 2) if um2 < 1.0 else 0.0
            uRe = uc + hu * chm
            lnE = (math.log(C_T) - K * cphi + sr * a * uRe
                   - 2.0 * m * math.log(rho)
                   - math.log(1.0 - rho ** -2)) + si_abs * hu * shm * a
        tot = tot + np.where(lnE > -700.0, np.exp(np.minimum(lnE, 700.0)),
                             MIN_BOUND)
    return tot


# --------------------------------------------- 2057: the split-rule bridge


def piece_lnE(a, uc, hu, m, si_abs):
    """Vectorized Trefethen ellipse bound (L-units) for the piece panel
    [uc-hu, uc+hu] carrying the m-point composite GL rule, as a function
    of |Im s'| alone (sr = a/2 > 0, the pipeline's Re s).  Same formula,
    constants and 1e-300 floor as rule_residual_lnE's inner branch.  The
    piece geometry is the bridge's P1; validity there is checked by gate
    P7 (small m, mp.quad truth) and by the clearance gates below."""
    sr = 0.5 * a
    si_abs = np.asarray(si_abs, dtype=float)
    rho = max(2.0, RHO_SAFE * rho_of_panel(uc, hu))
    chm, shm = _chm(rho)
    um2 = umax2(uc, hu, rho)
    cphi = ((1.0 - um2) / (1.0 + um2) ** 2) if um2 < 1.0 else 0.0
    uRe = (uc + hu * chm) if sr >= 0 else (uc - hu * chm)
    lnE = (math.log(C_T) - K * cphi + sr * a * uRe
           - 2.0 * m * math.log(rho) - math.log(1.0 - rho ** -2))
    lnE = lnE + si_abs * hu * shm * a
    val = np.where(lnE > -700.0, np.exp(np.minimum(lnE, 700.0)), MIN_BOUND)
    return val, rho


def split_panel_data(a, th, Xf, F, amp, delta, m, dxi=None, wlo=None,
                     whi=None):
    """Per-family bridge data (all floats, built once).

    The outer panels of the m-point six-panel rule are P_R = [2a/3, a] and
    P_L = [-a, -2a/3] (node slices 5m:6m and 0:m).  Each is cut at
    |u| = 1 - delta; P1 = the sub-panel toward the interior (uc, hu), P2 =
    the edge slice carried by the elementary |I| <= delta a exp(h_out)
    bound.  The piece rule S1 mirrors the committed construction exactly
    (r51.Model: F = a phi(X) W) at the SAME m.

    The piece's own construction deviation (float leggauss roots/weights
    and the phi chain, against the IDEAL piece rule the ellipse bound
    applies to) is booked as dp_k -- the same op-count formulas as
    fx_channels, on the certified (dxi, wlo, whi) tables of the SAME
    numpy root array (P4 certifies it; the piece map xs -> a(uc + hu xs)
    and ws -> a hu ws adds 3 U slots per term)."""
    uc = 0.5 * (2.0 / 3.0 + 1.0 - delta)
    hu = 0.5 * (1.0 - delta - 2.0 / 3.0)
    xs, ws = np.polynomial.legendre.leggauss(m)
    if dxi is None or len(dxi) != m or wlo is None or len(wlo) != m:
        dxi_u = np.full(m, 1e-15)
        wrel_u = np.full(m, 1e-8)
        bd_proxy = True
    else:
        dxi_u = np.asarray(dxi, dtype=float)
        wrel_u = (np.maximum(np.abs(np.asarray(wlo, dtype=float) - ws),
                             np.abs(np.asarray(whi, dtype=float) - ws))
                  / np.maximum(np.abs(ws), 1e-300))
        bd_proxy = False
    bd = {"slR": slice(5 * m, 6 * m), "slL": slice(0, m),
          "uc": uc, "hu": hu, "delta": delta, "m": m, "dxi_proxy": bd_proxy,
          "Xf": np.asarray(Xf, dtype=float), "F": np.asarray(F, dtype=float)}
    abs_p = []
    dp = np.zeros(5)
    epsFp_max = 0.0
    for side, sgn in (("R", 1.0), ("L", -1.0)):
        Xp = a * (sgn * uc + hu * xs)
        Wp = a * hu * ws
        Fp = a * (r59.phi_fun(Xp, a, K) * Wp)
        Wcv = (-2j * math.pi * a) * Xp
        Fpm = np.empty((m, 5), dtype=complex)
        for k in range(5):
            Fpm[:, k] = Fp * (Wcv ** k)
        bd["Xp_" + side] = Xp
        bd["Fpm5_" + side] = Fpm
        be = np.abs(Fp) * np.exp(0.5 * a * Xp)
        w1 = 2 * math.pi * a * Xp
        abs_p.append([float(np.sum(be * np.abs(w1) ** k)) for k in range(5)])
        up = np.abs(Xp) / a
        dp_ = np.maximum(1.0 - up * up, 1e-12)
        dXp = a * hu * dxi_u + 3.0 * U * (a + np.abs(Xp))
        ephi = (abs(K) / dp_) * U * (3.0 * up * up / dp_ + 2.0) + 8.0 * U
        ephiX = 2.0 * abs(K) * np.abs(Xp) / (a * a * dp_ * dp_) * dXp
        epsFp = (ephi + ephiX + wrel_u + 3.0 * U + 3.0 * U) * INS_F
        epsFp_max = max(epsFp_max, float(np.max(epsFp)))
        dFabs = np.abs(Fp) * epsFp * np.exp(0.5 * a * Xp)
        for k in range(5):
            dp[k] += float(np.sum(dFabs * np.abs(w1) ** k))
    bd["epsF_piece_max"] = epsFp_max
    bd["dp"] = [float(x) for x in dp]
    Fm = np.empty((len(bd["Xf"]), 5), dtype=complex)
    Wcf = (-2j * math.pi * a) * bd["Xf"]
    for k in range(5):
        Fm[:, k] = bd["F"] * (Wcf ** k)
    bd["Fm5"] = Fm
    bc = np.abs(bd["F"]) * np.exp(0.5 * a * bd["Xf"])
    w1c = 2 * math.pi * a * bd["Xf"]
    abs_c = [float(np.sum(bc * np.abs(w1c) ** k)) for k in range(5)]
    sr = 0.5 * a
    half = 1.0 / 6.0
    bd["elem_r"] = min(
        math.exp(min(math.log(2.0 * (2.0 * a * half))
                     + h_out(a, 2.0 / 3.0, 1.0, sr), 700.0)), 1e300)
    bd["elem_l"] = min(
        math.exp(min(math.log(2.0 * (2.0 * a * half))
                     + h_out(a, -1.0, -2.0 / 3.0, sr), 700.0)), 1e300)
    bd["B2sum"] = (delta * a * math.exp(min(h_out(a, 1.0 - delta, 1.0, sr),
                                            700.0))
                   + delta * a * math.exp(min(h_out(a, -1.0, -1.0 + delta,
                                                    sr), 700.0)))
    # allowance per slot: both sums' accumulation (4m terms) plus the piece
    # rule's own construction deviation (N_TOL_EXTRA slots) on the
    # absolute-sum scale Ac_k + Ap_k (the P6 lesson: the term scale, not
    # the value).
    bd["allow"] = [INS * ((r51.EPS_TERM + (2.0 * k + 4.0 * m) * U + amp)
                          * (abs_c[k] + abs_p[0][k] + abs_p[1][k])
                          + dp[k]) for k in range(5)]
    bd["abs_c"] = abs_c
    bd["abs_p"] = [abs_p[0], abs_p[1]]
    rho_r = max(2.0, RHO_SAFE * rho_of_panel(uc, hu))
    rho_l = max(2.0, RHO_SAFE * rho_of_panel(-uc, hu))
    bd["rho"] = (rho_r, rho_l)
    bd["clear"] = (ellipse_clear(uc, hu, rho_r),
                   ellipse_clear(-uc, hu, rho_l))
    return bd


def bridge_slots(a, th, xic, E, bd, m):
    """Per-slot (k = 0..4) (P)-channel bounds (L-units, the P2 channel
    bound |GL - I| per family) at the nodes xic, given the chunk's
    E = exp(z Xf) matrix (n x len(Xf)).  Returns (bounds, |D|, allow,
    piece-ellipse, inner): the same formula JetL5B.family_jets runs."""
    xic = np.asarray(xic, dtype=float)
    z = a * ((0.5 - 2j * np.pi * xic) + 1j * th)
    Fm5 = bd["Fm5"]
    acc_o = (E[:, bd["slR"]] @ Fm5[bd["slR"]]
             + E[:, bd["slL"]] @ Fm5[bd["slL"]])
    Ep_r = np.exp(z[:, None] * bd["Xp_R"][None, :])
    Ep_l = np.exp(z[:, None] * bd["Xp_L"][None, :])
    accp = Ep_r @ bd["Fpm5_R"] + Ep_l @ bd["Fpm5_L"]
    si_abs = a * np.abs(th - 2.0 * np.pi * xic)
    ell_r, _ = piece_lnE(a, bd["uc"], bd["hu"], m, si_abs)
    ell_l, _ = piece_lnE(a, -bd["uc"], bd["hu"], m, si_abs)
    inner = np.maximum(rule_bound_vec(a, si_abs, m)
                       - bd["elem_r"] - bd["elem_l"], 0.0)
    out = []
    dks = []
    for k in range(5):
        sqk = (2.0 * math.pi * a * a) ** k
        dk = np.abs(acc_o[:, k] - accp[:, k])
        bridge = dk + bd["allow"][k] + sqk * (ell_r + ell_l + bd["B2sum"])
        elem = sqk * (bd["elem_r"] + bd["elem_l"] + inner)
        out.append(np.minimum(elem, bridge))
        dks.append(dk)
    return out, dks, (ell_r, ell_l, inner)


# ------------------------------------------------------ S3: F/X channels
def fx_channels(fam, cert):
    """Per-family FC_k, XC_k (k = 0..4) in exact v-derivative units."""
    Xs, Ws, dxi, wlo, whi = (cert["X"], cert["W"], cert["dxi"],
                             cert["wlo"], cert["whi"])
    out = []
    for (a, th) in fam:
        Xf = np.asarray(Xs, dtype=float)
        W = Ws
        F = a * (r59.phi_fun(Xf, a, K) * W)
        base_e = np.abs(F) * np.exp(0.5 * a * Xf)
        u = np.abs(Xf) / a
        d = np.maximum(1.0 - u * u, 1e-12)
        dX = a * dxi + 3.0 * U * (a + np.abs(Xf))
        ephi = (abs(K) / d) * U * (3.0 * u * u / d + 2.0) + 8.0 * U
        ephiX = 2.0 * abs(K) * np.abs(Xf) / (a * a * d * d) * dX
        dWrel = np.maximum(np.abs(wlo - Ws), np.abs(whi - Ws)) \
            / np.maximum(np.abs(Ws), 1e-300) + 3.0 * U
        epsF = (ephi + ephiX + dWrel + 3.0 * U) * INS_F
        dFabs = np.abs(F) * epsF
        ww = 2 * math.pi * np.abs(Xf)
        zmax = a * (0.5 + 2 * math.pi * XI_MAX + abs(th))
        FC = np.array([a * float(np.sum(dFabs * base_e * ww ** k))
                       for k in range(5)])
        XC = np.empty(5)
        for k in range(5):
            term = np.abs(F) * np.exp(0.5 * a * Xf) * dX \
                * (ww ** k * zmax
                   + (k * 2 * math.pi * ww ** (k - 1) if k > 0 else 0.0))
            XC[k] = a * float(np.sum(term))
        out.append({"a": a, "theta": th, "FC": FC, "XC": XC,
                    "epsF_max": float(np.max(epsF)),
                    "dX_max": float(np.max(dX)),
                    "dWrel_max": float(np.max(dWrel))})
    return out


def a_side_data(fam, nodes, cert_a):
    """a-side (m = 400 at owner nodes) data bound: da_abs is an absolute
    bound on every |delta a_mat[i, j]|."""
    Xs4, Ws4, dxi4, wlo4, whi4 = (cert_a["X"], cert_a["W"], cert_a["dxi"],
                                  cert_a["wlo"], cert_a["whi"])
    da = 0.0
    eps_max = 0.0
    rule_max = 0.0
    zmaxs = []
    for (a, th) in fam:
        Xf = np.asarray(Xs4, dtype=float)
        W = Ws4
        F = a * (r59.phi_fun(Xf, a, K) * W)
        u = np.abs(Xf) / a
        d = np.maximum(1.0 - u * u, 1e-12)
        dX = a * dxi4 + 3.0 * U * (a + np.abs(Xf))
        ephi = (abs(K) / d) * U * (3.0 * u * u / d + 2.0) + 8.0 * U
        ephiX = 2.0 * abs(K) * np.abs(Xf) / (a * a * d * d) * dX
        dWrel = np.maximum(np.abs(wlo4 - Ws4), np.abs(whi4 - Ws4)) \
            / np.maximum(np.abs(Ws4), 1e-300) + 3.0 * U
        epsF = (ephi + ephiX + dWrel + 3.0 * U) * INS_F
        eps_max = max(eps_max, float(np.max(epsF)))
        dFabs = np.abs(F) * epsF
        for z in nodes:
            zc = complex(z)
            ew = np.exp(zc.real * Xf)
            d_ij = float(np.sum((dFabs + np.abs(F) * dX * abs(zc)) * ew))
            da = max(da, d_ij)
        zmaxs.append(a * (max(abs(complex(z).real) for z in nodes)
                          + max(abs(complex(z).imag) for z in nodes)
                          + abs(th)))
        sarr = [a * (complex(z) + 1j * th) for z in nodes]
        res = rule_residual_lnE(a, sarr, N_A)
        rule_max = max(rule_max, a * max(r["bound"] for r in res))
    da = max(da, rule_max)
    return {"da_abs": da, "epsF_a_max": eps_max, "rule_a_max": rule_max,
            "zmax_a": max(zmaxs)}


# --------------------------------------------------------- S4: KKT certify
def _ivmag_real(r):
    """Magnitude bound of an ivmpf via midpoint + radius (no comparisons:
    mpmath's iv comparison operators raise on overlapping intervals)."""
    return abs((r.a + r.b) / 2) + abs((r.b - r.a) / 2)


def _ivmag(x):
    """Magnitude bound of an iv number (ivmpc: |re| + |im|).  The bound is
    the interval |mid| + rad; `.b` extracts its upper endpoint singleton."""
    if isinstance(x, mp.iv.mpc):
        m = _ivmag_real(x.real) + _ivmag_real(x.imag)
    else:
        m = _ivmag_real(x)
    return float(m.b)


def kkt_certify(gram, a_mat, y, c_stored):
    n = gram.shape[0]
    mrow = a_mat.shape[0]
    K = mp.zeros(n + mrow, n + mrow)
    for i in range(n):
        for j2 in range(n):
            K[i, j2] = mp.mpc(complex(gram[i, j2]))
            K[i, n + j2] = mp.conj(mp.mpc(complex(a_mat[j2, i])))
    for i in range(mrow):
        for j2 in range(n):
            K[n + i, j2] = mp.mpc(complex(a_mat[i, j2]))
    X = K ** -1
    Kiv = mp.iv.matrix(K.rows, K.cols)
    for i in range(K.rows):
        for j2 in range(K.cols):
            Kiv[i, j2] = mp.iv.mpc(mp.mpf(str(mp.re(K[i, j2]))),
                                   mp.mpf(str(mp.im(K[i, j2]))))
    Xiv = mp.iv.matrix(X.rows, X.cols)
    for i in range(X.rows):
        for j2 in range(X.cols):
            Xiv[i, j2] = mp.iv.mpc(mp.mpf(str(mp.re(X[i, j2]))),
                                   mp.mpf(str(mp.im(X[i, j2]))))
    Eiv = Xiv * Kiv
    for i in range(K.rows):
        Eiv[i, i] = Eiv[i, i] - mp.iv.mpc(1, 0)
    theta = 0.0
    for i in range(K.rows):
        s = 0.0
        for j2 in range(K.cols):
            s += _ivmag(Eiv[i, j2])
        theta = max(theta, s)
    Xnorm = 0.0
    for i in range(X.rows):
        s = 0.0
        for j2 in range(X.cols):
            s += _ivmag(Xiv[i, j2])
        Xnorm = max(Xnorm, float(s))
    invnorm = Xnorm / (1.0 - theta) if theta < 1.0 else None
    b = mp.zeros(n + mrow, 1)
    for i in range(mrow):
        yv = complex(y[i])
        b[n + i] = mp.mpc(mp.mpf(repr(yv.real)), mp.mpf(repr(yv.imag)))
    sol = K ** -1 * b
    c_mp = np.array([complex(sol[i]) for i in range(n)])
    lam = np.array([complex(sol[n + i]) for i in range(mrow)])
    rn = 0.0
    for i in range(n + mrow):
        s = mp.iv.mpc(0, 0)
        for j2 in range(n):
            s += Kiv[i, j2] * mp.iv.mpc(
                mp.mpf(str(float(np.real(c_stored[j2])))),
                mp.mpf(str(float(np.imag(c_stored[j2])))))
        for j2 in range(mrow):
            s += Kiv[i, n + j2] * mp.iv.mpc(mp.mpf(str(mp.re(lam[j2]))),
                                            mp.mpf(str(mp.im(lam[j2]))))
        if i >= n:
            yv = float(np.real(y[i - n]))
            s = s - mp.iv.mpc(mp.mpf(str(yv)), mp.mpf(0))
        rn = max(rn, _ivmag(s))
    dc = invnorm * rn if invnorm is not None else None
    return {"theta": theta, "Xnorm": Xnorm, "invnorm": invnorm,
            "rnorm": rn, "dc_bound": dc, "c_mp": c_mp, "lambda_mp": lam}


# ------------------------------------------------------- S5: sigma / book
def sigma_eps(u):
    w = mp.mpc(mp.mpf("8.25"), -mp.mpf(u) / 2)
    xr = abs(w.real)
    yi = abs(w.imag)
    dmin = xr * xr + yi * yi if yi <= xr else 2 * xr * yi
    T0 = 2 * M13 / (abs(w) ** 12 * dmin)
    return float(INS_S * (T0 + 20 * mp.mpf(2) ** -53))


def mp_sigma(u):
    z = mp.mpf("0.25") - mp.mpf(u) / 2 * 1j
    return mp.log(mp.pi) - mp.re(mp.digamma(z))


def book_delta(xg, ps):
    out = np.zeros_like(xg)
    for num, lam in ps:
        c = 2 * lam / math.sqrt(num)
        out += c * (3.0 * U * np.abs(2 * math.pi * xg * math.log(num))
                    + 6.0 * U)
    return out


def mp_book(xg, ps):
    out = []
    for x in xg:
        s = mp.mpf(0)
        for num, lam in ps:
            nm = mp.mpf(int(num))
            s += 2 * mp.mpf(lam) / mp.sqrt(nm) \
                * mp.cos(2 * mp.pi * mp.mpf(x) * mp.log(nm))
        out.append(s)
    return out


def committed_book(xg, ps):
    out = np.zeros_like(xg)
    for num, lam in ps:
        out += 2 * lam / math.sqrt(num) * np.cos(2 * np.pi * xg
                                                 * math.log(num))
    return out


# ------------------------------------------------- S6: jet with L5 bundles
def _cj_add_abs(cj, vj, ad):
    """Add the bundle |ad| * (|vj| and its derivative slots) to a complex
    jet (jr, ji); vj = (vr, vi) is the same family's complex jet."""
    if ad == 0.0:
        return cj
    jr, ji = cj
    vr, vi = vj
    orr, oii = [], []
    for k in range(4):
        e = ad * (r51.b_sup(vr[k]) + r51.b_sup(vi[k]))
        orr.append(r51.b_add(jr[k], (np.zeros_like(jr[k][0]), e)))
        oii.append(r51.b_add(ji[k], (np.zeros_like(ji[k][0]), e)))
    orr.append(jr[4] + ad * (vr[4] + vi[4]))
    oii.append(ji[4] + ad * (vr[4] + vi[4]))
    return (orr, oii)


def solve_grid(fam, K_, xw, cnt, ps, c0b, c0c, c1b, c1c, dxi,
               shift=0.0, xlo=-XI_MAX, xhi=XI_MAX):
    """dQ = int K p^2 (g(c1) - g(c0)) on a uniform (optionally shifted)
    grid of spacing dxi over [xlo, xhi].

    g(c) = |c_b @ v|^2 |c_c @ v|^2, v the committed family-value chain.
    The shift (in units of dxi, 0 < shift < 1) makes the grid
    incommensurate with the nested family; the window endpoint xhi is
    appended as a final node (the last cell is then narrower).  Returns
    (dQ, diag); diag["trapz_abs"] is the |.|-integral of the same
    difference integrand, the scale of the post-chain arithmetic
    allowance."""
    n = int(round((xhi - xlo) / dxi)) + 1
    xg = xlo + dxi * (shift + np.arange(n))
    if shift != 0.0:
        xg = np.append(xg, xhi)
    v = r80.family_values(fam, K_, 0.5 - 2j * np.pi * xg, xw)
    p = np.real(r59.P_from_nodes(xg, cnt))
    ker = r54.kernel_at(xg, ps)
    W = ker * p * p
    lb0 = c0b @ v
    cc0 = c0c @ v
    lb1 = c1b @ v
    cc1 = c1c @ v
    g0 = np.abs(lb0) ** 2 * np.abs(cc0) ** 2
    g1 = np.abs(lb1) ** 2 * np.abs(cc1) ** 2
    dg = W * (g1 - g0)
    dQ = float(np.trapezoid(dg, xg))
    return dQ, {"trapz_abs": float(np.trapezoid(np.abs(dg), xg)),
                "n": len(xg)}


def pointwise_diff(fam, K_, xw, cnt, ps, c0b, c0c, c1b, c1c, xi):
    """Float D = W (g1 - g0) at one node; returns (D, W, v, p, ker)."""
    xg = np.array([xi])
    v = r80.family_values(fam, K_, 0.5 - 2j * np.pi * xg, xw)[:, 0]
    p = float(np.real(r59.P_from_nodes(xg, cnt))[0])
    ker = float(r54.kernel_at(xg, ps)[0])
    W = ker * p * p
    lb0 = complex(c0b @ v)
    cc0 = complex(c0c @ v)
    lb1 = complex(c1b @ v)
    cc1 = complex(c1c @ v)
    D = W * (abs(lb1) ** 2 * abs(cc1) ** 2 - abs(lb0) ** 2 * abs(cc0) ** 2)
    return D, W, v, p, ker


def e_supk(jet, k, rho, eps4=None):
    """Taylor sup of the ERROR channel over |t| <= rho.

    Slots 0..3 are the calculus's error bundles (the errors of the g^(k)
    slots).  The 4th-derivative tail uses K4 -- the value-channel
    4th-derivative sup -- scaled by eps4 (the multiplicative-perturbation
    envelope sigma_loc = min(2, 2 e0/(|g| + e0)); the default 2 is the
    crude |E^(4)| <= 2 sup|g^(4)| fallback).  NOT a value-channel sup:
    j_supk would overstate the error integrand by ~1e15 here.
    """
    s = jet[k][1]
    for m in range(1, 4 - k):
        s = s + (rho ** m / math.factorial(m)) * jet[k + m][1]
    c = 2.0 if eps4 is None else eps4
    return s + (rho ** (4 - k) / math.factorial(4 - k)) * c * jet[4]


class JetL5(r51.Model):
    """r51.Model with the L5 input channels in the error bundles."""

    def __init__(self, fam, K_, xw, base, corr, cnt, l5=None):
        r51.Model.__init__(self, fam, K_, xw, base, corr, cnt)
        self.l5 = l5
        if l5 is None:
            self.l5c = None
        else:
            self.l5c = [(l5["FC"][j] + l5["XC"][j]) * INS
                        for j in range(self.nfam)]
            self.adb = np.abs(l5["dbase"])
            self.adc = np.abs(l5["dcorr"])
            self.el_node = bool(l5.get("el_node", False))

    def family_jets(self, j, nodes, chunk):
        a, th, Xf, F, M, amp = self.consts[j]
        m = len(Xf)
        n = len(nodes)
        val = [np.empty(n, dtype=float) for _ in range(4)]
        err = [np.empty(n, dtype=float) for _ in range(4)]
        ival = [np.empty(n, dtype=float) for _ in range(4)]
        ierr = [np.empty(n, dtype=float) for _ in range(4)]
        econst = [(r51.EPS_TERM + k * 2.0 * U + m * U + amp) * M[k] * INS
                  for k in range(4)]
        Wc = (-2j * math.pi * a) * Xf
        Fm = np.empty((m, 4), dtype=complex)
        for k in range(4):
            Fm[:, k] = F * (Wc ** k)
        K4 = (r51.EPS_TERM + 8.0 * U + m * U + amp) * M[4] * INS
        sq = 2.0 * math.pi * a * a          # the (2 pi a^2) slot transport
        if self.l5 is not None:
            K4 = K4 + self.l5c[j][4]
        k4 = np.full(n, K4)
        for lo in range(0, n, chunk):
            hi = min(lo + chunk, n)
            xic = np.asarray(nodes[lo:hi], dtype=float)
            s = 0.5 - 2j * np.pi * xic
            z = a * (s + 1j * th)
            E = np.exp(z[:, None] * Xf[None, :])
            acc = E @ Fm
            if self.l5 is None:
                eln = None
            elif self.el_node:
                eln = INS * a * rule_bound_vec(
                    a, a * np.abs(th - 2.0 * math.pi * xic), M_RED)
            else:
                eln = np.full(hi - lo, float(self.l5["el"][j]) * INS)
            for k in range(4):
                val[k][lo:hi] = acc[:, k].real
                ival[k][lo:hi] = acc[:, k].imag
                ek = econst[k]
                if self.l5 is not None:
                    ek = ek + self.l5c[j][k] + (sq ** k) * eln
                err[k][lo:hi] = ek
                ierr[k][lo:hi] = ek
            if self.l5 is not None and self.el_node:
                k4[lo:hi] = k4[lo:hi] + (sq ** 4) * eln
        jr = [(val[k], err[k]) for k in range(4)] + [k4]
        ji = [(ival[k], ierr[k]) for k in range(4)] + [k4]
        return (jr, ji)

    def g_jet(self, nodes, rho, chunk):
        n = len(nodes)
        lb = cc = None
        for j in range(self.nfam):
            vj = self.family_jets(j, nodes, chunk)
            cv = r51.cj_scale(self.base[j], vj)
            dw = r51.cj_scale(self.corr[j], vj)
            if self.l5 is not None:
                cv = _cj_add_abs(cv, vj, float(self.adb[j]))
                dw = _cj_add_abs(dw, vj, float(self.adc[j]))
            lb = cv if lb is None else r51.cj_add(lb, cv)
            cc = dw if cc is None else r51.cj_add(cc, dw)
        two_pi = 2.0 * np.pi
        xin = np.asarray(nodes, dtype=float)
        P = None
        for c0 in self.cnt:
            fr = r51.j_const(np.full(n, c0.real))
            fi = [r51.b_const(c0.imag + two_pi * xin),
                  r51.b_const(np.full(n, two_pi)), r51.b_zero(n),
                  r51.b_zero(n), np.zeros(n)]
            f = (fr, fi)
            P = f if P is None else r51.cj_mul(P, f, rho)
        assert P is not None
        p = P[0]
        p2 = r51.j_mul(p, p, rho)
        A = r51.cj_abs2_j(lb, rho)
        B = r51.cj_abs2_j(cc, rho)
        return r51.j_mul(p2, r51.j_mul(A, B, rho), rho)


class JetL5B(JetL5):
    """JetL5 with the 2057 split-rule bridge in the (P) channel.

    l5["bridge"] carries the per-family piece data (split_panel_data).
    With bridge=False (or no bridge data) this class reproduces JetL5 --
    and therefore record 2056's jet -- bitwise (gate B6).  The per-slot
    (P) bound is min(elementary, bridged) and enters the k-th error slot
    DIRECTLY (no (2 pi a^2)^k transport: the slot-k difference is computed
    at slot k); the K4 entry takes the k = 4 bound."""

    def __init__(self, fam, K_, xw, base, corr, cnt, l5=None, bridge=True):
        JetL5.__init__(self, fam, K_, xw, base, corr, cnt, l5)
        self.bridge = bool(bridge and l5 is not None
                           and l5.get("bridge") is not None)

    def family_jets(self, j, nodes, chunk):
        if not self.bridge:
            return JetL5.family_jets(self, j, nodes, chunk)
        a, th, Xf, F, M, amp = self.consts[j]
        m = len(Xf)
        n = len(nodes)
        bd = self.l5["bridge"][j]
        val = [np.empty(n, dtype=float) for _ in range(4)]
        err = [np.empty(n, dtype=float) for _ in range(4)]
        ival = [np.empty(n, dtype=float) for _ in range(4)]
        ierr = [np.empty(n, dtype=float) for _ in range(4)]
        econst = [(r51.EPS_TERM + k * 2.0 * U + m * U + amp) * M[k] * INS
                  for k in range(4)]
        Wc = (-2j * math.pi * a) * Xf
        Fm = np.empty((m, 4), dtype=complex)
        for k in range(4):
            Fm[:, k] = F * (Wc ** k)
        K4 = (r51.EPS_TERM + 8.0 * U + m * U + amp) * M[4] * INS
        K4 = K4 + self.l5c[j][4]
        k4 = np.full(n, K4)
        for lo in range(0, n, chunk):
            hi = min(lo + chunk, n)
            xic = np.asarray(nodes[lo:hi], dtype=float)
            s = 0.5 - 2j * np.pi * xic
            z = a * (s + 1j * th)
            E = np.exp(z[:, None] * Xf[None, :])
            acc = E @ Fm
            bl, _, _ = bridge_slots(a, th, xic, E, bd, m)
            for k in range(4):
                val[k][lo:hi] = acc[:, k].real
                ival[k][lo:hi] = acc[:, k].imag
                ek = econst[k] + self.l5c[j][k] + INS * a * bl[k]
                err[k][lo:hi] = ek
                ierr[k][lo:hi] = ek
            k4[lo:hi] = k4[lo:hi] + INS * a * bl[4]
        jr = [(val[k], err[k]) for k in range(4)] + [k4]
        ji = [(ival[k], ierr[k]) for k in range(4)] + [k4]
        return (jr, ji)


_JET = {}


def _jet_task(args):
    lo, hi = args
    nd = _JET["nodes"][lo:hi]
    j = _JET["jet"].g_jet(nd, _JET["rho"], _JET["chunk"])
    e0 = np.asarray(j[0][1])
    v0 = np.asarray(j[0][0])
    sl = np.minimum(2.0, 2.0 * e0 / np.maximum(np.abs(v0) + e0, 1e-300))
    return (lo, e0, v0, np.asarray(j[1][1]), np.asarray(j[1][0]),
            np.asarray(e_supk(j, 2, _JET["rho"], sl)),
            np.asarray(r51.j_supk(j, 2, _JET["rho"])),
            np.asarray(j[4]), sl * np.asarray(j[4]))


def jet_pass(jet, nodes, rho, chunk, workers, span=4096):
    global _JET
    _JET = {"jet": jet, "nodes": nodes, "rho": rho, "chunk": chunk}
    phase_pool(workers)
    spans = [(lo, min(lo + span, len(nodes)))
             for lo in range(0, len(nodes), span)]
    res = pmap(_jet_task, spans)
    out = [np.empty(len(nodes)) for _ in range(8)]
    for lo, e, v, e1, v1, es2, s2, k4, ek4 in res:
        k = len(e)
        for arr, src in zip(out, (e, v, e1, v1, es2, s2, k4, ek4)):
            arr[lo:lo + k] = src
    return (out[0], out[1], out[2], out[3], out[4], out[5], out[6], out[7])


# ------------------------------------------------------------- mp helpers
def mp_matrix_col(v):
    """Exact mp column matrix from a numpy vector (repr-lifted floats)."""
    out = mp.matrix(len(v), 1)
    for i in range(len(v)):
        z = complex(v[i])
        out[i] = mp.mpc(repr(z.real), repr(z.imag))
    return out


def mp_family_value(Xf, F, z):
    s = mp.mpc(0)
    zm = mp.mpc(z)
    for xm, fm in zip(Xf, F):
        s += mp.mpf(fm) * mp.exp(zm * mp.mpf(xm))
    return s


def mp_g_eval(fam_consts, base, corr, cnt, xi):
    s = mp.mpc(mp.mpf("0.5"), -2 * mp.pi * mp.mpf(xi))
    lb = mp.mpc(0)
    cc = mp.mpc(0)
    for j, (a, th, Xf, F, M, amp) in enumerate(fam_consts):
        zm = mp.mpf(a) * (s + 1j * mp.mpf(th))
        v = mp_family_value(Xf, F, zm)
        lb += mp.mpc(base[j]) * v
        cc += mp.mpc(corr[j]) * v
    pv = mp.mpc(1)
    for c0 in cnt:
        pv *= (mp.mpc(c0) - s)
    return (mp.re(pv) ** 2) * abs(lb) ** 2 * abs(cc) ** 2


def mp_g_nop(fam_consts, b, c, xi):
    """Exact-arithmetic |lb|^2 |cc|^2 (NO p^2, NO kernel) at xi, from the
    stored float inputs: v at s = 0.5 - 2 pi i xi (the family-value
    convention).  This is the D1 reference shape: the float counterpart
    is pointwise_diff's D/W, and W (= K p^2, p = Re prod (c0 + 2 pi i xi)
    -- the committed P_from_nodes convention, NO 0.5 in p) is lifted as
    an input on the mp side.  (mp_g_eval below is 2057's evaluator: it
    carries the family s also inside p -- fine for B2/B3, where p cancels
    between the two sides, but wrong as a pointwise reference for D1.)"""
    s = mp.mpc(mp.mpf("0.5"), -2 * mp.pi * mp.mpf(repr(float(xi))))
    lb = mp.mpc(0)
    cc = mp.mpc(0)
    for j, (a, th, Xf, F, M, amp) in enumerate(fam_consts):
        zm = mp.mpf(a) * (s + 1j * mp.mpf(th))
        v = mp_family_value(Xf, F, zm)
        lb += mp.mpc(repr(float(b[j].real)), repr(float(b[j].imag))) * v
        cc += mp.mpc(repr(float(c[j].real)), repr(float(c[j].imag))) * v
    return abs(lb) ** 2 * abs(cc) ** 2


def mp_construct_F(Xf, W, a):
    F = []
    for x, w in zip(Xf, W):
        xm = mp.mpf(x)
        um = abs(xm) / mp.mpf(a)
        F.append(mp.mpf(a) * mp.exp(-mp.mpf(K) / (1 - um * um))
                 * mp.mpf(w))
    return F


# ------------------------------------------------------------------- main
def main():
    smoke = "--smoke" in sys.argv
    workers = 12
    chunk = 4096
    for i, arg in enumerate(sys.argv):
        if arg == "--workers":
            workers = int(sys.argv[i + 1])
        if arg == "--chunk":
            chunk = int(sys.argv[i + 1])
    gates = {}
    sections = {}

    # ---------------- S0: setup -------------------------------------
    rho_o, nodes_o, values, fam, xw400, gram, a_mat, _, _ = r37.setup(False)
    xw1600 = [r59.phi_weights(a, panels=6, m=M_RED) for (a, _th) in fam]
    base, info_b = r37.min_h1(gram, a_mat, np.ones(len(nodes_o), complex))
    corr, info_c = r37.min_h1(gram, a_mat, np.asarray(values, complex))
    cnt = r80.counterpart_nodes(rho_o)
    model = r51.Model(fam, K, xw1600, base, corr, cnt)
    c_k = np.array([2 * w / math.sqrt(num) for num, w in model.ps])
    om_k = np.array([2 * math.pi * math.log(num) for num, _ in model.ps])
    C_book = float(np.sum(c_k))
    C1_book = float(np.sum(c_k * om_k))
    gates["C3_setup"] = bool(
        model.nfam == NFAM_2051 and len(model.ps) == BOOK_2051
        and abs(model.support - SUPPORT_2051) < 1e-9
        and abs(C_book - C_BOOK_2051) <= TOL_C3 * C_BOOK_2051
        and abs(C1_book - C1_BOOK_2051) <= TOL_C3 * C1_BOOK_2051)
    sections["C3_setup"] = {
        "nfam": model.nfam, "book": len(model.ps),
        "support": model.support, "C_book": C_book, "C1_book": C1_book,
        "min_eig": info_b["min_eig"], "max_eig": info_b["max_eig"],
        "cond_raw": info_b["cond_raw"], "resid_b": info_b["resid"],
        "resid_c": info_c["resid"],
        "gram_condition_raw_2037": 1318248.416390374}
    log("setup: families %d book %d support %.4f C_book %.9f" %
        (model.nfam, len(model.ps), model.support, C_book))

    wc400 = r54.window_control(fam, xw400, base, corr, rho_o, model.ps)
    wc1600 = r54.window_control(fam, xw1600, base, corr, rho_o, model.ps)
    gates["C1_Q400"] = bool(np.sign(wc400["Q"]) < 0
                            and abs(wc400["Q"] - Q400_FROZEN)
                            <= TOL_Q * abs(Q400_FROZEN))
    gates["C2_Q1600"] = bool(np.sign(wc1600["Q"]) < 0
                             and abs(wc1600["Q"] - Q1600_FROZEN)
                             <= TOL_Q * abs(Q1600_FROZEN))
    sections["C1C2_window"] = {"Q400": wc400["Q"], "Q1600": wc1600["Q"]}
    log("C1 %s C2 %s (Q400 %.6e)" % (gates["C1_Q400"], gates["C2_Q1600"],
                                     wc400["Q"]))

    a_mat16 = r80.family_values(fam, K, np.asarray(nodes_o, complex),
                                xw1600).T
    baseB, _ = r37.min_h1(gram, a_mat16, np.ones(len(nodes_o), complex))
    corrB, _ = r37.min_h1(gram, a_mat16, np.asarray(values, complex))
    d_base_rel = float(np.max(np.abs(baseB - base)) / np.max(np.abs(base)))
    d_corr_rel = float(np.max(np.abs(corrB - corr)) / np.max(np.abs(corr)))
    gates["C4_tierB"] = bool(
        abs(d_base_rel / TIERB_DBASE - 1.0) <= TOL_C4
        and abs(d_corr_rel / TIERB_DCORR - 1.0) <= TOL_C4)
    sections["C4_tierB"] = {"d_base_rel": d_base_rel,
                            "d_corr_rel": d_corr_rel}
    log("C4 tier-B d_base %.4e d_corr %.4e" % (d_base_rel, d_corr_rel))

    # ---------------- S1: leggauss certification --------------------
    if smoke:
        Xs_s, Ws_s, dx_s, wlo_s, whi_s, st_s = certify_leggauss(120, 1)
        Xs, Ws, dxi, wlo, whi, st1600 = certify_leggauss(160, 1)
        dev_a10, samp = validate_oracle(160, n_sample=5)
        cert = {"X": Xs, "W": Ws, "dxi": dxi, "wlo": wlo, "whi": whi,
                "stats": st1600, "full": False}
        cert400 = cert
        gates["P4_cert"] = bool(st1600["zero_slope"] == 0
                                and st_s["zero_slope"] == 0
                                and st1600["dxi_max"] <= TOL_CERT)
        gates["A10_oracle"] = bool(dev_a10 <= float(E_VAL) * 10)
        sections["A10_oracle"] = {"dev": dev_a10, "n": 160,
                                  "sample": samp, "full": False}
    else:
        Xs, Ws, dxi, wlo, whi, st1600 = certify_leggauss(M_RED, workers)
        cert = {"X": Xs, "W": Ws, "dxi": dxi, "wlo": wlo, "whi": whi,
                "stats": st1600, "full": True}
        Xs4, Ws4, dxi4, wlo4, whi4, st400 = certify_leggauss(N_A, workers)
        cert400 = {"X": Xs4, "W": Ws4, "dxi": dxi4, "wlo": wlo4,
                   "whi": whi4, "stats": st400, "full": True}
        gates["P4_cert"] = bool(
            st1600["zero_slope"] == 0 and st1600["dxi_max"] <= TOL_CERT
            and st400["zero_slope"] == 0 and st400["dxi_max"] <= TOL_CERT)
        dev_a10, samp = validate_oracle(M_RED, n_sample=21)
        gates["A10_oracle"] = bool(dev_a10 <= float(E_VAL) * 10)
        sections["A10_oracle"] = {"dev": dev_a10, "n": M_RED,
                                  "sample": samp, "full": True}
    sections["cert_leggauss"] = {"m1600": cert["stats"],
                                 "m400": cert400["stats"]}
    log("P4 cert %s (dxi_max %.3e)  A10 dev %.3e"
        % (gates["P4_cert"], cert["stats"]["dxi_max"], dev_a10))

    # ---------------- S2: rule bounds + selftest --------------------
    el_win = []
    clear_min = 999.0
    xis_win = np.linspace(-XI_MAX, XI_MAX, 17 if smoke else 161)
    for (a, th) in fam:
        sarr = [a * (0.5 - 2j * math.pi * x) + 1j * a * th for x in xis_win]
        res, clear = rule_residual_lnE(a, sarr, M_RED, want_clear=True)
        el_win.append(a * max(r["bound"] for r in res))
        clear_min = min(clear_min, clear)
    el_win = np.array(el_win)
    p3_rows = []
    p3_bad = 0
    rng = np.random.default_rng(2056)
    for _ in range(2 if smoke else 8):
        a = float(rng.uniform(1.5, 4.8))
        th = float(rng.uniform(-2.0, 2.0))
        xi = float(rng.uniform(-0.8, 0.8))
        mm = int(rng.choice([6, 10, 20]))
        sarr = a * (0.5 - 2j * math.pi * xi) + 1j * a * th
        Xm, Wm = r59.phi_weights(a, panels=6, m=mm)
        f = r59.phi_fun(Xm, a, K) * Wm
        gl = float(np.sum(np.exp(sarr * Xm) * f).real)
        integ = mp.quad(lambda x: mp.e ** (-mp.mpf(K)
                                           / (1 - (x / mp.mpf(a)) ** 2))
                        * mp.e ** (mp.mpc(sarr) * x), [-a, a])
        err = abs(gl - float(mp.re(integ)))
        res = rule_residual_lnE(a, [sarr], mm)
        bnd = a * res[0]["bound"]
        ok = bnd >= err
        p3_bad += 0 if ok else 1
        p3_rows.append({"a": a, "theta": th, "xi": xi, "m": mm,
                        "err": err, "bound": bnd,
                        "log10_ratio": math.log10(max(bnd, 1e-300)
                                                  / max(err, 1e-300))})
    gates["P3_ruleselftest"] = bool(p3_bad == 0 and clear_min > 0.005)
    sections["P3_ruleselftest"] = {"rows": p3_rows, "bad": p3_bad,
                                   "clear_min": clear_min}
    log("P3 selftest bad %d clear_min %.4f" % (p3_bad, clear_min))

    # ---------------- P7: piece-ellipse selftest (small m) -----------
    # The bridge's |S1 - I_P1| term carries the Trefethen ellipse bound
    # on the PIECE geometry (uc = .8583, hu = .1417 at delta = .05), a
    # regime the 2056 P3 never exercised (its panels all had |uc| <= 5/6
    # with hu = 1/6 AND were floored anyway).  Validate bound >= truth
    # against mp.quad at the small m where the bound is not yet floored.
    p7_rows = []
    p7_bad = 0
    p7_clear = 999.0
    p7_right = 999.0
    rng7 = np.random.default_rng(2057)
    for _ in range(2 if smoke else 8):
        a7 = float(rng7.uniform(1.5, 4.8))
        th7 = float(rng7.uniform(-2.0, 2.0))
        xi7 = float(rng7.uniform(-0.8, 0.8))
        mm7 = int(rng7.choice([6, 10, 20]))
        s7 = a7 * (0.5 - 2j * math.pi * xi7) + 1j * a7 * th7
        uc7 = 0.5 * (2.0 / 3.0 + 1.0 - DELTA_SPLIT)
        hu7 = 0.5 * (1.0 - DELTA_SPLIT - 2.0 / 3.0)
        rho7 = max(2.0, RHO_SAFE * rho_of_panel(uc7, hu7))
        p7_clear = min(p7_clear, ellipse_clear(uc7, hu7, rho7))
        # the ellipse must MISS u = 1: rightmost real point < 1
        chm7, _shm7 = _chm(rho7)
        p7_right = min(p7_right, 1.0 - (uc7 + hu7 * chm7))
        xs7, ws7 = np.polynomial.legendre.leggauss(mm7)
        Xp7 = a7 * (uc7 + hu7 * xs7)
        Wp7 = a7 * hu7 * ws7
        fp7 = r59.phi_fun(Xp7, a7, K) * Wp7
        gl7 = complex(np.sum(np.exp(s7 * Xp7) * fp7))
        integ7 = mp.quad(lambda x: mp.e ** (-mp.mpf(K)
                                            / (1 - (x / mp.mpf(a7)) ** 2))
                         * mp.e ** (mp.mpc(s7) * x),
                         [mp.mpf(a7) * mp.mpf(uc7 - hu7),
                          mp.mpf(a7) * mp.mpf(uc7 + hu7)])
        # COMPLEX residual: the ellipse bound bounds |GL - I| (the M(rho)
        # phase term covers Im s'), so the truth test uses the modulus of
        # the complex difference, not the real parts.
        err7 = abs(gl7 - mp.mpc(integ7))
        bnd7 = float(piece_lnE(a7, uc7, hu7, mm7,
                               np.array([abs(float(np.imag(s7)))]))[0][0])
        ok7 = bnd7 >= err7
        p7_bad += 0 if ok7 else 1
        p7_rows.append({"a": a7, "theta": th7, "xi": xi7, "m": mm7,
                        "err": err7, "bound": bnd7, "rho": rho7,
                        "log10_ratio": math.log10(max(bnd7, 1e-300)
                                                  / max(err7, 1e-300))})
    gates["P7_piece_ellipse"] = bool(p7_bad == 0 and p7_clear > 0.001
                                     and p7_right > 0.0)
    sections["P7_piece_ellipse"] = {"rows": p7_rows, "bad": p7_bad,
                                    "clear_min": p7_clear,
                                    "rightmost_gap": p7_right}
    log("P7 piece-ellipse bad %d clear_min %.4f rightmost_gap %.4f"
        % (p7_bad, p7_clear, p7_right))

    # ---------------- A11: rule_bound_vec vs rule_residual_lnE -------
    a11 = []
    a11ok = True
    for (a, th) in fam[:3]:
        for u in (0.0, 3.7, 55.0, 240.0, a * (2 * math.pi * XI_MAX + abs(th))):
            ref = float(rule_residual_lnE(a, [a * 0.5 + 1j * u], M_RED)[0]
                        ["bound"])
            got = float(rule_bound_vec(a, np.array([u]), M_RED)[0])
            dev = abs(got - ref) / max(ref, 1e-300)
            a11.append({"a": a, "u": u, "ref": ref, "vec": got, "rel": dev})
            a11ok = a11ok and dev <= 1e-12
    gates["A11_rulevec"] = bool(a11ok)
    sections["A11_rulevec"] = a11
    log("A11 rulevec %s (worst rel %.2e)"
        % (a11ok, max(r["rel"] for r in a11)))

    # ---------------- S3: F/X channels ------------------------------
    fam_c = fx_channels(fam, cert)
    FC = np.array([c["FC"] for c in fam_c])
    XC = np.array([c["XC"] for c in fam_c])
    l5_win = {"FC": FC, "XC": XC, "el": el_win, "el_node": True,
              "fc0": FC[:, 0], "xc0": XC[:, 0]}
    bridge_data = [split_panel_data(fam[j][0], fam[j][1], model.consts[j][2],
                                    model.consts[j][3], model.consts[j][5],
                                    DELTA_SPLIT, M_RED,
                                    dxi=cert["dxi"], wlo=cert["wlo"],
                                    whi=cert["whi"])
                   for j in range(len(fam))]
    sections["S3_bridge_setup"] = {
        "delta": DELTA_SPLIT, "m_piece": M_RED,
        "dxi_proxy": bool(bridge_data[0]["dxi_proxy"]),
        "epsF_piece_max": max(bd["epsF_piece_max"] for bd in bridge_data),
        "dp0_max": max(bd["dp"][0] for bd in bridge_data),
        "abs_c0_max": max(bd["abs_c"][0] for bd in bridge_data),
        "abs_p0_max": max(max(bd["abs_p"][0][0], bd["abs_p"][1][0])
                          for bd in bridge_data),
        "allow0_max": max(bd["allow"][0] for bd in bridge_data),
        "covers_2056_el": max(bd["allow"][0] for bd in bridge_data)
        / max(bd["elem_r"] + bd["elem_l"] for bd in bridge_data)}
    l5_win["bridge"] = bridge_data
    if not all(np.isfinite(bd["allow"][k]) for bd in bridge_data
               for k in range(5)):
        raise SystemExit("bridge allowance not finite")
    a_data = a_side_data(fam, nodes_o, cert400)

    def p_bound_at(j, xic):
        """(P)-channel bounds (L-units, k = 0..4) at nodes xic for family j."""
        a, th, Xf, F, M, amp = model.consts[j]
        bd = bridge_data[j]
        xiv = np.atleast_1d(np.asarray(xic, dtype=float))
        z = a * ((0.5 - 2j * np.pi * xiv) + 1j * th)
        E = np.exp(z[:, None] * Xf[None, :])
        bl, dks, _ = bridge_slots(a, th, xiv, E, bd, M_RED)
        return bl, dks

    elu_rows = []
    a13_ok = True
    for j, (a, th) in enumerate(fam):
        u_end = a * (2 * math.pi * XI_MAX + abs(th))
        u_hump = a * abs(th - 2 * math.pi * (-6.68))
        xi_end = -XI_MAX if th > 0 else XI_MAX
        xi_hump = -(-6.68) if th < 0 else -6.68
        bl_e, _ = p_bound_at(j, xi_end)
        bl_h, _ = p_bound_at(j, xi_hump)
        elem_2056 = a * float(rule_bound_vec(a, np.array([u_end]), M_RED)[0])
        brd = a * float(bl_e[0][0])
        a13_ok = a13_ok and brd <= elem_2056 * (1.0 + 1e-15)
        elu_rows.append({
            "a": float(a), "theta": float(th),
            "u_end": float(u_end), "u_hump": float(u_hump),
            "el_end": float(a * rule_bound_vec(a, np.array([u_end]),
                                               M_RED)[0]),
            "el_hump": float(a * rule_bound_vec(a, np.array([u_hump]),
                                                M_RED)[0]),
            "el_2056": elem_2056,
            "bridge_end": brd, "bridge_hump": a * float(bl_h[0][0]),
            "gain_end": elem_2056 / brd if brd > 0 else None,
            "gain_hump": (a * float(rule_bound_vec(a, np.array([u_hump]),
                                                   M_RED)[0])
                          / (a * float(bl_h[0][0]))
                          if float(bl_h[0][0]) > 0 else None),
            "allow0": float(bridge_data[j]["allow"][0]),
            "clear": [float(x) for x in bridge_data[j]["clear"]],
            "rho": [float(x) for x in bridge_data[j]["rho"]],
            "B2sum": float(bridge_data[j]["B2sum"])})
    gates["A13_bridge_gain"] = bool(a13_ok and all(
        r["bridge_end"] <= r["el_2056"] for r in elu_rows))
    sections["S3_channels"] = {
        "el_node_profile": elu_rows,
        "FC_k_max": [float(np.max(FC[:, k])) for k in range(5)],
        "XC_k_max": [float(np.max(XC[:, k])) for k in range(5)],
        "el_max": float(np.max(el_win)),
        "epsF_max": max(c["epsF_max"] for c in fam_c),
        "dX_max": max(c["dX_max"] for c in fam_c),
        "dWrel_max": max(c["dWrel_max"] for c in fam_c),
        "a_side": a_data}
    log("S3 FC0 max %.3e XC0 max %.3e el_max %.3e epsF %.3e" %
        (np.max(FC[:, 0]), np.max(XC[:, 0]), np.max(el_win),
         max(c["epsF_max"] for c in fam_c)))

    # -------- S3b: a-side idealisation gap (REGISTERED, measured) ---
    a3b = []
    save_dps = mp.mp.dps
    mp.mp.dps = 60
    pairs = [(0, 0), (7, 16)] if not smoke else [(7, 16)]
    for (i, j) in pairs:
        aj, thj = fam[j]
        zj = aj * (complex(nodes_o[i]) + 1j * thj)
        Xj, Wj = r59.phi_weights(aj, panels=6, m=400)
        fj = r59.phi_fun(Xj, aj, K) * Wj
        zm = mp.mpc(repr(complex(zj).real), repr(complex(zj).imag))
        gl = mp.mpf(0)
        for xi, fi in zip(Xj, fj):
            gl += mp.mpf(repr(float(fi))) * mp.e ** (zm * mp.mpf(repr(float(xi))))
        a_rule = mp.mpf(repr(float(aj))) * gl
        ajm = mp.mpf(repr(float(aj)))
        integ = mp.quad(lambda x: mp.e ** (-mp.mpf(K)
                                           / (1 - (x / ajm) ** 2))
                        * mp.e ** (zm * x), [-ajm, ajm], maxdegree=10)
        a_true = ajm * integ if mp.isfinite(integ) else mp.mpf("nan")
        st_val = complex(a_mat[i, j])
        rvt = abs(a_rule - a_true)
        a3b.append({
            "node": int(i), "fam": int(j),
            "s_prime": [float(complex(zj).real), float(complex(zj).imag)],
            "stored": float(abs(st_val)),
            "float_vs_exact_rule": float(abs(mp.mpc(repr(st_val.real),
                                                    repr(st_val.imag))
                                             - a_rule)),
            "rule_vs_true": float(rvt) if mp.isfinite(rvt) else None,
            "true": float(abs(a_true)) if mp.isfinite(a_true) else None})
    mp.mp.dps = save_dps
    sections["S3b_a_side"] = {
        "rows": a3b,
        "analytic_incumbent_bound": a_data["rule_a_max"],
        "status": "REGISTERED, not enclosed"}
    log("S3b a-side: %s" % ["(n%d,f%d) stor %.2e rule-vs-true %.2e"
                            % (r["node"], r["fam"], r["stored"],
                               r["rule_vs_true"]) for r in a3b])

    # ---------------- S4: solve channel -----------------------------
    kkt_b = kkt_certify(gram, a_mat, np.ones(len(nodes_o)), base)
    kkt_c = kkt_certify(gram, a_mat, np.asarray(values), corr)
    nq = gram.shape[0]
    Gm = mp.matrix(nq, nq)
    for i in range(nq):
        for j2 in range(nq):
            Gm[i, j2] = mp.mpf(float(np.real(gram[i, j2])))
    evals = mp.eigsy(Gm, eigvals_only=True)
    nE = evals.rows * evals.cols
    ev = [float(evals[i // evals.cols, i % evals.cols]) for i in range(nE)]
    lmax = max(ev)
    lmin = min(ev)
    floor = max(lmax * 1e-12, 1e-18)
    wmarg = lmin - nq * U * lmax
    wrel = wmarg / lmax
    # Floor regime: the committed rule inverts with max(ew, floor).  In the
    # uniform-floor regime (floor >= lmax) the exact-arithmetic rule value
    # is inv = ev/floor @ ev^T = I/floor, i.e. the min-norm interpolant
    # A^H (A A^H)^{-1} y -- independent of the eigenbasis.  The committed
    # solve is therefore certified against the exact KKT solve of the
    # stored matrices (kkt_certify), with the floor correction measured
    # exactly in mp (|c_KKT - c_minnorm|).
    floor_uniform = floor >= lmax
    floor_free = floor <= lmin
    gates["P5_kkt"] = bool(kkt_b["theta"] <= 1e-3 and kkt_c["theta"] <= 1e-3
                           and wrel > 1e-9
                           and (floor_uniform or floor_free))
    nq2 = gram.shape[0]
    Gm2 = mp.matrix(nq2, nq2)
    for i in range(nq2):
        for j2 in range(nq2):
            Gm2[i, j2] = mp.mpc(complex(gram[i, j2]))
    Am = mp.matrix(nq2, nq2)
    for i in range(nq2):
        for j2 in range(nq2):
            Am[i, j2] = mp.mpc(complex(a_mat[i, j2]))
    Sm = Am * Am.H
    c_mn_b = Am.H * (Sm ** -1 * mp_matrix_col(np.ones(nq2)))
    c_mn_c = Am.H * (Sm ** -1 * mp_matrix_col(np.asarray(values)))
    floor_corr_b = float(max(abs(c_mn_b[i] - kkt_b["c_mp"][i])
                             for i in range(nq2)))
    floor_corr_c = float(max(abs(c_mn_c[i] - kkt_c["c_mp"][i])
                             for i in range(nq2)))
    dbase = np.abs(kkt_b["c_mp"] - base) + INS_S * floor_corr_b
    dcorr = np.abs(kkt_c["c_mp"] - corr) + INS_S * floor_corr_c
    cnorm = float(max(np.max(np.abs(kkt_b["c_mp"])),
                      np.max(np.abs(kkt_c["c_mp"]))))
    lnorm = float(max(np.max(np.abs(kkt_b["lambda_mp"])),
                      np.max(np.abs(kkt_c["lambda_mp"]))))
    l5_win["dbase"] = dbase
    l5_win["dcorr"] = dcorr
    sections["S4_solve"] = {
        "theta_base": kkt_b["theta"], "theta_corr": kkt_c["theta"],
        "rnorm_base": kkt_b["rnorm"], "rnorm_corr": kkt_c["rnorm"],
        "invnorm": kkt_b["invnorm"], "dc_base": kkt_b["dc_bound"],
        "dc_corr": kkt_c["dc_bound"],
        "d_base_meas": float(np.max(np.abs(kkt_b["c_mp"] - base))),
        "d_corr_meas": float(np.max(np.abs(kkt_c["c_mp"] - corr))),
        "d_base_tot": float(np.max(dbase)), "d_corr_tot": float(np.max(dcorr)),
        "lmin": lmin, "lmax": lmax, "floor": floor, "weyl_margin": wmarg,
        "weyl_relative": wrel, "floor_uniform": bool(floor_uniform),
        "floor_free": bool(floor_free),
        "floor_over_lmax": float(floor / lmax),
        "floor_corr_base": floor_corr_b, "floor_corr_corr": floor_corr_c,
        "da_abs_registered": a_data["da_abs"]}
    log("P5 %s theta %.2e/%.2e wrel %.2e lmin %.3e lmax %.3e floor/lmax "
        "%.2e unif %s  dc %.3e floorcorr %.2e/%.2e" %
        (gates["P5_kkt"], kkt_b["theta"], kkt_c["theta"], wrel, lmin, lmax,
         floor / lmax, floor_uniform, kkt_b["dc_bound"], floor_corr_b,
         floor_corr_c))

    # ---------------- S9: solve channel, direct difference -----------
    # c_mn is the exact min-norm solve of the stored matrices; its float
    # cast is what the O-chain can carry, so the cast is charged (via the
    # l5_cast envelope below).  l5_ns = the 2057 configuration with the
    # solve channel zeroed: the main-pass envelope of the F/X/(P)
    # channels only.
    cmn_b_f = np.array([complex(c_mn_b[i]) for i in range(nq2)])
    cmn_c_f = np.array([complex(c_mn_c[i]) for i in range(nq2)])
    l5_ns = dict(l5_win)
    l5_ns["dbase"] = np.zeros_like(dbase)
    l5_ns["dcorr"] = np.zeros_like(dcorr)
    l5_cast = {"FC": np.zeros_like(FC), "XC": np.zeros_like(XC),
               "el": np.zeros_like(el_win), "el_node": False,
               "dbase": INS * U * np.abs(cmn_b_f),
               "dcorr": INS * U * np.abs(cmn_c_f)}
    sd = {"cast_max_b": float(np.max(INS * U * np.abs(cmn_b_f))),
          "cast_max_c": float(np.max(INS * U * np.abs(cmn_c_f)))}
    dxi_m = 0.01 if smoke else DXI_MAIN
    dxi_c = 0.02 if smoke else DXI_COARSE
    dq_main, dgm = solve_grid(fam, K, xw1600, cnt, model.ps,
                              base, corr, cmn_b_f, cmn_c_f, dxi_m)
    dq_coarse, _ = solve_grid(fam, K, xw1600, cnt, model.ps,
                              base, corr, cmn_b_f, cmn_c_f, dxi_c)
    dq_phi, _ = solve_grid(fam, K, xw1600, cnt, model.ps,
                           base, corr, cmn_b_f, cmn_c_f, dxi_m,
                           shift=PHI_SHIFT)
    dev_c = abs(dq_main - dq_coarse)
    dev_p = abs(dq_main - dq_phi)
    qe_grid = 4.0 * max(dev_c, dev_p)
    rel_c = dev_c / max(abs(dq_main), 1.0)
    rel_p = dev_p / max(abs(dq_main), 1.0)
    tol_d2 = 0.05 if smoke else TOL_D2
    gates["D2_grid_controls"] = bool(rel_c <= tol_d2 and rel_p <= tol_d2)
    sd.update({"dxi_main": dxi_m, "dxi_coarse": dxi_c, "shift": PHI_SHIFT,
               "dQ_main": dq_main, "dQ_coarse": dq_coarse, "dQ_phi": dq_phi,
               "dev_coarse": dev_c, "dev_phi": dev_p,
               "rel_coarse": rel_c, "rel_phi": rel_p, "qe_grid": qe_grid,
               "trapz_abs_dg": dgm["trapz_abs"], "n_main": dgm["n"],
               "cmn_b_max": float(np.max(np.abs(cmn_b_f))),
               "cmn_c_max": float(np.max(np.abs(cmn_c_f))),
               "cmn_b_dev": float(np.max(np.abs(cmn_b_f - base))),
               "cmn_c_dev": float(np.max(np.abs(cmn_c_f - corr)))})
    sections["S9_solve_direct"] = sd
    log("S9 dQ %.8e (coarse dev %.3e phi dev %.3e) qe_grid %.3e "
        "trapz|WdG| %.3e" % (dq_main, dev_c, dev_p, qe_grid,
                             dgm["trapz_abs"]))

    # ---------------- S5: sigma / book ------------------------------
    u_pts = np.array([0.0, 0.5, 1.0, 2.0, 5.0, 10.0, 20.0, 40.0, 80.0,
                      125.6, 160.0, 200.0, 251.3])
    if smoke:
        u_pts = u_pts[[0, 4, 8]]
    a7 = []
    a7ok = True
    for u in u_pts:
        sf = float(r59.rig.sigma_vec(np.array([u]))[0])
        sm = mp_sigma(mp.mpf(u))
        eps = sigma_eps(u)
        ratio = abs(sf - float(sm)) / eps
        a7.append({"u": float(u), "dev": abs(sf - float(sm)),
                   "eps": eps, "ratio": ratio})
        a7ok = a7ok and ratio < 1.0
    gates["A7_sigma"] = bool(a7ok)
    xg_s = np.linspace(-XI_MAX, XI_MAX, 2 if smoke else 5)
    bf = committed_book(xg_s, model.ps)
    bm = mp_book(xg_s, model.ps)
    db = book_delta(xg_s, model.ps)
    a8 = [{"xi": float(x), "dev": abs(float(bf[i] - bm[i])),
           "bound": float(db[i]),
           "ratio": abs(float(bf[i] - bm[i])) / float(db[i])}
          for i, x in enumerate(xg_s)]
    gates["A8_book"] = bool(all(r["ratio"] < 1.0 for r in a8))
    om_grid = np.linspace(0.0, 2 * np.pi * XI_MAX, 2001)
    sig_grid_max = float(np.max(np.abs(r59.rig.sigma_vec(om_grid))))
    gates["SIGMAX"] = bool(sig_grid_max <= SIG_MAX)
    sections["S5_kernel"] = {"A7": a7, "A8": a8,
                             "sig_grid_max": sig_grid_max,
                             "eps_sigma0": sigma_eps(0.0),
                             "db_max": float(np.max(db))}
    log("A7 %s A8 %s sig_max %.6f eps_sig(0) %.3e db_max %.3e" %
        (gates["A7_sigma"], gates["A8_book"], sig_grid_max,
         sigma_eps(0.0), float(np.max(db))))
    log("A8 ratios %s" % ["%.3f" % r["ratio"] for r in a8])

    # ---------------- S6: A9 rule mp checks -------------------------
    a9 = []
    a9ok = True
    ncase = 1 if smoke else 6
    for (a, th) in fam[:ncase]:
        xi = th / (2 * math.pi)
        sarr = a * (0.5 - 2j * math.pi * xi) + 1j * a * th
        Xm, Wm = xw1600[fam.index((a, th))]
        f = r59.phi_fun(Xm, a, K) * Wm
        gl = float(np.sum(np.exp(sarr * Xm) * f).real)
        integ = mp.quad(lambda x: mp.e ** (-mp.mpf(K)
                                           / (1 - (x / mp.mpf(a)) ** 2))
                        * mp.e ** (mp.mpc(sarr) * x), [-a, a])
        err = abs(gl - float(mp.re(integ)))
        res = rule_residual_lnE(a, [sarr], M_RED)
        bnd = a * float(res[0]["bound"])
        a9.append({"a": a, "theta": th, "xi": xi, "err": err,
                   "bound": bnd, "ratio": err / bnd})
        a9ok = a9ok and err <= bnd
    gates["A9_rule"] = bool(a9ok)
    sections["A9_rule"] = a9
    log("A9 %s" % gates["A9_rule"])

    # ---------------- S6b: A12 bridge truth / arithmetic --------------
    # A12a: the bridged (P) bound >= the TRUE full-rule residual at
    # (family, xi) points with |Im s'| <= 24, by mp.quad dps 40 (the A9
    # shape, on the bridged bound).  A12b: at window-edge nodes, where no
    # quadrature resolves the rule, reproduce BOTH sums in mp (dps 50,
    # repr-lifted stored floats) and require |D_float - D_mp| <= allow.
    a12a = []
    a12a_ok = True
    fam_sel = [0, 5, 10, 16] if not smoke else [0, 16]
    fm_mp = mp.mpf(K)
    for j in fam_sel[:2 if smoke else 4]:
        a, th = fam[j]
        Xf = np.asarray(model.consts[j][2])
        F = np.asarray(model.consts[j][3])
        for u0 in (0.0, 24.0):
            xi = th / (2.0 * math.pi) - u0 / (2.0 * math.pi * a)
            z = a * ((0.5 - 2j * math.pi * xi) + 1j * th)
            glc = complex(np.sum(np.exp(z * Xf) * F)) / a          # L-units
            am = mp.mpf(repr(float(a)))
            zm = mp.mpc(repr(float(z.real)), repr(float(z.imag)))
            integ = mp.quad(lambda x: mp.e ** (-fm_mp
                                               / (1 - (x / am) ** 2))
                            * mp.e ** (zm * x), [-am, am], maxdegree=8)
            true_res = abs(glc - mp.mpc(integ))                    # L-units
            bl, _ = p_bound_at(j, xi)
            bnd = INS * float(bl[0][0])
            elem6 = float(rule_bound_vec(a, np.array([u0]), M_RED)[0])
            ok = true_res <= bnd
            a12a_ok = a12a_ok and ok
            a12a.append({"fam": int(j), "a": float(a), "theta": float(th),
                         "xi": float(xi), "u0": u0,
                         "true_res": float(true_res), "bound": bnd,
                         "elem_2056": elem6,
                         "ratio": float(true_res) / bnd if bnd > 0 else None,
                         "bridge_le_elem": bool(float(bl[0][0]) <= elem6)})
    gates["A12a_bridge_truth"] = bool(a12a_ok)
    sections["A12a_bridge_truth"] = a12a
    log("A12a %s (worst ratio %.3e)"
        % (a12a_ok, max(r["ratio"] for r in a12a)))
    a12b = []
    a12b_ok = True
    for j in ([16] if not smoke else [0]):
        a, th = fam[j]
        bd = bridge_data[j]
        xm_outer = np.concatenate([bd["Xf"][bd["slR"]], bd["Xf"][bd["slL"]]])
        xm_piece = np.concatenate([bd["Xp_R"], bd["Xp_L"]])
        for xi in (XI_MAX, -XI_MAX):
            z = a * ((0.5 - 2j * math.pi * xi) + 1j * th)
            zm = mp.mpc(repr(float(z.real)), repr(float(z.imag)))
            for k in (0, 2):
                term_o = np.concatenate([bd["Fm5"][bd["slR"], k],
                                         bd["Fm5"][bd["slL"], k]])
                term_p = np.concatenate([bd["Fpm5_R"][:, k],
                                         bd["Fpm5_L"][:, k]])

                def _mpsum(xs, ts):
                    s = mp.mpc(0)
                    for x_, t_ in zip(xs, ts):
                        tc = complex(t_)
                        s += mp.mpc(repr(tc.real), repr(tc.imag)) \
                            * mp.e ** (zm * mp.mpf(repr(float(x_))))
                    return s

                dmp = abs(_mpsum(xm_outer, term_o) - _mpsum(xm_piece,
                                                            term_p))
                _, dks = p_bound_at(j, xi)
                dfl = float(dks[k][0])
                ok = abs(dfl - float(dmp)) <= bd["allow"][k]
                a12b_ok = a12b_ok and ok
                a12b.append({"fam": int(j), "xi": float(xi), "k": k,
                             "D_float": dfl, "D_mp": float(dmp),
                             "allow": float(bd["allow"][k]),
                             "dev_over_allow": (abs(dfl - float(dmp))
                                                / bd["allow"][k])})
    gates["A12b_bridge_arith"] = bool(a12b_ok)
    sections["A12b_bridge_arith"] = a12b
    log("A12b %s (%d rows)" % (a12b_ok, len(a12b)))

    # ---------------- S7: U-grid passes -----------------------------
    dxi_u = 0.1 if smoke else 0.001
    nodes_u = np.linspace(-XI_MAX, XI_MAX,
                          int(round(2 * XI_MAX / dxi_u)) + 1)
    if smoke:
        nodes_u = np.linspace(-XI_MAX, XI_MAX, 801)
        dxi_u = float(nodes_u[1] - nodes_u[0])
    jet0 = JetL5(fam, K, xw1600, base, corr, cnt, None)
    jetL = JetL5B(fam, K, xw1600, base, corr, cnt, l5_ns)
    jet57 = JetL5B(fam, K, xw1600, base, corr, cnt, l5_win)
    jet56 = JetL5(fam, K, xw1600, base, corr, cnt, l5_win)
    jet_cm = JetL5(fam, K, xw1600, cmn_b_f, cmn_c_f, cnt, l5_cast)
    jet_cm0 = JetL5(fam, K, xw1600, cmn_b_f, cmn_c_f, cnt, None)
    jn = np.array([-13.25, 0.31, 7.77, 21.5])
    jb = r51.Model.g_jet(model, jn, 0.001, 4096)
    j0 = jet0.g_jet(jn, 0.001, 4096)
    p2 = 0.0
    for k in range(4):
        for part in (0, 1):
            d = np.max(np.abs(j0[k][part] - jb[k][part])
                       / np.maximum(np.abs(jb[k][part]), 1e-300))
            p2 = max(p2, float(d))
    p2 = max(p2, float(np.max(np.abs(j0[4] - jb[4])
                              / np.maximum(np.abs(jb[4]), 1e-300))))
    gates["P2_jet"] = bool(p2 <= TOL_P2)
    ns6 = nodes_u[:: max(1, len(nodes_u) // 16)][:16]
    C_r52, EG_r52 = r52.committed_and_bound(model, ns6, xw1600, 512)
    j6 = jet0.g_jet(ns6, dxi_u, 512)
    v_jet6 = np.asarray(j6[0][0])
    e_jet6 = np.asarray(j6[0][1])
    # P6 scale (2056 formulation).  Both calculi evaluate the SAME chain;
    # they differ only in accumulation order, so the deviation is bounded
    # by the SUM of the two certified forward-rounding allowances: r52's
    # EG and the jet's own null-channel err0.  The first drafts gated
    # against the safe-magnitude product S6 (below) and read 2.3e-07 --
    # S6 bounds the chain's VALUE magnitudes, not the two accumulators'
    # rounding, whose scale is the per-family absolute sum
    # sum_i |F_i| e^{0.5 a X_i} ~ 1.7e-12 (measured).  S6 stays as a
    # recorded control.
    s6 = 0.5 - 2j * np.pi * ns6
    v6 = r80.family_values(fam, K, s6, xw1600)
    lb_s = (np.abs(base)[:, None] * np.abs(v6)).sum(axis=0)
    cc_s = (np.abs(corr)[:, None] * np.abs(v6)).sum(axis=0)
    p_s = np.ones(len(ns6))
    for c0 in cnt:
        p_s = p_s * (abs(c0.real) + abs(c0.imag) + 2.0 * np.pi * np.abs(ns6))
    S6 = p_s ** 2 * (lb_s ** 2) * (cc_s ** 2)
    alw = EG_r52 + e_jet6
    p6rows = [{"xi": float(x),
               "dev": float(abs(v_jet6[i] - C_r52[i])),
               "allow": float(alw[i]),
               "ratio": float(abs(v_jet6[i] - C_r52[i]) / alw[i]),
               "dev_over_S6": float(abs(v_jet6[i] - C_r52[i]) / S6[i])}
              for i, x in enumerate(ns6)]
    p6 = float(np.max([r["ratio"] for r in p6rows]))
    gates["P6_value"] = bool(p6 <= TOL_P6)
    sections["P2P6"] = {"p2_rel": p2, "p6_rel": p6, "p6_rows": p6rows,
                        "scalar_eg_vs_jet_err0_ratio":
                        [float(np.asarray(j6[0][1])[i]
                               / max(EG_r52[i], 1e-300))
                         for i in range(4)]}
    log("P2 %s (%.2e) P6 %s (%.2e)" % (gates["P2_jet"], p2,
                                       gates["P6_value"], p6))

    # ---------------- B6: bridge-off regression ----------------------
    # JetL5B with bridge=False must reproduce JetL5 (record 2056's jet)
    # bitwise: same el_node channel, same everything.
    jetBoffAt = JetL5B(fam, K, xw1600, base, corr, cnt, l5_win, bridge=False)
    j56n = jet56.g_jet(jn, 0.001, 4096)
    jBn = jetBoffAt.g_jet(jn, 0.001, 4096)
    b6 = 0.0
    for k in range(4):
        for part in (0, 1):
            d = float(np.max(np.abs(np.asarray(jBn[k][part])
                                    - np.asarray(j56n[k][part]))))
            b6 = max(b6, d)
    b6 = max(b6, float(np.max(np.abs(np.asarray(jBn[4])
                                     - np.asarray(j56n[4])))))
    gates["B6_nobridge_bitwise"] = bool(b6 == 0.0)
    sections["B6_nobridge"] = {"max_abs_dev": b6,
                               "note": "JetL5B(bridge=False) vs JetL5, "
                                       "4 sample nodes, all bundles + K4"}
    log("B6 bridge-off bitwise %s (%.1e)" % (gates["B6_nobridge_bitwise"],
                                             b6))

    # MAIN PASS: the 2058 configuration -- bridge on, solve channel
    # ZEROED out of the envelope (l5_ns).  The envelope this returns is
    # int e_g^{ns} of the header assembly.
    err0, val0, err1, val1, esup2, sup2, k4A, ek4 = jet_pass(
        jetL, nodes_u, dxi_u, chunk, workers)

    def _tr(y):
        return float(np.sum(0.5 * (y[1:] + y[:-1]) * dxi_u))

    # EULER-MACLAURIN CORRECTED TRAPEZOID (the 2056 quadrature).  For f in
    # C^4 on the window,
    #   int f = T_h(f) - (h^2/12)(f'(b) - f'(a)) + R,
    #   |R| <= (2 zeta(4)/(2 pi)^4) h^4 int |f''''| = (h^4/720) int |f''''|
    # (the classical zeta-form EM remainder; 2 zeta(4)/(2 pi)^4 = 1/720
    # exactly to the digits used).  Hence the certified upper bound
    #   int f <= T_h(f) + (h^2/12)(|f'(a)| + |f'(b)|) + (h^4/720) int|f''''|.
    # Error channel: |E'| at the ends is bounded by the k=1 error slot, and
    # |E''''| <= sigma_loc K4 (the modelling bound, NONCLAIMS).
    # Value channel: the derivative slot carries the exact g', so |g'| at
    # the ends is known; |g''''| <= K4.
    # The first drafts charged (h^2/12) int sup_cell |E''| instead: the
    # |.|-sum error slots inflate that ~1e10x at cancellation nodes
    # (smoke means err2 3.7e16 against err0 0.73) and the price read
    # 1.3e+18.  The EM endpoint form depends on the error function's own
    # derivative at TWO points only, which the cancellation cannot inflate.
    h2_12 = dxi_u ** 2 / 12.0
    h4_720 = dxi_u ** 4 / 720.0
    tr_e, tr_v = _tr(err0), _tr(val0)
    em_e = h2_12 * (float(abs(err1[0])) + float(abs(err1[-1])))
    reg_e = h4_720 * _tr(ek4)
    em_v = h2_12 * (float(abs(val1[0])) + float(abs(val1[-1])))
    reg_v = h4_720 * _tr(k4A)
    int_eg = tr_e + em_e + reg_e
    int_g = tr_v + em_v + reg_v
    db_u = book_delta(nodes_u, model.ps)
    epsK = max(sigma_eps(0.0), float(np.max(db_u)))
    # ---------------- R57: the 2057 price, reproduced in this run ------
    # Same grid, same quadrature, the FULL 2057 l5 configuration (bridge
    # + dbase/dcorr): the frozen 2057 headline must land on the frozen
    # figures, so every 2058 difference below is same-run.
    er0_57, vl0_57, er1_57, vl1_57, es2_57, sp2_57, k4_57, ek4_57 = \
        jet_pass(jet57, nodes_u, dxi_u, chunk, workers)
    tr_e57 = _tr(er0_57)
    em_e57 = h2_12 * (float(abs(er1_57[0])) + float(abs(er1_57[-1])))
    reg_e57 = h4_720 * _tr(ek4_57)
    int_eg57 = tr_e57 + em_e57 + reg_e57
    tr_v57 = _tr(vl0_57)
    em_v57 = h2_12 * (float(abs(vl1_57[0])) + float(abs(vl1_57[-1])))
    reg_v57 = h4_720 * _tr(k4_57)
    int_g57 = tr_v57 + em_v57 + reg_v57
    charge_value57 = (SIG_MAX + C_book) * int_eg57
    charge_kernel57 = epsK * (int_g57 + int_eg57)
    charge_l5_57 = charge_value57 + charge_kernel57
    r57_dev = [abs(int_eg57 / INT_EG_2057 - 1.0),
               abs(charge_value57 / CHARGE_VALUE_2057 - 1.0),
               abs(charge_l5_57 / CHARGE_L5_2057 - 1.0)]
    # Smoke runs the 0.1 grid: the h^4 REGRESS term (h = 0.1) dwarfs the
    # trapz there, while the frozen figures are the 0.001-grid ones (their
    # regress is 1.677e-01 of 3.976762e+06), so smoke compares the
    # h-INDEPENDENT part -- the trapz of err0 -- exactly as 2057's R56
    # smoke compared tr_e56 against its 0.1-grid control.
    if smoke:
        gates["R57_2057_price"] = bool(abs(tr_e57 / INT_EG_2057 - 1.0)
                                       <= 0.05)
    else:
        gates["R57_2057_price"] = bool(max(r57_dev) <= TOL_R57)
    sections["R57_2057_price"] = {
        "int_eg_57": int_eg57, "int_eg_2057": INT_EG_2057,
        "err0_trapz_57": tr_e57,
        "charge_value_57": charge_value57,
        "charge_value_2057": CHARGE_VALUE_2057,
        "charge_l5_57": charge_l5_57, "charge_l5_2057": CHARGE_L5_2057,
        "total_ideal_57": TOTAL_2055 + charge_l5_57,
        "rel_dev": r57_dev, "grid": dxi_u, "nodes": len(nodes_u),
        "smoke_cmp": ("err0_trapz vs frozen int_eg" if smoke else "full"),
        "smoke_mode": bool(smoke)}
    log("R57 int_eg %.6e (2057 %.6e, rel %.2e) charge_value %.6e "
        "charge_L5 %.6e (rel %.2e)" % (int_eg57, INT_EG_2057, r57_dev[0],
                                       charge_value57, charge_l5_57,
                                       r57_dev[2]))

    # ---------------- B7: the zeroing moved the error channel only ----
    # The VALUE slots (val0, val1) must be bitwise untouched by zeroing
    # dbase/dcorr: they are built from the family value slots only.  The
    # K4 slot is NOT compared: k4 is an ERROR slot by design (the solve
    # channel's ad * (vr[4] + vi[4]) term lands there), so int_g's
    # regress term moves with it -- B7 compares the value-only pieces.
    b7_val = bool(np.array_equal(val0, vl0_57)
                  and np.array_equal(val1, vl1_57))
    b7_tr = bool(tr_v == tr_v57 and em_v == em_v57)
    gates["B7_zeroing"] = bool(b7_val and b7_tr)
    sections["B7_zeroing"] = {
        "val0_val1_bitwise": b7_val, "tr_v_em_v_bitwise": b7_tr,
        "val_trapz_ns": tr_v, "val_trapz_full": tr_v57,
        "k4_note": "k4/ek4 and the int_g regress term move with the "
                   "error channel by design (the solve channel's K4 entry)",
        "int_g_ns": int_g, "int_g_full": int_g57,
        "int_eg_ns": int_eg, "int_eg_full": int_eg57}
    log("B7 zeroing: val0/val1 bitwise %s, tr_v/em_v bitwise %s"
        % (b7_val, b7_tr))

    # ---------------- D4: the same-grid marginal solve reading --------
    diff_solve = int_eg57 - int_eg
    d4_ratio = diff_solve / SOLVE_DECOMP_2057
    # Smoke again reads the h-independent trapz level: at the 0.1 grid the
    # regress terms differ between the two configs and dominate int_eg.
    diff_tr = tr_e57 - tr_e
    if smoke:
        gates["D4_diff_solve"] = bool(
            diff_tr > 0 and 0.1 <= diff_tr / SOLVE_DECOMP_2057 <= 10.0)
    else:
        gates["D4_diff_solve"] = bool(
            diff_solve > 0 and D4_LO <= d4_ratio <= D4_HI)
    sections["D4_diff_solve"] = {
        "int_eg_full": int_eg57, "int_eg_ns": int_eg,
        "diff_solve": diff_solve, "solve_decomp_2057": SOLVE_DECOMP_2057,
        "ratio": d4_ratio, "diff_trapz": diff_tr,
        "trapz_ratio": diff_tr / SOLVE_DECOMP_2057,
        "smoke_cmp": ("err0_trapz difference" if smoke else "full")}
    log("D4 marginal solve reading %.4e / 2057 %.4e = %.3f"
        % (diff_solve, SOLVE_DECOMP_2057, d4_ratio))

    # ---------------- D1/D3: arithmetic envelopes + truth -------------
    # The difference's arithmetic allowance: the two chains' own
    # certified forward-rounding envelopes (jet0 at c_stored with no
    # channels; jet_cm at c_mn with ONLY the coefficient-cast envelope),
    # integrated by the same corrected-trapezoid convention.
    ar0 = jet_pass(jet0, nodes_u, dxi_u, chunk, workers)
    acm = jet_pass(jet_cm, nodes_u, dxi_u, chunk, workers)
    ae0, av0_, ae1, av1_, aes2, as2, ak4, aek4 = ar0
    int_e0 = _tr(ae0) + h2_12 * (float(abs(ae1[0])) + float(abs(ae1[-1]))) \
        + h4_720 * _tr(aek4)
    ae0c, _, ae1c, _, _, _, _, aek4c = acm
    int_ecm = _tr(ae0c) + h2_12 * (float(abs(ae1c[0]))
                                   + float(abs(ae1c[-1]))) \
        + h4_720 * _tr(aek4c)
    qe_arith = (INS * (int_e0 + int_ecm)
                + 32.0 * U * sd["trapz_abs_dg"])
    charge_solve = abs(sd["dQ_main"]) + sd["qe_grid"] + qe_arith
    charge_value = (SIG_MAX + C_book) * int_eg + charge_solve
    charge_kernel = epsK * (int_g + int_eg)
    sections["D_arith"] = {
        "int_e_round_c0": int_e0, "int_e_cast_cm": int_ecm,
        "err0_c0_max": float(np.max(ae0)),
        "err0_c0_med": float(np.median(ae0)),
        "err0_cm_max": float(np.max(ae0c)),
        "err0_cm_med": float(np.median(ae0c)),
        "ratio_cm_over_c0": int_ecm / max(int_e0, 1e-300),
        "post_chain_32U": 32.0 * U * sd["trapz_abs_dg"],
        "qe_arith": qe_arith, "charge_solve": charge_solve,
        "charge_solve_over_dQ": charge_solve / max(abs(sd["dQ_main"]),
                                                   1e-300)}
    log("D_arith int_e0 %.4e int_ecm %.4e qe_arith %.4e charge_solve "
        "%.6e (dQ %.6e)" % (int_e0, int_ecm, qe_arith, charge_solve,
                            sd["dQ_main"]))
    d1_rows = []
    d1_ok = True
    d3_rows = []
    d3_ok = True
    for x in (D1_NODES if not smoke else D1_NODES[1:2]):
        xa = np.array([x])
        Df, Wf, vf, pf, kf = pointwise_diff(fam, K, xw1600, cnt, model.ps,
                                            base, corr, cmn_b_f, cmn_c_f, x)
        Wm = mp.mpf(repr(float(Wf)))
        g0m = mp_g_nop(model.consts, base, corr, x)
        g1m = mp_g_nop(model.consts, cmn_b_f, cmn_c_f, x)
        Dm = Wm * (g1m - g0m)
        e0x = float(np.asarray(jet0.g_jet(xa, 0.001, 64)[0][1])[0])
        exm = float(np.asarray(jet_cm.g_jet(xa, 0.001, 64)[0][1])[0])
        exn1 = float(np.asarray(jet_cm0.g_jet(xa, 0.001, 64)[0][1])[0])
        exns = float(np.asarray(jetL.g_jet(xa, 0.001, 64)[0][1])[0])
        exfl = float(np.asarray(jet57.g_jet(xa, 0.001, 64)[0][1])[0])
        alw = INS * (e0x + exm) + 32.0 * U * abs(float(Df))
        dev = abs(float(Df) - float(Dm))
        d1_rows.append({"xi": float(x), "D_float": float(Df),
                        "D_mp": float(Dm), "dev": dev, "allow": alw,
                        "ratio": dev / alw, "W_float": float(Wf),
                        "p": pf, "ker": kf,
                        "g0_mp": float(g0m), "g1_mp": float(g1m)})
        d1_ok = d1_ok and dev <= alw
        d3_rows.append({"xi": float(x), "err0_c0": e0x, "err0_cm": exm,
                        "err0_cm0": exn1, "err0_ns": exns,
                        "err0_full": exfl,
                        "ns_le_full": bool(exns <= exfl),
                        "cm_ge_cm0": bool(exm >= exn1)})
        d3_ok = d3_ok and exns <= exfl and exm >= exn1
    gates["D1_diff_truth"] = bool(d1_ok)
    gates["D3_monotone"] = bool(d3_ok)
    sections["D1_diff_truth"] = d1_rows
    sections["D3_envelope_monotone"] = d3_rows
    log("D1 truth %s (worst ratio %.3e)  D3 monotone %s"
        % (d1_ok, max(r["ratio"] for r in d1_rows), d3_ok))
    sections["S7_integrals"] = {
        "grid": dxi_u, "nodes": len(nodes_u),
        "err0_max": float(np.max(err0)), "err0_med": float(np.median(err0)),
        "err0_trapz": tr_e, "em_err_slots": em_e, "corr_regress": reg_e,
        "err1_ends": [float(err1[0]), float(err1[-1])],
        "esup2_max": float(np.max(esup2)),
        "val0_max": float(np.max(val0)), "sup2_max": float(np.max(sup2)),
        "val_trapz": tr_v, "em_val_channel": em_v, "reg_val": reg_v,
        "val1_ends": [float(val1[0]), float(val1[-1])],
        "sig_loc_max": float(np.max(np.minimum(
            2.0, 2.0 * err0 / np.maximum(np.abs(val0) + err0, 1e-300)))),
        "k4_trapz": _tr(k4A), "ek4_trapz": _tr(ek4),
        "int_eg": int_eg, "int_eg_note": "the NO-SOLVE envelope "
        "(l5_ns main pass) -- the solve channel is charged by charge_solve",
        "int_g": int_g,
        "db_u_max": float(np.max(db_u)), "epsK": epsK,
        "charge_solve": charge_solve,
        "charge_value": charge_value, "charge_kernel": charge_kernel}
    log("S7: int_eg(ns) %.4e (tr %.4e + EM %.4e + reg %.4e) int_g %.4e "
        "(tr %.4e + EM %.4e) charge_solve %.4e charge_value %.4e "
        "kernel %.4e" %
        (int_eg, tr_e, em_e, reg_e, int_g, tr_v, em_v, charge_solve,
         charge_value, charge_kernel))

    # decomposition (single-channel jets at a coarse grid; the solve
    # channel is NOT a single-channel envelope any more -- its direct
    # reading lives in S9_solve_direct / D_arith / D4_diff_solve)
    dxi_c = 0.01 if smoke else 0.004
    nodes_c = np.linspace(-XI_MAX, XI_MAX,
                          int(round(2 * XI_MAX / dxi_c)) + 1)
    decomp = {}
    for nm, keys in (("F", ("FC",)), ("X", ("XC",)),
                     ("rule_bridge", ("el",)), ("rule_2056", ("el_wsup",))):
        l5s = {"FC": np.zeros_like(FC), "XC": np.zeros_like(XC),
               "el": np.zeros_like(el_win), "fc0": np.zeros_like(FC[:, 0]),
               "xc0": np.zeros_like(XC[:, 0]), "el_node": False,
               "dbase": np.zeros_like(dbase), "dcorr": np.zeros_like(dcorr)}
        if "FC" in keys:
            l5s["FC"] = FC
            l5s["fc0"] = FC[:, 0]
        if "XC" in keys:
            l5s["XC"] = XC
            l5s["xc0"] = XC[:, 0]
        if "el" in keys:
            l5s["el"] = el_win
            l5s["el_node"] = True
            l5s["bridge"] = bridge_data
        if "el_wsup" in keys:
            l5s["el"] = el_win
            l5s["el_node"] = True
        if "dbase" in keys:
            l5s["dbase"] = dbase
            l5s["dcorr"] = dcorr
        jc = (JetL5B(fam, K, xw1600, base, corr, cnt, l5s)
              if nm == "rule_bridge"
              else JetL5(fam, K, xw1600, base, corr, cnt, l5s))
        e_c, v_c, e1_c, v1_c, es_c, s_c, k4_c, ek4_c = jet_pass(
            jc, nodes_c, dxi_c, chunk, 1 if smoke else workers)
        dc = dxi_c
        tr_c = float(np.sum(0.5 * (e_c[1:] + e_c[:-1]) * dc))
        em_c = dc ** 2 / 12.0 * (float(abs(e1_c[0])) + float(abs(e1_c[-1])))
        rg_c = dc ** 4 / 720.0 * float(np.sum(
            0.5 * (ek4_c[1:] + ek4_c[:-1]) * dc))
        decomp[nm] = tr_c + em_c + rg_c
    sections["S7_decomp_coarse"] = {"grid": dxi_c, "shares": decomp}

    # ---------------- S8: gram cross-read (registered) ---------------
    gp2 = gram_alt(fam, 2 * GAUSS_POINTS)
    gp3 = gram_alt(fam, GAUSS_POINTS // 4, panels=12)
    gmax_abs = float(np.max(np.abs(gram)))
    d12 = float(np.max(np.abs(gram - gp2)) / gmax_abs)
    d13 = float(np.max(np.abs(gram - gp3)) / gmax_abs)
    gram_reading = {"d_2400_vs_4800_rel": d12,
                    "d_2400_vs_comp12x600_rel": d13,
                    "delta_c_effect_meas": kkt_b["invnorm"]
                    * (max(d12, d13) * gmax_abs * (cnorm + lnorm))}
    sections["S8_gram"] = gram_reading
    log("S8 gram d12 %.3e d13 %.3e" % (d12, d13))

    # ---------------- S10b: anchors B3/B5 ---------------------------
    # (B2, the solve channel's pointwise-envelope truth, is RETIRED with
    # the channel: 2058's replacements are D1 (the direct difference vs
    # mpmath) and D3 (the envelope monotonicity), both above.)
    cents = [0.0, -6.68, 20.0] if not smoke else [-6.68]
    b3 = []
    b3ok = True
    l5s_f = {"FC": FC, "XC": np.zeros_like(XC), "el": np.zeros_like(el_win),
             "fc0": FC[:, 0], "xc0": np.zeros_like(XC[:, 0]),
             "el_node": False,
             "dbase": np.zeros_like(dbase), "dcorr": np.zeros_like(dcorr)}
    jF = JetL5(fam, K, xw1600, base, corr, cnt, l5s_f)
    for x in cents:
        consts2 = []
        for j, (a, th, Xf, F, M, amp) in enumerate(model.consts):
            Fmp = mp_construct_F(Xf, np.asarray(xw1600[j][1]), a)
            consts2.append((a, th, Xf, Fmp, M, amp))
        g0 = float(mp_g_eval(model.consts, list(base), list(corr), cnt, x))
        g1 = float(mp_g_eval(consts2, list(base), list(corr), cnt, x))
        ef = float(np.asarray(jF.g_jet(np.array([x]), 0.001, 64)[0][1])[0])
        b3.append({"xi": x, "dev": abs(g1 - g0), "bound": ef,
                   "ratio": abs(g1 - g0) / ef})
        b3ok = b3ok and abs(g1 - g0) <= ef
    gates["B3_Fchan"] = bool(b3ok)
    sections["B3_Fchan"] = b3

    st = r51.selftest()
    gates["B5_selftest"] = bool(st.get("pass", bool(st))
                                if isinstance(st, dict) else bool(st))
    sections["B5_selftest"] = st

    # ---------------- S10: assembly ---------------------------------
    charge_l5 = charge_value + charge_kernel
    total_ideal = TOTAL_2055 + charge_l5
    gates["B4_positivity"] = bool(
        all(np.isfinite(v) and v >= 0 for v in (charge_value, charge_kernel,
                                                charge_l5, total_ideal)))
    all_pass = all(bool(v) for v in gates.values())
    if not all_pass:
        verdict = "ANCHOR-FAIL"
    elif total_ideal < BAR10:
        verdict = "IDEAL-L2-VIABLE"
    elif total_ideal < BUDGET3:
        verdict = "IDEAL-L2-GRAY"
    else:
        verdict = "IDEAL-L2-FAIL"
    assembly = {
        "total_2055": TOTAL_2055, "charge_value": charge_value,
        "charge_kernel": charge_kernel, "charge_l5": charge_l5,
        "total_ideal": total_ideal, "total_over_bar10": total_ideal / BAR10,
        "total_over_budget3": total_ideal / BUDGET3,
        "margin_x": BAR10 / total_ideal,
        "charge_solve": charge_solve,
        "charge_solve_over_dQ": charge_solve / max(abs(sd["dQ_main"]),
                                                   1e-300),
        "dQ_main": sd["dQ_main"], "qe_grid": sd["qe_grid"],
        "qe_arith": qe_arith,
        "charge_l5_2057": CHARGE_L5_2057,
        "gain_x": (CHARGE_L5_2057 / charge_l5 if charge_l5 > 0 else None),
        "total_ideal_2057": TOTAL_IDEAL_2057,
        "total_ideal_2057_over_bar10": TOTAL_IDEAL_2057 / BAR10,
        "int_eg_over_2057": int_eg / INT_EG_2057,
        "int_eg_2057": INT_EG_2057}
    out = {"record": 2058, "status": verdict, "owner": "one-copy G8-H",
           "rho": [float(rho_o.real), float(rho_o.imag)],
           "scale": r37.SCALE, "support": model.support,
           "book_size": len(model.ps),
           "object": "O* = ideal-construction twin of the committed "
                     "m=1600 pipeline; ladder value fixed at O; (P) "
                     "channel bridged (delta = 0.05) and the solve "
                     "channel charged by the direct functional difference "
                     "Q(c_mn) - Q(c_stored)",
           "constants": {"BUDGET3": BUDGET3, "BAR10": BAR10,
                         "TOTAL_2055": TOTAL_2055, "SIG_MAX": SIG_MAX,
                         "C_book": C_book, "M13": "1/24", "C_T": C_T,
                         "INS_PHI": INS_PHI, "INS_F": INS_F,
                         "INS_S": INS_S, "RHO_SAFE": RHO_SAFE,
                         "DELTA_SPLIT": DELTA_SPLIT,
                         "PHI_SHIFT": PHI_SHIFT, "DXI_MAIN": DXI_MAIN,
                         "DXI_COARSE": DXI_COARSE},
           "gates": {k: bool(v) for k, v in gates.items()},
           "assembly": assembly, "sections": sections,
           "nonclaims": [
               "the 4th-derivative tail of the error channel in the S7 "
               "quadrature carries the multiplicative-perturbation scale "
               "sigma_loc = min(2, 2 err0/(|g|+err0)) times the "
               "value-channel K4 (the perturbation is multiplicative with "
               "local relative size err0/|g|; the cap 2 is the crude "
               "|E^(4)| <= 2 sup|g^(4)| fallback).  This is a modelling "
               "bound, not a proven enclosure: the regress term it bounds "
               "is the Euler-Maclaurin remainder (dxi^4/720) int sigma_loc K4, "
               "measured in S7_integrals.corr_regress",
               "the pointwise envelope err0 and the sigma_loc K4 tail are "
               "integrated by the corrected trapezoid on the 0.001 grid "
               "(80001 nodes); the refinement control is the 0.1-grid smoke "
               "value of the same integral (7.771e+07 vs 7.507e+07, 3.5%), "
               "and the 4.3x margin absorbs the difference -- the envelope "
               "integral is a resolved-grid convention, not a certified "
               "sup-over-cells enclosure",
               "the Gram construction rule (GAUSS_POINTS single-panel GL, "
               "sub-geometric flat-singularity residual) is REGISTERED and "
               "MEASURED (S8), not enclosed",
               "the a_mat idealisation gap (m = 400 rule vs true Laplace "
               "integral at the owner-node arguments) is REGISTERED and "
               "MEASURED (S3b), not enclosed: the analytic incumbent for "
               "the worst pair is recorded in S3_channels.a_side.rule_a_max "
               "(2.73e-08 before the h_out tightening, 3.41e-13 in this "
               "run -- still vacuous against the 1e-12 entry scale), "
               "matched pairs agree with mp.quad to 12+ digits, and "
               "mismatched pairs sit at the rule's alias floor; the solve "
               "channel therefore certifies the stored matrices "
               "(O* = exact solve of the stored matrices)",
               "the P3/A9 selftests validate the rule-bound structure at "
               "small m and small |Im s'|; the m = 1600 window bounds rely "
               "on the same formula with margin e^{-2000}-scale",
               "the exp/sqrt/cos constants (8U, 6U) are op-count "
               "constants, not libm proofs",
               "2057 bridge: the (P) channel's outer panels use "
               "min(elementary, bridged); the bridged form carries the "
               "computed difference |GL_c - S1| plus (a) the two sums' "
               "accumulation allowance on the absolute-sum scale, (b) the "
               "piece rule's construction deviation dp_k against the IDEAL "
               "piece rule the ellipse bound applies to (fx_channels "
               "op-count formulas on the certified tables of the SAME "
               "numpy root array, plus 2 map slots -- the elliptical term "
               "itself is floored at 1e-300 and the A12b arithmetic check "
               "is exact on the same float data).  The piece's truth is "
               "validated at small m (P7) and at the A12a points; at "
               "m = 1600 the ellipse term is dead, so the bridge's only "
               "live terms are the computed difference and the allowances",
               "2057 bridge: A12a runs mp.quad at |Im s'| <= 24 only "
               "(where the quadrature resolves the rule); the extreme-node "
               "check (A12b) is an exact-arithmetic reproduction of the two "
               "sums, not a quadrature truth test -- the true residual at "
               "the window edge is not computed anywhere, only bounded",
               "2058 solve: dQ's grid allowance is a CONTROL, not a "
               "certified enclosure: the charge takes 4x max(dev_coarse, "
               "dev_phi) (D2), the same resolved-grid convention as the "
               "envelope integrals; the arithmetic allowance rides on the "
               "two null-channel jet envelopes (INS (int e_round_c0 + "
               "int e_cast_cm) + 32U int |W dg|), whose pointwise truth "
               "is the P2/P6/B3 pattern and whose coverage of THIS "
               "difference is gate D1 (mpmath at hump and window-edge "
               "nodes); D1's mp side evaluates the full chain in mp at "
               "dps 50 from EXACTLY the stored float inputs (stored "
               "floats are exact in O) with the float W lifted exactly, "
               "so it isolates the outer chain + W multiply",
               "2058 solve: the coefficient-cast envelope INS U |c_mn| "
               "is a crude relative-U bound on the mp->float cast of the "
               "exact min-norm solve; the exact c_mn differs from the "
               "committed float solve by the measured d_b 3.963e+04 / "
               "d_c 2.186e+07 (v-scale), so the cast is ~1e-16/1.7e-9 of "
               "the perturbation actually charged by dQ -- it is carried "
               "for form, not because it binds",
               "L4 (record 2053) stands, evaluator-independent; COVER "
               "open; not a producer theorem; not RH"],
           "elapsed_s": None}
    path = os.path.join(ROOT, "results", "2058_l5_solve.json")
    with open(path, "w", encoding="utf-8", newline="\n") as f:
        json.dump(out, f, indent=2, default=float)
        f.write("\n")
    print("VERDICT", verdict)
    print("charge_L5 %.6e = value %.6e + kernel %.6e (2057: %.6e, "
          "gain %.3fx)" % (charge_l5, charge_value, charge_kernel,
                           CHARGE_L5_2057, CHARGE_L5_2057 / charge_l5))
    print("charge_solve %.6e = |dQ| %.6e + qe_grid %.3e + qe_arith %.3e"
          % (charge_solve, abs(sd["dQ_main"]), sd["qe_grid"], qe_arith))
    print("total_ideal %.6e = %.4fx bar10 (%.4fx budget3)" %
          (total_ideal, total_ideal / BAR10, total_ideal / BUDGET3))
    out["elapsed_s"] = round(time.time() - T0, 1)
    with open(path, "w", encoding="utf-8", newline="\n") as f:
        json.dump(out, f, indent=2, default=float)
        f.write("\n")
    print("RESULT", path)
    print("elapsed", round(time.time() - T0, 1), flush=True)


def gram_alt(fam, m, panels=1):
    amax = max(a for a, _ in fam)
    xg, wg = np.polynomial.legendre.leggauss(m)
    if panels == 1:
        x = amax * xg
        w = amax * wg
    else:
        edges = np.linspace(-amax, amax, panels + 1)
        X, W = [], []
        for j in range(panels):
            lo, hi = edges[j], edges[j + 1]
            X.append(0.5 * (hi - lo) * xg + 0.5 * (lo + hi))
            W.append(0.5 * (hi - lo) * wg)
        x = np.concatenate(X)
        w = np.concatenate(W)
    phi = np.zeros((len(fam), len(x)), dtype=complex)
    dphi = np.zeros_like(phi)
    for j, (a, theta) in enumerate(fam):
        u = x / a
        inside = np.abs(u) < 1.0
        core = np.zeros_like(x)
        core[inside] = np.exp(-K / (1.0 - u[inside] ** 2))
        phase = np.exp(1j * theta * x)
        phi[j] = core * phase
        deriv = np.zeros_like(x)
        den = 1.0 - u[inside] ** 2
        deriv[inside] = core[inside] * (-2.0 * K * x[inside]
                                        / (a * a * den * den))
        dphi[j] = (deriv + 1j * theta * core) * phase
    gram = (phi.conj() * w) @ phi.T + (dphi.conj() * w) @ dphi.T
    return (gram + gram.conj().T) / 2.0


if __name__ == "__main__":
    main()