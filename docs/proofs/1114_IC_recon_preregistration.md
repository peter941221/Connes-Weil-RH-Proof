# 1114b - I-C recon probe: model-declared a_det table + spectral-band fraction

Date: 2026-09-03 (night), companion to 1114_IC_problem_statement.md.

Status: PRE-REGISTRATION committed BEFORE the run. Everything here is a
DECLARED MODEL (scaling reconnaissance), not a certificate and not a
theorem. No thresholds gate anything; expectations below are registered
falsifiers of the DIAGNOSIS (report, do NOT patch).

## 0. Part 1 - detector window radius a_det(k), two model branches

Zero rho_k = 1/2 + i*gamma_k (model assumes RH-consistent location at
these heights - reconnaissance input, not an claim). Per the D1 chain
(1114_IC_problem_statement.md §0b):

    n0 = min n : gamma_k < 2^(n+1)
    R  = 2^(n0+1) + 2 + sqrt(1.5^2 + gamma_k^2)        (Lean: :142-144)
    ball nodes: all j != k with |gamma_j - gamma_k| < R (RH-line metric)

    C_model = prod_{j in ball} (1 + R / |gamma_j - gamma_k|)
        (declared Lagrange-type product bound for the interpolation
         constant the assembly lemma must suppress)
    n_hi = ceil(log2(max(C_model, 2)))                 (worst branch)
    n_lo = ceil(log2(gamma_k^2 + 4))                   (decay-only
        branch: ||z-rho||^2 <= ~T^2+4 suppressed by 2^-n at eps = 1)

    a_det_lo = n_lo + 2,  a_det_hi = n_hi + 2
    deficit  = a_det - a_cert_max (4, certified) and - 5 (1113 horizon)

zeros k = 1,2,3,4,5,7,10,15,20; gamma_1..~gamma_65 precomputed
(mpmath zetazero, dps=30) so every ball is fully contained.

## 1. Part 2 - spectral disjointness fraction f_band(k)

Certified-window spectral stand-in: the band |xi| <= gamma_1 (the
few-zero low-frequency corner dominating lambda_min(Z|_V), per the Q-F2
diagnosis of 1114 §1 G2). Model detector test:

    g(u) = chi(u/a) * cos(T*u),  chi(v) = exp(-1/(1-v^2)), a = a_det_lo

(the FAVOURABLE choice - larger a narrows the spectral bump and only
pushes f_band DOWN; sensitivity reported at a_det_hi too). f_band =
(FFT energy of g in the band)/(total FFT energy), uniform grid 2^20
points on (-2a, 2a) (zero pad x2); resolution pi/a -> caveat band
edge quantization ~ a few bins at k=1 (peak sits exactly at edge).

## 2. Registered expectations (diagnosis falsifiers, report-only)

    R1  a_det_lo(k=1) >= 8, monotone-ish growth in k
        (support gap >= 3 beyond the certified horizon even on the
         favourable branch)
    R2  f_band(1) in [0.3, 0.7]; f_band(k >= 2) < 5e-2 and decreasing
    R3  deficit_hi(k) >= 11 for every k
    Falsifiers: a_det_lo < 6 anywhere -> the class gap may be closable
    by radius extension: REPORT and revisit 1114 §1-2 framing;
    f_band(k>=2) > 0.1 -> spectral-disjointness diagnosis wrong:
    REPORT. Nothing about the certificates themselves is at stake.

## 3. Artifacts and scope

Output: printed tables + docs/proofs/1114_IC_recon.json
(k, gamma, R, N_ball, delta_min, C_model, n_lo, n_hi, a_det_lo,
a_det_hi, f_band at a_det_lo and a_det_hi). Model numbers are
reconnaissance of SCALE ONLY; they constrain no Lean obligation and
certify nothing. Runtime: seconds. RH NOT claimed; no map change keyed.

## 3b. POST-RUN ADDENDUM (runs 16:2x + rerun with closed balls)

Run ledger: run 1 (KMAX=90) aborted cleanly at the model level - balls
at k=15/20 were OPEN (T+R = 260/284 > gamma_90 = 219), silently
undercounting N_ball; bug fixed (KMAX=170 + per-row closure assert)
BEFORE the numbers were used anywhere; run 2 (this record) has all
balls closed. First-run defect note also booked: `mp.dps` on the
mpmath top level is a set-time AttributeError - Pyright flagged it at
write time and the flag was real (law 56 discipline cuts both ways:
verify diagnostics against the interpreter, fix what is true).

Verdict table (registered expectations, §2):

    R1  a_det_lo(k=1) = 10 >= 8            OK
    R1b growth                         OK (10 -> 15 favorable branch)
    R2a f_band(1) = 0.320 in [0.3, 0.7]    OK (edge-bin quantization
                                           caveat registered: xi-res
                                           0.314 vs peak width 0.1)
    R2b f_band(k>=2) <= 8.9e-10, decreasing OK
    R3  deficit_hi >= 11 every k           FALSIFIED at k=1 (def_hi = 8:
                                           only 7 ball nodes) - booked
                                           per report-only protocol;
                                           OK from k=2 (30 -> 263)

Realized headline numbers (model, declared):

    k=1 :  R = 32.2, N_ball = 7,  a_det in [10, 13], f_band = 0.32
    k=5 :  R = 99.0, N_ball = 43, a_det in [13, 86], f_band = 3.3e-16
    k=20:  R = 207,  N_ball = 127, a_det in [15, 268], f_band = 6.6e-30

The R3 "falsification" narrows nothing: the support gap (def_lo >= 5
everywhere and growing) plus the super-geometric pin decay from 1113
(pin(a) < 1e-26 for a >= 10 against a 2.6e-19 float noise floor) close
the brute-force window route AT THE FAVOURABLE BRANCH too. The only
live conclusion is unchanged and sharper: domination (Stage B), not
membership - the dominance lemma must bound the detector's gate value
by window-family data WITHOUT the detector lying in any certified V.

Sharpened shape (drives the 1114 §2 prescription):

  * Pilot target = k=1: the ONLY case with f_band = 0.32 (a third of
    model spectral energy already inside the certified low band), and
    its entire ball configuration (7 zeros, height < 47, visible
    primes < exp(2*10) = 4.9e8) sits INSIDE the Platt-Trudgian 3e12
    verified regime - Stage A input is finite tabulated data there.
    Favorable-branch k <= 10 (exp(2*14) = 1.4e12) also fit; the worst
    branch escapes the floor immediately.
  * Spectral disjointness is absolute from k=2: 8.9e-10 and falling
    like a smooth-bump transform tail - no band-based route can reach
    higher zeros; any general dominance argument must be
    configuration-local (ball data), not statistical.

Artifacts: 1114_IC_recon.json committed; probe (KMAX + closure assert
+ mpmath import fix) committed. RH NOT claimed; no map change keyed.
