# 1113 - the (a,8) radius-family certified scan: cells (3,8) and (5,8)

Date: 2026-09-03 (night, post-1112).

Status: PRE-REGISTRATION, committed BEFORE the run. 1110/1112's named
next #2. The gate-top over the window class V(a,8) is pinned at
-pinning(a) = -lambda_min(Z|_V(a,8)); the two certified radii give
pin(2) = 1.4433774e-06 (1112) and pin(4) = 2.5999281e-10 (1112), i.e.
per-unit decay ratio r = (pin(4)/pin(2))^(1/2) = 1.342e-02. This scan
measures a = 3 and a = 5 on the 1112 dependency-safe interval machine,
extends the A+P = -Z identity diagnostic (1105/1110 style,
p6_weil.zero_gram with Nz=600+tail as the reference side) to the two
new radii, and books the pure-arch column of 1106 F.6 at the mid-radii
(f0.tops, same anchor-verified implementation).

## 0. Registered extrapolation (falsifiable, computed BEFORE the run)

    pin(3) = pin(2)*r = 1.937e-08  band [9.7e-09, 3.9e-08]
    pin(5) = pin(4)*r = 3.49e-12   band [1.7e-12, 7.0e-12]
    pure-arch top_arch(a=3) in (0.854, 1.781), top_arch(5) in (1.781, 3.79)
    (monotone F.6 law; identity check only - no gate).
    Falsifiers (report, do NOT patch): band violation => geometric law
    wrong, book the two realized ratios r(2->3), r(4->5) and refit;
    arch non-monotone => F.6 column contradicted at mid-radii.

## 1. Cells, constants, verdict mapping (literal, law 42)

Cell machinery = 1112 VERBATIM (arb 300-bit GL builder, vanishing rows
s = 0, 1/2, 1, von Mangoldt Lambda(q)/sqrt(q) weights law 49, true
interval box = arb rad + 8-ulp widen + TRUNC = (20+10*sum_w2)*TAU,
two FIXED-float whitening congruences read as exact rationals,
CENTER_CHOL = 4*eps entrywise comparison sums on HRAD/GRAD (fix batch 1
of 1112), positive test = entrywise diagonal dominance of the
identity-centered second-whitened box).

    (3,8): GL-512, TAU=1e-17, DELTA=4.0e-09, EPS=1e-10, VANISH_S as above
           (predicted box rad ~2.4e-14/entry; HRAD ~ 1e-11; budget at
           DELTA 4e-9 ~ 1e-2 * soft-alignment geometry => PASS-IV38
           predicted, certified top <= -1.54e-08 + EPS = -1.53e-08 < 0;
           U < 0 across the whole pin(3) band).
    (5,8): GL-512, TAU=1e-20, DELTA=7.0e-13, EPS=1e-10
           REGISTERED PREDICTION: STRADDLE-IV58. At the (4,8) realized
           box radii (~1.8e-14/entry -> HRAD ~5e-12), ANY DELTA that
           keeps U = -pin(5) + DELTA < 0 gives worst-row budget
           ~ 5*HRAD/DELTA >> 1: the pin(5) band [1.7e-12, 7e-12] sits at
           or BELOW the whitened noise floor, so a=5 lies beyond the
           CERTIFICATION HORIZON of this machine (GL-512, arb entry
           precision). The cell is still RUN: it measures pin(5) in the
           float domain (eigvalsh absolute noise ~2.6e-19 on the
           ~1e-3 pencil norm - pin(5) is ~7e6x above it), reports the
           identity diagnostic, and books the horizon.
           Falsifier: slack > 0 => (4,8)-style noise orthogonality even
           better than modeled; upgrade to PASS-IV58, book U.

    Verdict selector: PASS-IV-c iff (min slack > 0 AND U+EPS < 0).
    U >= 0 => STRADDLE-IV-c (DELTA wider than realized pin; printed,
    no cholesky attempted). Nothing else fires; float top_mid < 0 is
    reported as measurement FLOAT-NEG-c (NOT a certificate) in every
    cell.

Gates (ABORT-class, inherited literals): G-env (flint), G-coef (<=10,
shared calibration), G-width (max arb entry width <= 1e-7), G-xcheck
(symmetrized generalized route, <= 1e-12, law 53), G-contain (box
Gershgorin covers top_mid), G-reactive (s=1/2 row += 0.1 moves top by
>= 1e-6, law 54). Fix-batch protocol on any ABORT: root-cause, measure
law 54 leverage if the canary is the suspect, commit fix BEFORE rerun,
never weaken a floor.

## 2. Identity + arch columns (measurement, no gate)

Per new radius a: p6_weil.zero_gram(a, 8, Nz=600, tail=True) -> lamZ =
lambda_min(Z); D(a) = top_mid + lamZ registered diagnostic (1110
pattern: D(2) 6.40e-11, D(4) 1.558e-14 realized; band D(a) <= 1e-10
absolute - at a=5 D/pin may EXCEED 1 by design (different quadrature
machines, absolute comparison only; booked honestly, no relative
claim). f0.tops(a, 8): top_arch, min_prime columns extend the F.6
table; anchor drift check f0 vs committed F.1 anchors <= 2e-3 (1106
literal), else ABORT-ANCHOR.

## 3. Artifacts and scope

Bundle docs/proofs/1113_cert.json: same ingestion schema as 1112
(outward rational G/M full-space enclosures, U_outward, fixed whitening
data, row_slacks, verdict) for any cell that completes; the STRADDLE
cell still emits its data with verdict STRADDLE (no certificate claim
is attached to a STRADDLE box - the future ingestion brick must check
verdict before trusting PosSemidef). Runtime: (3,8) ~2 min, (5,8)
~15-25 min (2500 shifts GL-512), one process. Window classes only;
Lean gate Prop NOT discharged; I-C / Q-F2 untouched (record 1114);
a >= 6 deferred (prime-shift cost 4*sqrt(exp(2a)) ~ 14k at a=6 -
TRUNC/precision engineering or exact integration first). RH NOT
claimed; no map change keyed.

## 3b. POST-RUN ADDENDUM (run 2026-09-03 16:04-16:09, one run, zero ABORTs)

Run ledger: single clean run (~6 min total; (3,8) seconds, (5,8) ~4
min). All six inherited gates green in both cells:

    gate         (3,8)            (5,8)           budget
    G-coef       3.15e-02 (bit-identical across 1108/1110/1112/1113)  <= 10
    G-width      7.45e-16          1.24e-15        <= 1e-07
    G-xcheck     5.38e-16          7.30e-15        <= 1e-12
    G-reactive   7.72e-02          2.835e+00       >= 1e-06
    anchor drift 3.66e-07 (shared)                  <= 2e-3
    G-contain, G-env              passed both.

Verdicts (selector of §1 executed literally):

    cell   top_mid           DELTA      U            min slack   VERDICT
    (3,8)  -1.614048887e-08  4.0e-09    -1.214049e-08  +0.9785   PASS-IV38
    (5,8)  -4.425156442e-13  7.0e-13    +2.574844e-13  (skipped) STRADDLE-IV58

LANDING STATEMENT (new third certified radius):

    top(A+P)|_{V(3,8)} <= -1.2140489e-08 + 1e-10 (inherited channels)
                       = -1.204049e-08 < 0   [DEPENDENCY-SAFE interval cert]

pin(3) = 1.614049e-08 inside registered band [9.7e-09, 3.9e-08]: BAND-OK.
pin(5) = 4.425156e-13 BELOW band floor 1.7e-12 (3.8x): BAND-VIOLATION -
the registered falsifier of §0 FIRED and is booked here per protocol
(report, do NOT patch; no threshold touched):

    realized per-unit ratios  r(2->3) = 1.1183e-02   r(3->4) = 1.6108e-02
                              r(4->5) = 1.7020e-03   (fit was 1.342e-02)

The two-point geometric law survives 2->4 (r wanders 1.1-1.6e-02) but
COLLAPSES at 4->5 by another order of magnitude: the certified margin
decays SUPER-geometrically once a > 4. The STRADDLE selector fired via
the U >= 0 route (DELTA 7e-13 wider than the realized pin), not the
registered whitened-noise-floor route; slack was therefore never
attempted and (5,8) carries NO certificate claim (bundle row_slacks =
null, chol_Rc = null as registered). Direction of the surprise matters
for 1114/I-C: the horizon is CLOSER than modeled - brute-force window
certification degrades faster than the exponential that the (2,4)
pair suggested, so the function-class gap to the detector class is
wider, not narrower, than §1's estimate.

Probe print defect (post-run fix in the same commit): the pre-run
ratio guard was written as the chained comparison "pins[hi] > 0.0 >
pins[lo]" (fires only for hi>0 AND lo<0), so all three positive ratios
printed "undefined". Pure display bug - every quantity used by any
gate or verdict was untouched; the ratios above were reconstructed
arithmetically from the printed pins (and verified against the bundle
top_mid values). Fixed to "pins[hi] > 0.0 and pins[lo] > 0.0".

Identity column (§2): A+P = -Z now confirmed at FOUR radii on the
cross-machine absolute diagnostic:

    a=2  D = 6.40e-11 (1110/1105, GL-256)     a=3  D = 1.541e-14
    a=4  D = 1.558e-14 (1110)                 a=5  D = 2.044e-14

all <= 1e-10 band; the three GL-512 values agree at ~2e-14 and the
GL-256 (a=2) value is a 4000x quadrature-scale outlier (as expected -
absolute band, no relative claim, law 44 discipline).

F.6 pure-arch column (anchor-verified, measurement only):
top_arch(3) = +1.346238 in (0.854466, 1.781109) OK;
top_arch(5) = +2.198382 in (1.781109, 3.789978) OK; monotone bracket
2<3<4<5 OK (no gate fires - pure-arch has no prime term by construction).

Named next, updated: (i) rational-Cholesky ingestion brick for the
THREE PASS classes (2,8)/(3,8)/(4,8) boxes (1111 bridge is the Lean
endpoint); (ii) an a=5 re-attempt is NOT booked - pin(5) = 4.4e-13 vs
HRAD ~ 5e-12 says the whitened slack would FAIL at any U<0 DELTA, so
exact integration (or a coarser spectral truncation K < 8) must come
first; (iii) 1114 I-C recon probe (running); (iv) a >= 6 unchanged
(deferred, and now doubly so). RH NOT claimed; no map change keyed.
