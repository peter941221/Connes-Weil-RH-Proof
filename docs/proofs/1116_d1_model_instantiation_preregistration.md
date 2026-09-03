# 1116 - the D1 model detector, instantiated at k=1: first domination data point

Date: 2026-09-03 (late night, cont. 5, after 1115 landed). Status:
PRE-REGISTRATION committed BEFORE any run. MODEL record: it instantiates
and measures; it certifies nothing and claims nothing. RH NOT claimed;
no map change keyed.

## 0. Why this is the right first strike at Stage B

1114 §4(3) prescribes: build Stage B (LOCAL-ZERO-CONFIGURATION
DOMINANCE) FIRST at k=1. Every dominance certificate is a comparison
`GATE(detector square) <= sup over certified windows + error`, so the
prerequisite data point is the LEFT side for the actual pinned
construction - the D1 assembly of record 1089
(`exists_pinnedOrbitDetector_with_window_and_visiblePrimes`). No
numerical twin of that object has ever been built (the 1100b scan built
window-side top directions only; the 1114b recon used the 1086 chirp
carrier, whose route is CLOSED - it must not be recycled here). This
record builds the twin from the Lean definitions read verbatim:

    healthyUnscaledTargetNodes rho = FE-orbit{rho, 1-rho*, rho*, 1-rho}
        U {rho+1/2, 1/2, 1, 3/2}
    target values (healthyUnscaledTargetValue): rho -> 1,
        1-star rho -> -1, rho+1/2 -> -1, everything else -> 0
    selectedOwner root:  raw(s) = B(s)^(n+1) * C(s)
        B = bilateral Laplace of the base window (support (-1,1)),
        C = bilateral Laplace of the correction (support (-1,1)),
        interpolation: raw(z) = y(z) at all target nodes, raw(w) = 0
        at every ball node outside targetNodes
    source test:  g(x) = e^{x/2} * (base^{*(n+1)} convolution corr)(x)
        (halfDensityShift is the MULTIPLIER e^{x/2}, not a translation)
    square: F(x) = (g* * g)(x) = int conj(g(-t)) g(x-t) dt
    gate: archimedeanTerm(F) + finitePrimeSum(F)  (record 1089 file)
      arch = Re[(log(4pi)+gamma) F(0)
                + int_0^inf (e^{y/2}(F(y)+F(-y)) - 2 F(0)) / D(y) dy],
           D(y) = e^y (1 - e^{-y/2})^2   (SelectedWeilFormula.lean:103)
      prime = sum_{prime powers q <= ceil(e^{2 a_det})}
              vonMangoldt(q)/sqrt(q) * (F(log q) + F(-log q))

Configuration (k=1, favorable branch, copied from 1114b Part 1):
rho = (1/2 + delta, i*gamma_1), gamma_1 = 14.134725...;
n0 = 3, R = 2^4 + 2 + dist(2, rho) = 16 + 2 + sqrt((3/2-delta)^2 + T^2)
= 32.219; ball zero-nodes (counted by |z - rho| <= R): the 7 line
zeros gamma_2..gamma_8 (21.02..43.33), the conjugates 1/2 - i*gamma
with gamma <= R - T: only gamma_1 = 14.13 -> 28.27 < 32.219 (plus the
conjugate copies of rho itself: rho*, 1-rho are ball members and get
value 0 through the orbit rule), target pair rho, 1-rho*;
n = n_lo = 8 -> a_det = n + 2 = 10; visible-prime bound e^{20} =
4.85e8 - INDEPENDENTLY re-deriving 1114's declared "< 4.9e8" from the
definitions is itself a fidelity check of this section (S0-pre).

Correction basis (MODEL choice, declared): c(x) = sum_{m=0}^{M-1}
a_m x^m chi(x) on the C-infinity bump chi(x) = exp(-1/(1-x^2)) on
|x| < 1, with M = (#constraints); moment rows computed as d^m B/dz^m
by Gauss-Legendre (N = 900) at each node; mpmath dps >= 80; the
constraint count here is 17 at every scan delta (fix batch 3,
pre-run, machine-enumerated: the first registration said 16 by
conflating the gamma_1 line-zero pair {1/2 +- i*gamma_1}, which for
delta > 0 are NOT orbit members, with orbit nodes; correct split:
8 distinct orbit/target entries + 9 forced line zeros
{1/2 +- i*gamma_1} U {1/2 + i*gamma_j : j = 2..8}). The
quadratic-decay constant of the TRUE construction is existential; the
model's realized log2(max|c|) is REPORTED and compared to 1114b's
modeled log2C - mismatch is a report, not a patch target.

## 1. Gates (assertions), registered BEFORE the run

S0 (instantiation fidelity; abort-class if any fails):
  S0.1  solved correction reproduces ALL raw values:
        |raw(z_i) - y_i| <= 1e-8 * max(1,|y_i|) at every constraint
        node, computed by INDEPENDENT quadrature (different N).
  S0.2  support: chi, corr inside (-1,1); h = base^{*9} * corr inside
        (-10,10) checked on the FFT grid; F = square inside
        (-20.05, 20.05) likewise.  AMPLITUDE-RELATIVE threshold
        (max|.|outside / max|.|total <= 1e-12) - fix batch 2,
        registered BEFORE any run: the favorable-branch coefficients
        are O(1e37) (discovered at self-test stage), so an absolute
        1e-12 floor is the wrong yardstick; the relative form is the
        literal reading of "vanishes outside the support".
        Same batch: the h-reconstruction is built by centered circular
        FFT convolutions of resolved sample grids (the frequency-
        product route needed Gauss-Legendre accuracy up to xi ~ 1.8e3,
        where 900 points under-resolve by ~1.5 per wavelength and the
        aliasing corrupted the reconstruction - caught by the
        convention self-test, zero S1 data consumed), and the s-side
        raw(z) evaluations moved to mpmath dps 80 (float64 re-summation
        of 1e37-scale coefficients against O(1) values is pure
        cancellation noise).
  S0.3  PARSEVAL CROSS-CHECK (the load-bearing one): the x-side FFT
        correlation F, evaluated by bilateral Laplace at the nodes
        (quadrature), must satisfy |Fhat(z) - raw(z)*conj(raw(-z-bar))|
        / |Fhat(z)| <= 1e-6 at a probe list of >= 6 nodes including the
        target pair; this is the check that the x-side and s-side
        objects are the same function (law-16 family).

S1 (the data point, report-class, NO thresholds to pass):
  S1.1  per delta in {1/2, 1/4, 1/8, 1/16, 1/64, 1/256}: GATE(F) =
        arch + prime, each piece printed separately with the
        [0, step] first-cell handled analytically (law: 1100b's cell
        must not be dropped - here the y-integral is direct Simpson at
        step 1e-4 plus the analytic small-y series).
  S1.2  comparison table against the certified negative reach: the
        window certificate gives top(A+P)|_V(a,8) <= -pin(a) with
        pin = {1.4434e-6, 1.6140e-8, 2.5999e-10} at a = {2,3,4} -
        print GATE(F)/pin(4), GATE(F)/pin(3), GATE(F)/pin(2): the
        SIGN of the normalized margin and its delta-dependence is the
        domination-feasibility datum (does any convex combination of
        certified window forms plausibly sit above this detector form?
        A gate value >= 0 says NO at that delta, and that is the
        finding, not a failure).
  S1.3  conditioning of the 17x17 interpolation matrix (report; if
        the solver cannot reach S0.1 at dps 80, that is itself booked
        evidence that the favorable-branch n=8 point sits outside
        float-grade realizability and the pilot must move - report
        only).

Registered expectations (1114b-primed): the design INTENT of the
pinned detector is that its gate is exactly the obligation (P2), so
prior expectation is genuinely split; the informative datum is the
SIGN and the delta-scaling. A gate NEGATIVE for all deltas with a
margin >> pin(4) would mean the D1 detector at k=1 is already on the
safe side of the RH-consistent sign at model level - then the
domination search (1116b) has a target; a gate POSITIVE for any delta
means the domination lemma, if it exists, must be configuration-local
(the positive cell must be excluded by the Ford/Platt floor, i.e.,
Stage A does real work) - also a usable finding. ABORT class fires
ONLY on S0 failures (machine is wrong), never on signs.

## 2. Artifacts and run protocol

Probe: docs/proofs/1116_d1_model_probe.py (numpy + mpmath; prime
sieve to 4.85e8 via odd-only bytearray; everything else stdlib).
Run on the Linux-side mirror via the resource-aware wrapper;
acceptance = log content (S0 asserts + printed S1 tables), not exit
code. This document and the probe commit BEFORE the run; every ABORT
gets a root-caused fix batch committed before rerun; zero threshold
weakenings ever. Outputs echoed into a JSON for the addendum.

Scope: MODEL, declared, one configuration (k=1 favorable branch,
n = n_lo = 8). The transcendental semantics of the TRUE detector
(existence of the Lean correction object with quadratic decay, true
Laplace values, triple vanishing) are NOT instantiated here and NOT
claimed. What 1116 buys is the first numerical sight of the LEFT
SIDE of the Stage-B inequality for the actual pinned construction -
the object the domination search must dominate and the object whose
Lean contract 1116c will fix once the shape is seen. RH NOT claimed;
external consultation route remains dormant (in-house per the
standing directive); no map change keyed.
