# 1109 - certified-optimal U by bisection on the 1108 interval machine

Date: 2026-09-03 (night, cont.).

Status: PRE-REGISTRATION, committed BEFORE the run. Record 1108
(certified top(A+P)|_V <= -4.0e-07, VERDICT PASS) named this as its
next brick #1.

## 0. Observation that makes the brick cheap

1108's registered dual optimizer returned f(NU*) = -1.443377e-06,
EXACTLY the constrained midpoint top - exact S-lemma duality, zero
duality gap. The certificate T(NU, U) := U*G - M - R^T NU - NU^T R
is INCREASING in U (d/du = G, positive definite), so for a FIXED
NU* the interval-Cholesky oracle is a monotone predicate in U and
its pass-set is an up-closed interval. Bisecting U with that
oracle returns the smallest certified upper bound reachable with
this NU* and this pivot floor.

Machine: BYTE-COPY of the committed 1108 probe at 4d955f2 through
the G-margin gate (same IV import, same GL-256 arb entries, same
TAU, same registered BFGS start set, rng seed 1108, PIVOT_FLOOR
1e-9, WIDTH_BUDGET 2e-8, TAU 1e-14) with the single-Cert section
replaced by the bisection below. Deterministic reproduction of
NU* is itself a GATE this time (G-anchor1108).

## 1. Registered constants and bisection protocol

    U_CERT     = -4.0e-07   (1108 headline; the bisection HI start)
    U_HEADLINE = -1.40e-06  (registered pass bar for the tightening)
    U_LO       = f(NU*) - 5.0e-8   (registered fail side)
    N_BISECT= 40            (range 1.043e-06 / 2^40 ~ 9.5e-19)
    BRACKET_MAX = 1e-13     (final HI-LO; wider => ABORT-BRACKETW)
    LAMZ60  = +1.443313051e-06  (diagnostic constant: full-precision
                 lambda_min(Z_60|V) from the committed p6_weil
                 zero_gram(2, 8, Nz=60, tail=False), float64)

Oracle cert_of(U): build T_int(U, NU*) exactly as 1108 section 1
step 4 (arb entries widened by 4*TAU), Moore interval Cholesky,
PASS iff all 8 pivot absmin >= 1e-9.

Protocol order (all registered, no adaptive deviation):
1. G-anchor1108: cert_of(U_CERT) must PASS (deterministic NU*
   reproduction; if not, ABORT-ANCHOR - the 1108 certificate did
   not re-run bit-stable and nothing downstream is trusted).
2. G-bracket: cert_of(U_LO) must FAIL (if it passes, the floor
   extrapolation is wrong by > 5e-8; ABORT-BRACKET, no threshold
   is ever moved to fit).
3. Bisection 40 steps on [U_LO, U_CERT] with cert_of as the
   monotone oracle.
4. Re-run cert_of(U_HI) at the end (assert; guards float
   non-monotonicity of the arb construction at the last bit).

## 2. Registered prediction (falsifiable, banked before the run)

1108's realized numbers give the pass-margin slope: min pivot
absmin 4.82e-05 at delta = U_CERT - top = 1.043e-06, ratio
4.62e-02. If pivots scale linearly in delta (they do to first
order), delta_pass ~ PIVOT_FLOOR / 4.62e-02 ~ 2.2e-08, so

    PREDICTED: VERDICT = PASS-ENCLOSED,
    U_opt = U_HI ~ -1.443377e-06 + 2.2e-08 ~ -1.4214e-06,
    tightening of the certified margin above the true top by a
    factor ~ 47x (1.043e-06 / 2.2e-08).

The distance U_opt - true_top is dominated by the REGISTERED
PIVOT_FLOOR 1e-9 (a soundness knob, not physics); a lower floor
is the obvious future lever and its failure mode remains
soundness-preserving (an interval pivot that dips below the floor
fails the certificate, it does not fake one).

## 3. Verdict mapping (literal, law 42)

- PASS-ENCLOSED: G-anchor and G-bracket both fired as registered,
  final bracket <= BRACKET_MAX, and U_HI <= -1.40e-06.
  Certified statement: top(A+P)|_V <= U_HI (report U_HI to 9
  digits), plus the diagnostic U_HI + LAMZ60 printed.
- STRADDLE-TIGHT: all gates green, bracket converged, but
  U_HI > -1.40e-06. The record then reports the certified bound
  at U_HI anyway (the HI end always certifies - it passed the
  oracle) but claims NO headline tightening; the prediction in
  section 2 is falsified and stays in the addendum.
- STRADDLE-OPEN: inherited from G-margin (no NU* clears
  -4.5e-7) - unchanged from 1108.
- ABORT-*: G-env/G-coef/G-width/G-agree inherited; plus
  ABORT-ANCHOR, ABORT-BRACKET, ABORT-BRACKETW.
No FAIL branch exists (inability to certify is never refutation,
1101/1108 precedent). RH unclaimed; diagnostics never promote.

## 4. Scope (unchanged from 1108)

Same 5-dimensional registered window class at (a = 2, K = 8),
same triple-vanishing rows R. Tightening a certified upper bound
on a numerical class functional changes NO Lean artifact and NO
map entry; the Q-F2 function-class gap, the infinite-dimensional
gate sign, and RH are all untouched. The point of the brick: the
campaign now holds an ENCLOSURE of top(A+P)|_V, which is the
object any future E0 wiring should cite - and its floor-dominated
gap to the -lambda_min(Z) identity prediction, made explicit.

Environment and execution: identical to 1108 (WSL
/usr/bin/python3, uv-cache python-flint + .venv-probe PYTHONPATH,
log local gitignored). Runtime = 1108 table build (minutes) +
42 interval Choleskys (negligible). RH unclaimed.
