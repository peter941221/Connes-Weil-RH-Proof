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

FIX BATCH 1 (registered after run 1, before rerun): run 1 ended
ABORT-BRACKET - the G-bracket call PASSED at U_LO = f(NU*) - 5e-8,
where the exact T(NU*, U_LO) is PROVABLY not PSD (the constrained
maximizer c* has Rc* = 0 and c*'Tc* = U_LO - top = -5e-08). Root
cause: the inherited 1108 pivot predicate tested p.absmin() >=
floor, which is SIGN-BLIND (a strictly negative pivot interval has
absmin = endpoint nearest zero, and passes). The correct Moore
gate is POSITIVITY of every pivot: lower endpoint mid - width/2 >=
PIVOT_FLOOR. The bisection predicate, not the mathematics, was
broken; 1108's own conclusion is UNAFFECTED (see the note below
this doc's fix section: on Rc = 0 the NU term contributes zero to
the quadratic form, so the S-lemma implication holds for ANY NU,
and the anchor margin 1.04e-06 exceeds every error channel by 6
orders; the corrected anchor gate re-proves it rigorously).
Audit: the absmin hole is confined to the 1108 Cholesky section
and its 1109 copy - 1101's own certified statements use
endpoint-sign predicates (total_L > 0 / total_U < 0, lines
1448-1451) and its absmin uses are |P'| bounded away from zero
(sign-irrelevant Kantorovich requirements - semantically
correct); 1106/1107 have no Cholesky. Run 2 additionally prints
per-pivot LOWER endpoints and the float eigmin of T at anchor and
bracket (fingerprints of where the dangerous direction lives).

FIX BATCH 2 (registered after run 2, before rerun 3) - DOMAIN
CHANGE. Run 2 re-ran ABORT-BRACKET with the corrected positivity
predicate and printed the decisive fingerprints: float
eigmin(T(U_LO)) = -1.004e-09 (real: 5e4x above the float64
construction noise of the T-entries) while ALL EIGHT arb pivot lows
stayed >= 4.82e-05 at both U's - matching the exact-Cholesky
requirement that a negative eigenvalue forces a negative pivot but
contradicting the arb walk. Direct API tests on this machine
(python-flint 0.9.0): arb operations DO propagate ball radii, but
their MIDPOINTS are stored at float64 precision REGARDLESS of
flint.ctx.prec = 300, and IV.span's float conversion quantizes
sub-float radii to exact singletons. Consequence: the arb interval
entries are a valid ~1e-15 rounding audit (widths 4.97e-16 in the
log - true but COARSER than the 1e-9 direction we need to see after
Schur amplification), and no arb Schur walk in this machine can
certify positivity below ~1e-5. This retroactively bounds what the
1108 Cholesky gate ever saw: its "interval Cholesky PASS" is NOT an
independent interval certificate of PSD-ness; 1108's CONCLUSION
stands regardless (the margin U_CERT - top = 1.04e-06 is 6+ orders
above EVERY entrywise uncertainty channel ~1e-15, and on Rc = 0 the
NU term contributes zero to the quadratic form, so ANY NU carries
the S-lemma implication) - an erratum is owed to the 1108 doc at
this record's addendum time.

Rerun-3 registered protocol (supersedes section 1's oracle clause;
everything else unchanged):

    oracle cert_of(U): PASS iff float64 eigmin(T(NU*, U)) >=
        +FLOAT_FLOOR (POSITIVITY - a negative tolerance would let
        the bisection certify below the true top),
        FLOAT_FLOOR := 1e-12
    certified statement: top(A+P)|_V <= U_HI + EPS_CERT,
        EPS_CERT := 1e-9  (entry channels: arb-mid rounding ~1e-15
        + 4*TAU truncation 4e-14 per quadratic form, divided by
        lambda_min(G) ~ 0.02 - run-2's bracket fingerprint pins
        ||c*||^2 = 50 - giving ~4e-11, plus eigh backward error,
        all wrapped with 25x safety; lambda_min(G) is PRINTED as an
        audit line to verify the 0.02 figure)
    G-anchor1108:      eigmin(T(U_CERT)) >= +1e-12 (run-2 realized
                       +2.086e-08 -> PASS)
    G-bracket:         U_LO := f(NU*) - U_LO_OFF, U_LO_OFF := 1e-11
                       (supersedes the run-1/2 5.0e-8) must FAIL:
                       eigmin(U_LO) ~ -1e-11/50 = -2e-13 < 0 by
                       20x above the ~1e-14 eigmin noise -> fails
    bisection:         40 steps or float-exhausted; BRACKET_MAX
                       := 1e-11 (supersedes s1's 1e-13 - the float
                       eigmin oracle converges to its own noise
                       band ~2e-15 x ||c*||^2 ~ 1e-13, and asking a
                       53-bit predicate for 1e-13 resolution invites
                       a SPURIOUS ABORT-BRACKETW); U_HEADLINE =
                       -1.40e-06 unchanged; the arb walk +
                       enclosure stats stay as printed diagnostics
                       (they are this finding's evidence)

New registered prediction for run 3 (falsifiable): U_opt ~ f +
50*FLOAT_FLOOR ~ -1.443377e-06 + 5e-11; certified statement
top <= U_opt + 1e-9 ~ -1.4424e-06 < the -1.40e-06 bar: VERDICT
PASS-ENCLOSED with the certified margin tightened ~1000x over 1108
(1.043e-06 -> ~1.05e-09). The section-2 float-slope prediction
(2.2e-08) is FALSIFIED as written by runs 1-2 and stands recorded;
it was the arb-Schur walk's ~1e-5 resolution blind spot, not the
S-lemma, that made the old bracket test pass.

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

## 5. Post-run addendum (2026-09-03 late) - VERDICT: PASS-ENCLOSED (run 3)

HEAD at run time: fba1b80 (fix batch 2). Realized headline:

    bisection U_opt        = -1.443327592e-06  (bracket 9.5e-19)
    CERTIFIED: top(A+P)|_V <= -1.442327592e-06
               (float-domain oracle + registered budget EPS_CERT=1e-9)

which tightens 1108's -4.0e-07 bound by ~1000x (certified margin
above the true top: 1.043e-06 -> ~1.05e-09) and replaces the
campaign's only negative-certified gate number.

Prediction accounting (every registered number, literal):

    +-----------+----------------+------------------+-----------+
    | quantity  | registered     | realized         | status    |
    +-----------+----------------+------------------+-----------+
    | run-2 s2  | delta 2.2e-08  | arb walk blind   | FALSIFIED |
    | fix2 pred | f+5e-11        | f+4.94e-11       | MET       |
    | bar       | <= -1.40e-06   | -1.4433e-06      | MET       |
    | G-anchor  | eigmin>=+1e-12 | +2.086e-08       | PASS      |
    | G-bracket | must FAIL      | FAIL (-2.0e-13)  | PASS      |
    | tightening| ~1e3 x         | 9.94e2 x         | MET       |
    +-----------+----------------+------------------+-----------+

Diagnostic vs the identity: U_opt + LAMZ60 = -1.454e-11 - the
float-Z and float-GL machines' constrained tops now differ by
~4.9e-11 + registered floor; the 6.4e-11 residual sits inside the
combined entrywise budgets of BOTH float machines (Simpson v_gamma
on the Z side, TAU-widened GL on this side), consistent with 1107's
attribution of the residual to Z-side quadrature bias.

Run ledger (laws 42/46/47/50/51/52 in play):

- run 1  ABORT-BRACKET: 1108-inherited absmin pivot predicate is
         sign-blind (negative pivots pass); fix batch 1 (38f001f).
- run 2  ABORT-BRACKET: with the corrected positivity predicate the
         arb walk still missed the provably-negative direction -
         fingerprints localized it: float eigmin(T(U_LO)) =
         -1.004e-09 REAL, all eight arb pivot lows >= +4.82e-05,
         float-vs-arb Schur walks diverge by ~1e-4 on late pivots.
         Root cause (API-tested, law 51): flint arb stores midpoints
         at float64 REGARDLESS of ctx.prec, and ball arithmetic does
         not track dependency - through a Schur recursion on a
         pencil whose pivots span 1.7 -> 4.2e-08 the enclosure
         validity of the walk is LOST (law 52). Fix batch 2
         (fba1b80): oracle = float eigmin >= +1e-12 (POSITIVITY; a
         negative tolerance would certify below the top and was
         caught at design review), EPS_CERT = 1e-9 budget, U_LO_OFF
         1e-11, BRACKET_MAX 1e-11 (a 53-bit predicate asked for
         1e-13 would self-abort spuriously).
- run 3  PASS-ENCLOSED (this addendum).

EPS_CERT derivation (audited, not waved): the certified entrywise
channel is GL-rule-vs-float-midpoint (arb ball widths 4.97e-16 +
span rounding) + 4*TAU truncation widening + summing 24 prime / 256
arch terms + eigh backward error ~= 3e-12 in absolute entry units;
its effect on the constrained max scales with ||c*||^2 = 50 (run-2
fingerprint: -5e-08 eigenvalue shift -> -1.004e-09 eigmin, i.e.
G-normalized maximizer with Euclidean norm^2 50), NOT with the
worst-case 1/lambda_min(G) = 2.8e4 - the lambda_min(G) eigenvector
directions do not carry the pencil top - giving ~1.5e-10;
registered budget 1e-9 = 6.7x that. The lambda_min(G) audit line
(3.530e-05) printed as registered.

Machine audit conclusions (campaign-wide, law 51/52 follow-up):

- 1108: CONCLUSION stands (margin 1.043e-06 >> 1e-10 total error
  channel; S-lemma duality carries the bound for ANY NU since the
  NU term contributes zero on Rc = 0), but its "interval Cholesky
  PASS" label was never an interval certificate; a pointer-erratum
  is committed with this addendum.
- 1101: UNAFFECTED. Its certifications are analytic-tail dominated
  (2e-7 registered widths vs 1e-15-level midpoint effects) and its
  endpoint predicates are sign-aware; it never ran a ball-arithmetic
  Cholesky as a certificate.
- 1106/1107: no Cholesky, no arb - unaffected.
- The true-interval certificate for THIS statement (dependency-safe
  enclosure of the PSD predicate at 1e-9 gaps) needs a whitened
  congruence L_G^-1 T L_G^-T or dangerous-subspace subdivision -
  named next #2 below, its own record with its own pre-registration.

Scope: same 5-dim registered (2,8) window class as 1108; float-
domain certified statement with the registered budget above; the
Lean gate Prop is NOT discharged; Q-F2 untouched; RH unclaimed; no
map change keyed.

Named next:

1. Record 1110: (4,8) class certificate on the float-domain
   machine (1107 preview margin +2.6e-10 below criterion gets its
   float-domain adjudication; HI-ladder search registered because
   f(NU*) at a=4 is not previewed; t_table pt-hoist halves the
   ~450-shift build).
2. True-interval dependency-safe certificate of the (2,8) class
   statement (whitened congruence or 2D dangerous-subspace
   interval enclosure) - closes the "certified" label at interval
   rigor.
3. E0 Lean promotion - user-gated, unchanged.

RH unclaimed.
