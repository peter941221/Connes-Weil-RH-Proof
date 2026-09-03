# 1108 - interval-certified upper bound on the (2,8) window gate top (pre-registration)

Date: 2026-09-03.

Status: PRE-REGISTRATION, committed BEFORE the run. Records 1100b/1101
pinned the total-gate top at zero within the float/interval noise and
NAMED the certified-upper-bound machinery (law 34) as the target.
Records 1105/1106/1107 turned the Weil identity A + P = -Z into
decision-grade fact and previewed (1107, PASS) the SOS upper bound
top(A+P)|_V <= -lambda_min(Z_N) + tau_N at (2,8) with preview margin
+1.443e-06. This record replaces the float64 diagnostic machine with
an arb interval machine end-to-end and certifies, for the registered
window class below,

    CLAIM:   top(A + P)|_V  <=  U := -4.0e-07   < 0,

which makes 1108 the first record to certify a STRICTLY NEGATIVE gate
top on the triple-vanishing window space (no eigenvalue-sign surgery:
the S-lemma certificate below replaces both the sign resolution and,
in this v1 scope, the explicit SOS decomposition - the interval
machine computes A, P, G, R themselves, so the f0 quadrature bias of
~4.6e-7 that forced the identity detour in 1107 never enters).

Scope discipline: window-class functional under the 1100/1101
registered conventions (radius a = 2, root-orbit W_0; basis K = 8;
triple vanishing s in {0, 1/2, 1}; visible prime powers q < e^{2a}).
NOT a proof of the Lean gate Prop for any detector; the Q-F2
function-class gap is untouched; RH is not claimed; no map change is
keyed to any branch of this record.

## 1. Certified chain (what the machine proves, line by line)

Raw basis phi_k(u) = P_{k-1}(u/a) * bump(u/a), k = 1..8, bump(x) =
exp(-1/(1-x^2)) on |x| < 1 else 0; all interval-evaluable in closed
form with arb (python-flint), global precision 300 bits.

1. Interval entries (directed rounding, rule sum arb-exact):
   G_ij = int phi_i phi_j                       (8x8, Gram)
   R_si = int phi_i e^{s t}, s in {0,1/2,1}     (3x8, moments)
   P_ij = 2 sum_q (Lambda(q) / sqrt q) int phi_i(t) phi_j(t + log q) dt
   (visible q < e^{2a}, shift log q, weight von Mangoldt Lambda(q)/sqrt q
    = log p / sqrt q for q = p^k - the f0.lam_sieve convention; run-1
    localization caught my first derivation mis-weighting prime powers
    by k, 0.204 at P00; fix batch 2)
   A_ij via pair table B_kl(y) = int phi_k(t) phi_l(t - y) dt and
   arch(f) = C_ARCH F0 + int_0^{2a} [e^{y/2}(F(y)+F(-y)) - 2 F0] /
             (2 sinh y) dy + F0 * log tanh(a)     (tail closed form)
   M := A + P.
2. S-lemma certificate (exact duality for one quadratic constraint +
   linear equalities - trust-region family; G ≻ 0 gives Slater):

   CLAIM(U)  <=>  exists NU in R^{8x3}:
        T(NU) := U*G - M - R^T NU - NU^T R   is POSITIVE SEMIDEFINITE.

   (For c with Rc = 0: c'Tc = c'(UG - M)c, and c'Gc = ||h||^2, so T
   PSD on the whole space proves the constrained bound for EVERY
   exactly-triple-vanishing h in the window span - the exact null
   space, no basis perturbation, no approximate-membership bookkeeping.)
3. Candidate NU: float midpoint pencil; gradient L-BFGS on
   f(NU) = lambda_max(L^{-1}(M + R^T NU + NU^T R)L^{-T}), L =
   chol(G_mid); analytic gradient 2*(R_s ytilde)(ytilde_t), ytilde =
   L^{-T}u. REGISTERED FIXED START SET (best kept; no adaptive
   re-registration): zeros; the KKT warm start solving
   (R^T NU + NU^T R) c* = (lam0 G - M) c* for the top pencil pair by
   least squares; three jittered restarts 1e-2*N(0,1) on the warm
   start (rng seed 1108).
4. Interval verdict: every T_int entry is the arb enclosure widened
   by 4*TAU (truncation contribution; arb widths alone carry rounding
   only). Moore-style recursive interval Cholesky of that T_int(NU*):
   every pivot interval must have absmin >= 1e-9; if all 8 pivots
   pass, EVERY matrix in the interval enclosure is PD, hence the TRUE
   T is PD, hence top(A+P)|_V <= U is certified.

## 2. Registered truncation and arithmetic bounds (literal)

- GL rule: n = 256 nodes per integral; nodes/weights are float64
  roots taken as EXACT dyadics - the rule is then a closed interval
  expression; the only gap is rule-vs-integral truncation.
- G-coef (calibration, run-time asserted): Chebyshev coefficients
  a_l = (2/pi) int_0^pi g(cos th) cos(l th) dth of two class
  representatives g = bump * P_7^2 and bump * P_5 * P_7 at degrees
  l in {100, 200, 300}, mpmath dps=40: ASSERT
  max |a_l| * e^{2 sqrt(l)} <= 10 (the Gevrey-3/2 flat-endpoint
  coefficient decay class shared by every integrand in this record:
  inner bump x polynomial products, and the outer y-integrand whose
  kernel 1/(2 sinh y) poles at i*pi*k admit ellipse rho = 1.5, so the
  endpoint bump decay dominates).
- Registered truncation: every GL(256) rule error <= TAU := 1e-14:
  |int - rule| <= 2a*pi*2*sum_{l >= 512} |a_l| <= 4*pi*20*e^{-45.25}
  *25 < 1e-14 using the asserted class bound.
  Any width in a matrix entry above 2e-8 => ABORT-BUDGET (bug, not
  physics).
- C_ARCH, log, exp, sin, cos, sinh all arb; Euler constant and pi
  from the 1101 105-digit strings via the imported IV wrapper.

## 3. Gates (all ABORT-class, pre-registered literals)

- G-env:    python-flint import + arb transcendental check (inherited
            from the imported 1101 module top level).
- G-coef:   as section 2.
- G-width:  max entry width of G, R, A, P, M <= 2e-8.
- G-margin: f(NU*) from the MIDPOINT pencil <= -4.5e-7 (candidate
            must clear U by 5e-8 of float margin before the interval
            check is asked to do work).
- G-agree (diagnostic, not a gate): float raw-basis top printed next
            to the f0 null-basis anchor -9.773e-07; expected |diff|
            <= 2e-6 (the f0 arch-kernel quadrature bias is the
            quantity under test - a large DIFFERENCE IS THE NEWS, so
            only |diff| > 1e-2 aborts as implementation failure).

## 4. Verdict mapping (literal, law 42)

- PASS:      interval Cholesky of T_int(NU*) fully green =>
             top(A+P)|_V <= -4.0e-07 CERTIFIED.
- STRADDLE-OPEN: no NU* passes G-margin, or interval Cholesky fails
             while all widths <= 1e-16 (dependency overestimate):
             print lambda_hat_float, pivot widths, best f(NU); no
             certified statement either way.
- ABORT-*:   any section-3 gate; verdict withheld, fix registered
             before any rerun (1101 procedure).
No branch claims or refutes RH-direction content beyond the window
class; a FAIL-style outcome is NOT defined (inability to certify is
STRADDLE-OPEN, per 1101 precedent).

## 5. Environment and execution

probe 1108_certified_sos_top_probe.py; WSL-side /usr/bin/python3 with
PYTHONPATH = uv-cache python-flint archive + .venv-probe
site-packages (numpy/scipy/mpmath); IV imported VERBATIM from the
committed 1101 probe module (zero transcription). Runtime minutes
expected (36 pair tables x 256 inner x 256 outer arb nodes). Log
local (gitignored); numbers live in this doc's post-run addendum.
RH unclaimed.

## 6. Post-run addendum (2026-09-03 night) - VERDICT: PASS

HEAD at run time: 4d955f2 (fix batch 2). Run 3 was green on first
execution with both fix batches. The headline:

    top(A+P)|_V  <=  -4.0e-07   CERTIFIED on the (2,8) window class.

First strictly negative CERTIFIED gate top in the campaign (1101
could only certify the +/-9.68e-08 straddle band; the law-34
"certified-upper-bound machinery" named there is now landed).

Realized vs registered (literal):

    +------------+---------------------+------------------------------+
    | gate       | registered          | realized                     |
    +------------+---------------------+------------------------------+
    | G-coef     | worst ratio <= 10   | 3.15e-02 (l=100; 300x room) |
    | G-width    | <= 2e-8             | 4.97e-16                     |
    | G-margin   | f(NU*) <= -4.5e-7   | -1.443377e-06 (3.2x clear)   |
    | G-agree    | no abort <= 1e-2    | diff -4.66e-07 (see below)   |
    | Cholesky   | 8 pivots >= 1e-9    | min absmin 4.82e-05 (4.8e4x) |
    +------------+---------------------+------------------------------+

Run ledger (ABORTs honored, zero threshold weakenings, 1101
procedure):

- run 1  ABORT-AGREE (+1.079e+01): the G-agree diagnostic computed
         the UNCONSTRAINED raw pencil instead of the constrained
         top. Fix batch 1 (e691488, committed before rerun): SVD
         null-basis reduced pencil, same rank rule as
         f0.null_setup.
- run 2  ABORT-AGREE (constrained top +0.381 vs anchor -9.773e-07):
         localized by per-block 30-digit mpmath recomputation
         against the f0 anchor machine - G00/A00/R00 matched to 8
         digits; P00 alone was off by 0.204 (mine 1.18350217 vs f0
         0.97972861). Root cause: prime-power weights must be von
         Mangoldt Lambda(q)/sqrt(q) = log p / sqrt q at q = p^k
         (the f0.lam_sieve convention); my derivation used
         log q / sqrt q, over-weighting prime powers by k. Fix
         batch 2 (4d955f2) + convention registered in section 1.
- run 3  PASS (this addendum).

Identity reconciliation (the cross-construction 1107 named next):
the certified machine's midpoint constrained top -1.443377e-06
matches the INDEPENDENT zero-Gram prediction - lambda_min(Z_60|V)
full precision = +1.443313051e-06 (committed
p6_weil.zero_gram(2, 8, Nz=60, tail=False), float64):

    |top_arb + lambda_min(Z_60)| = 6.395e-11   (4.4e-05 relative)

Two independent machines - interval-GL arb pencil vs float Simpson
zero-Gram - agree on top(A+P)|_V = -lambda_min(Z_60) to 4+
significant figures. Consequences:

- the 1105-1107 identity branch (A + P = -Z) is confirmed at
  certified precision;
- f0's anchor -9.773e-07 is ASSIGNED THE QUADRATURE BIAS: its
  -4.66e-07 distance from the arb midpoint equals the 4.6e-07
  residual 1107 predicted between lambda_min(Z_60) and the
  f0-biased pin depth;
- the true pin depth of the registered (2,8) class is
  1.4433e-06, not 9.773e-07 (1107's lambda_min flatness across
  N = 60/120/300 stands; f0's top was the biased side -
  a correction to how 1105's "true pin depth" phrasing should be
  read);
- the S-lemma certificate needed NEITHER mu-sign surgery NOR the
  explicit Z route: the dual multiplier NU* absorbed the whole job
  (f(NU*) = -1.443377e-06 = the constrained top itself - exact
  duality, as the trust-region S-lemma guarantees).

Scope caveats (unchanged from the header): the claim covers the
5-dimensional registered window class (Legendre x bump, K = 8) at
radius a = 2. It does NOT discharge the Lean gate Prop for any
detector, does NOT touch the Q-F2 function-class gap, and is
consistent with 1100b/1101 - their near-zero total-gate tops are
suprema over DIFFERENT truncation subspaces (sine/leg families), so
the sign of the gate on the infinite-dimensional triple-vanishing
space is untouched by this record. RH is not claimed; no map change
is keyed to any branch of this record.

Named next (in order):

1. Certified-optimal U: bisection over U on the cached interval
   matrices (rebuild is minutes; Cholesky is milliseconds) - the
   largest U whose T_int(NU*_U) passes turns one certificate into a
   certified ENCLOSURE of top(A+P)|_V itself; identity predicts the
   answer to contain -1.4433e-06 within ~1e-10.
2. Same certificate at (4,8), where 1107's preview margin came in
   +2.6e-10 BELOW criterion - adjudicates float noise vs class
   geometry.
3. E0 promotion of the S-lemma certificate into Lean (user-gated:
   1105 authorized the re-registration direction; the pre-reg +
   approval for the gate itself are still owed).

RH unclaimed.
