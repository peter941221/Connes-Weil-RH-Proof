# 1110 - (4,8) window-class certificate on the audited float-domain machine

Date: 2026-09-03 (late night).

Status: PRE-REGISTRATION, committed BEFORE the run. 1109's named
next #1. This record adjudicates 1107's registered (4,8) preview:
lambda_min(Z_N|_V) = +2.600074418e-10, N-FLAT to 10 digits across
N = 60/120/300 - at radius 4 the zero side of the Weil formula
contributes nothing below the first zero (gamma_1 ~ 14.1 > log 18),
so Z_60 IS Z - the identity branch predicts top(A+P)|_V =
-2.600074418e-10 strictly negative. 1107 could not resolve that
depth on its float preview machine; the GL-512 interval-audited
machine registered here can, and its certification semantics are
the ones 1109's audit established (float-domain statement +
registered eps budget; NO ball-Cholesky, NO S-lemma search).

## 0. What the machine computes, and why this shape

Class: a = 4, K = 8, phi_k(u) = P_{k-1}(u/4) exp(-1/(1-(u/4)^2));
triple vanishing rows s in {0, 1/2, 1}; visible prime powers
q < e^{2a} = 2981 (~450 of them); von Mangoldt weights
Lambda(q)/sqrt(q) (law 49). Entries G, R, A, P built by GL-512
nested arb ball rules (nodes/weights as exact dyadics; arb gives a
float64-midpoint ball - law 51 - used as the entry rounding AUDIT;
the arithmetic decision is float64, law 52 semantics).

RULE TAU: the G-coef gate (same 6 reference coefficients, same
Gevrey-3/2 bound |a_l| <= 10 e^{-2 sqrt(l}) - reference integrands
are scale-invariant in x = u/a, so realized ratios must match
1108's 3.15e-02) justifies the tail from l >= 1024: with domain
lengths 8/8, registered truncation per integral TAU_48 := 1e-20
(tail estimate < 2.5e-25, 4 orders of margin).

THE CERTIFIED QUANTITY: the constrained top of the pencil,

    top_mid := lambda_max( L^-1 (B^T M B) L^-T ),
    B = null basis of float R (SVD, rank rule 1e-11 =
        f0.null_setup), L = chol(B^T G B), M = A + P.

    CLAIM (certified):  top(A+P)|_V  <=  top_mid + EPS_48,
    EPS_48 := 1e-10  (a-priori channel table, every channel audited
        live at runtime:
        (i)   GL truncation: prime channel 2 x (sum_q w_q) x TAU_48
              - sum_w PRINTED; PNT estimate sum_{p<=2981} log p/sqrt p
              ~ 2 sqrt(2981) ~ 110, times 2 plus prime powers ~ 2.3e2
              -> channel ~2.3e-18;
              arch inner/outer channels <= ~1e-18;
        (ii)  arb-ball/float64 entry rounding ~1e-15 x 64 entries
              propagated through the pencil: generalized-eigenvalue
              first-order shift <= ||dM|| + |top| ||dG|| divided by
              the G-normalization - audit prints lambda_min(G),
              sigma_min(R);
        (iii) eigh / eigvalsh backward error ~1e-13 x ||Bhat||;
        (iv)  null-space rotation under exact-vs-float R: angle
              ~ ||dR||/sigma_min(R) ~ 1e-13, top changes at second
              order for the maximizer (first-order term killed by
              stationarity) -> negligible;
        all channels wrapped by a 1e4 safety factor -> 1e-10.)

Why no S-lemma/Cholesky here: on the reduced pencil the top is a
single symmetric eigenvalue - searching multipliers (1108/1109)
buys nothing once the float null space IS the registered class
constraint, and a floating-NU T-pencil would ADD an R-rounding
channel (c*'dR.nu ~ 1e-10) comparable to the entire (4,8) pin.
The bisection theater of 1109 is absent by design: no oracle has
discretionary resolution left to exploit.

## 1. Protocol and gates (literal, law 42)

    A_R=4; K=8; N_GL=512; TAU_48=1e-20; WIDTH_BUDGET=1e-7
    LAMZ48 = 2.600074418e-10
    XCHECK_MAX = 1e-12; REACT_MIN = 1e-6

1. G-coef: as 1108 (assert worst ratio <= 10).
2. Tables: hoisted phi-node values (engineering only - matrices
   bit-identical to the un-hoisted composition); G-width gate
   <= 1e-7 (expected ~1e-14).
3. Reduced pencil top_mid (primary: chol-whitened eigh).
   G-xcheck (law-50 must-fail canary, part 1): scipy.linalg
   .eigvalsh(B^T M B, B^T G B) generalized driver - INDEPENDENT
   routine; assert |top_a - top_b| <= XCHECK_MAX, else ABORT-XCHECK.
   G-reactive (canary part 2): recompute top_a with ONE randomly
   chosen R entry sign-flipped (rng seed 1110, entry registered in
   the run as printed): the corrupted pencil's top must move by at
   least REACT_MIN - a pipeline that cannot see corrupted data is
   not computing; ABORT-REACT otherwise.
4. Audit print block: lambda_min/max(G), sigma_min(R), sum of prime
   weights, ||c*||^2 of the maximizing vector, max entry widths.
5. G-sign guard (direction fixed at pre-reg self-review - the
   first draft had the inherited -4.5e-7 bar which would have
   blocked its OWN prediction): if top_mid >= 0, exit
   STRADDLE-ZERO (no strict-negativity program exists on this
   machine; the certified bound top_mid + EPS_48 is still
   reported).

Verdict mapping (literal):
    PASS-NEG48:  top_mid < 0 AND top_mid + EPS_48 < 0.
       Certified: top(A+P)|_V <= top_mid + EPS_48 < 0 at (4,8).
       Identity diagnostic printed: D := top_mid + LAMZ48,
       flagged MET if |D| <= 2e-10, TENSION otherwise (tension
       does not flip the verdict - it books the next record's
       adjudication task).
    STRADDLE-ZERO: top_mid >= 0, or top_mid < 0 but
       top_mid + EPS_48 >= 0. Certified bound reported, strict
       negativity NOT certified at this eps level; prediction
       falsified; escalation knobs printed (which channel of the
       budget dominates at a=8 scale).
    ABORT-*: gates; fix registered before any rerun.
No FAIL branch: inability to certify negative is never refutation.

## 1b. FIX BATCH 1 (run 1: ABORT-XCHECK; committed before rerun)

Run 1 realized top_mid = -2.599918657200e-10 (inside the registered
prediction band, section 2) but the G-xcheck canary aborted:
eigvalsh(Mz,Bz) read +3.584039075737e+01, |diff| = 3.58e+01.

Root cause - the CANARY, not the pipeline: the prime-shift overlap
satisfies the exact identity B(-xi)^T = B(xi), and every visible
shift is in ONE direction (xi = log q > 0), so P^T != P and
M = A + P carries a skew part of size ~||M|| ~ 1e1. The primary
pencil_top symmetrizes after congruence (correct: the quadratic
form c^T M c depends only on (M+M^T)/2). The xcheck passed the RAW
non-symmetric Mz to scipy.linalg.eigvalsh, which reads only one
triangle and silently treats skew garbage as the matrix - hence a
result on the ||M|| scale. 1108/1109 were immune: their T-pencil
symmetrizes by construction.

Fix: compare the generalized route on the same quadratic form -
eigvalsh((Mz+Mz.T)/2, (Bz+Bz.T)/2) (Bz asymmetry is ball-level
~1e-16, symmetrized for hygiene). Gate constants and selectors
UNCHANGED (no threshold weakening, law 39/42 - this is the
canary's input contract being corrected to state the true identity
it should test). The canary remains independent: LAPACK sygvx
generalized driver vs Cholesky-whitened heev.

## 1c. FIX BATCH 2 (run 2: ABORT-REACT; committed before rerun)

Run 2 realized top_mid = -2.599918657200e-10 (inside the
prediction band), G-xcheck green at |diff| = 2.57e-18, but
ABORT-REACT: sign-flipping R[2,3] moved the top by only 1.082e-10
(< REACT_MIN 1e-6).

Root cause (diagnostic run, not speculation): the (4,8) class has
NEARLY INACTIVE CONSTRAINT ROWS -

    top|null(R)         = -2.599919e-10
    top|null(drop s=0)  = -3.815861e-13   (s=0 row: O(1e-10) leverage)
    top|null(drop s=1/2)= +7.891679e-01   (s=1/2 row: THE load-bearer)
    top|null(drop s=1)  = -9.640712e-13   (s=1 row: O(1e-10) leverage)
    top unconstrained   = +4.123968e+01

plus a clean parity split: M cross-parity block 1.55e-15, G cross
3.98e-90 (analytic zero), even-sector top +1.202e+01, odd-sector
top -1.553e-11. The rng picked an entry of the s=1 row - flipping
it moves the null space but not the top, because that row's whole
contribution to the top is at 1e-10 scale, same size as the pin
itself. The pipeline is NOT blind (dropping rows or the whole
constraint moves the top by 0.79 / 41).

Fix - change the corruption, NOT the floor (law 39): deterministic
canary = offset the s=1/2 row, R_cor[1,:] += 0.1 (every component).
The drop-row1 experiment registers its leverage at +7.9e-01, so a
0.1 shift must move the top by >> REACT_MIN; and if the pencil
ever ignored R entirely, the corrupted and true tops would
coincide at +41 and the gate still fires. rng retired. REACT_MIN
stays 1e-6.

## 2. Registered prediction (falsifiable)

top_mid in [-3.2e-10, -2.0e-10] (identity branch +- the GL machine
own ~5e-11 entry channel); G-xcheck |D| <= 1e-13 (same matrix,
two eigensolvers); identity diagnostic |top_mid + LAMZ48| <= 2e-10
MET; VERDICT PASS-NEG48 with certified top <= -(1.6e-10 .. 2.5e-10).
Falsifiers, each a booked fact: (a) top_mid > -1e-10 => the GL-512
machine pins a (4,8) top far above the Z prediction - identity
branch strained at a=4 (or GL bias larger than budget); (b)
top_mid >= 0 - would contradict 1105/1109's certified identity
lineage and force a full entry-by-entry audit like 1108's run-2
localization; (c) G-xcheck > 1e-12 => float eigensolver instability
at cond ~ ||G||/lambda_min(G) - record the condition, move the
pencil to a G-orthonormal chart in a follow-up.

## 3. Scope, environment, runtime

Window class at radius 4 only; Lean gate Prop NOT discharged; Q-F2
untouched; infinite-dimensional sign untouched; RH NOT claimed; no
map change keyed. WSL /usr/bin/python3, uv-cache flint +
.venv-probe; runtime dominated by the table build: ~(512 y + ~450
prime + 1 G + 3 R) arb-ball tables at 512^2-equivalent work,
~1.5-2 h; log local (gitignored); numbers live in this doc.
