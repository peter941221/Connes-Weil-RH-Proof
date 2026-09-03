# 1115 - rational-Cholesky ingestion brick: the algebraic half of Lean certification

Date: 2026-09-03 (night, cont. 4). Status: PRE-REGISTRATION committed
BEFORE any run/build. This is the brick registered OPEN in 1111 s5 and
re-named in 1112/1113 addenda: it converts the COMMITTED rational
bundles (1112_cert.json classes (2,8)/(4,8); 1113_cert.json class
(3,8)) into the Lean statement `isTopBound U G M R` of 1111
(Dev/E0SlemmaBridge.lean) WITHOUT trusting any float-computed kernel
object. RH NOT claimed; no map change keyed.

## 0. Why the chain must be rebuilt over Q

The 1112 float chain (SVD null basis Zn, float cholesky L, float Rc)
is the right epistemic instrument for DISCOVERY (it produced the
certificates) but it is a poor ingestion target: Zn spans ker(R_mid)
only to float precision, so R*K = 0 is not decidable, and the
law-55 CENTER_CHOL channel exists precisely because float centers
displace. The exact-Q chain deletes the whole class of channels:

    mid_G = (G_lo + G_hi)/2, rad_G = (G_hi - G_lo)/2   [exact Fractions]
    mid_M, rad_M likewise;  U := upper fraction of U_outward (conservative)
    R := exact rationalization of the float R_mid entries (floats ARE
         exact rationals; the SAME numbers 1112 used)
    Dmid := U*mid_G - mid_M ;  Drad := U*rad_G + rad_M  (entrywise, Q)
    K := EXACT nullspace basis of R (3x8 -> 5 columns, rational RREF)
    Dred := K^T Dmid K (5x5 Q),  Dred_rad := |K|^T Drad |K| entrywise
           (|K^T dK K| <= |K|^T |dK| |K| is the exact propagation -
            no center-drift term exists over Q)
    EXACT LDL^T over Q (NOT Cholesky - pivots would need sqrt of
    non-square rationals): Dred = L D L^T, L unit lower triangular
    (rational), D diagonal rational, pivots D_ii > 0 checked exactly.
    Whitening congruence Lam := L^-1 (unit lower inverse, rational):
    G' := Lam Dred Lam^T = D exactly diagonal;
    rad' := |Lam| Dred_rad |Lam|^T.
    positive test = entrywise DD on the whitened box corners:
        slack_i := G'_ii - rad'_ii - sum_{j != i} (|G'_ij| + rad'_ij)
                 >  0  [Q, exact]
    (surjectivity of the congruence for the PSD pullback: Lam
    invertible, so w ranges over all Q^5 as x = Lam^T w does)

Kernel closure without rank theory: W := R^T (R R^T)^-1 (exact Q when
det(R R^T) != 0 - one 3x3 check), T := [K | W] with det(T) != 0
(exact). Then R*T = [0 | I_3], so for any c with R c = 0 and c = T y:
y_low = R T y = 0, c = K y_up, i.e. c in span K - verified by two
decidable rational identities (R K = 0 and R W = I) + invertibility
of T. All hypotheses of the Lean theorem are entrywise rational
identities discharging by norm_num.

## 1. Lean side (module Dev/C1WindowRationalIngest.lean + Audit)

Lemmas to prove ONCE (generic, small):
  (L1) 2 |x y| <= x^2 + y^2; strict DD with positive diagonal =>
      PosSemidef (Gershgorin-free elementary proof, ~20 lines);
  (L2) congruence preserves PSD (Mathlib has it: PosSemidef
      IsSymmetric... use Matrix.PosSemidef.of_mul / adapt);
  (L3) kernel closure: given R (3x8 Q), K (8x5 Q), W (8x3 Q) with
      R*K = 0, R*W = I, T = [K|W] invertible: R.mulVec c = 0 ->
      exists x, c = K.mulVec x  (explicit via T⁻¹);
  (L4) the ingestion theorem: from the DD-slack hypothesis on the
      whitened box + the exact LDL^T identity L D L^T = Dred (all
      rational data):
      forall c, R.mulVec c = 0 ->
        dotProduct c (mid_M *v c) <= U * dotProduct c (mid_G *v c).
Three concrete instances (one per class) as generated data sections;
each: R*K, R*W, detT, L*L^T, and the 5 DD-slack inequalities =
norm_num on ~150 rational matrices/inequalities of ~60-digit entries.

## 2. Registered expectations and falsifiers (preprocess probe)

Expected (from 1112's float slacks + this chain being conservative in
the box-center sense but channel-free):

    (2,8): min slack ~ 0.89 (float was 0.89425 worst row)
    (3,8): min slack ~ 0.97 (float 0.97853)
    (4,8): min slack ~ 0.90 (float 0.92844)

FALSIFIER: any class with slack <= 0 in the EXACT chain -> report, do
NOT patch, do NOT proceed to the Lean brick for that class; booked
alternatives (registered in advance): (i) a second whitening iteration
over Q on the failing corner, (ii) rebalancing the box center via the
bundle's inner data, (iii) declaring the exact-Q ingestion class-
specific and shrinking the brick to the passing classes. The (5,8)
STRADDLE cell is EXCLUDED (verdict-checked ingestion; it carries no
certificate). The transcendental side (true data in the outward box;
ker R_true vs ker R_mid) is OUT OF SCOPE here - this brick closes the
ALGEBRAIC chain from bundle to isTopBound, as registered.

## 3. Artifacts

Probe docs/proofs/1115_rational_ingestion_preprocess.py (pure stdlib
Fraction - no numpy, no float anywhere after parsing): prints per class
the 5 exact DD slacks (decimal rendering for reading only), sizes of
the rational data, det/positivity checks; writes 1115_qchain.json =
the Lean data files' source (K, W, L, L_inv, Dred, rad', slack list,
U, mid_G, mid_M as fraction strings). Runtime: seconds-minutes
(8x5 RREF + 5x5 Cholesky over Q with ~60-digit entries). If the probe
is green, the Lean build is the "run" of this record and follows the
same ABORT protocol (RED iterations root-caused, fix batches
committed before rebuild, zero threshold weakenings).

## 3b. FEASIBILITY ADDENDUM (run 2026-09-03, after fix batches 1-2)

Gate GREEN on all three classes - the exact-Q chain survives the box
geometry with NO falsifier fired. Run ledger: fix batch 1 (a4dfdfc->
18b598e): unit-lower-inverse recurrence dropped the k=j and interior
k in (j,i) terms; caught by the EXACT congruence self-check. Fix
batch 2 (cfc17b7): whitening congruence written as Lam^T Dred Lam
instead of Lam Dred Lam^T - only the latter collapses L D L^T to D;
same self-check caught it again (the self-check earned its keep twice;
the two REDs were code bugs in MY probe, not certificate geometry -
every LDL pivot was positive from the first run).

Realized exact-Q DD slacks (min over the 5 whitened rows):

    class   U            det(RR^T)   det(T)     min slack      float 1112/13
    (2,8)  -1.0434e-06   9.988e-05  -1.775e+02  +1.851287e-08  (0.89425*diag)
    (3,8)  -1.2140e-08   2.224e-02  -1.230e+01  +3.468136e-10  (0.97853*diag)
    (4,8)  -1.5999e-10   1.462e+00  -1.585e+00  +1.330538e-11  (0.92844*diag)

Reading: slack/diagonal >= 0.98 in every row of every class - over Q
the whitened box corners are dominated by their centers (the radp
channel is >= 100x smaller than d_i even in the worst entry), so the
float-domain CENTER_CHOL machinery (law-55's fix batch) has NO exact
analogue and the Lean DD test is a pure positivity check on huge
rational diagonal-dominance inequalities. All 15 inequalities + the
identities R*K=0, R*W=I, L D L^T = Dred (exact), det(T) != 0 are
norm_num-able; no threshold was ever in doubt (zero weakenings).
1115_qchain.json committed as the Lean data source. Next: the Lean
brick (generic DD lemma + kernel closure + 3 concrete instances); the
transcendental half remains out of scope as registered. RH NOT
claimed; no map change keyed.

## 3c. THEOREM-SHAPE REFINEMENT (booked after the probe, BEFORE the
Lean build; no threshold touched, mechanism strictly stronger)

The exact-Q probe revealed a fact the §0 design under-claimed: since
the MID data are exact rationals and the LDL^T pivots d_i are EXACTLY
positive rationals (all 15 printed GREEN), the CENTER of each box
carries a closed-form SUM-OF-SQUARES certificate over Q:

    U*mid_G - mid_M =: D;  K^T D K = L * diag(d) * L^T;  d_i > 0
    =>  for c in ker R (c = K x by the explicit left-inverse V and
        the E*R = A / RREF structure):  c^T D c = sum_i d_i (L^T x)_i^2 >= 0.

So the ingestion splits into two theorems per class:
  * (T-center) isTopBound U mid_G mid_M R via the exact LDL^T SOS -
      NO interval/box/whitening arithmetic in the proof at all (the
      box machinery was the DISCOVERY instrument; the certificate is
      closed-form);
  * (T-box) for all real Gt/Mt entrywise inside the rational box:
      the bound holds on ker R - via L1 (DD => PSD) applied to the
      whitened box corners, using the 5 exact slacks booked in §3b.
T-center implies the 1112 landing statement for the float-CENTER
data; T-box is the statement the transcendental half (law-34 chain)
will consume. Both are proved in Dev/C1WindowRationalIngest*.lean;
fixed shapes n = 8, m = 3, k = 5 throughout (no generic-n pain).


## 3d. POST-RUN ADDENDUM (2026-09-03 late night) - VERDICT PASS

The Lean brick landed GREEN. Acceptance triple from the landing log
(1115_Qfinal): zero `error:` lines, zero `sorryAx`, zero own warnings,
`Build completed successfully (1776 jobs)`, and all four public
declarations - the generic theorem
`C1WindowRationalIngest.isTopBound_of_closure_sos` and the instance
headlines `Q28.top`, `Q38.top`, `Q48.top` - depend on EXACTLY
[propext, Classical.choice, Quot.sound].  Zero thresholds were touched
anywhere in the campaign (law-39 honoured).

What is now certified in Lean, per class:

    class   U (rational upper of the bundle)   exact-Q min slack
    (2,8)   -1231802638776891/1180591620717411303424   +1.851287e-08
    (3,8)   -3669237615059765/302231454903654240776192 +3.468136e-10
    (4,8)   -193419435787029/1208925819614629174706176 +1.330538e-11

each proving `E0SlemmaBridge.isTopBound U G M R` through the
hypothesis-free implication mechanism of 1111 + the closed-form SOS

    c in ker R  =>  c'(U*G - M)c = sum_i d_i (L^T x)_i^2 >= 0,

with x the explicit closure witness (V *v c, from K*V + W*R = I_8) -
NO interval/ball/whitening arithmetic inside the proof; the box
machinery remains what it always was: the DISCOVERY instrument.

### RED ledger (Lean phase; probe-phase batches 1-2 live in §3b)

    batch  finding (root-caused, not patched around)
    3      PROBE FINDING, kept as DATA: raw float-domain centers are
           NOT exactly transpose-symmetric (max |M_ij - M_ji| = 7.0e-01
           / 2.5e+00 / 7.1e+00 at (2,8)/(3,8)/(4,8); G side exactly
           symmetric, 0.0).  The antisymmetric part contributes
           exactly 0 to every quadratic form (generic theorem
           `qf_transpose`), so no certificate ever emitted is
           affected; but the exact equation K^T (U G - M) K = L D L^T
           would be FALSE for the raw center.  Resolution: explicit
           symmetrization Dc := (D + D^T)/2 + the qflip - the §3c
           "T-center" shape, promoted from design note to theorem.
    4      bad import path (Mathlib.LinearAlgebra.Matrix.Notation) and
           the instance diamond: numeral-matrix smuls elaborate
           through DIFFERENT SMul instances at different file
           positions (pp.all trace: instSMulOfMul path vs module
           path), so `rw` refuses to match visually identical terms.
           Architecture fix: the smul-bearing term U • G - M is
           elaborated EXACTLY ONCE, exported as hD; every other site
           speaks of the free variable D; hDc is the ADDITIVE
           identity.  Generic module then GREEN standalone (1.2 s).
    5      concrete Q28: (i) every Fraction-division def is
           noncomputable over Real.instDivInvMonoid; (ii) norm_num
           [list] preprocessing lacks beta/Fin clean-up (fin_cases
           residues `(fun i => i) <0, _>`); (iii) unscoped
           `set_option maxHeartbeats` is REJECTED for resource
           options (the sanctioned form is `... in <decl>`).
    6-9    closure-behaviour anatomy of the 64 fin_cases foci, settled
           by measurement (each mis-shape announces itself LOUDLY):
           hKV all-simp; hD/hDK/hKDK carry arithmetic in EVERY focus
           (sequential `;` correct, the seqFocus lint demands it);
           hDc/hWR/hcl/hLd/hLdLt MIXED (some entries simp-closed, some
           bignum) - the `<;>` combinator is the only shape that
           neither errors on empty nor idles on closed.  Final shape
           map is in docs/proofs/1115_generate_lean.py (SHAPE dict),
           justified line-by-line by logs 1115_Qfull3/4/5.
    hD heartbeat: the kernel check of the numeral-equality proof over
           the 40-400-digit centers needs > 200000 heartbeats on this
           declaration ONLY (scoped raise, 2e7; every other
           declaration passes at default - measured, not guessed).

### Semantics: what this brick does and does NOT claim

IN: the ALGEBRAIC half only, as registered - committed rational bundle
data => isTopBound (1111's contract), with no float-computed kernel
object trusted (law-55's center-displacement channel and the
1108-style positivity-testing hole (law-52) are structurally absent
over Q; the DD slacks are DISCOVERY data and appear nowhere in the
proof terms - only the exact LDL^T identity and pivot positivity do).

STILL OUT (unchanged, as registered §2): the transcendental half -
true Gram data inside the outward boxes, and ker R_true vs ker R_mid -
remains the law-34 chain's own obligation (consumed by 1114's I-C
framing).  RH is NOT claimed anywhere here; no map change keyed.
