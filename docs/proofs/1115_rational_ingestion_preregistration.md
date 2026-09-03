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
