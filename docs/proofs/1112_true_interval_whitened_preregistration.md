# 1112 - true-interval (dependency-safe) PSD certificate of the reduced pencil, both classes

Date: 2026-09-03 (night, post-1111).

Status: PRE-REGISTRATION, committed BEFORE the run. 1110's named next
#1, and the record that makes 1111's Lean bridge NON-VACUOUS on real
data. 1109's machine audit established (laws 51/52) that a python-flint
arb Schur/Cholesky walk is ball arithmetic (float64 midpoints, no
dependency tracking) and is NOT an interval certificate; this record
certifies the SAME two class statements - (2,8) and (4,8) reduced-
pencil tops - by a dependency-safe construction that never Choleskys
an uncertain matrix.

## 0. The dependency-safe mechanism (whitened congruence + Gershgorin)

The ONLY positive test is entrywise DIAGONAL DOMINANCE (a finite family
of inequalities `2 a_ii > sum_{j!=i} |a_ij|`), and it is applied AFTER
two FIXED-float congruences so the uncertain data enters only through
AFFINE maps (no nonlinear reuse - the law-52 hole cannot appear):

  1. Interval envelope. Reuse the 1108/1110 arb box builder (GL-256 for
     a=2, GL-512 for a=4, TAU registered as 1108/1110). Convert each
     arb ball (mid, rad) to a TRUE interval box [mid - w, mid + w],
     w := rad + WIDEN, WIDEN := 8 ulps of the float64 midpoint. Rationale
     (law 51): arb stores its midpoint at float64, so the 300-bit arb
     value differs from the float mid by <= 0.5 ulp, and arb rad already
     covers the per-op rounding; 8 ulps is a registered overprovision for
     the float-representation + the IV-span conversion. The box is a
     valid enclosure of the true class entry. PLUS the GL truncation
     channel: entry half-width gets TRUNC_PER_ENTRY := 20 * TAU (1108 s2
     registers <= TAU per integral; every entry is one/two nested
     integrals, 20x overprovision - this channel DOMINATES the a=2 box:
     2e-13 vs arb 5e-16).

  2. Fixed null basis + Gram whitening. B = SVD null basis of float
     R_mid (rank rule 1e-11, = 1110 / f0.null_setup), P = Bᵀ G_mid B,
     L = chol(P) (float, P PD: 1110 printed lambda_min(G), and P is G on
     the null space). The reduced whitened pencil
         Hbox := L⁻¹ (Bᵀ [M] B) L⁻ᵗ
     is AFFINE in the interval box entries of [M] (fixed float matrices
     on both sides), so Hbox is a SOUND interval matrix (each entry is an
     independent affine form of the box variables; no Schur, no division
     by an uncertain pivot). top_mid := lambda_max(L⁻¹ (Bᵀ M_mid B) L⁻ᵗ)
     (float) = the 1109/1110 realized top.

     Self-review rigor fix (pre-commit): the box half-width is
     SYMMETRIZED (w := (w + wᵗ)/2) BEFORE the congruence - the symmetric
     pencil's entry radius is exactly |C| w_sym |C|ᵗ - and the first
     draft's "+ |CMC − CMCᵗ|/2 as float-asym" term is DELETED: that
     quantity is M's TRUE skewness (one-directional prime shifts; law 53
     provenance), not rounding, and the symmetrized midpoint C(M+Mᵗ)/2Cᵗ
     already handles it. Rounding of the float congruence itself is
     covered by the CENTER_CHOL comparison-sum bound of section 1b
     (fix batch 1; a pre-commit 1e-13 scalar floor was found to be both
     under-provisioned and structurally wrong for an entrywise product-
     rounding channel - superseded BEFORE run 2, see 1b).

  3. Slack U + second fixed whitening. U := top_mid + DELTA (DELTA > 0
     registered per class, below -top_mid so U < 0). D := U I - Hbox
     (interval, affine-safe). D_mid := U I - Hbox_mid is float-PD with
     lambda_min = DELTA. Rc := chol(D_mid) (float). Second congruence
         Gbox := Rc⁻¹ [D] Rc⁻ᵗ,  midpoint EXACTLY I,
     again affine in the box => a sound interval box around the identity.

  4. Gershgorin / diagonal-dominance verdict. For each row i:
         slack_i := lower(Gbox_ii) - sum_{j != i} upper(|Gbox_ij|).
     Gbox is the affine image of D which is the affine image of [M]; if
     min_i slack_i > 0 then EVERY real matrix in the Gbox box is strictly
     diagonally dominant with positive diagonal, hence PD (row diagonally
     dominant + positive diagonal => PD, Mathlib's own
     Matrix.isPosDef_of_diagDominant). Since Gbox = Rc⁻¹ D Rc⁻ᵗ and
     Rc is fixed invertible, D is PD for every matrix in the D-box, in
     particular the TRUE D, hence lambda_max(true Hbox) <= U, hence
         CERTIFIED: top(A+P)|_V  <=  U   =  top_mid + DELTA < 0.

No interval Cholesky, no ball Schur, no sign surgery. The whole
uncertainty argument is (affine propagation) + (entrywise inequalities),
which is exactly the dependency-safe shape 1109 named.

## 1. Protocol, constants, gates (literal, law 42)

Per class c in {(2,8): N_GL=256,TAU=1e-14}, {(4,8): N_GL=512,TAU=1e-20}:

    A_R, K=8, VANISH_S=(0,1/2,1), von_mangoldt weights (law 49)
    WIDEN_ULPS = 8 ; TRUNC_PER_ENTRY = 20*TAU
    CENTER_CHOL = 4*eps_float * (|X| @ |mid| @ |Y|T) comparison-sum bound
    on the float-CENTER displacement of each affine image, added to HRAD
    and GRAD (fix batch 1; replaces the pre-commit 1e-13 floor)
    DELTA(2,8) = 4.0e-07 ;  DELTA(4,8) = 1.0e-10   (registered, U<0 both:
    U(2,8) ~ -1.04e-06, U(4,8) ~ -1.6e-10; DELTA chosen against the
    amplification formula slack ~ 1 - n_dim * rad_H / DELTA with
    rad_H ~ (TRUNC/entry radius) * ||L^-1||^2, ||L^-1||^2 ~ 1/lambda_min(G|ker)
    ~ 1.4e4..2.9e4 (1110 printed 7.06e-05 / 1108 3.53e-05))
    GD-pos:   lambda_min(P) > 0 (chol raises -> ABORT-GRAMCHOL)
    GD-domin: min_i slack_i > 0  -> PASS-IV-c ; else STRADDLE-IV-c

Gates (all ABORT-class, fix registered before rerun):
    G-env, G-coef, G-width: inherited 1108/1110 literals.
    G-xcheck (law 50 canary, INPUT CONTRACT per law 53): the reduced
        pencil is fed to scipy eigvalsh ONLY as (X+Xᵗ)/2; assert the
        Gershgorin-implied bound lambda_max(Hbox_hi) >= top_mid (the box
        must CONTAIN its own midpoint top; a box that excludes the float
        value it was built from means the enclosure is BROKEN). Realized:
        top_mid must lie in [lambda_min(Hbox_mid-side)...] - concretely
        assert upper(lambda_max of Hbox_hi matrix) >= top_mid and
        lower(lambda_max of Hbox_lo) <= top_mid, else ABORT-CONTAIN.
    G-reactive (law 50 canary, MEASURED leverage per law 54): offset the
        load-bearing s=1/2 row R_mid[:,] += 0.1, recompute top; must move
        by >= 1e-6 (proves the pipeline reads the data feeding the box).

Verdict mapping (literal):
    PASS-IV28 / PASS-IV48:  diagonal-dominance slack_i > 0 for all rows.
        Certified top <= U_c = top_mid + DELTA_c < 0 at that class,
        DEPENDENCY-SAFE (no ball arithmetic in the positive test).
        Emits a JSON artifact (1112_cert.json): rational OUTWARD-rounded
        enclosures of G,M,R (via Fraction on the box endpoints), U as an
        exact rational, DELTA, and the fixed-float B,L,Rc serialized -
        the ingestion bundle 1111's PosSemidef consumer + a future rational
        Cholesky brick will read.
    STRADDLE-IV-c: slack fails at >=1 row. Report the tightest row, the
        achieved radius, the 1/DELTA amplification; this is a REAL result
        (class not interval-certifiable at entry precision ~1e-16 with
        this DELTA), logged, not patched. NO FAIL branch (inability to
        certify is never refutation).

Registered prediction (falsifiable, recomputed after the TRUNC channel was
added to step 0 - the earlier 2e-8/5e-11 DELTA pair was inconsistent with
it, fixed pre-run, pre-completion):
    (2,8): rad_M = 20*1e-14 = 2e-13 dominates arb 4.97e-16;
           rad_H ~ 2e-13 * 2.9e4 ~ 5.8e-9; min slack ~ 1 - 5*5.8e-9/4e-7
           ~ 0.93 -> PASS-IV28 with certified top <= -1.04e-06
           (weaker NUMERICALLY than 1109's -1.442327592e-06 but
           DEPENDENCY-SAFE; the gap is the TRUNC channel, a future
           higher-N_GL or exact-integration run closes it).
    (4,8): rad_M ~ max(2e-19, arb 9.94e-16 + 8ulp) ~ 1.6e-15;
           rad_H ~ 1.6e-15 * 1.4e4 ~ 2.3e-11; slack ~ 1 - 5*2.3e-11/1e-10
           ~ -0.15 -> STRADDLE-IV48 PREDICTED: the a=4 pin (2.6e-10) does
           not leave DELTA room against its entry radius. Then (4,8)
           STAYS the float-domain certificate (1110) and only (2,8)
           upgrades - an honest bifurcation by design.
    Falsifiers: (2,8) slack < 0 => amplification model wrong, print
    ||L^-1||^2 and per-row radii and localize; (4,8) slack > 0 => model
    pessimistic, upgrade and book the real coupling.

## 1b. FIX BATCH 1 (registered pre-rerun, after run 1: PASS-IV28 +
PASS-IV48, but the registered (4,8) prediction STRADDLE was falsified
UPWARD — min slack +9.528e-01 vs predicted ~ -0.15; the pre-registered
falsifier said "model pessimistic -> upgrade and book the real
coupling", and the coupling audit found a genuine unregistered channel)

Channel audit (diagnostic recomputation from the bundle, Rc round-trip
|diff| 7.8e-17 / 1.1e-15 — the bundle is self-consistent):

  1. WHY the model was pessimistic (booked): the registered formula
  rad_G ~ rad_M * ||L-1||^2 * ||Rc-1||^2 treats the box noise as
  worst-case-aligned with the SOFT eigendirection of Dmid (the DELTA
  direction). Realized: Dmid spectra {4.0e-07, 3.2e-05, 7.3e-05, 7.9e-03,
  8.4e-02} at (2,8) and {1.0e-10, 3.7e-08, 2.7e-06, 4.9e-06, 1.2e-03} at
  (4,8) — the DELTA-isolated direction is ONE of five, and the GL-
  quadrature box noise is nearly ORTHOGONAL to the top-state direction
  (the F.5 mechanism: the top state is a Z-zero direction). Realized
  per-entry GRAD max 8.3e-02 / 4.9e-02 vs model 1.6e-01 / 2.0e+00 =
  pessimism 1.9x (2,8) / 40.6x (4,8). The verdict literals are
  unaffected (min-slack > 0 is the test either way); the PREDICTION
  model is corrected, not the gate.
  2. THE UNREGISTERED HOLE (the reason for the rerun): each affine box
  is centered at a FLOAT product (CMC_sym, Gmid), while the soundness
  chain reads the fixed float matrices as EXACT rationals — the
  displacement |float-center - exact-center| is a real channel that the
  pre-commit 1e-13 "floor" both under-provisioned (realized
  |Gmid_sym - I| = 9.5e-13 at (2,8) and 6.2e-11 at (4,8), i.e. 600x the
  floor) and structured wrongly (a scalar floor cannot bound an
  entrywise product-rounding pattern). Law-47 mirror applied: a PASS
  must survive re-derivation of its own arithmetic, so the channel is
  bounded, not waved off: CENTER_CHOL := 4 * eps_float *
  (|X| @ |mid| @ |Y|T) added to HRAD and GRAD (standard two-product
  matmul rounding bound, entrywise; realized cost ~1e-9 (2,8) / ~5e-8
  (4,8) against slack budgets 4.7e-02 - PASS survives with ~6 orders of
  margin if the bound is correct, and if it does not, that is a real
  STRADDLE).
  3. ZERO threshold changes: DELTA, EPS, canary literals, verdict
  mapping all untouched; the change strictly INCREASES radii.

## 2. Scope, environment, runtime

Window classes only; 1111's Lean PosSemidef is NOT mechanically
discharged here (the JSON is the input to a future rational-Cholesky
ingestion brick - registered OPEN in 1111 s5); the Lean gate Prop is NOT
discharged; Q-F2 / infinite-dimensional sign untouched; RH NOT claimed;
no map change keyed. WSL /usr/bin/python3 (uv-cache flint + .venv-probe).
Runtime = two table builds (GL-256 ~ minutes, GL-512 ~ 6 min) + trivial
eigh/chol tail. Log local (gitignored); numbers live in this doc.
