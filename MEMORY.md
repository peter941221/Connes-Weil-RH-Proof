# MEMORY.MD

Current route snapshot + rotating change log. Compressed 2026-08-27: full
history lives in git history, `docs/proofs/`, and
`_precompress_backup_2026-08-27/`. Working rules live in `AGENTS.md`.

## Current snapshot (2026-08-27)

- Route: C1 same-owner mainline, ROOT form (`[-log 2/2, log 2/2]`); design
  record `docs/proofs/1043`. RH NOT claimed.
- Committed frontier `13bae3d`: CC20 window-operator chain landed through the
  L2-kernel quotient lift (`applyKernelLp`, proof 1043 s6g-s6v). The generic
  equation-(121) engine is complete: uniform displacement bound, weighted
  correlation fold, Fubini discharge, operator-norm adapter.
- Pending commit (working tree): s6w/s6x square-window readback leaves -
  `pairing_applyKernel_windowedDisplacementKernel_eq_weightedCorrFold` and
  `norm_pairing_applyKernel_endpointKernelOnSquare_le_of_l1Weight` give the
  concrete endpoint owner `K_I` an L1 x L2 x L2 scalar pairing bound.
- Next bricks, in order:
  1. Concrete finite-rank difference profile `K_I - T`
     (`T = lambda * rankOne phi phi`) with certified envelope feeding eq-(121).
  2. Eq-(100) slope identity + GATE 1 numeric certificate (Yoshida rational
     LDL^T, or CC20 rank-one gamma ~ 2.94355 in `13 < 4*gamma/log 2 < 17`).
  3. Universal W4b / coverage root; capstone already formal:
     `sourceRH_of_rootSupportedHealthyDetectorData_and_endpointCertificates`.
- GATE 2 (Titchmarsh/Cartwright square-form bridge): deferred, not attempted.

Settled verdicts never to re-litigate:

- Bare whole-line HS premise is FALSE for every nonzero test (`bareHS_iff_zero_test`);
  plain-window cutoff trace family is an empty producer (docs/proofs/1016).
- Pure-analysis budget ladder cannot reach the ROOT window: true zero of the
  budget expression R* ~ 1.98e-3, and B(log 2) ~ +3.9 > 0 - only the endpoint
  theorem (vanishing orthogonality) closes the gap.
- Gate 2 (arithmetic-to-spectral equality) closed via center-2 contour assembly;
  Yoshida detector existence closed as a conditional consumer on the right half.
- Numerical eigenvalues/probe floats are NEVER transported into Lean.

Provenance for GATE 1 numeric certificates: Yoshida 1992 paywalled (class
C(a) = supp phi subset [-a,a] confirmed from preview); Bombieri 2000, "Remarks
on Weil's quadratic functional I" verified it at t = log(2)/2 - full text free
at bdim.eu (local extracted text under `/home/peter/blogs/bombieri.txt`; PDF
never committed). Recheck Bombieri eq-(7.3) normalization before transcribing.

## Change Log

- 2026-08-27 AGENTS/MEMORY : compressed both files to live-route essentials;
  full prior versions backed up under `_precompress_backup_2026-08-27/`.
- 2026-08-27 README : pushed status dashboard (commit 906bbd4).
- 2026-08-27 C1CC20WindowedPairingReadback(+Audit) : s6x - concrete K_I owns
  the eq-(121) L1xL2xL2 pairing bound; audits 2698 jobs, axiom-clean.
- 2026-08-27 C1CC20WindowedDisplacementReadback(+Audit) : s6w - window
  identity `K_I f = 1_I * K(1_I * f)` at raw and a.e.-quotient level; 2695
  jobs, axiom-clean.
- 2026-08-27 C1CC20FiniteRankApproximation(+Audit) : constructed the
  normalized Fourier rank-one projections, proved their square-window kernels
  lift exactly to `rankOne`, packaged equation-(119) `T` and its shared L1
  profile, and discharged equation (120) with automatic Fubini; 2700 jobs,
  axiom-clean.  Primary CC20 DOCX readback confirms 1732 paired alpha/d values
  (with an unpaired terminal angle sentinel 1733), but a rigorous equation-(115)
  certificate still needs strict lambda data, the 11-term chi formula/remainder,
  and certified absolute-value integration.  The fixed-window feedback cost
  `C(R)` has no definition or quantitative producer in the tree, so that route
  is not yet formally closed or rejected.
- 2026-08-27 C1CC20NegativeIndex(+Audit) : proved without numerical input that
  positivity of the endpoint defect form on one linear-functional kernel
  forces every strictly negative complex subspace to have finrank at most one;
  specialized the functional to the CC20 Riesz bad direction; 3617-job paired
  batch axiom-clean.
- 2026-08-27 C1CC20EndpointSpectralOwnerGuard(+Audit) : proved the existing
  endpoint spectral owner permits arbitrary replacement of `analyticModeDeriv`
  while preserving all its other certificate fields, so it cannot honestly
  produce endpoint positivity without lower analytic laws; 3617-job paired
  batch axiom-clean.
- 2026-08-27 C1CC20EndpointAnalyticModeData(+Audit) : added the minimum genuine
  derivative owner and proved derivative uniqueness plus a negative replacement
  guard; this closes the arbitrary-derivative defect without storing endpoint
  positivity as source data; 2562-job paired build axiom-clean.
- 2026-08-27 six leaf pairs committed in five coherent commits (ff29431..
  4f00d51) after SHA-verified WSL replay audit; docs/proofs/1043 gained section
  6y : Bombieri-2000 scope-check GO at t = log 2 / 2, normalizations (7.1)-(7.5)
  captured elementary/digamma-free, Theorem 12 ruled out as a producer
  (constant -1.29 - O(1) at our window), Theorem 8/Lemma 10 flagged
  conditional-only.
- 2026-08-27 scan located (`~/bombieri_weil_qf.pdf`, out of repo, 53 pp) :
  (7.1) sign erratum fixed (MINUS between the cosines; text layer was lossy),
  K* definition and completed Lemma-10 Gram identity certified by visual read
  plus numerical triangle closure (worst 8.9e-16); doc 1043 §6y rewritten in
  place; engine README provenance refreshed to make Bombieri sec-7 the
  transcription source.
- 2026-08-27 C1BombieriSection7Readback(+Audit) : first Lean slice of the
  Bombieri sec-7 lane - bombieriK (sinc with removable value 1 at 0),
  bombieriKstar verbatim from book p.203, and the master re/im split lemma
  for K on any `a + b*I`; 1507-job build axiom-clean
  (`[propext, Classical.choice, Quot.sound]`, no sorryAx); real-arg and
  pure-imag special cases plus the (7.1)/(Lemma-10)/(7.2)-(7.5) identities
  are the next slices.
- 2026-08-27 C1BombieriSection7Symmetry(+Audit) : the general Bombieri (7.1)
  symmetry law landed - bombieriKstar_symmetryLaw (full off-diagonal closed
  form, t != 0, x != y), its scalar engine bombieri7_core, the cosine-pair
  collapse wCollapse, and the punchline corollary bombieriKstar_symmetric
  ((1/4+x^2) K*(x,y;t) = (1/4+y^2) K*(y,x;t)); 1509-job audit axiom-clean
  ([propext, Classical.choice, Quot.sound], no sorryAx); commit ce15ee3
  pushed and ls-remote verified.  binop% complex-ambient normalization block
  (numeral divisions / complex power of a cast / cast-level division) is the
  key new mechanic, recorded in doc 1043 section 7.  Lemma-10 Gram identity
  and the (7.2)-(7.5) ownership chain are the next slices.
- 2026-08-28 C1BombieriSection7Lemma10(+Audit) : the Bombieri Lemma-10 Gram
  identity landed - bombieriKstar_lemma10 (book p.210 display verbatim:
  2t K* = 2 sin(t(x-y))/(x-y) minus the two exponential-bracket correction
  terms, t != 0, x != y), the reusable quarter-turn identity
  bombieriK_I_mul (K(I*u) = sinh u / u), and the Complex.sinh defining
  bridges expBracket / sinhBracket; audit 1510 jobs, axiom-clean
  ([propext, Classical.choice, Quot.sound], no sorryAx).  Key mechanic
  recorded in doc 1043 section 7: freeze compound denominators with `set`
  BEFORE field_simp (its inner ring_nf expands inverse arguments and
  orphans the factored nonzero facts); bare ring treats inverses as
  atoms.  Next slice: the (7.2)-(7.5) ownership chain.
- 2026-08-28 C1BombieriSection7H(+Audit) : the (7.3) normalized kernel
  landed - bombieriH (H(x,y;t) = 2t K*/(1/4+y^2)), the readback
  bombieriH_mul_weight_eq, and the flagship bombieriH_symmetric
  (H(x,y;t) = H(y,x;t), t != 0, x != y): the (7.3) normalization
  symmetrizes the kernel via the (7.1) law, the entrance for the
  symmetric-matrix sign count of (7.4).  Audit 1511 jobs axiom-clean
  ([propext, Classical.choice, Quot.sound], no sorryAx).  Mechanics:
  mul_assoc is LEFT-associated (flatten with the backward rewrite);
  mul_left_comm needs explicit instantiation.  Next: (7.4)/(7.5) matrix
  layer over Fin n; z_gamma = X_rho needs a fresh book p.204 read.
- 2026-08-28 C1BombieriSection7Gamma(+Audit) : the (7.2)/(7.4)/(7.5)
  finite-Gamma matrix layer landed - bombieriWOfZ (w = (1/4+gamma^2) z),
  bombieriHMatrix + bombieriHMatrix_transpose (H(Gamma;t) symmetric),
  bombieriHMatrix_mulVec_weight (H on the weighted vector = 2t times the
  raw K*-matrix on z, i.e. (7.4) is exactly (6.4)),
  bombieriEigenvec_iff (scalar-Lambda eigenvector readback), bombieriD
  (det[I - Lam smul H]) + bombieriD_zero (D(0,t) = 1).  Leaf + audit
  1706 jobs, axiom-clean ([propext, Classical.choice, Quot.sound], no
  sorryAx).  Section-6 X_rho definition (6.1)-(6.4) transcribed into doc
  1043 section 6y from the book p.202 visual read (Lambda = 1/lambda is
  a SCALAR).  Mechanics: v4.30 Matrix.transpose notation is
  namespace-scoped; mulVec v i = sum j, M i j * v j holds by rfl (root
  dotProduct, no Matrix.dotProduct); transport h : w = ... w via
  congrArg, never rw.  Next: Lemma-10/Theorem-8 conditional sign
  detector; then K_I-T finite-rank profile toward GATE 1.
- 2026-08-28 C1BombieriSection8Boundary(+Audit) : the Lemma-10 detector
  skeleton landed - bombieriEvenOddBoundary (book p.211 even/odd boundary
  recombination: raw two-point correction = tanh(t/2)-weighted even square
  + coth(t/2)-weighted odd square) + bombieriEvenOddBoundary_nonneg
  (both weights positive for t > 0).  Book pp.209-212 read: Lemma 9
  (lambda real), Corollary (8.4) (D_N real-rooted), Lemma 10 full
  statement, chain (8.5)-(8.15) recorded in doc 1043 section 6y.
  ERRATUM 2: the p.211 bracket is the REAL-symmetric a*conj b + conj a*b,
  not the printed minus form (fails already at a = b = 1).  Leaf + audit
  1707 jobs, axiom-clean.  v4.30: Complex.conj/Complex.abs are GONE
  (use star/starRingEnd and Complex.normSq); two-stage field_simp
  (freeze atoms -> unfold defs -> push_cast -> clear inverse powers).
  Open: the analytic (8.13)/(8.14) integral steps; detector only, never
  unconditional GATE 1.

- 2026-08-28 commit 6cfcba2: slice 7a of the analytic (8.13) chain LANDED --
  C1BombieriSection8Wirtinger(+Audit): the even envelope phiEven with
  derivative and ODE phi'' = (1/4)phi, derivative transport through the
  Real->Complex cast (hasDerivAt_cast), the product-rule derivative of
  g*phi', and ibpCoreEven = the IBP core identity
  (integral of g'phi' + g(1/4)phi over [-t,t] = [g phi'] endpoints) via
  intervalIntegral.integral_eq_sub_of_hasDerivAt.  Leaf 2654 jobs, audit
  2655 jobs, 6 declarations axiom-clean, 0 sorryAx.  Mechanics: compound
  casts with single ascription get SPLIT by binop% in the complex ambient
  (use inner : Real ascription or explicit Complex.ofReal); negative
  literals need (-2 : Real) ascription or they fall through to Z; -x/2
  elaborates as (-x)/2 not x/(-2); specialization at x := -t leaves - -t
  (rw [neg_neg] at the FTA result).  Open: envelope integral R = 2 sinh t,
  Q-shift identity, Q(F) >= 0 real channel, odd-case mirror, (8.14)
  assembly; detector only, never unconditional GATE 1.

- 2026-08-28 commit 49e7fa1: slice 7b of the analytic (8.13) chain LANDED --
  C1BombieriSection8WirtingerSlice2(+Audit): pointwise square expansions
  phi^2 = e^u+2+e^-u and phi'^2 = (1/4)(e^u-2+e^-u), ibpCoreEven_zero
  (IBP core vanishes at zero endpoints -- the cross-term killer), and
  envelopeIntegralEven: (1/4)int phi^2 + int phi'^2 = e^t - e^-t
  (= 2 sinh t) over [-t,t], the R of Q(g) = Q(F) + |c|^2 R.  Leaf 2655
  jobs, audit 2656 jobs, 5 declarations axiom-clean, 0 sorryAx.
  NEW HAZARD: interval-integral notation binder AMBIGUITY -- in
  (1/4) * int f + int g the second integral is SUCKED INTO the first
  integrand (fun x => f x + int g); parenthesize every integral inside
  arithmetic; found via pp.explicit on the rw-failure dump.  Mathlib has
  NO intervalIntegral.integral_exp (use the FTA route); integral_comp_neg
  is premise-free; integral_congr takes Set.EqOn (uIcc a b).
