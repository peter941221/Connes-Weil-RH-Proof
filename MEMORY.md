# MEMORY.MD

Current route snapshot + rotating change log. Compressed 2026-08-27: full
history lives in git history, `docs/proofs/`, and
`_precompress_backup_2026-08-27/`. Working rules live in `AGENTS.md`.

## Current snapshot (2026-08-29)

- Route: C1 same-owner mainline, ROOT form (`[-log 2/2, log 2/2]`); design
  record `docs/proofs/1043`. RH NOT claimed.
- Committed frontier `1954294`: the Bombieri Lemma-10 DETECTOR chain has its
  finite (8.11) assembly landed - section-7 readback + (7.1) symmetry + Lemma-10
  Gram identity + (7.2)-(7.5) finite-Gamma matrix layer, and the FULL
  Wirtinger (8.13) inequality `wirtingerFull` plus its (8.11) transport
  bricks: the finite-window exponential integral (ExpSum), the (8.5)
  exponential sum `Z(u) = sum e^{-i gamma u} z_gamma` with its
  term-by-term derivative and mass expansion over Gram pairs (ExpMass),
  the Q-form readback `1/4 int|Z|^2 + int|Z'|^2 =
  sum (1/4 + gamma_i gamma_j)(z_i conj z_j) winInt` over the Gram pairs
  (QForm), the boundary bridge `sum gamma_i (gamma_i - gamma_j)
  winInt (conj z_i z_j) = (sum bfac)(sum efac) - (sum bfac')(sum efac')`
  - the rank-two factorization the Lemma-10 correction terms carry
  (BoundaryBridge), now with its public endpoint readback
  `conj(Z'(-t)) Z(-t) - conj(Z'(t)) Z(t)`, and the eigen-relation Gram transport
  `sum w conj(w) = Lam * sum_ij 2t K* z_j conj(w_i)` from the (7.4)
  premise, stated division-free in Lam (EigenGram), plus the pointwise
  Lemma-10 substitution pair: the off-diagonal `winInt`/correction split
  and the weighted diagonal identity
  `2t K*(r,r;t) = 2t - (cosh t - cos(2tr)) /
  (sinh t * (1/4 + r^2))` (KstarSubst).
- Latest verified slice: `C1BombieriSection8EndpointCorrection` factors the
  elementary correction channel of the weighted (7.1) kernel entries into
  the real-symmetric endpoint correction of (8.11).  It uses finite endpoint
  product expansion and opposite-phase pairing, so repeated ordinates remain
  valid and no Lemma-10 bracket expansion is needed.
- Latest verified total assembly: `C1BombieriSection8TotalAssembly` proves
  `KstarGram = integral qIntegrand(Z,Z') - endpointCorrection` and carries
  the (7.4) eigen-relation to that finite (8.11) right side without division
  by `Lam`.  Its output is now consumed by the endpoint/Wirtinger and
  reciprocal-sign folds.
- Latest verified Wirtinger fold: `C1BombieriSection8EndpointWirtinger`
  identifies `endpointCorrection` with the even/odd endpoint part of
  `wirtingerFull_weights`, proving `KstarGram = ofReal S` for some
  `S >= 0`.  Its output is now consumed by the reciprocal-sign fold; no
  unconditional endpoint sign is claimed.
- Latest verified reciprocal-sign fold: `C1BombieriSection8LambdaSign`
  keeps `lam : Real`, `(lam : Complex) * Lam = 1`, and `z != 0` as explicit
  premises, then proves `0 < lam` in the reciprocal branch.  A zero
  eigenvalue needs no reciprocal and remains for the Theorem-8 sign count.
- Latest verified CC20 finite-rank gap chain:
  `C1CC20FiniteRankOperatorReadback` reads the equation-(119) Fourier profile
  back as the bounded ROOT-window operator `T`; `C1CC20FiniteRankDifference`
  names `chi - tau` and proves that its lifted kernel is `K_I - T`; and
  `C1CC20FiniteRankGapCertificate` turns an independent profile `L1` mass
  certificate into the equation-(121) pairing bound, the operator-norm gap,
  and the Lemma-second rank-one consumer.  Its three fields are analytic
  regularity plus `integral norm(chi - tau) <= epsilon1`; no numerical
  equation-(115) certificate has been asserted.  The new
  `C1CC20FiniteRankLocalGapCertificate` aligns that consumer with the actual
  ROOT-local support, and `C1CC20FiniteRankHalfGapCertificate` turns CC20's
  half-window Fact-1 shape into the local certificate from ROOT-local
  `ContinuousOn` plus endpoint/finite-profile evenness.  The paired
  `plus/minus` reindexing producer is now formalized in
  `C1CC20FiniteRankProfileSymmetry`; no whole-line mass is inferred from the
  paper's local bound.
- Latest verified CC20 equation-(115) source boundary:
  `scripts/cc20_eq115/extract_source.py` validates the two CC20-linked DOCX
  artifacts by fixed SHA-256 and DOCX/XML structure, then emits the first
  1,732 angle and coefficient entries as exact rational source nodes.  The
  angle document's exact final `1733` sentinel and both unused terminal
  records are retained explicitly.  The reader rejects a swapped input before
  writing output.  It provides no strict `lambda` interval, analytic `chi`
  enclosure, or absolute-value integral.
- Latest verified CC20 gamma sandwich:
  `C1CC20GammaCoercivity` converts a symmetric row-band enclosure into lower
  and upper complex matrix-form bounds by a finite AM-GM fold.  It was forced
  to re-elaborate with its audit on 2026-08-29: zero `error:` lines, footer
  `Build completed successfully (2943 jobs)`, and only
  `[propext, Classical.choice, Quot.sound]` for all three declarations.
- Latest verified coefficient positivity:
  `C1CC20Eq115CoefficientPositivity` is generated from the exact extracted
  table as 1,732 branch-local `rfl` equations plus one `interval_cases`
  aggregation sweep.  The final `gamma5` log records its successful 1242 s
  build.
- Latest verified equation-(119) owner correction:
  the published operator sums over all integers with `d(0) = 0`; the previous
  `Fin 1732 x Bool` owner omitted `lam * e_0`.  `cc20Eq115Data` now uses
  `Option (Fin 1732 x Bool)`, fixes `none` at zero, and retains the old paired
  payload as `cc20Eq115NonzeroData`.  The audited readback is
  `T_full = lam * e_0 + T_nonzero`.  The generator reproduces the corrected
  file at SHA-256 `3059ebbd73113df0b6c09dc366827ece22756572ef7d84c9c6d09283a6282d25`.
- Latest verified Bessel scope correction:
  `C1CC20GammaBesselCoercivity` still proves the honest bound
  `q_T >= (1 - lam) * ||xi||^2`, and `C1CC20Gate1BesselDischarge` remains an
  accepted specialized branch under `lam < 1`.  CC20's reported scale is near
  `lam = 1.05158 > 1`, so these declarations do NOT discharge paper-scale
  payload (gamma).  That payload again requires the exceptional direction,
  complement spectral bound, and rank-one repair.  Final ext4 audit:
  `Build completed successfully (3649 jobs)`, zero `error:`, zero `sorryAx`;
  51 readbacks have `[propext, Classical.choice, Quot.sound]`, and the pure
  equivalence `cc20Eq115NegIndex` has `[propext]`.  The final scope-label
  cleanup keeps `lam < 1` as an explicit `_hlam1` route guard; its owner and
  audit were re-elaborated with `Build completed successfully (3633 jobs)`
  and no local unused-variable warning.  Record `docs/proofs/1050`.
- RH route judgment after the paper-scale audit:
  ROOT-window CC20 positivity is a local archimedean base case, not a density
  theorem for arbitrary supports.  The Lean coverage proposition is already
  proved equivalent to Mathlib RH once detector existence is supplied.  The
  recommended narrower global target is detector-selected semi-local
  positivity for each constructed detector and its finite visible prime set;
  this still needs new semi-local positive-trace mathematics.
- Next bricks, in order:
  1. Payload (gamma): paper-scale finite-section/Toeplitz certificates for
     exceptional overlap, complement coercivity, and the rank-one determinant.
  2. Payloads (alpha/beta): concrete prolate modes, Appendix-F tail, endpoint
     profile enclosure, and the exact Fact-1 L1 table.
  3. Payload (delta): the Theorem-7/eq-(83) same-owner trace identity plus
     eq-(99)-(104), yielding ROOT-window endpoint positivity.
  4. Detector-selected semi-local finite-prime positivity, then the landed
     `SourceRH` and Mathlib RH bridges.  Do not name the RH-equivalent coverage
     root as though it were an ordinary completeness lemma.
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
- 2026-08-28 `7dcc3bb`: Wirtinger slice 7c leaf `C1BombieriSection8WirtingerSlice3` (+Audit, 2656/2657 jobs, 0 sorryAx) — Q-shift identity qShiftEven: Q(F + c phi) = Q(F) + c conj(c) (e^t - e^-t); integral_star_interval (conj through the interval integral via root-level integral_conj + Ioc show-bridge), xIntegral_zero/conj_zero (cross killers, integral-level transport only - conj has NO HasDerivAt over R), rIntegral, qIntegrand_expansion. Mechanics: Complex.ofReal_mul/ofReal_add are cast-LEFT (merge needs backward rw); binop% lifts show-arguments containing real arithmetic into the complex ambient (use bare-variable helpers + explicit instantiation); funext lambda-have beats theorem-rw for higher-order patterns; ascribe IntervalIntegrable ... volume ... types or the measure sticks as a metavariable; noncomputable on every def with a real numeral division. Records: doc 1043 section 7 bullet. Remaining (8.13): Q(F) >= 0 real channel, odd-case mirror coth(t/2), (8.14) assembly. DETECTOR only.
- 2026-08-28 `b711bbc`: Wirtinger slice 7d leaf `C1BombieriSection8WirtingerSlice4` (+Audit, 2658 jobs, 0 sorryAx) - the real channel: qF_real (Q(F) = ofReal-cast of 1/4 * (int normSq F) + (int normSq F') via Complex.mul_conj + integral_ofReal) and sqMass_nonneg (real expression >= 0 for t >= 0). Mechanics: Complex has NO order so Q(F) >= 0 must be stated as an equality to a real cast plus a real-side nonnegativity; intervalIntegral.integral_nonneg takes TWO explicit args (a <= b, then the Set.Icc pointwise bound); Complex.continuous_normSq exists; mul_conj form: z * (starRingEnd C) z = ofReal (normSq z). Supporting: qIntegrand un-privated in Slice3. Next (8.13): even-case corollary tanh weight, odd mirror coth, (8.14) assembly. DETECTOR only.
- 2026-08-28 `a0c750f`: Wirtinger slice 7e leaf `C1BombieriSection8WirtingerSlice5` (+Audit, 2659 jobs, 0 sorryAx) - the EVEN case of (8.13): flagship wirtingerEven (for even Z, Q(Z) = ofReal(normSq(Z t) * (e^t - e^-t)/phiEven(t)^2 + S) with S >= 0) via c := Z(t)/phiEven(t), F = Z - c phi (even remainder vanishing at +-t) + qShiftEven + real channel; phiEven_even/phiEven_ne_zero; tanhHalf_eq_ratio. Mechanics: Real.tanh x is DEFINED as (Complex.tanh x).re in v4.30 - unfold destroys the goal, use Real.tanh_eq_sinh_div_cosh; import Mathlib.Analysis.SpecialFunctions.Trigonometric is GONE, hyperbolics live in Mathlib.Analysis.Complex.Trigonometric; field_simp leaves ring-closable residues. Next: odd mirror (coth weight, phi- = e^{u/2} - e^{-u/2}), then (8.14) assembly. DETECTOR only.
- 2026-08-28 `d748827`: Wirtinger slice 7f leaf `C1BombieriSection8WirtingerSlice6` (+Audit, 2658/2659 jobs, 0 sorryAx) - the ODD envelope core: phiOdd = e^{u/2} - e^{-u/2}, phiOddDeriv = 1/2(e^{u/2}+e^{-u/2}), phiOdd_ode ((phi_-)')' = (1/4) phi_-, square expansions phi_-^2 = e^u-2+e^-u / phi_-'^2 = (1/4)(e^u+2+e^-u), ibpCoreOdd + ibpCoreOdd_zero (IBP mirror), envelopeIntegralOdd: (1/4)int phi_-^2 + int phi_-'^2 = e^t - e^-t - the SAME constant R as the even case (the +-2 t-terms cancel). First build clean; the ring-failure text in the log tail was INFO-level (zero error lines). Next: qShiftOdd + wirtingerOdd. DETECTOR only.
- 2026-08-28 `78db13c`: Wirtinger slice 7g leaf `C1BombieriSection8WirtingerSlice7` (+Audit, 2660 jobs, 0 sorryAx) - the ODD case of (8.13), completing the even/odd pair: qShiftOdd (Q(F + c phi_-) = Q(F) + c conj(c) (e^t - e^-t), Q-integrand parity-independent), flagship wirtingerOdd (odd Z, t > 0: Q(Z) = ofReal(normSq(Z t) * (e^t - e^-t)/phiOdd(t)^2 + S), S >= 0), coshHalf_div_sinhHalf_eq_ratio ((e^t - e^-t)/(e^{t/2}-e^{-t/2})^2 = cosh(t/2)/sinh(t/2) = the book's coth(t/2); Mathlib v4.30 has NO Real.coth anywhere - state through cosh/sinh). NEW MECHANICS: (1) weight identity needs explicit difference-of-squares hfac BEFORE field_simp - otherwise residuals carry (a-b)^2-inverse and (a-b)-inverse as DISTINCT ring atoms that never cancel; (2) in the odd-endpoint hypothesis, rw phiOdd_odd puts the negation INSIDE the cast (ofReal (-phiOdd t)) - Complex.ofReal_neg must pull it out before field_simp (ring treats the two casts as different atoms). Next (8.13): (8.14) assembly over the eigenvalue equation, then Thm 8 sign count. DETECTOR only.
- 2026-08-28 `617e707`: parity-split pairing FIX — qSplit's second slot swapped to the TRUE derivatives (even part <-> (Zp - Zp*neg)/2, odd part <-> (Zp + Zp*neg)/2); parallelogram algebra symmetric in the fp pairing but only the cross pairing feeds wirtingerEven/wirtingerOdd; 2661 jobs, axiom-clean.
- 2026-08-28 `3e769f6`: Wirtinger slice 9 leaf `C1BombieriSection8WirtingerFull` (+Audit, 2663 jobs, 0 sorryAx) - the FULL (8.13): flagship wirtingerFull (Q(Z) = ofReal(R/phi+^2 |Z+(t)|^2 + R/phi-^2 |Z-(t)|^2 + S), S >= 0, via qSplit + wirtingerEven on Z+ + wirtingerOdd on Z-) and wirtingerFull_weights (tanh(t/2) + coth(t/2) weights, book-verbatim). NEW MECHANICS: outer C-valued => reflection chain rule is HasDerivAt.scomp (plain .comp needs outer on the algebra K'), derivative arrives as SMUL (-1:R). Zp(-u) bridged by neg_one_smul; HasDerivAt.div_const's constant is in the TARGET space (2 : C); rw-instantiated RHSs arrive beta-reduced (drop the simp only [] - it errors "made no progress"); linter.style.show FLAGS show-as-defeq-change as ERROR (use simp only [] for beta); import closure of Slice6/7 chain EXCLUDES Slice5 - import WirtingerSlice5 explicitly for wirtingerEven. Next: (8.11) transport onto the (8.5) exponential sum, lambda >= 0 assembly, exponential independence, Thm 8 sign count. DETECTOR only.
- 2026-08-28 `5465468`: Wirtinger slice 10 leaf `C1BombieriSection8ExpSum` (+Audit, 2665 jobs, 0 sorryAx) - the finite-window exponential integral: integral_exp_i_window (int_{-t}^{t} e^{i*theta*u} du = ofReal(2 sin(theta*t)/theta), theta != 0) + theta=0 diagonal 2t - the integral readback of the Gram identity's sinc term, engine of the (8.10)->(8.11) step. Route: real channel, NO complex division - exp_mul_I Euler split, cos half by real FTA with sin(theta*u)/theta antiderivative (theta divided INSIDE - no integral-linearity node-mismatch), sin half odd via integral_symmetry_half_real (local real mirror - the landed integral_symmetry_half is C-valued and binop% silently lifts real inputs through a cast). NEW MECHANICS: Real.hasDerivAt_sin/cos live in Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv - NOT in the closure of Analysis.Complex.Trigonometric, import explicitly; integral_eq_sub_of_hasDerivAt's 2nd arg is IntervalIntegrable f' (integrability of the DERIVATIVE, not continuity); mul_neg is now stated a * -b = -(a * b) (forward direction); integral_const_mul takes NO integrability premise; Complex.real_smul bridges the algebra smul in integral_const's (b-a) . c (root smul_eq_mul is Mul.toSMul-only); bare mul_comm hits the first mul in traversal order possibly INSIDE a cast - close Euler-split tails with ring. Next: (8.5) exponential sum over Fin n, then the Gram-quadratic readback lambda*sum|w|^2 = Q(Z) - boundary, then the >= 0 assembly. DETECTOR only.
- 2026-08-28 `a3f49e3`: Wirtinger slice 11 leaf `C1BombieriSection8ExpMass` (+Audit, 11 declarations, 0 sorryAx) - the (8.5) exponential sum Z(u) = sum e^{-i*gamma*u} z_gamma (noncomputable def expSum in single-cast form), its term-by-term HasDerivAt.sum derivative (coefficient vector becomes w_i = (-i*gamma_i) . z_i - the (7.4) coordinate change), and the flagship mass expansion int_{-t}^{t} (Z . conj Z) du = sum_i sum_j (z_i . conj z_j) . winInt t (gamma_j - gamma_i), with winInt unifying diagonal 2t (theta=0) and off-diagonal sinc 2 sin(theta*t)/theta - the integral readback of the Lemma-10 Gram identity's kernel. Route: conjugation via open scoped ComplexConjugate (the scope notation for starRingEnd C - map_mul/map_sum apply verbatim); expPair_mul folds each pair into e^{i(gamma_j-gamma_i)x} via mul_mul_mul_comm + exp_add; finite-sum exchange through intervalIntegral.integral_finsetSum over a NAMED per-i integrand gramPair (no higher-order patterns), per-pair window through the slice-10 case split integral_winInt. NEW MECHANICS: Complex.conj is NOT a constant in v4.30 - it is scoped notation for (starRingEnd C) in scope ComplexConjugate (write bare conj after open scoped ComplexConjugate); HasDerivAt.congr does NOT exist (environment lacks HasFDerivAtFilter.congr) - use a funext function-equality have + rw ... at h; the real name is Finset.sum_apply (Pi.sum_apply does not exist); IntervalIntegrable.sum's conclusion is the Pi-sum form (sum j, f j), not fun x => sum j, f j x - bridge with a funext hfun have (symbolic-n Pi-sum defeq stall: rw's trailing rfl may or may not close the beta, so keep the rfl optional); rw [defName] on a noncomputable def can fail "using equation theorems" - use unfold defName (which beta-reduces by itself in this context; a following simp only [] then errors "made no progress"); higher-order integral_finsetSum patterns only match with the integrand pinned as a named def plus (f := ...) named args. Next: Gram-quadratic readback lambda*sum|w|^2 = Q(Z) - boundary, then lambda >= 0 assembly, exponential independence, Thm 8 sign count. DETECTOR only.
- 2026-08-28 `81e153b`: Wirtinger slice 12a leaf `C1BombieriSection8QForm` (+Audit, 5 declarations, 0 sorryAx) - first half of the (8.11) readback: the Wirtinger Q-form of the (8.5) sum in the qIntegrand owner, over Gram pairs: 1/4 int|Z|^2 + int|Z'|^2 = sum_i sum_j (1/4 + gamma_i*gamma_j)(z_i conj z_j) winInt t (gamma_j - gamma_i), the derivative coefficient dcoef_i = (-i*gamma_i) z_i contributing gamma_i*gamma_j per pair (I * -I = 1). NEW MECHANICS: expSum continuity is FREE from hasDerivAt_expSum (differentiable implies continuous - no Pi-sum unfolding); mass continuity rides continuous_star.comp (normSq is Real-valued - cannot state the fun x => Z x * conj Z x equality); mul_mul_mul_comm needs ALL FOUR args explicit; Finset.sum_add_distrib under double sums must be applied with (s :=) (f :=) (g :=) ALL explicit - the bare higher-order pattern fails when summands mention an outer binder, and the direction must be read off the actual goal (the <-merge fires on the LEFT side, flipping the needed .symm). Next: eigen-relation assembly lambda*sum|w|^2 = Q(Z) - boundary, lambda >= 0 fold with wirtingerFull, exponential independence, Thm 8 sign count. DETECTOR only.
- 2026-08-28 `7353968`: Wirtinger slice 12b leaf `C1BombieriSection8BoundaryBridge` (+Audit, 5 declarations, 0 sorryAx) - second brick of the (8.11) readback: the weighted double sum sum_ij gamma_i*(gamma_i - gamma_j)*winInt t (gamma_j - gamma_i)*(conj z_i z_j) factors completely into rank-two boundary products (sum bfac)(sum efac) - (sum bfac')(sum efac') (flagship gamma_sin_boundaryBridge), bfac_i = (gamma_i I e^{-i gamma_i t}) conj z_i, efac_j = e^{i gamma_j t} z_j, primed = conjugate-angle variants. Engine per pair (boundaryPair): theta*winInt t theta = 2 sin(theta t) (mul_winInt_eq_sin, if-split unifying diagonal 0 with sinc), Euler half-turn -2 sin a = I(e^{ia} - e^{-ia}) (negTwoSinI), angle split e^{i(gamma_j - gamma_i) t} = e^{i gamma_j t} conj(e^{i gamma_i t}) (conj_expI), then Finset.sum_mul_sum - exactly the rank-two structure the Lemma-10 correction terms carry. NEW MECHANICS: Complex.ofReal_neg must go FORWARD to pull a negation out of a cast (the <- direction needs -↑?r which a goal with up(-x) never shows); binop% elaborates 2 * Real.sin (theta*t) / theta as 2 * (sin/theta) - division INNERMOST - so rw chains over the displayed left-assoc shape fail, robust closer is field_simp with theta != 0 in context; push_cast turns up(Real.sin (0*t)) into Complex.sin (0 * up t) via the ofReal_sin simproc (then zero_mul + Complex.sin_zero, i.e. simp, not the Real-side lemmas); the double-sum split sum sum (X - Y) = sum sum X - sum sum Y at BOTH levels goes through simp only [Finset.sum_sub_distrib] (rw cannot name the outer binder in (f :=)); a forall i j pair lemma on summands under binders again needs simp only, not rw (same lesson as 12a's dcoef_mul_conj). Next: eigen-relation assembly lambda*sum|w|^2 = Q(Z) - boundary, lambda >= 0 fold with wirtingerFull, exponential independence, Thm 8 sign count. DETECTOR only.
- 2026-08-28 `18b9b82`: Wirtinger slice 12c leaf `C1BombieriSection8EigenGram` (+Audit, 3 declarations, 0 sorryAx) - first half of the eigen-relation assembly: from the (7.4) premise w = Lam . H(Gamma;t) w (w = bombieriWOfZ gamma z) the flagship bombieriEigen_gram derives sum_i w_i conj(w_i) = Lam * sum_ij 2t K*(gamma_i,gamma_j;t) z_j conj(w_i) with conj(w_i) = (1/4 + gamma_i^2) conj(z_i) - stated DIVISION-FREE in Lam, so the lambda >= 0 fold never divides. NEW MECHANICS: the first slot of the eigen-equation is transported by congrArg (fun c => c * conj w_i) (hpc i) - an rw of the component equation rewrites the w_i inside the conjugation too (sharpest instance of the congrArg-never-rw mechanic); Finset.mul_sum is the b-on-LEFT form while Finset.sum_mul is sum-on-LEFT - distributing a post-sum factor needs the LATTER (rw [mul_assoc, Finset.sum_mul]), pulling Lam out of a sum needs mul_sum's <- direction. Next: Lemma-10 substitution (sinc channel -> Q-form + rank-two boundary products), lambda >= 0 fold with wirtingerFull, exponential independence, Thm 8 sign count. DETECTOR only.
- 2026-08-28 `0137ee5`: Wirtinger slice 12d leaf `C1BombieriSection8KstarSubst` (+Audit, 2667 jobs, 0 sorryAx) - the two entry-level Lemma-10 substitutions needed by the remaining (8.11) finite sum: `bombieriKstar_lemma10_winInt` converts the off-diagonal sinc channel to `winInt t (y-x)` minus the two bracket corrections; `bombieriKstar_twoT_diag` reads the diagonal as `2t - (cosh t - cos(2tr)) / (sinh t * (1/4+r^2))`. Important mathematical correction: the `(1/4+r^2)` factor survives after multiplying the diagonal closed form by `2t`; it cannot be dropped. Mechanics: derive `sinh t != 0` from `Real.sinh_eq` + `div_eq_zero_iff` + `Real.exp_injective`, prove the rational cancellation in Real, then use an explicit cast-normalization `hfin` rather than complex `field_simp`. Next: finite-sum assembly with slices 12a--12c, then the lambda-sign fold. DETECTOR only.
- 2026-08-28 C1BombieriSection8BoundaryBridge(+Audit) : exposed the rank-two
  boundary factors as public exponential-sum endpoint identities and proved
  `gamma_sin_boundaryEndpoint`, which reads the weighted finite double sum as
  `conj(Z'(-t)) Z(-t) - conj(Z'(t)) Z(t)`; 2668-job audit, axiom-clean,
  zero sorryAx.  This supplies the boundary input for the remaining (8.11)
  finite-sum assembly and remains DETECTOR only.
- 2026-08-28 C1BombieriSection8KernelWeights(+Audit) : proved the uniform
  weighted entry form of (7.1), including both repeated-ordinate diagonal and
  off-diagonal cases: `(1/4+x^2) 2t K*` is the Q-form `winInt` coefficient
  minus the elementary endpoint-correction coefficient.  `winInt_neg` gives
  its frequency evenness for finite-sum reindexing; 2668-job audit,
  axiom-clean, zero sorryAx.  The diagonal cancellation is proved in Real
  before one Complex cast, avoiding incompatible hyperbolic-function casts.
- 2026-08-28 C1BombieriSection8EndpointCorrection(+Audit) : factored the
  weighted (7.1) elementary correction double sum into Bombieri's exact
  (8.11) real-symmetric endpoint correction through
  `kernelEndpointCorrection_eq_endpointCorrection`; 2669-job audit,
  two declarations axiom-clean, zero sorryAx.  `expSum_endpoint_product`
  provides the reusable finite endpoint-product expansion.  The route avoids
  expanding Lemma-10's bracket factors and preserves repeated ordinates.
- 2026-08-28 C1BombieriSection8TotalAssembly(+Audit) : assembled the
  weighted (7.1) finite `K*` Gram sum into the (8.11) form
  `integral qIntegrand(Z,Z') - endpointCorrection` through
  `bombieriKstarGram_eq_qIntegrand_sub_endpointCorrection`, then transported
  the (7.4) eigen-relation through the same equality with the division-free
  `bombieriEigen_gram_total`; 2672-job audit, two declarations axiom-clean,
  zero sorryAx.  The Q-form transposition uses `winInt_neg`; the endpoint
  channel uses the cosine-symmetric correction coefficient.  DETECTOR only.
- 2026-08-28 C1BombieriSection8EndpointWirtinger(+Audit) : identified the
  (8.11) endpoint correction with the even/odd boundary in
  `wirtingerFull_weights`, yielding the nonnegative real remainder
  `integral qIntegrand - endpointCorrection = ofReal S` and therefore
  `KstarGram = ofReal S`, `S >= 0`; 2673-job audit, four declarations
  axiom-clean, zero sorryAx.  The exact weight conversion uses
  `tanh(t/2) = (exp t - 1)/(exp t + 1)` and its odd reciprocal together
  with the squared-norm-of-a-half identity.  DETECTOR only.
- 2026-08-28 C1BombieriSection8LambdaSign(+Audit) : made the reciprocal
  eigenvalue fold explicit: from the (7.4) weighted eigen-relation,
  `(lam : Complex) * Lam = 1`, and nonzero `z`, derives
  `lam * WMass = S`, `S >= 0`, then `0 <= lam` and `0 < lam` in the
  reciprocal branch; 2674-job audit, five declarations axiom-clean,
  zero sorryAx.  The realness and reciprocal relation remain caller
  premises, and the zero-eigenvalue branch is not conflated with this one.
  DETECTOR only.
- 2026-08-28 `429b747`: CC20 finite-rank gap chain LANDED --
  `C1CC20KernelLpLift` now lifts kernel addition, scalar multiplication,
  subtraction, zero, and finite sums; `C1CC20FiniteRankOperatorReadback`
  identifies the equation-(119) finite Fourier profile with its bounded
  operator `T`; `C1CC20FiniteRankDifference` identifies the named
  equation-(115) profile `chi - tau` with `K_I - T`; and
  `C1CC20FiniteRankGapCertificate` consumes only analytic regularity plus
  `integral norm(chi - tau) <= epsilon1` to derive the equation-(121) pairing
  bound, operator-norm gap, and rank-one negative-form consumer.  Forced
  3637-job audit rebuild: 31 standard-axiom lines, zero errors, zero sorryAx.
  No strict numeric profile enclosure is claimed.
- 2026-08-28 `553b30d`: CC20 equation-(115) source reader LANDED --
  `scripts/cc20_eq115/extract_source.py` validates the two paper-linked DOCX
  inputs by fixed SHA-256, DOCX/XML structure, exact 1,733-token counts, and
  the final angle sentinel `1733`; it emits the first 1,732 entries of each
  table as exact rational records with raw token and per-node source string,
  retaining both unused terminal records.  Real-source extraction emitted
  3,466 source nodes; a swapped-document test was rejected before output.
  Boundary: this validates `alpha/d` data only.  A strict `lambda` interval,
  analytic `chi` enclosure, and certified `integral |tau - chi|` remain open.
- 2026-08-28 C1CC20FiniteRankLocalGapCertificate(+Audit) and
  C1CC20FiniteRankHalfGapCertificate(+Audit) : aligned the equation-(115)
  certificate interface with CC20 Fact 1.  ROOT-local zero extension preserves
  the square-window difference kernel, while ROOT-local `ContinuousOn` and
  evenness convert
  `2 * integral_[0,log 2] |tau - chi|` into the local whole-support mass used
  by equation-(121).  Forced audits: 3635 and 3636 jobs, standard axioms only,
  zero sorryAx.
- 2026-08-28 C1CC20FiniteRankProfileSymmetry(+Audit) : formalized the paired
  finite-index `plus/minus` producer for the equation-(120) profile.  A finite
  equivalence negates `frequency` and `perturbedFrequency` while preserving
  `coefficient`; finite reindexing makes the profile even, including any
  zero-frequency fixed point.  The HalfGap adapter now requires only
  ROOT-window `ContinuousOn`, avoiding a false global-continuity obligation at
  zero-extension boundaries.  Forced 3638-job audit rebuild, standard axioms
  only, zero sorryAx.  Instantiation for the extracted table and the strict
  Fact-1 mass inequality remain open.
- 2026-08-28 scripts/cc20_eq115/data + gen_eq115_table.py : committed the two
  published eq-(115) DOCX inputs (SHA-256-pinned, extractor revalidates every
  run) and the deterministic Lean table generator; the extractor reproduces
  cc20_eq115_manifest.json byte-identically.  Provenance chain now
  DOCX -> manifest -> Lean module, all committed.
- 2026-08-28 C1CC20Eq115Table(+Audit) : generated table module - 1732 angles +
  1732 coefficients as exact rationals, initially stored as the paired nonzero
  data set `(Fin 1732 x Bool)` with sign in the Bool slot.  The missing central
  equation-(119) term was found and repaired on 2026-08-29; see proof 1050.
- 2026-08-28 C1CC20Eq115Symmetry(+Audit) : concrete negation data, profile
  evenness for every lam, ROOT-window continuity of the finite profile, and
  cc20Eq115_halfGapCertificate assembling the Fact-1 half-gap certificate
  for the extracted table - reducing it to exactly two analytic caller
  fields (chi continuity + strict mass); 6 declarations axiom-clean, zero
  sorryAx, 3640-job build.  Design record docs/proofs/1044.
- 2026-08-28 C1CC20Eq115MassBound(+Audit) : the Fact-1 strict-mass
  consumption layer - l1_uniform_grid (uniform grid + per-tile bounds
  gives delta * sum mass), l1_tail_bound (last piece ends exactly at the
  irrational log 2, symbolic tail length, no numeric evaluation), and
  cc20Eq115_halfGapCertificate_of_uniformGrid turning a grid bound table
  plus the two analytic caller fields into the full half-gap certificate;
  5 declarations axiom-clean, zero sorryAx, 3642-job batch build.  The grid
  table itself is deliberately NOT produced: the chi side needs the
  concrete endpoint enclosure (Sturm-Liouville regularity absent from
  Mathlib), and tau alone is provably not small - exact-rational
  sum_n (1 - d_n) = -114996652757599/312500000000000 gives
  tau(0) = -1.062 * lambda, so a tau-only quadrature would certify a
  useless O(lambda) bound.  Design record docs/proofs/1045.
- 2026-08-28 C1CC20Gate1Assembly(+Audit) : the GATE 1 conditional
  assembly for the CONCRETE extracted table - one entry point composing
  the grid layer into the eq-(121) operator-norm gap, the Lemma-second
  rank-one conclusion, the 13 < 4*gamma/log 2 < 17 band, and the
  slope-matched endpoint residual trace - (4a/log 2)*rank <= 0 under the
  eq-(100) trace identification; 5 declarations axiom-clean, zero
  sorryAx, 3644-job batch build.  Corrections: the gamma-weighted
  residual is NOT derivable from this chain (needs 2*ePrime >= 1) - the
  honest constant is the repair weight a.  T-side spectral judgment: the
  eq-(119) operator does NOT decouple into 2x2 blocks (sinc-type Gram
  coupling), so the coercivity block needs a certified eigenvalue
  enclosure of a 3464x3464 matrix with log-2-transcendental entries.
  GATE 1 residue is now exactly four named payloads (alpha endpoint
  enclosure, beta grid table, gamma T-spectral block, delta archimedean
  comparison).  Design record docs/proofs/1046.
- 2026-08-29 C1CC20GammaCoercivity(+Audit) : added and forced-rebuilt the
  generic symmetric-row-band AM-GM sandwich for complex matrix forms; 2943
  jobs, zero errors, and all three declarations audit to the standard axioms.
- 2026-08-29 C1CC20Eq115CoefficientPositivity +
  scripts/cc20_eq115/gen_positivity.awk : generated 1,732 exact-rational
  branch equations and a single `interval_cases` positivity sweep; final leaf
  build recorded at 1242 s.  The real nonnegativity corollary weakens first
  with `le_of_lt` before its target-directed `mod_cast`.
- 2026-08-29 C1CC20GammaBesselCoercivity(+Audit),
  C1CC20GammaBesselProbe, and probe_sinh.lean : recorded the proposed
  Fourier/Bessel coercivity route and its API probes.  Forced `gamma6` is red
  with 15 root errors; neither the Bessel claims nor its audit are accepted.
- 2026-08-29 docs/proofs/1047 and AGENTS/MEMORY : corrected the checkpoint
  record to distinguish the accepted sandwich/positivity leaves from the red
  Bessel research frontier.
- 2026-08-29 C1CC20GammaBesselCoercivity(+Audit) : repaired the RED Bessel
  theorem to accepted at its explicit `lam < 1` premises.  The later
  paper-scale audit shows this is a non-paper branch, not payload (gamma).
- 2026-08-29 C1CC20Gate1BesselDischarge(+Audit) : exhibited Bessel-compatible
  gap data and discharged `hT` only in the specialized `lam < 1` consumers;
  proof 1050 supersedes the earlier paper-facing status interpretation.
- 2026-08-29 eq-(119) owner + route audit : restored the missing `n = 0`
  summand with `Option (Fin 1732 x Bool)`, proved
  `T_full = lam * e_0 + T_nonzero`, and added the paper-scale Bessel rejection
  guard.  The first batch paid the 1131 s generated-coefficient rebuild and
  exposed two root proof errors; the second exposed one projection readback;
  final round: 3649 jobs, success footer, zero errors, zero sorryAx, standard
  axiom set.  README/AGENTS/docs 1044/1047-1050 now record that ROOT positivity
  still needs detector-selected semi-local mathematics before RH.
- 2026-08-29 C1MetricProjectionResponseGuard(+Audit) and proof 1051 : tied
  the active C1 response definition to the old Gram-corrected endpoint metric
  projection exactly (`projectionResponse = detector o (R_0 - R_S)`).  The
  one-prime expansion has a candidate one-crossing `p^2` term with coefficient
  `a^2`, versus the Euler logarithm's `a^2/2`. The response identity is
  Lean-checked; the noncompact source-Sonin channel readback remains an
  analytic premise, so the coefficient verdict is conditional. The WSL2
  focused build finished at 3161 jobs with zero errors and standard axioms
  only. This does not reject a genuinely new semilocal positive owner.
- 2026-08-29 C1ProjectionSquareCanonicalCutoffGuard(+Audit) and proof 1052 :
  promoted the existing canonical `D2` obstruction to an import-facing no-go
  guard. For every nonzero source test and trace-class fixed response, the real
  trace of `cutoffWindowToResponseDefect` cannot tend to zero; the current
  positive projection-square ledger therefore cannot close by a canonical
  residual-to-zero argument. Qualified proof 1051: its response identity is
  Lean-checked, while the factor-two `p^2` conclusion still needs a
  source-Sonin principal-channel readback. The broader semilocal search is not
  rejected.
- 2026-08-29 docs/proofs/1053_semilocal_prolate_asymptotic_hard_bone.md :
  route audit narrowed the only uneliminated RH-facing construction to an
  asymptotic, two-cutoff semilocal prolate cross-spectral trace. Fixed-cutoff
  projection and positive-multiplier owners remain rejected. Proof 1054 then
  showed that P2a is only a necessary first-order target; no conditional Lean
  producer is permitted before the coefficient-complete P2b cancellation.
- 2026-08-29 docs/proofs/1054_semilocal_prolate_second_variation_gate.md :
  exact three-point cyclic-pair calculation showed that the Poisson/logarithmic
  measure path has a strictly nonzero iterated first-harmonic second response
  after subtracting the direct `cos(2 L s)` response, even for an exactly
  prolate-normalized positive cross-spectral Hilbert-Schmidt energy. This does
  not reject a special Gamma/Meixner-Pollaczek cancellation, but it makes P2b,
  not P2a, the first coefficient-complete go/no-go gate.
- 2026-08-29 docs/proofs/1055_semilocal_p2b_verdict.md (with
  1055_semilocal_p2b_probe.py, p2b_probe_results.json, p2b_probe_run.log) :
  P2b DECIDED = DEAD. Three separable claims. (A) The harness exactly
  reproduces the 1054 counterexample (Delta = -0.354698, PASS), so generic
  QR/Toda algebra cannot cancel the iterated first-harmonic response, and no
  mechanism exists (Ong--Remling needs bounded Jacobi; CCM24 coefficients grow
  like n). (B) Decisive new finding - the gate's numerical test is itself
  infeasible at fixed precision: cyclic-vector -> Jacobi-coefficient recovery
  amplifies deep-coordinate noise by prod a_j ~ K!/K^(1/4) against a signal
  floor set by band depth 4*pi*lambda^2; the SAME base energy (g=1, two
  float representations of the identical cyclic vector) differs 39-268% at
  every tested lambda, and Lanczos coefficients exceed the truncation norm
  bound by depth 5-6. The earlier interim "iterated channel 1e3-1e8x direct,
  no lambda decay" reading is WITHDRAWN as amplifier output, not physics; the
  JSON rows carry the measured dE0 blowup label in place of that claim.
  (C) No P0/P1 self-adjoint realization exists in CCM24 (formal expression
  (5) only), so P2b as a kill test was never meaningful. Consequence: the
  last surviving global-shape candidate from 1053 is eliminated; the active
  program is exactly the four GATE 1 paper-scale payloads plus the
  detector-selected semi-local step, and no probe/owner may reference the
  prolate family until a proved realization + analytic one-crossing identity
  exist (verdict section 5 revival conditions). AGENTS 7c gains laws (8) and
  (9) from this round; 7d replaces the P2b warning with the closure.
- 2026-08-30 C1ProlateResponseTraceLegalityUnitScale(+Audit) : brick #1 of the
  Option-C semi-local bridge landed as a green leaf with its two analytic cruxes
  bracketed. The Gate-2 readback premise `hresponse` (trace legality of the
  selected-detector response at unit scale) is now a theorem: the response
  decomposes as detectorOperator ∘ prolateDifference − detectorOperator ∘
  compressionDifference, and each band piece is packaged as an l2Sum Hilbert--
  Schmidt pair whose left-bounded sandwich makes it trace-class along any named
  global basis. F2 is now fully proven this round: fourierCompressionFactor_adjoint_comp_self
  ((Q E)^dagger (Q E) = E Q E, from the two star projections + idempotence) and
  compressionFactorPairData_traceProduct_eq are both axiom-clean, so
  detectorCompressionChange_isTraceClassAlong_at_unit carries no sorryAx of its own.
  The ONLY `sorryAx` carrier left in the leaf is the isolated F1 semilocal crux
  targetProlateRemainder_unit_isTraceClassAlong; its consumers detectorProlateChange and
  the capstone projectionResponse_isTraceClassAlong_at_unit inherit it transitively.
  Paired build after deleting the leaf .olean: real Built line (33s), footer
  Build completed successfully (3198 jobs), zero ^error:. Mechanics (recorded for
  the commit round): boundedSandwich_isTraceClassAlong needs a carrier basis, so
  the sandwich is taken with an explicitly-typed ContinuousLinearMap.id finiteSCarrier
  and simpa'd through [identity, comp_id] (mirrors CCM24SourceProlateTrace.lean:167);
  dot-notation .smulRight must stay on the same line as its closing paren or it
  degrades to function application; a `have h : f(f _)=f_ := by intro x` with `_`
  placeholders leaves un-synthesized metavariables - close idempotence with a concrete
  target + exact congrArg (the F1 pattern). Open: the single F1 semilocal crux
  targetProlateRemainder_unit_isTraceClassAlong (target-side unit-scale kernel summability;
  source mirror CCM24UnitScaleStrictAngle.lean:1501 not directly reusable, independent
  family structure) is now the ONLY gap - F2 closed this round. Committed as the brick #1
  green leaf + paired audit.

- 2026-08-30 records 1056/1057/1058 (analysis batch, no Lean change): F1
  scoping + the most dangerous breakpoint cleared of suspicion (1056): the
  unit-scale crux `targetProlateRemainder_unit_isTraceClassAlong` is OUTSIDE
  the 1055 freeze (fixed lambda=1 star-projection model objects, no W_(lambda,S)
  / asymptotics) and is explicitly NOT a revival payment (Ruling 2); scope
  verdict GO with reclassification - the plumbing shortcut fails because the
  finite Euler transport is a TRANSLATION polynomial (`ccm24PrimeEulerTrans-
  portEquiv = prod (1 - c_p Shift_-logp)`), translations do not commute with
  support projections, and the isometry is consumed exactly at
  `prolateFactor_summable_of_strictAngle (U : H ≃ₗᵢ[ℂ] H)`
  (ProlateTraceReduction.lean:214); brick #2 = 2a generalize reduction via the
  existing Gram bridge (`targetSoninProjection_eq_gramCorrected`), 2b target
  angle bound by perturbation (needs margin check: source bound vs sum p^-1/2),
  2c translation-stability of the crossing HS decay. Pre-flight: 2b margin
  check is the one thing that can revoke GO. 1057: fetched the CC20 e-print
  raw tex (sha256 b01d353b..20f3fc, 170 numbered equations) and pinned the
  delta chain VERBATIM - eq-(141) maininequ (c = 4*gamma/log 2), (142)-(143)
  + the E(f) chain, (140) negativeNI, (134) spectral0, the gamma numerics
  (b ~ 0.05158, a ~ 0.064, eps2 ~ 0.00441, eps1 ~ 0.00122, <zeta|xi_0> ~
  0.94865, second gap > 0.227784, 13 < c_best < 17); the repo numbering is
  EXACT (eq-(115)=computerverif, (119)=opT, (121)=opTbound); FLAG: intro
  theorem vanishes at +i/2 AND 0 but final theorem only at -i/2 with the
  rank-one penalty (detector consumer must match ONE); 1049-B's HTML sweep
  is superseded. 1058: alpha reconnaissance probe GREEN in all three blocks -
  the paper's own eq-(170) arithmetic reproduced to six digits (tail
  2.36527e-12 <= 2.366e-12; nu identity; nu_35 = 4.11e-81; p(n) <= 120n^2),
  prolate eigenvalues [0.981046, 0.749620, 0.243593, ...] decay per-step
  ~ (C/n)^2 with the float64 collocation floor at index ~11 (lambda_10 ~
  1e-22 => validated campaign needs MP/ARB for n >= 7), slope series
  summable at reconnaissance level. Net: alpha SHAPE = 11-mode validated-ODE
  campaign with a published tail, not open-ended; convention question (which
  spectrum is the paper's lambda(n)) recorded open. Scripts: fetch_cc20.sh
  (WSL NAT proxy via default gateway - localhost proxies not mirrored, new
  7a rule), cc20_pin.sh/cc20_number.sh (tex maps), run_1058_probe.sh
  (venv-46937-py312). No Lean edits; F1 remains the only sorry carrier of
  the C1 thread; 1055 freeze untouched and still binding.

## 2026-08-30 (second batch) - record 1059: the pre-flight fired, and the convention closed

Same-day follow-through on the 1056 pre-flight and the 1058 open item.
1059 (1) REVOKED brick-2b: closing the target angle bound by perturbing the
source bound through the Euler transport needs delta > 0.985166 already at
S = {2} (kappa(T_2) = (1+2^{-1/2})/(1-2^{-1/2}) = 5.828427, coefficient
c_p = p^{-1/2} exact, pool CCM24VisiblePrime = {p : 1 < p} unbounded), while
CCM24UnitScaleStrictAngle.lean:1403-1413 proves only 0 < delta <= 1 for
unitLeakageLowerBound. Related trap recorded: prolateFactor U composes two
orthogonal projections (ProlateTraceReduction.lean:38-40), so its norm <= 1
is automatic - strictness is the entire content, never count the bound.
Posture: F1 stays the leaf's named conditional premise (R2 default); 2a
Gram-corrected reduction proceeds as algebra; R1 (target-side angle lemma
from additive-kernel geometry, log p >= log 2 window-shift gap) deferred to
its own design record. (2) PINNED the lambda(n) convention from raw tex
967-983: lambda(n) = Wang lambda_{2n}^{c=2pi} = even-parity branch of the
collocation spectrum with kernel sin(2 pi D)/(pi D) on [-1,1]; probe block
B2 measures [0.9999428, 0.9593903, 0.2746660, 3.478238e-3, 7.465620e-6,
5.820371e-9] and verifies the paper's (983) bound on it. This corrected the
1058 label error (the old "c = 2 pi" row was omega = pi) and moved MP/ARB
onset to n >= 6; the tightest alpha enclosure is mode 0 (p(0) ~ 93.5 off the
1 - lambda(0)^2 ~ 1.14e-4 denominator). Lesson banked in AGENTS 7d: the
1056-style "reserved revocation condition" pattern WORKS - a one-evening
paper pre-flight retired a scheme that would have cost weeks mid-build;
always price the uniformity quantifier (here: forall families) before
scheduling the brick. 1056 amended (s5b), 1058 verdict amended (s2/s3),
README C1/alpha boxes rewritten. No Lean edits; the F1 sorry at
C1ProlateResponseTraceLegalityUnitScale.lean:121 stands as the thread's
documented premise; 1055 freeze untouched and still binding.

## 2026-08-30 (third batch) - record 1060 + brick: GATE 1 delta contract wired

First Lean change since brick #1: new Dev leaf
C1CC20ArchimedeanComparisonWiring.lean (+ paired Audit) turns the delta
payload from the assembly's "NOT claimed here" prose into a named contract:
structure CC20ArchimedeanComparison {k, trace, eTerm, gamma,
trace_nonnegative, h142, hEchain, h143} whose fields are exactly CC20's
(142) trace split, the E-chain rank bound, and (143) k-hat(0) = -2 g-hat(0).
Producer noncomputable def builds CC20EndpointTraceCertificate with the paper
coefficient 4*gamma/log 2; the proof is purely the vanishing mechanism:
half-node + h143 => normSq = 0 => E(f) <= 0; h142 => trace <= W_infinity;
zero-node kills the certificate's rank coordinate. Composition theorem
qw_nonneg_of_archimedeanComparison reaches 0 <= qw g. Build evidence: 3607
jobs, no error lines, zero sorryAx, all three public declarations on
[propext, Classical.choice, Quot.sound]. Coordinate landmine (1060 s2):
chain rank at laplaceAt s=1/2 vs certificate rank at s=0 are NEVER
identified - the triple set {0,1/2,1} (paper nodes {rho=0,-i/2,+i/2}, the
union of intro+final vanishing sets) zeroes both; safe-side resolution of
the 1057 s5 flag; revisit this leaf if any consumer weakens vanishing.
Residual delta obligation is now three checklists fields, gated on the
gamma paper-scale payload (k-construction on the log owner + (140) chain).
Build lessons banked as AGENTS 7f: def-namespace prefix is not the type
(error-recovery sorry binders fake downstream linarith failures); Type-
valued certificate => noncomputable def; rw-at fails on projections =>
calc chain. README delta box upgraded [CONTRACT WIRED]; timeline names
0e787b0 for the 1059 batch and frontier URL corrected (was stale 74b6203).

## 2026-08-30 (fourth batch) - record 1061: alpha campaign slice T1 data in hand

No Lean change. The alpha 11-mode campaign got its first concrete data
slice: probe docs/proofs/1061_alpha_lambda_t1_probe.py (runner
scripts/run_1061_probe.sh, log /home/peter/cc20/probe1061.log) computes the
full candidate table lambda(n), n = 0..10, at dps 60 by parity-block
Gauss-Legendre collocation of the omega = 2pi kernel; cross-truncation
M = 44 vs 56 leaves 33-80 stable digits per mode (max |diff| 4.98e-60),
matching the 1058 float64 anchor to 9.7e-8 and satisfying the paper's
(983) bound on the branch. Key structural finding: the contract field
eigenvalue_sq_lt_one SPLITS - n >= 2 is discharged by (983) alone
(bound(2) = 0.754 < 1, monotone: pure-arithmetic Lean brick B1), and only
modes 0-1 need validated enclosures (margins 1.145e-4 / 7.957e-2, 26+
orders above noise). The commutant (SL operator, exact sparse Legendre
matrix with x^2 built as X@X of the Bonnet tridiagonal) yields the chi_n
the T2 ODE enclosures consume, with chi_0 = 5.494 matching the c - 0.789
large-c asymptotic. Two methodology bugs fixed en route and banked as
AGENTS 7c laws (12)-(13): import-time dps-freeze of module-level mpmath
constants faked a 5e-18 plateau; a hand-signed x^2 coefficient made a
positive operator's ground eigenvalue negative. Read the contract
CC20EndpointSpectralData verbatim into the record's T1-T4 target map;
T2 (interval-Taylor modes + continuation across the regular-singular
x = 1) is the next probe slice, and README alpha box now reads
[T1 TABLE IN HAND].

## 2026-08-30 (fifth batch) - record 1062: T2/T3 anchor validation CAUGHT the 1059 convention bug

No Lean change. The 1062 probe (docs/proofs/1062_alpha_t2t3_mode_anchor_probe.py,
runner scripts/run_1062_probe.sh, log /home/peter/cc20/probe1062.log) wired
the contract's own endpointSlope_eq_spectral identity up to the paper's
published anchor eps'(1+) ~ 22.9965 to validate the mode dictionary before
booking any enclosure. The ODE falsification gate PASSED at 1e-33 (the sinc
integral representation IS the paper's analyticMode, and continuation across
the regular-singular x=1 is automatic because the integrand's x-dependence is
ENTIRE - not a hard target after all), but the raw anchor sum came out
5.379035, NOT 22.9965. Chasing that mismatch through the raw tex found the
1059 s4 pin was a SQUARE ROOT off: tex:967-983 defines lambda(n) as the
eigenvalue of the SINGLE windowed Fourier operator P_1 F P_1 (prolateeq/
cosalphan) with ALTERNATING sign (-1)^n, whereas the collocation kernel
sin(2pi(x-y))/(pi(x-y)) = P_1 F P_1 F gives the SQUARED (concentration)
spectrum, so the whole 1061 table [0.99994, 0.95939, ...] is lambda(n)^2 and
the true lambda(n) = (-1)^n sqrt(those) = the paper's own printed list
[0.999971, -0.979485, 0.524086, -0.0589766, ...]. Two normalization factors
then close it: weight = mu^2/(1-mu^2) = lam_c/(1-lam_c), and the paper's
L^2(R)_ev inner product is 1/2 int_R (innerltwoeven), so a unit-norm mode is
sqrt(2) x the standard-L2 value. Under the corrected convention the term t(n)
= (lam_c/(1-lam_c)) * 2 * xi_probe(1)^2 reproduces the paper's PRINTED t(n)
list digit for digit (t(0)=11.9719...t(4)=0.000125459, all <= 2.7e-6 rel) and
the sum hits 22.9964756839 vs the published 22.9965. Consequences booked: the
contract's eigenvalue field is the SIGNED lambda(n); the eigenvalue_sq_lt_one
split SURVIVES (n>=2 by (983) on |mu|, bound(2)=0.75394<1 monotone) but with
corrected mode-0/1 margins 5.7247e-5 / 4.0610e-2 (the 1.14e-4/7.96e-2 figures
1061 printed were the squared-operator margins, 2x too generous); the
tightest enclosure budget is mode 0 at <5.7e-5, and a new innerltwoeven
sqrt(2) normalization lemma joins the instance checklist. AGENTS 7c gains law
(14) (a composition kernel gives the SQUARED spectrum; verify inner-product
normalization; wire the contract identity to the paper's derived number
BEFORE booking a convention pin) and the 7d lambda-pin + T1-split bullets are
rewritten to the corrected reading; records 1058 s3 item 4, 1059 s4, 1061 all
get AMENDMENT sections pointing here (nothing deleted). This is the 1059
lesson - price derived quantities before scheduling bricks - catching its own
predecessor: the mismatch was findable the instant the anchor was wired, which
is exactly what 1061 s1 prescribed and 1062 executed.

## 2026-08-30 (sixth batch, superseded correction below) - record 1063 probe

Task from Peter: rank the most dangerous breakpoints, deep-dive F1, and render
a binary verdict ("打通" or "确定打不了") on the semilocal crux. F1 = the sole
sorryAx carrier in `C1ProlateResponseTraceLegalityUnitScale.lean:117-121`,
`targetProlateRemainder_unit_isTraceClassAlong`. Pinned every model object to
Lean source (GlobalLogHaar:30 half-line E; CCM24HardyTitchmarsh:43-126,331-380
source HT; EulerTransport:182-206; SemilocalFourierSupport:31-83; FiniteS-
ProjectionTrace:145-220) and derived the KEY identity HT_S = f^{-1} M_{m_S} R f
with m_S(xi) = m(xi) mu_S/conj mu_S, mu_S = prod_p (1 - p^{-1/2} e^{-2 pi i xi
log p}) - the transport is a pure phase twist, self-adjoint unitary involution
for EVERY S (gate: HT^2=I, HT=HT* to 3e-12; odd-N grids mandatory, even N drops
Nyquist and silently breaks m(-xi)=conj m(xi), 8e-1 vs 3e-12). Built
docs/proofs/1063_f1_target_angle_probe.py (angle sum of M=E Q_S E, meet split by
first gap, scipy loggamma anchored to mpmath dps-50 at 4.6e-15) and
1063b_f1_weighted_probe.py (finite-dimensional detector-weighted statistics,
Gaussian scales k=0.3/1/3).

PRELIMINARY NUMERICAL INTERPRETATION (superseded below; not a formal verdict):
nonmeet Sum cos^2 over xi_max 12.8->25.6->51.2->102.4: src {PROVEN anchor}
3.18/3.43/3.12/2.47 FLAT; {2,3,5} 10.21/15.18/20.88/28.28 grows ~xi_max^0.4; top
angle pinned at 0.378-0.735.  The dt comparison (4097/T20 20.8779 versus
8193/T40 20.8784 at the same window) supports interval-driven growth in the
finite-grid model.  The phase-twist explanation is a conjectural continuum
mechanism, not an essential-spectrum theorem.

PRELIMINARY REPAIR INTERPRETATION (superseded below): the weighted statistics
plateau for the tested grids and motivate a smoothing analysis only.  They do
not give an owner-independent theorem, a proof of F1', or a cyclic readback.
The raw sorry has since been deleted; GATE 1 mainline is untouched.

## 2026-08-30 (seventh batch) - correct F1' boundary and reduce active order

The record-1063 grid sweep is an operational numerical guard, not a Lean
negation: its source anchor, phase/involution gates, and dt-quarter check pass
(for `{2,3,5}` at xi_max=51.2, 20.8779 versus 20.8784), while the nonempty
families grow over the tested windows.  It retires the historical raw F1 as the
next proof target, but does not establish continuum non-compactness, an
essential spectrum, or a named-basis trace-class theorem.

Critical correction: `PositiveTrace.IsTraceClassAlong` is summability of a
complex diagonal series on one named Hilbert basis (`PositiveTrace.lean:32-39`).
The 1063b finite-dimensional weighted statistic therefore does not prove F1'
for `D oL K_S`.  With `D = C† C` and `K_S = A† A`, that operator is generally
non-self-adjoint, so finite-dimensional cyclic trace algebra is not a legal
continuum readback.

`C1ProlateResponseTraceLegalityUnitScale.lean` now deletes the raw F1 sorry,
uses `targetProlateRemainderDetectorWeightedTraceLegality` only as an explicit
analytic contract, and proves the active-order identity
`D K_S = (A C)† (A C) + C† [C,K_S]`.  The positive part has a genuine
two-Hilbert--Schmidt consumer conditional on
`targetProlateDetectorRightSmoothingFactorSummable`; the root commutator is
also Lean-reduced to the concrete signed `E/Q_S/R_S` four-branch ledger.  The
remaining analytic work is (1) prove named summability of `A C`, and (2) build
a legal pair owner for that signed root-commutator.  Connes--Consani Lemma D.1,
arXiv:2006.13771, covers a specific quantized differential/Schwartz
commutator; it does not produce either finite-S target result.

## 2026-08-31 (eighth batch) - record 1064: the F1' semilocal bridge chain is Lean-green

The four-brick second-support chain landed green under WSL2 and must move as
one atomic commit because the imports nest: `C1SemilocalHardyTitchmarshUnitarity-
Reduction` <- `C1SemilocalFourierProjectionUnitaryBridge` <-
`C1SemilocalDetectorSecondSupportBridge` <- `C1SemilocalRootSecondSupport-
Bridge`, each with a paired #check/#print axioms audit (8 files total). Build
evidence (build4, WSL ext4 mirror): footer `Build completed successfully
(3174 jobs)`, zero error lines, zero sorryAx, and all 16 audited declarations
on exactly `[propext, Classical.choice, Quot.sound]` as a single distinct set.

What the root brick closes: S2's TARGET second-support branch of F1'. The
finite-S Hardy--Titchmarsh projection commutes with the convolution root up to
a unitary sandwich - `targetFourierSupport_rootCommutator_eq_reflectedRoot`
rewrites `cc20Commutator (HS * E * HS) C` into `HS * (E * B - B * E) * HS`, i.e.
the commutator of the target projection is a Hardy--Titchmarsh conjugate of
the COMPACT reflected-root boundary commutator;
`targetRootSecondSupportCommutatorBranch_eq_reflectedRoot` restates it at branch
level for direct S2 consumption. Supporting structure in the chain: HT root
conjugation equals reflection (plus its Fourier-multiplier form and both
involutions), and the spectral reflected root equals ordinary convolution by
the reflected compact root (`reflectedSpectralRoot_eq_reflectedConvolution`).

State of F1': (a) S2 second-support branch is now closed at root level in
Lean; (b) remaining S2 work = ONE legal Hilbert--Schmidt pair owner for the
THREE signed branches (the E/Q/R ledger from record 1063's four-branch
reduction); (c) S1 unchanged - named-basis summability of `A C`
(`targetProlateDetectorRightSmoothingFactorSummable`). GATE 1 mainline
untouched; RH unclaimed. New tactic hazards banked in AGENTS 7b: rw
all-occurrences semantics, noncomm_ring on endomaps (pure-* only, no positional
h args, ignores local a*a=1), mul_one/one_mul not simp-marked for `→L[ℂ]`
endomaps, and comp-chain vs pure-* defeq.

## 2026-08-31 (ninth batch) - record 1065: S2 pair owner green under one prolate-factor contract

S2 now closes in Lean from EXACTLY ONE new named analytic contract. The brick
`C1ProlateRootCommutatorPairOwner` (+ paired audit leaf; design record
docs/proofs/1065) builds `targetProlateRootCommutatorPairData`: base data D0
owns K_S as the positive square of its bounded factor F_K = Q_S (E - R_S)
(existing adjoint-composition theorem), two boundedSandwich transports put the
convolution root on either side, and l2Sum + smulRight(-1) forms the signed
difference. The crux equation `T_P = cc20Commutator(C, K_S)` closes by
rw [l2Sum_traceProduct_eq_add, smulRight_traceProduct_eq, D1 eq, D2 eq] then
simp only [sub_eq_add_neg, neg_one_smul, cc20Commutator]. The root never
appears as a Hilbert--Schmidt leg (bounded dressing only), so NO self-adjoint
or unitary assumption on C is required - this is why the two-sided sandwich
shape (option D) beat the oriented-difference alternatives in 1065's options
table. The E/Q/R four-branch ledger stays the ESTIMATE route; legality does not
consume it.

The single new obligation S2-FK-HS = `targetProlateRemainderFactorSummable`
(owner-free: Summable |F_K (globalBasis i)|^2) is named, producer-pending, and
likely shares a producer with S1 (equivalent if the root were unitary on the
carrier - not yet promoted). The F1' capstone is now a two-contract corollary:
`targetProlateRemainderDetectorWeightedTraceLegality_of_rightSmoothing_and_
remainderFactorSummable`: S1 + S2-FK-HS => F1'. Closing F1' at unit scale from
here on is PURELY analytic production of the two summability facts - no more
Lean owner machinery.

Build evidence (build #3): footer `Build completed successfully (3200 jobs)`,
zero error lines, zero sorryAx; all 11 audited declarations on exactly
[propext, Classical.choice, Quot.sound]. The build ran against the warm NTFS
mirror because wsl.exe inherited the Windows caller cwd (no explicit cd);
dual-mirror olean-mtime discipline is now banked in AGENTS 7a, and two new 7b
hazards: implicit dot on a parenthesized applied receiver in def bodies fails
resolution (use pipe-forward or fully-qualified call), and named defs like
cc20Commutator are not auto-unfolded by bare simp only. RH unclaimed; GATE 1
mainline untouched.

## 2026-08-31 (tenth batch) - record 1066: F1' collapses to ONE analytic contract

The two remaining F1' contracts are related by pure plumbing, and the brick
`C1ProlateSingleContractReduction` (+ paired audit; design record
docs/proofs/1066) records that as four declarations. The capstone corollary
`targetProlateRemainderDetectorWeightedTraceLegality_of_remainderFactorSummable`
closes F1' at unit scale from the SINGLE contract S2-FK-HS =
`targetProlateRemainderFactorSummable`: S1 follows in one line via committed-green
`summable_normSq_precomp` (HilbertSchmidtIdeal.lean:56-77; all three basis slots are
globalBasis, operator := F_K, bounded := rootConvolution owner - PREcomposition; the
postcomp sibling gives `C oL F_K`, the wrong order), and S2-legality was already brick
1065's pair owner consuming the same contract.

The iff theorem is what retires the second producer: S2-FK-HS is termwise identical to
the retired raw-F1 series via the record-1063 diagonal identity ((|F_K e_i|^2 : R) : C)
= <e_i, K_S e_i> (proof verbatim from git 74b8cbb; direction A is new but closes with
h.congr + Summable.of_norm only). The single open contract IS numerically the {2,3,5}
series record 1063 flagged (~xi_max^0.4 growth over four octaves), so 1063's operational
guard is INHERITED, not a verdict: the probe measured nonmeet angle mass of M = E Q_S E
while K_S = M - R_S leaves two unproved bridges (meet-residual control; grid-to-continuum
basis). Next slice = record 1067 candidate: measure |F_K_model|_HS^2 = Tr(M - R_S) directly
in the 1063 rig before scheduling an analytic producer.

Build evidence (build #4, warm NTFS mirror): first run red on ONE error - the brick split
record-1065's corollary name across two source lines and Lean read line one as the complete
identifier (no identifier continuation across newlines; hazard banked in AGENTS 7b); second
run green: footer `Build completed successfully (3201 jobs)`, zero error lines, zero sorryAx,
all four declarations on exactly [propext, Classical.choice, Quot.sound]. New 7a hazard too:
bare binary under non-interactive wsl bash -c is not on PATH and flock reports phantom
EXIT=0 with no build at all (log-evidence acceptance catches it). RH unclaimed; GATE 1
mainline untouched.

2026-08-31 RH_ROUTE_MECHANISM.md : new root-level three-view mechanism doc (a) RH compressed
to the 5-line checklist (all five roots dated c59e955e, 2026-07-10; live #print axioms run on
the warm mirror reproduced the e99ba6f ledger digit-for-digit, build footer 3775 jobs, zero
error lines); (b) scaffolding census: Source+Route 8,402 axiom-clean theorems / 266,381 lines,
zero axioms, zero sorries, plus the five-sentence glosses and acceptance instruments; (c) the
demolished false paths with named death certificates (59f8ff8 bare-HS, 08-26 budget ladder,
1052 D2, 1055 prolate double death, 1063 raw-F1, 1059 brick-2b REVOKED, 80 plan/ screens).
Side audit finding banked here: the full-tree axiom census is 39 declarations (the earlier
"40" counted a backtick prose hit in WeilC1NonEmptyProducer.lean:6 - corrected), of which
5 are LIVE under the RH closure, 8 wrapped-off-chain, and 26 declared-but-unconsumed
deadweight candidates for a zero-risk hygiene prune (NOT yet done; Dev-only, no consumers).
Docs only; no .lean touched; RH unclaimed.

## 2026-08-31 (eleventh batch) - record 1067: direct Tr(M-R_S) probe - BRIDGE 1 closes, ROUTE B stands

The single open F1' contract is now measured DIRECTLY in the record-1063 rig
(design docs/proofs/1067 + probe 1067_fk_hs_direct_trace_probe.py; commit
34feb2d). R_S pinned as the star projection of the MEET
(CCM24SemilocalFourierSupport.lean:134-137), so R_S_model = P_W with W = U n V and
Tr(K_S)_model = Tr(M) - dim(U n V) = SUM_{theta>0} cos^2(theta_n) EXACTLY - the meet
residual is identically zero in finite dimensions. Measured three independent ways
(spectrum of B, the Hermitian U-block of Q_S; Re Tr(M) - d plus eigvalsh(M - R_S_model);
||Q_S(E - P_W)||_F^2 entry-level): all agree to <= 2.6e-11 on every one of the 20 cases
(< 1e-8 closure gate). BRIDGE 1 (meet-residual control) CLOSED. Cross-validation exact:
source gap-split meet count reproduces 1063's 42/117/303/746 at all four octaves;
nonmeet_1063style matches every published raw sum to 4 decimals; dt-quarter pair on the
deciding family {2,3,5} is machine-level (rel-diff 5.3e-5).

VERDICT per the pre-stated fork: GROWTH -> ROUTE B. fk_hs_sq({2,3,5}) = 16.20/20.17/
26.87/34.27 over xi_max 12.8->102.4 (increments +3.97/+6.70/+7.40 INCREASING - no
saturation bend; measured exponent ~0.36, same sublinear regime as 1063's raw ~0.4 since
fk = raw + O(1)); source anchor flat [6.18, 7.12] at every resolution and octave.
Consequences: (1) the UNWEIGHTED IsTraceClassAlong K_S - which record-1066's iff
identifies termwise with S2-FK-HS = targetProlateRemainderFactorSummable - FAILS for
{2,3,5} in this model; S2-FK-HS AS CURRENTLY SHAPED is not producible from this family's
data. (2) F1' must be routed through the D-weighted statement (Tr(D oL K_S): record 1063
saturation + owner-independent), scheduled as its OWN design record - Lean re-route swaps
the corollary's S2-FK-HS premise for targetProlateRemainderDetectorWeighted_isTraceClassAlong
and re-shapes around D K_S = (A C)^dagger(A C) + C^dagger[C, K_S]; this round measures only,
no Lean changed. (3) BRIDGE 2 (grid->continuum basis) stays open but SHARPENED: the strict
meet d sits O(1) below the gap-split block by a bounded <=6 near-1 fringe whose eigenvalues
creep toward 1 with N ({2,3,5} bottom trio 0.99418 -> 0.99699 over the four octaves) - extra
directions of the infinite-dimensional Sonin meet not yet converged at finite resolution;
either continuum reading keeps ~xi^0.4 growth, so BRIDGE 2's resolution cannot change this
verdict, only its constant term. GUARD STATUS: 1063's {2,3,5} guard ambiguity (the probe
measured M while the contract faces K_S = M - R_S) is now RESOLVED in the unfavorable
direction - the growth regime survives intact plus an O(1) fringe; ROUTE B stands.

Operational: single deterministic run accepted on log evidence only (20 SUMMARY lines +
56/56 gate lines, zero NUL bytes, no FAIL/error/traceback; full log in the Linux-side
verification environment, unversioned per the 1063 convention). An early duplicate launch
ran concurrently and was killed by exact PID; its block-buffered stdout would have been lost
on SIGKILL (a normal-exit final flush rewrites from byte 0 and overwrote the fragment
cleanly). New AGENTS 7a hazards banked: uv bare-binary path, python -u for redirected long
probes, background-task "completed exit 0" unverified until pgrep empty + end banner in log
(two pythons thrash OpenBLAS), WSLg X-noise /tmp-file-then-cat in one call, $var loss even
single-quoted across the wsl boundary. RH unclaimed; GATE 1 mainline untouched (alpha B1/B2
enclosures still next on that line).

2026-08-31 (mechanism-doc pass): RH_ROUTE_MECHANISM.md finalized into three
number-free views: (a) RH -> five checkable sentences; (b) the operating
system (paper claim -> probe -> certified data -> Lean theorem -> audit gate);
(c) converted from the closed-roads grading table to a box-per-sentence
walkthrough of the five live lines (says / why hard / owes), with the graded
road record kept as a one-line pointer into README + docs/proofs. View (b) now
sits at the very top of README.md; the old journey map and its tag legend were
removed from README (223 lines), the "milestone count is not an honest
measure" paragraph retained. The same three views were inserted (HTML-escaped,
no added heading) at the top of an out-of-repo interview-preparation page.
Box alignment normalized mechanically: single-box interiors now uniform per
box group; the pre-existing 1-column GATE border drift was fixed. RH unclaimed.

## 2026-08-31 (twelfth batch) - record 1068: the D-weighted route's unmeasured bone measured - OUTCOME A

2026-08-31 docs/proofs/1068_root_commutator_ledger_probe_and_verdict.md :
pre-registered (commit d5f936e, fork stated before data) + executed the
four-branch ledger / root-commutator probe in the 1067 rig, measuring the two
contracts the 1067 ROUTE B re-route consumes (S1' right-sandwich HS, S2 root
commutator C-dagger-[C,K_S] trace-legality) - the quantities 1063b never touched.
Verdict OUTCOME A per the pre-stated fork: at k=1 EVERY D-weighted quantity is
O(1) and monotone DECREASING over the four octaves ({2,3,5}: p_hs_sq
3.5661->3.5356, l_hs_sq 0.2086->0.1688, l_tr1 1.3462->1.2850, s_tr1
0.5800->0.5395, t_tr1 3.7836->3.7319) while the k=0 control on the same code
path grows 16.20->34.27 reproducing 1067 exactly (and strict meet d minus
1067's gap-split = the s5.3 fringe {3,3,4,4} exactly). All Lean identity
residuals (ID-1/2/3) <= 1e-11 machine level; dt-invariance at the real pair
<= 3e-4 all families; src anchor flat 1.006. Structural finds: (a) the leaf's
globalBasis is universally quantified, so the produceable S2 route is forced
basis-independent -> trace-norm / pairData HS-legs path (leaf:243/:301);
(b) in the xi-character basis (diagonalizing C) the diagonal of C-dagger-[C,K_S] is
ALGEBRICALLY ZERO (measured 0.0000 everywhere) - the S2 danger lives only off
that basis; (c) br_out = br_refl exactly, Sonin branch collapses under k=3.
Consequences: next brick = the D-weighted re-route DESIGN RECORD (swap the
capstone premise to the two-contract corollary leaf:370-381), then producers
P1 (continuum HS of F_K C for the ACTUAL root) and P2 (four-branch ledger via
pairData - classical commutator-smoothing adaptation; the quasi-periodic twist
is the named difficulty). No Lean change this round. AGENTS 7a gains the
env-metacharacter rule. RH unclaimed.

2026-08-31 (audit rehearsal for the interview): synced the repo (HEAD
7e04a34) to the warm ext4 mirror and re-ran the ledger chain live: build
footer "Build completed successfully (3775 jobs)", zero ^error: lines, and
`lake env lean ConnesWeilRH/Dev/RhOutputAxiomLedger.lean` printed exactly the
8-axiom residual (3 Lean ticket + the 5 named roots; unchanged since 08-10).
Confirmed at 7e04a34: bridge theorem still :8069, the two iff theorems still
:1518/:1537; word-level `grep -rnw sorry` on Source/ returns only the two
doc-comment prose hits (ObjectTheoremBasePackage.lean:2793/:2806); real
standalone `sorry` tactic lines live in exactly 4 files, all Dev/_*.lean
scratch, none imported by the mainline. The step-by-step live command
sequence was placed at the top of the out-of-repo interview-preparation
notes page. RH unclaimed; no repo source changes this pass.
