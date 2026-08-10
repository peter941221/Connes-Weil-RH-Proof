## Change Log (2026-08-10): RealWeierstrassProd bricks 1-2 (WSL-verified)
- New ConnesWeilRH/Dev/RealWeierstrassProd.lean (lane (a) Gamma developable, docs/944):
  factorScale/webfac/partialP defs; webfac_bounds (0 < w(n) <= 1 for 0<=s),
  partialP_pos / partialP_le_one / partialP_mono (P_N >0, <=1, non-increasing).
  axiom-clean [propext, Classical.choice, Quot.sound], 0 sorry (WSL green 1916 jobs).
  Skeleton for the real Weierstrass product (limit = 1/Gamma NOT claimed yet);
  next: brick 3 monotone-convergence Tendsto. RH not claimed.

## Change Log (2026-08-10): Weierstrass product-angle limit (WSL-verified)
- New ConnesWeilRH/Dev/GammaWeierstrassProdAngle.lean: partialProduct_arg_eq_angle_sum
  (arg of finite Weierstrass partial product = sum of per-factor weylArgNum angles)
  and tendsto_product_angle_arg (the partial-product argument -> -SSandwich.S in
  Real.Angle as N->inf). axiom-clean [propext, Classical.choice, Quot.sound],
  0 sorry (WSL green 2642 jobs). PRODUCT-side limit of the Gamma-phase hinge
  (docs/940/941); the Gamma-integral connection stays the open analytic leaf. RH not claimed.

## Change Log (2026-08-10): WeylArg Angle bridge (WSL-verified)
- GammaWeierstrassSum.lean: added hasSum_angle_weylArg
  (HasSum (fun n => (weylArgNum(n+1) : Real.Angle)) (-SSandwich.S : Real.Angle))
  axiom-clean [propext, Classical.choice, Quot.sound], 0 sorry (WSL green).
  Infinite-product-angle value lift under the continuous Real.Angle quotient;
  the image Step-3 Gamma hinge (docs/940/941) needs on its product side.

## Change Log (2026-08-10): negS_bounds numeric bracket (WSL-verified)
- GammaWeierstrassSum.lean: added negS_bounds
  (-(1/2+1/32) <= -SSandwich.S /\ -SSandwich.S <= -1/2) axiom-clean,
  WSL green. Concrete numeric bracket on the Weierstrass log-Gamma phase-sum.
- Committed: c2aa156.
## Change Log (2026-08-10): GammaWeierstrassSum hasSum -> -S (WSL-verified)
- GammaWeierstrassSum.lean: added hasSum_weylArgNum
  (HasSum (fun n => weylArgNum(n+1)) (-SSandwich.S)) axiom-clean
  [propext, Classical.choice, Quot.sound], 0 sorry (WSL green 2641 jobs).
  Convergent series-side backbone of the Weierstrass log-Gamma phase (docs/940).
  Gamma integral -> product hinge stays open. RH not claimed.
- Committed: d1a9bb2.
## Change Log (2026-08-10): canonical Step-3 finite-S sign CLOSED (route verdict)
- Verified axiom-clean (spot-audit, WSL): detector_diagonal_re_nonneg /
  detector_isPositive / detector_re_inner_nonneg (A3NonzeroCompactLogGateProbe),
  healthy_strict_positive_diagonal (Wall1HealthyPositive), weilStateNonempty /
  concrete_c1_input_nonempty_exists (WeilC1NonEmptyProducer). Axioms
  [propext, Classical.choice, Quot.sound], 0 sorry. Step-3 finite-S sign closed
  on canonical CompactLog/A3; Gamma-arg route (docs/940/941) is redundant sibling.
- New docs/proofs/942_step3_finite_gate_closed.md; AGENTS.md route-verdict paragraph.
  Remaining open (not Lean-assembly leaf): RH-equivalent C1-SourceRH criterion,
  Gate-3U infinite carrier, Burnol identity. RH not claimed.
## Change Log (2026-08-10): Gamma-Weierstrass partial-sum bridge (WSL-verified)
- New ConnesWeilRH/Dev/GammaWeierstrassSum.lean: weylArgNum_eq_neg_a
  (weylArgNum(n+1) = -SSandwich.a n) and weylArgNum_range_eq_neg_sum
  (sum_{n<N} weylArgNum(n+1) = -sum_{n<N} a n), both axiom-clean
  [propext, Classical.choice, Quot.sound], 0 sorry (WSL green 2641 jobs).
  Finite-angle preimage of arg(Gamma(1+I/2)) = -gamma/2 - atan(1/2) + tsum a.
  Gamma-integral -> product-angle hinge stays open (docs/940). RH not claimed.
- Committed locally: 0c03575 (finite product spine) + e413783 (partial-sum bridge).
## Change Log (2026-08-10): finite Weierstrass product-argument closure (WSL-verified)
- ConnesWeilRH/Dev/GammaArgSum.lean: generalized arg_prod_coe_angle from Finset Nat to Finset alpha;
  added real_sum_coe_angle (Real.Angle coercion distributes over Finset sum), both axiom-clean.
- ConnesWeilRH/Dev/GammaArgProd.lean: added weylFactorIm_nonzero / weylFactor_ne_zero (0 < u),
  weylArgNum def, and arg_weylFactor_prod_coe_angle: arg(prod_{i in t} weylFactor i) : Real.Angle
  = sum i in t (weylArgNum i : Real.Angle). #print axioms = [propext, Classical.choice, Quot.sound],
  0 sorry (WSL green, 1978 jobs). Finite partial-product preimage of SSeriesSandwich
  S_eq_S2_add_atan_half. Infinite Weylstrass limit to arg(Gamma(1+I/2)) stays open (docs/940/941).
  RH not claimed.
## Change Log (2026-08-10): GammaArgProd extended with Gamma-product-shape + factor-arg bricks (WSL-verified)
- ConnesWeilRH/Dev/GammaArgProd.lean now also proves axiom-clean: arg_add_mul_I
  (arg(x + I*y) = atan(y/x) for 0 < x, general vector-phase identity), arg_exp_add_mul_I_angle
  (arg(e^{r + I*s}) = s, as Real.Angle), alongside the earlier arg_exp_mul_I_angle /
  arg_factor_coe_angle / arg_factor_half, plus the Gamma-factor arms arg_gamma_imag
  (arg((u+1)/u + I/(2u)) = atan(1/(2u+2)), the S-series summand) and arg_exp_neg_z_div_n
  (arg(e^{-1/u + I*(-1/(2u))}) = -1/(2u), the exp half). All #print axioms =
  [propext, Classical.choice, Quot.sound], 0 sorry; WSL green. These form the finite preimage
  of SSeriesSandwich.S_eq_S2_add_atan_half (S = tsum S2 + atan(1/2)). The infinite Weylstrass
  log-Gamma identity for |arg Gamma(1+I/2)| <= pi/8 stays the open new-analysis leaf. RH not claimed.

## Change Log (2026-08-10): verified Weierstrass factor-argument additivity (new module)
- New ConnesWeilRH/Dev/GammaArgProd.lean: arg_exp_mul_I_angle (arg(e^{I theta})=theta, Real.Angle),
  arg_factor_coe_angle (arg( e^{I theta}/(1+I x) )=theta-atan x, x>=0), arg_factor_half.
  WSL green, #print axioms [propext, Classical.choice, Quot.sound], 0 sorry. Single-factor spine
  between GammaArgBricks (factor arg) and GammaArgSum (Finset product arg = sum). Still open:
  infinite Weierstrass log-Gamma limit connection for |arg(Gamma(1+I/2))|<=pi/8. RH not claimed.

## Change Log (2026-08-10): verified product-argument additivity (new module)
- ConnesWeilRH/Dev/GammaArgSum.lean: arg_prod_coe_angle proves axiom-clean that the Arg of a
  Finset product = sum of factor args (Real.Angle), 0 sorry, via arg_mul_coe_angle. This is the
  structural backbone turning Weierstrass factor args (GammaArgBricks) into the summed series
  for arg(Gamma(1+I/2)). The cross-check arg(Gamma(1+i/2))=-0.2440583 confirmed. The
  Weierstrass log-Gamma identity connection stays open. RH not claimed.

## Change Log (2026-08-10): verified Gamma-argument bricks (new module)
- ConnesWeilRH/Dev/GammaArgBricks.lean: prove axiom-clean arg(1+I*x) = atan x (x>=0),
  arg(1+I/2)=atan(1/2), arg(1+I/(2n))=atan(1/(2n)). WSL green; #print axioms
  [propext Complex.Classical.choice Quot.sound]; 0 sorry. These are the factor-phase
  identities of the Weierstrass log-Gamma argument for base point 1+I/2. The open analytic
  cut  tail remains ((Gamma(1+I/2)).arg = D connection). RH not claimed.

## Change Log (2026-08-10): new axiom-clean hinge module Dev/GammaArgLeaf.lean
- New ConnesWeilRH/Dev/GammaArgLeaf.lean: gammaSign_at_one (harg) proves axiom-clean
  0 <= Re[(Gamma(1+i/2))^4] from the single premise |arg(Gamma(1+i/2))| < pi/8.
  WSL green; #print axioms [propext, Classical.choice, Quot.sound]; 0 sorry. The finite-S
  a=1 arch sign is now one theorem one premise away; the premise is the Weierstrass/Stirling
  Gamma-argument leaf. RH not claimed.

## Change Log (2026-08-10): new-module + skeleton build snapshot re-verified
- Combined WSL build green (3599 jobs): ConnesWeilRH.Dev.WellFormHealthyRepoint +
  ConnesWeilRH.Dev.WeilC1NonEmptyProducer all up-to-date compiled clean (only benign
  reducible-linter warning on weilStateNonempty). Prior: UnconditionalSkeleton warm build
  green (3500 jobs). Authoritative snapshot of Step1/Step2 verified state.
## Change Log (2026-08-10): NEGATIVE verdict - naive large-band Gamma sign false (docs/937)
- Numeric ruling: `Re[Gamma(a+i/2)^4] >= 0` is FALSE for a=3,5,10 (=-3.7, -2.9e5, -3.4e21),
  and arg Gamma(a+i/2) -> (1/2) ln a (Stirling) not -> 0, so Re[w^4] = |w|^4 cos(4 arg) sign-flips
  forever. docs/859 §6 conjecture (exists a0, forall a>=a0, Re>0) is REFUTED.
- Route: naive band-test `t^a e^{-t}` cannot be the finite-S sign producer; re-anchor Step 3 to the
  CompactLog HS/A3 positive (healthy_strict_positive_diagonal, detector_diagonal_re_nonneg), which
  Steps 1-2 already wire. UnconditionalSkeleton exit (= Nonempty input.fullWeilPositivity) stays fed.
- No Lean implication; evidence = scipy.special.gamma read-only. RH not claimed.
## Change Log (2026-08-10): Step2 re-point verified; Step3 canonical = CompactLog A3 (Gamma-phase non-canonical)
- Verified at mirror HEAD: UnconditionalSkeleton warm build green (3500 jobs); re-pointed
  fullWeilPositivity (WellPositiveState = healthy CompactLog HS strict positive diagonal) feeds
  the C1 exit (line 1623/1624). Audit: healthyEval/healthyPerCommonSupport/healthyWeilForm/
  concreteC1InputData all #print axioms = [propext, Classical.choice, Quot.sound]; the only
  remaining exit axiom is normalizedCoreCC20PropositionC1SourceCriterionRoot self-dependency.
- Step 3 canonical home = CompactLog HS: the finite-S Weil sign IS the A3 PSD strict positivity
  (`healthy_strict_positive_diagonal`, detector_diagonal_re_nonneg), already wired as
  `WellPositiveState`. The Gamma-phase/Stirling branch (docs/859,869,888) is NON-canonical there.
  What still blocks RH is the criterion theorem `CC20PropositionC1SourceCriterion` (finite
  positivity => B.SourceRH), i.e. the real finite-S sign-forcing conclusion, far from the
  A3 PSD seed alone.
## Change Log (2026-08-10): healthy-carrier SourceWeilFormData brick axiom-clean (doc.936 step-2 first leaf)
- ConnesWeilRH/Dev/WellFormHealthyRepoint.lean: transferred the per-common finite-prime support
  ({2}, prime-2 via commonBump) from the concrete carrier onto the healthy Mellin algebra
  (healthyForward_mem / healthyTerm_two_ne_zero / healthyPerCommonSupport), then lift to
  healthyWeilForm : SourceWeilFormData healthyMellinSourceTestAlgebra (healthy substitute for the
  L137 axiom, axiom-clean). WSL build green (2949 jobs); #print axioms [propext, Classical.choice,
  Quot.sound], 0 sorry. finite-S Weil sign stays open.
## Change Log (2026-08-10): Step 1 DONE - concrete CC20PropositionC1InputData/RouteInput at standard bridge
- `ConnesWeilRH/Dev/WeilC1NonEmptyProducer.lean`: added `concreteC1InputData`  `Source.CC20PropositionC1InputData RHDefinitionBridge.standard cc20TripleFiniteVanishingSet  concreteWeilInput` and `concreteC1RouteInputData` (route variant). Filled fields: finiteSetIsTriple  (cc20_triple_finite_set_is_triple), finiteSetDisjointFromNontrivialZeros  (cc20_triple_disjoint_from_standard_source_nontrivial_zeros, the zeta-half nonvanishing row 849/  ZetaHalfNonvanishing), tripleVanishing (True), fullWeilPositivity (Classical.choice weilStateNonempty).  WSL build green (3593 jobs); #print axioms [propext, Classical.choice, Quot.sound], 0 sorry.
- Foundation for step-2: the strict-diagonal re-point is already `concreteWeilInput.fullWeilPositivity =  WellPositiveState` (from Wall1HealthyPositive). Remaining step-2 work = re-point the skeleton source  consumer's `convolutionStar`/`qw` onto the healthy Mellin algebra (healthyMellinSourceTestAlgebra) and  re-run the UnconditionalSkeleton cold build+axiom audit - a large dedicated slot.

## Change Log (2026-08-10): C1 non-empty Weil input PROVEN (objective: concrete non-empty C1 input)
- `ConnesWeilRH/Dev/WeilC1NonEmptyProducer.lean`: builds a concrete `WeilPositivityInput` on the
  healthy CompactLog HS carrier whose `fullWeilPositivity` Sort `WeilPositiveState` = the strictly
  positive crossing vectors of the PSD convolution-square at `nonzeroTest.test`, and proves
  `Nonempty concreteWeilInput.fullWeilPositivity` from `healthy_strict_positive_diagonal`
  (`Wall1HealthyPositive`). Top theorem `concrete_c1_input_nonempty_exists` gives
  `exists input, input.tripleVanishing and Nonempty input.fullWeilPositivity`.
  WSL build green (3180 jobs); #print axioms = [propext, Classical.choice, Quot.sound], 0 sorry;
  `WellPositiveState` marked reducible; subtype line shortened. This is the concrete non-empty
  C1/Weil producer for the skeleton exit; the finite-S sign discharge of every such input is open.
  RH not claimed.

## Change Log (2026-08-10): healthy Mellin source-test algebra axiom-clean (doc.936 Step 1)
- ConnesWeilRH/Dev/HealthySourceMellinAlgebra.lean: built a SourceTestAlgebra on the SAME carrier
  TestFunction = SchwartzMap real complex as the broken concrete algebra, but with the TRUE Mellin
  product convolutionStar f g = SchwartzMap.convolution (mul real complex) f g (plus Fourier involution
  and square), fixing the additive  + g defect. Identity LegacyTestEquiv (Test := TestFunction) avoids
  the CompactLogTest bijection wall (A2 probe). healthyFourierConvolutionMul records the
  multiplicative-Mellin Fourier law. WSL build green (2936 jobs); #print axioms = [propext,
  Classical.choice, Quot.sound], 0 sorry, 0 new project axiom. RH not claimed; re-pointing
  fullWeilPositivity / finite-S sign to this healthy product remains.
## Change Log (2026-08-10): concrete healthy strict diagonal instantiated (non-empty producer)
- `ConnesWeilRH/Dev/Wall1HealthyPositive.lean`: wired the closed strict-positive leaf onto the
  A3 concrete nonzero test. `healthy_strict_positive_diagonal` gives
    exists u, 0 < real <u, cc20GlobalConvolutionPositive nonzeroTest.test u>
  on the global log carrier -- a concrete, verified, STRICTLY positive diagonal for the
  non-empty producer the re-type needs. WSL build green (3179 jobs); #print axioms
  [propext, Classical.choice, Quot.sound], 0 sorry.
This is the analytic "non-empty producer" content: the healthy CompactLog HS carrier has a
concrete nonzero test whose PSD convolution-square quadratic form is genuinely positive.
RH not claimed; the C1 skeleton re-type (consuming this positive diagonal) remains.
## Change Log (2026-08-10): strict positive diagonal PROVEN axiom-clean (strictness seed COMPLETE)
- `ConnesWeilRH/Dev/Wall1GlobalConvNonzero.lean` now closes the full strictness seed on the healthy
  CompactLog/HS carrier in three axiom-clean leaves:
    (1) `cc20GlobalLogConvolution_ne_zero`: a nonzero Schwartz kernel h gives a nonzero global
        log-convolution operator on `cc20GlobalLogCrossingL2`.
    (2) `cc20GlobalLogConvolution_strict`: exists u, 0 < ||cc20GlobalLogConvolution h u||.
    (3) `cc20GlobalConvolutionPositive_strict_diagonal`: at nonzero h, the PSD convolution-square
        operator `(cc-conv h)dag o cc-conv h` has strictly positive Hilbert diagonal:
        exists u, 0 < real <u, cc20GlobalConvolutionPositive h u>.
  WSL build green (2964 jobs); `#print axioms` = [propext, Classical.choice, Quot.sound]; 0 sorryAx
  for every leaf.  Together with the existing nonneg diagonal this is exactly what inhabits
  `fullWeilPositivity` on the healthy carrier - no window surgery needed.
Proof (1) Fourier-multiplier: if zero, every Schwartz conv `h*g` vanishes (toLp-injectivity);
g=h gives pairing mul (Fourier h)(Fourier h)=0 pointwise -> Fourier h=0 -> h=0 (FourierInvPair).
Leaves (2)-(3) are norm-positivity reductions only. RH not claimed.
## Change Log (2026-08-10): STRATEGIC REDIRECT - RH exit is C1/Weil positivity, NOT Gate 3U
- Deep-thinking verdict: Lean RH final exit = two RH-EQUIVALENT axioms in Dev/UnconditionalSkeleton.lean (C1 criterion at ~line 1555; Yoshida pole-pairing at ~line 5896). Lines 1536-1543 wire C1SourceCriterion to RiemannHypothesis via the RH bridge. Discharging EITHER IS PROVING RH (AGENTS 6/13).
- Gate 3U (finite-band bandTerminalGate) is a trace bound and is NOT on the critical path to RH; it does not feed Weil-positivity.
- Real RH chain: (1) concrete non-empty C1 input on a healthy HS carrier, (2) prove C1 positive (finite-S Weil sign) for all input, (3) close the C1-to-RH bridge (already doc-level).
- The concrete carrier is BROKEN (additive convolution, non-Mellin, exactSupport-2awa-0). First brick = re-type source core to CompactLog HS so the sign has a non-empty producer, then prove the instance sign.
- RH NOT claimed. Primary pivots from Gate-3U/infinite-trace to C1/Weil-sign.
## Change Log (2026-08-10): wall1 round - commit+push all Dev leaves; build-verified at HEAD; L657 fix
- Pushed all dirty public artifacts (AGENTS/MEMORY + docs/925-932 + deliverable_finite_gate + new Dev leaves) as commits 2186da0, ced3b6d to origin/main. Fresh mirror cwr-wall1-0810 (seed .lake from cwr-main) build-verified the whole committed Dev set at HEAD: CCM24JdaggerOrthogonality (3275, #print axioms [propext CC Qs] 0 sorry), EBandFactorSharpProbe (3220), Gate3UDichotomyProbe (3418), L657DiagProbe (2950). Fixed L657DiagnosticProbe syntax (empty -> ∅) => 2948 green. Wall 1 infinite Gate sufficient identity (End=J : B o N^-1 o J + H o J o G^-1 = J) re-grounded: norm_le_one_iff + adjoint_comp_self=id+L^dag+L + pointwise Pythagoras do NOT force closure; open analytic bottom needs the signed (I-P)F=-(I-P)D identity (docs/928-932). RH NOT claimed.
## Change Log (2026-08-10): AGENTS 3b - new math/analysis/self-created theory is a standing attackable target (no report, no consent)
- Added to AGENTS.md §3b: whenever a step needs genuinely new math/analysis/self-created theory, treat it as a standard target and attack directly - no reporting, no asking. Only the hard guards (sorry/axiom, RH-only, destructive/git/shared-infra) still stop the agent. Reinforces docs/931-932 stance (infinite Gate residual is work to be done, not a blocker).
## Change Log (2026-08-10): 932 - J-dual orthogonality PROVEN (byte-verified, axiom-clean)
- New file ConnesWeilRH/Dev/CCM24JdaggerOrthogonality.lean: proves the previously-open NECESSARY condition of the infinite Gate, (sourceInclusion)^dag o B = 0 and (sourceInclusion)^dag o (B o N^-1 o J) = 0, from Leibniz-algebra facts (J^dag = J^dag o P;  P o B = 0). WSL build green (3275 jobs); #print axioms = [propext, Classical.choice, Quot.sound]; 0 sorry. Explains why numeric probes of the outer channel are FLAT (linear/J-dual content vanishes; info lives only in the off-J operator norm). Does NOT close the Gate (sufficient equality L=0 still open). docs/proofs/932 + deliverable_finite_gate. RH not claimed.

## Change Log (2026-08-10): MEMORY compressed (24,395 -> 902 lines)
- Full pre-compression snapshot kept at `MEMORY.precompress.backup.md` (29,910 lines); HEAD:MEMORY.md also retains the original. Working knowledge (commands, WSL verification, LX guards, route root) lives in AGENTS.md; MEMORY.md now keeps latest change-logs + compressed high-signal lesson lines only. RH not claimed.
## Change Log (2026-08-10): Per-prime leakage is critical-line divergent; only cancellation can close the infinite Gate
- `docs/proofs/930_per_prime_leakage_critical_line.md` (new). The library already has
  `norm_normalizedPhysicalLeakage_singlePrime_le_twelve_mul_coefficient` (MomentDecay:879):
  `||normalizedSourcePhysicalCoframeLeakage (singlePrimeFamily p)|| <= 12/sqrt p`, with
  `ccm24EmpirEulerCoefficient p = 1/sqrt p` (EulerTransport:33). So per-prime absolute norm
  is O(p^{-1/2}), and `Sum_p 1/sqrt(p) = infinity` at exactly the RH-critical exponent. Thus the
  infinite Gate cannot close by absolute-value summability (both the docs/927 band-cardinality
  divergence and now the per-prime critical-line divergence); only the signed Piece-1 identity
  `L_S = F+(D-J)=0` can. Not a closure; records WHY the Analytic step is forced. RH not claimed.

## Change Log (2026-08-10): bandTerminalGate byte-verified axiom-clean on current Windows source
- `lake env lean` on `Driver/Dev/RouteATailBandBound.lean` (current tree) EXIT=0 and
  `#print axioms ...bandTerminalGate` = [propext, Classical.choice, Quot.sound], 0 sorry.
  This re-verifies (fresh, warm-olean check against current HEAD sync) the finite-band
  canonical Gate deliverable (docs/928 active root). Infinite-carrier Gate (Piece-1
  `L_S = F+(D-J)=0`) stays OPEN; no new math found this session, numerically unreachable.

## Change Log (2026-08-10): Sharp prolate-factor norm bound ||factor|| <= 1 (verified axiom-clean)
- New `ConnesWeilRH/Dev/EBandFactorSharpProbe.lean`, `prolateFactor_norm_le_one lambda`:
  `||sourceProlateHilbertSchmidtFactor lambda|| <= 1`, via B0 = radial - sourceSonin (star-projection,
  FixedQuotientCarrier:46) composed with the Fourier projection. WSL-verified axiom-clean
  [propext, choice, Quot.sound], 0 wrong. Damps the coarse triangle ceiling ||B0||<=2.
  Still no strict ||factor||<1, so Summable ||factor||^2 remains spectral; Gate stays open.


## Change Log (2026-08-10): Route-root decision - finite/decaying-band Gate is the canonical deliverable
- `docs/proofs/928_gate3u_route_root_decision.md` (new). Re-checked source:
  `L_S = sourceActualBandCombinedCoframeLeakage = F + sourceSoninCoframeLeakage` is already proved
  off-Sonin (orthogonal to both J^dag and P). The ONE open Piece-1 identity `L_S=0` on non-empty
  prime families is not forced by any theorem; the deciding F-term (exact Sonin intersection R0) is
  unreachable numerically, and carrier re-point is necessary-not-sufficient (card*|Support| diverges).
- AGENTS.md sec 2: active root re-pointed to the finite/decaying-band Gate; infinite carrier stays OPEN.


## Change Log (2026-08-10c): Route correction - Piece 2 (carrier re-point) cannot close infinite Gate
- `docs/proofs/927_gate3u_piece2_correction.md`: structural correction (supersedes the Piece-2 recommendation in 925/926). In-repo check: `RouteATailBandBound.bandTerminalGate` = `(card rho)*(||Support|| + ||Tail||)`; `||Tail||` decays exp(-B/4), but `||Support(B)||` does NOT decay and sums the `{D<=B}` indices with a fixed op-norm, so `(card rho)*||Support||` diverges as the band covers the infinite carrier. Separately the operator middle (Fourier multiplier) is neither compact/HS/trace-class there. Hence the loop (the load-bearing infinite-carrier Gate) requires Piece 1 - the analytic `(I-P)F=-(I-P)D` identity - and a carrier swap alone cannot close it. Updated 926 with a supersede pointer. RH not claimed.
## Change Log (2026-08-10): Gate-3U fork assessment (evidence-based) + existing-lever audit
- `docs/proofs/926_gate3u_fork_verdict.md`: closure-vs-refutation assessment for the infinite-carrier Gate. Key finding: all nominally-forcing levers are ALREADY in-repo - `norm_sourceActualBandForwardCoframe_le_one` (|F|<=1), `D_S^dag D_S = I + L^dag L`, `|D_S|<=1 <-> L=0` (EndpointContractionGuard), and the numerical (D-J) ~ 0.61-0.62 (probe 884 re-run). So the Gate is down to a single analytic identity `(I-P)F=-(I-P)D` with no in-repo mechanism and adverse numerics; F contains the numerically unreachable Sonin projector R0, blocking a formal refute. Recommendation: pursue Piece-2 carrier re-point (authorized) before betting on closure. RH not claimed.

## Change Log (2026-08-10): Gate-3U frontier reset + numeric reproduction
- `docs/proofs/925_gate3u_frontier.md`: finite-band (route-A) Gate CLOSED (axiom-clean); infinite-carrier Gate OPEN, split into (1) analytic identity `(I-P)F=-(I-P)D` (Proof-717 / docs/872; F contains the unreachable Sonin projector R0) and (2) the carrier/trace-layer seam (docs/860; authorized under AGENTS sec3b). Reprobed 884: anchor 0.6245 exact, flat 0.609-0.620. RH not claimed.

## Change Log (2026-08-09): Gate-3U dichotomy probe leaf (restored from lost working tree)
- `Dev/Gate3UDichotomyProbe.lean`: `emptyFamily`, `leakage_zero_of_visiblePrimes_nil`, `emptyFamily_leakage_zero`, and `gate3UDichotomyObligation` (OPEN converse: nonempty -> nonzero leak). Nil-side of `D_S == J` dichotomy; converse open (docs/872, 872b). RH not claimed.

## Change Log (2026-08-09): Hilbert-side B gate fully closed+axiom-clean (consolidated, build-verified)
Building `HilbertTraceClosure` + `BGateSlotHilbertProbe916` together on the mirror: 3186 jobs green,
`gate_slot_all = [propext, Classical.choice, Quot.sound]`, zero sorry/axiom; `closedTraceModel` builds.
The whole Hilbert archimedean B gate (gate ∀g, trace-template, trace-square, Mellin, sign-norm) is
axiom-clean on Windows source (HilbertCarrierReTypedSymbols + HilbertTraceModelClosure, committed). The
ONLY remaining piece of a real "打穿B" is the mechanical SourceObject/carrier re-wire (route
sourceHilbertGate := gate_slot_all) plus a full cold build of the route consumer chain — architecture
scope, needs a dedicated build window.## Change Log (2026-08-09): 916 gate-slot leaf BUILD-VERIFIED axiom-clean
`Dev/BGateSlotHilbertProbe916.lean` closes the archimedean gate slot on the Hilbert carrier (zero `sorry`, zero new `axiom`):
`gate_slot_all : ∀ g, HilbertCarrierReTyped.hilbertSchmidtGate (reTypedArchimedean) g`, and `#print axioms` =
`[propext, Classical.choice, Quot.sound]` (WSL, 3185 jobs).  This is the finite first half of the B re-route:
the route `sourceHilbertSchmidtGate` (`Objects.CC20TraceObjectPackage`) is satisfiable axiom-free once it
adopts `reTypedArchimedean`.  Lesson: the single persistent mirror is stale-and-dirty — its `.olean` for
`HilbertCarrierReTypedSymbols` was STALE (stored an older `uInfinityNormalized:=False` body while the source
is `True`), so `HilbertTraceModelClosure` appeared broken; deleting the stale `.olean` fixed the build and the
committed source was never wrong.  Per §5, refresh the owning module's `.olean` before concluding a leaf is
broken; never change a committed file on a stale-cache diagnosis. Remaining B work = SourceObject 载体 wiring
(§4 steps 2-3), needs a full cold build. No RH claimed.
## Change Log (2026-08-09): 915 B-lane decision doc — the gate re-route is the sole real Gate-3U/B door; no build this round
`docs/proofs/915_b_gate_reroute_decision.md` pins the B-lane's remaining act: the route
`Objects.CC20TraceObjectPackage.sourceHilbertSchmidtGate : ∀ g, hilbertSchmidtGate g` is currently
axiom-filled, and the only non-empty axiom-clean gate evidence lives on the Hilbert operator
carrier (`Gate_nonempty`, `HilbertTraceModelClosure.closedTraceModel`). Closing B = re-type the
route archimedean.Test to `cc20GlobalLogCrossingL2` and fill that field from `Gate_nonempty`
(Option A). NOT built here: the sole persistent WSL mirror is a different git lineage (`.lake`
7.9G) so a normal re-type + long cold build is a dedicated slot. No RH claimed.
## Change Log (2026-08-08, end-of-session): H2 Dev/UnconditionalSkeleton cold build green
Source-layer landing verified end-to-end. Full mirror sync then lake build
ConnesWeilRH.Dev.UnconditionalSkeleton (flock-guarded, cwr-h2probe1) completed with exit 0:
[3495/3495] Built ConnesWeilRH.Dev.UnconditionalSkeleton, plus intermediary Route/Ledger,
RouteTheorem, CC20RouteRealization, ZetaHalfNonvanishing, S2B1TraceScale, CCM25SourceDataGuards
all green. The hdom wiring at line 688 compiles (the simpa [normalizedCoreSourceAnalyticCoreFromTheorems]
closes the defeq). Axiom audit:
initePrimeDominance_of_certificates =
[propext, Classical.choice, Quot.sound] (axiom-free, 0 sorry); Dev core

ormalizedCoreSourceModelConstructorCoreFromTheorems cascades only into the two pre-existing
...Root axioms (
ormalizedCoreCCM25FinitePrimeArithmeticSourceDataRoot +
ormalizedCoreSourceWeilFormDataRoot),
no sorryAx, no new project axiom. RH not claimed. Prerequisite: synced the full Windows Source tree to the
mirror (32 stale .lean files, incl. CCMSourceDataGuards archived form) before the build; a stale
CCM25SourceDataGuards/FinitePrimeSourceDataBridge gave rror: build failed on the pre-sync run.
## Change Log (2026-08-08): H2 hdom is PROVEN (not assumed) via concrete certs + routed

Follow-up to the H2 landing: `finitePrimeDominance` is not a free assumption at the Source layer.
New lemma `SourceWeilFormData.finitePrimeDominance_of_certificates`
(`Source/AnalyticSourceModel.lean`): from `CCM25Concrete.FinitePrimeInterface.FixedLambdaArithmeticSourceTestCertificates
ForAllTests W.toWeilFormSymbols` the prime-support dominance is derived as `concrete coverage (~ visible (f
g) -> n in globalIndexSet) + narrowed per-common reverse (commonGlobalIndex -> visible common)`. Warm-verified: `AnalyticSourceModel` green (2943 jobs), `#print axioms` = `[propext, Classical.choice, Quot.sound]`, 0 sorry.
MANUSCRIT (UnconditionalSkeleton clean but NOT Dev-cold-built yet): `Dev/UnconditionalSkeleton:688` now passes this
`finitePrimeDominance_of_certificates` (on `normalizedCoreSourceWeilWeilDataRoot` + `normalizedCore...ArithmeticCertificatesFromTheorems`) to `ofSourceAnalyticCore` (which now requires `hdom`). This Dev change transits existing-axiom; full `UnconditionalSkeleton` cold build (>a session) is the remaining verification; not run here. RH not claimed.

## Change Log (2026-08-08): H2 forward-row narrowing LANDED at Source layer, green + axiom-clean

With Peter's authorization (Option A: dominance version), narrowed `PerCommonSourceFinitePrimeSupport` forward rows
from `\u2200 F` to per-`common` in `Source/AnalyticCore.lean` and wired the route. Verified on warm mirror
cwr-h2probe1: `AnalyticCore` + `AnalyticSourceModel` build green (2943 jobs), axioms =
`[propext, Classical.choice, Quot.sound]`, zero sorry. Changes:
- structure `sourceVisibleGlobalIndex` / `sourceVisibleRestrictedIndex` now per-`common; `visible_mem` and the four
  generic theorems (`globalPrimeIndex_mem_of_prime_power_visible`, `globalCoverage`,
  `restrictedPrimeIndex_mem_of_prime_power_visible_cutoff`, `restrictedCoverage`) re-scoped to per-`common.
- three `toWeilFormSymbols_*` wrappers re-scoped to `A.legacy.encode W.common` (via the `*_exact` iff `.mpr`).
- `finite_prime_term_normalization_statement` now takes an explicit `hdom` (route-level dominance):
  per-common coverage cannot derive arbitrary-`convolutionStar f g` coverage, so it needs the dominance hypothesis.
- new `SourceWeilFormData.finitePrimeDominance` def; `SourceWeilFormData.toCCM25SourceModel` and
  `SourceModelConstructorCore.ofSourceAnalyticCore` thread `hdom`.
NOT yet re-wired: `Dev/UnconditionalSkeleton:688` calls `ofSourceAnalyticCore` without `hdom`; supplying it there
needs a concrete-dominance derivation on the (still axiom-mounted) `normalizedCoreSourceWeilFormWeilRoot` source +
a long `UnconditionalSkeleton` cold build (orthogonal to this round). RH not claimed.


# MEMORY.md

Last compressed: 2026-08-10. Prior full text at git HEAD:MEMORY.md and
MEMORY.precompress.backup.md.


## Current Result

Result: the repository does not contain an unconditional proof of the Riemann
Hypothesis.

The corrected global-log crossing phase now has a generic continuous-kernel
Hilbert-Schmidt owner in
`ConnesWeilRH.Source.CC20Concrete.ContinuousKernelHilbertSchmidt`. Its
`pairData_trace_eq_kernel_inner` theorem proves the `A†B` basis trace equals
the paired section integral, with coefficient integrability and absolute
diagonal summability discharged from continuity on compact finite-measure
spaces. `SelectedCrossingKernel` specializes this to the two crossing
orientations on compact source/kernel intervals; its public trace theorem has
no caller-supplied analytic side conditions and the focused audit uses only
`propext`, `Classical.choice`, and `Quot.sound`. The support reduction is now
complete: the two section pairings equal the same selected values `F(b)` and
`F(-b)`, and their traces equal `b F(b)` and `b F(-b)`. After the Euler-log
weight, `eulerLog_weighted_pair_traces_eq_finitePrimeTerm_pow` proves that the
sum of these actual compact `A†B` operator traces is the existing
`finitePrimeTerm (p^m)`. The canonical positive-interval specialization also
discharges the support premise from the existing Yoshida source-test bridge.
The remaining crossing obligation is not the coefficient: it is the
same-object identification of this compact kernel factorization with the
named whole-line `C_h* C_h J_b`/semilocal metric variation, then multi-prime
assembly, the sign gate, and the RH consumer.

The whole-line crossing geometry has since been strengthened in
`GlobalLogCrossing`: `cc20SingleCrossingOperator_coeFn` unfolds the two
half-line indicators, and
`cc20SingleCrossingOperator_coeFn_eq_Icc_indicator` proves that for `b >= 0`
the operator is, almost everywhere, the translated input restricted to
`Icc (-b) 0`. This is the exact length-`b` boundary interval used in the
compact crossing kernels. The remaining bridge is specifically the smoothed
operator identity (`C_h* C_h J_b` versus the compact `A†B` factorization), not
the raw crossing geometry.

Plan 016 Contract M0 is complete at the trace-class interface. The proved
source-normalized identity is

```text
PositiveTrace_(S,Lambda_op)(g)
  = QW_lambda_qw(g,g)
      - Pole_lambda_qw(g)
      + D_(S,Lambda_op)(F_g).
```

Plans 016--023 are rejected as executable RH routes. No active plan currently
meets the guaranteed-route standard. The first rejected Nyman block route is
plan 020: its
finite Nyman--Mobius identities are valid, but its M4 bottom retains the full
inverse-Gram non-cancellation inequality and therefore has not lowered the
RH-producing statement to an independent arithmetic theorem. Plan 021's exact
local divisor-gradient cancellation also fails globally because its future
multiple propagation increases the weighted energy.

The compactness rejection guard is now formalized in
`ConnesWeilRH.Source.CC20Concrete.CompactBadSpace.not_compact_eq_smul_id`.
It proves that a compact operator on an infinite-dimensional complex normed
space cannot equal a nonzero scalar multiple of the identity. The focused
M2/M4 import audit prints only `propext`, `Classical.choice`, and `Quot.sound`.
This is the abstract polarization/compactness guard behind the CC20
`-2 Id + K_I` counterexample; it does not yet encode the concrete CC20
remainder operator or claim that all Connes routes are impossible.

The first 023 feasibility result repairs the rejected Yoshida assembly at the
only valid algebraic level. The theorem
`exists_residualWindow_correction_full_product_interpolation` constructs a
residual-window correction whose complete rescaled convolution product, not
merely its correction factor, has prescribed values on a finite node set. It
requires the rescaled base factor to be nonzero at those nodes. The source and
audit modules build with only `propext`, `Classical.choice`, and `Quot.sound`.
This removes neither the finite-node base-nonvanishing gate nor the coupled
nearby-radius/far-tail gate, so Plan 016 remains rejected and no RH consumer
has been rewired.

The first 017 gate is low-cluster selection, not the final Hurwitz bridge. The
known prolate mechanism creates approximately `2 * lambda^2` near-radical
modes. Therefore a small Rayleigh quotient or a vanishing residual without a
relative spectral gap does not identify the lowest eigenvector. Current source
evidence supplies Gram--Schmidt candidates and numerical/graphical agreement,
but no QW/prolate operator-norm, Riesz-projection, effective-matrix, or relative
gap theorem. The immediate experiment computes the exact first two even
prolate-derived QW matrix entries, bounds coupling to the rest of the growing
cluster, and compares all errors with the proposed first gap. Do not build 017
route wrappers before this gate passes.

The first R1 source audit is partial rather than rejected. For the normalized
`h_0,h_4` prolate combination with zero integral, the remaining point defect is
exactly proportional to `chi_0-chi_2`, while its out-of-band Fourier leakage
norm is an exact combination of `1-chi_0^2` and `1-chi_2^2`. The full Poisson
formula expresses the lower support tail through those two defects. See
`docs/proofs/017_qw_prolate_r1_first_verdict.md`. This creates a concrete
analytic producer candidate below the numerical agreement, but no QW
spectral-projection estimate has been proved.

Keep cluster selection separate from full-bottom ownership. A low prolate
Rayleigh value or a first-even effective matrix cannot exclude lower negative
QW directions. Full-bottom ownership alone does not imply RH: the source
explicitly says that the lowest spectral value need not be nonnegative.
Full-bottom ownership plus a nonnegative lowest eigenvalue along a cofinal
sequence would imply positivity for every compactly supported Weil test and
therefore contains the RH-level arithmetic breakthrough. Treat ownership and
sign as separate gates.

The second R1 audit is also partial. `QW_lambda` is an unbounded closed form,
not an `L2` tail norm, so the exact Fourier leakage norm cannot by itself bound
the proxy's Rayleigh value. A formal truncation identity would follow if
`g_lambda=E(h_lambda)` were a radical vector in a common global form domain,
but the published radical theorem assumes both `h(0)=0` and `integral h=0`.
The finite-`lambda` proxy has zero integral and a nonzero point defect. A new
extended-domain Mellin/explicit-formula theorem and a logarithmic graph-norm
tail bound are therefore required. Qualitative high-frequency coercivity from
the archimedean `log |t|` symbol gives compact resolvent for fixed `lambda`, but
does not control the growing low/intermediate complement uniformly. See
`docs/proofs/017_qw_prolate_tail_and_bottom_verdict.md`.

Plan 017 is rejected as a guaranteed executable route, not as a proof that the
Connes spectral strategy is impossible. The real-zero/Hurwitz implication is
valid, but the large-support even-simplicity condition reduces to an open,
critically tight Herglotz resolvent inequality whose margin is only the
minuscule even/odd ground gap. The Poisson `L2` defect and qualitative
coercivity do not control that relative gap. The required compact-open transfer
from the explicit proxy to the genuine ground state is itself RH-closing and
has no lower projection theorem. See
`docs/proofs/017_final_feasibility_verdict.md`. Do not implement R2--R5 under
017 without a new arithmetic near-resonance theorem.

Plan 018 was the next feasibility experiment. No route currently meets the
project's guaranteed-route standard. Its selected object was Suzuki's explicit
unconditional screw-norm defect
`Delta(t) = ||S_t||_2^2/(2*pi) + g(t)`. Its half-line vanishing is equivalent
to RH, so it is not yet a producer. The next admissible milestone is an exact
unconditional off-critical defect formula followed by a sign, evolution, or
uniqueness theorem that forces `Delta=0` without importing Weil positivity.

CC20 fixes the remainder sign as `+D`; CCM25 fixes the restricted form as
archimedean plus pole minus finite primes. The route's vanishing conditions
kill the pole. They do not kill `D`. The proof certificate is
`docs/proofs/016_corrected_trace_identity.md`.

`lambda_qw` and `Lambda_op` are different source parameters. The first bounds
the CCM25 support window and prime-power sum. The second defines the operator
cutoff projections. No checked source proves their equality.

Plan 012 has a source-level mathematical rejection. The direct fixed-S
commutator argument constructs the selected Hilbert-Schmidt operator and its
`L2` kernel, but the active no-defect consumer is false for the genuine CC20
model. The evidence is recorded in:

```text
docs/proofs/cc20-012-mathematical-verdict.md
```

CC20 Theorem `thmqkey1` gives

```text
D o Q(xi * xi^*) = inner(xi, (-2 Id + K_I) xi)
```

with `K_I` compact Hilbert-Schmidt. On the infinite-dimensional zero-integral
subspace this form cannot vanish identically. A compact smooth witness yields
a positive-definite test that vanishes at `0` and `+/- i/2` but has nonzero
trace remainder. Thus the current exact equality
`supportSquareTrace = qwLambda` cannot be produced from the source operator.
Both 012 roots remain active, and no Lean file was changed for this verdict.

The final target is:

```text
_root_.RiemannHypothesis
```

The current theorem is conditional in two independent ways. Its axiom graph
contains the six project roots below, and its full type contains an
unconstructed typeclass premise:

```text
unconditional_rh_skeleton :
  forall [NormalizedSelectedSourceCoreTraceQWLambdaCalibrationProvider],
    RiemannHypothesis
```

`#print axioms` alone does not reveal ordinary or typeclass premises. Final
audits must print both the complete theorem type and its axioms.

The theorem `unconditional_rh_skeleton` compiles, but its axiom graph still
contains six project roots:

```text
normalizedCoreCC20PropositionC1SourceCriterionRoot
normalizedCoreCCM25FinitePrimeArithmeticSourceDataRoot
normalizedCoreS2B1RemainderRowsOutsideNoBulkRoot
normalizedCoreS2B1TracePackageRemaindersRoot
normalizedCoreSourceWeilFormDataRoot
normalizedSelectedFinalRouteDetectorCriterionCoverageRoot
```

The first and last roots are RH-level:

```text
normalizedCoreCC20PropositionC1SourceCriterionRoot
normalizedSelectedFinalRouteDetectorCriterionCoverageRoot
```

Closing the other four data roots cannot prove RH while either RH-level root
remains active.

## Current Dependency Map

```text
unconditional_rh_skeleton
  |
  +-- B2 scalar-calibration provider                 [implicit premise]
  |
  +-- CC20 Proposition C1 source criterion            [RH-level]
  |
  +-- CCM25 finite-prime arithmetic source data       [016 M1; historical 013]
  |
  +-- S2-B1 remainder rows outside no-bulk            [016 M0-M4; historical 012]
  |
  +-- S2-B1 trace-package remainders                  [016 M0-M4; historical 012]
  |
  +-- source Weil-form data                           [016 M1; historical 013]
  |
  +-- selected detector criterion coverage            [RH-level; 016 M5-M6]
```

Remaining work has one active entrypoint:

```text
016  unified remaining gaps
```

Plans 012-014 remain historical evidence. Plan 016 absorbs their unfinished
work and the proposed 015 audit. Its central theorem is conditioned Yoshida
detector existence for the finite bad remainder space.

## 011 Accepted Result

Plan:

```text
plan/011_2026-07-10_S2B1_matched_scalar_identification_plan.md
```

The false universal scalar family was rejected by a zero/bump counterexample,
and the old no-argument scalar root was removed. The matched B2 scalar now comes
from the same `SourceTraceReadOffData` object used by the route.

Named evidence:

```text
not_normalizedCoreS2B1ActualScalarIdentificationFamily
normalizedSeedQWLambdaScalarIdentificationOfNormalizedPackageTraceData
normalizedSeedQWLambdaScalarIdentification_nonempty_iff_supportSquareQWLambdaReadOffSourceData
normalizedRouteBackedCC20SquareRestrictedSupportSquareQWLambda_of_traceFrontComparisonSplitB2Rows
normalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonQWPoleRows_nonempty_iff_components
```

The B2 route projection is proved. The QW/pole route remains B3/RH-level and is
not a lower producer.

## Current Analytic Model Gap

Three definitional theorems expose the present model:

```text
normalizedCoreTraceAmplitude_eq_encodedEvaluationNorm
normalizedCoreConvolutionStar_eq_add
normalizedCoreHilbertSchmidtGate_iff_traceClass_cyclicLegal
```

Their content is:

```text
trace amplitude = norm of the encoded test at zero
convolution      = pointwise addition
HS gate          = traceClass and cyclicLegal
```

This model has no concrete integral operator, Schwartz kernel, Hilbert-Schmidt
norm, trace-class positive square, or ordinary infinite-dimensional trace.
`SourceCanonicalHilbertModelData` supplies a Hilbert carrier and coordinate
equivalence only. `SourceScalingActionData` supplies continuous linear scaling
maps and group laws only.

Mathlib v4.30.0 contains finite-dimensional trace results in:

```text
Mathlib/Analysis/InnerProductSpace/Trace.lean
```

The repository search found no reusable infinite-dimensional
`HilbertSchmidtOperator`, `IsHilbertSchmidt`, or `TraceClass` framework. The
historical 012 design therefore selected a project-local measurable kernel
layer. Plan 016 Contract M2 retains that choice for the valid positive-trace
theorem. The layer uses an explicit nuclear decomposition to define ordinary
trace, proves agreement with every countable orthonormal-basis diagonal series,
and then proves equality with the kernel norm-square integral for the selected
positive square.

## 012 Ownership Correction

The first review of the historical plan 012 found a circular input boundary.
The existing
`SourceTraceReadOffData` already stores:

```text
hilbertSchmidtGate
positiveTraceNonnegative
fullTraceReadOffBridge
restrictedTraceReadOffBridge
```

It cannot produce the operator, Hilbert-Schmidt witness, ordinary trace, or
read-off theorem that those fields represent. Plan 012 therefore started from a
`SourceCC20PreTraceInputData` owner containing only route/test identity,
fixed-S/window/cutoff data, coordinate rows, and admissibility. The completed
analytic owner was meant to construct `SourceTraceReadOffData` downstream.
The later no-defect counterexample rejected that final projection. Plan 016
replaces it with a corrected owner that retains the source remainder `D_S`.

The same review established four additional gates:

```text
P and P_hat must be self-adjoint idempotents
theta(g*) must be the adjoint and represent the convolution square
ordinary trace must be independent of the kernel-mass definition
the complex ordinary trace must equal the real A* A kernel mass explicitly
remainder scalars must unfold to evaluations, defect operators, or strip data
```

One bounded factor and one Hilbert-Schmidt factor produce a Hilbert-Schmidt
product, not a trace-class product. Each cyclic trace move must use either two
Hilbert-Schmidt factors or a trace-class/bounded pair.

The historical execution-readiness review split the former circular Phase 0
into two gates:

```text
Phase 0A  source certificates for the fixed-S kernel and remainder transport
Phase 0B  generic L2 operator and nuclear-trace foundations
Phase 1   exact selected operator and kernel
Phase 2   fixed-S estimate for that kernel and Hilbert-Schmidt construction
```

The first source-only audit selected Fork B/F/H. A later direct mathematical
derivation superseded that feasibility judgment:

```text
K_S-invariant scattering coordinate     available
commutator Hilbert-Schmidt estimate      proved
L2 kernel representation                 proved
exact no-defect trace read-off            false
```

The evidence is recorded in:

```text
docs/proofs/cc20-fixed-s-kernel-source-certificate.md
docs/proofs/cc20-fixed-s-remainder-source-certificate.md
```

The direct proof uses CCM24's unitary scattering coordinate rather than the
nonunitary map `eta_S`. It writes the compressed operator as a sum of two
cross-half-line commutators. Their weighted `L2` kernel norms prove the
Hilbert-Schmidt property and give the ordinary positive trace.

The current consumer still cannot use that operator. CC20 Theorem `thmqkey1`
shows that its omitted remainder equals the quadratic form of `-2 Id + K_I`,
where `K_I` is compact Hilbert-Schmidt. That form does not vanish on the full
triple-vanishing test class. Plan 012 is rejected rather than blocked.

The 2026-07-10 WSL ext4 verification built
`ConnesWeilRH.Dev.UnconditionalSkeleton`. The first attempt replayed a stale
`ObjectTheoremBasePackage` import artifact and could not see its new constructor
input. Rebuilding that owning module repaired the cache, and the Dev target then
passed. An import-facing scratch audit printed these project roots for
`unconditional_rh_skeleton`:

```text
normalizedCoreCC20PropositionC1SourceCriterionRoot
normalizedCoreCCM25FinitePrimeArithmeticSourceDataRoot
normalizedCoreS2B1RemainderRowsOutsideNoBulkRoot
normalizedCoreS2B1TracePackageRemaindersRoot
normalizedCoreSourceWeilFormDataRoot
normalizedSelectedFinalRouteDetectorCriterionCoverageRoot
```

The focused output contained the Mathlib foundations `propext`,
`Classical.choice`, and `Quot.sound`, plus those six project roots. It contained
no `sorryAx`. Both 012 roots remain active after a fresh import-facing build.

The repository's first Lean API bottom is
`SourceCC20FixedSQuotientMeasureCoordinate`. `RouteInputs.ccm24` exposes the
canonical model, scaling action, Fourier grading, and comparison maps only as
Props. `SourceCanonicalHilbertModelData` supplies an arbitrary real Hilbert
carrier without a measure or complex `L2` realization. Mathlib has an adele-ring
type but no repository-visible `X_S=A_S/O_S^*` quotient measure, semilocal
Fourier `L2` operator, or cutoff projections.

The project-local trace contract now uses an explicit countable nuclear
decomposition. `SourceCC20OrdinaryTrace` is the absolutely summable nuclear
series; basis-series equality supplies basis and decomposition independence.
The fixed-S estimate is proved only after Phase 1 constructs the exact
`operatorKernel`, removing the old Phase 0/Phase 1 dependency cycle.
`SourceCC20KernelCoordinateData` belongs to the pure
`Source/CC20KernelCoordinate.lean` module so Phase 0B trace foundations do not
depend on the Phase 1 operator module.

## Active Mathematical Boundaries

### CC20 trace boundary

The source paper uses the positive compressed scaling trace on
`L^2(R)^ev`:

```text
Tr(theta(g) S theta(g)*)
```

The project manuscript uses the fixed-S operator:

```text
A_(S,Lambda_op,g)
  = P_hat_(S,G)(Lambda_op) P_(S,G)(Lambda_op) theta_S(g)

PositiveTrace = Tr(A* A)
```

Plan 016 must keep the route test `g`, convolution square, operator, kernel,
Hilbert-Schmidt norm, positive trace, `QW_lambda_qw`, pole pairing, and nonzero
remainder `D_(S,Lambda_op)` on one data-bearing owner. It must keep
`lambda_qw` separate from `Lambda_op` and forbids the old no-defect projection.

### CCM25 finite-prime boundary

The current canonical source-data route must preserve one concrete owner across
source-Weil-form data, visible arithmetic, canonical atoms, package certificate
data, and direct term masses. Equality of `WeilFormSymbols` alone cannot
transport data whose type depends on the full owner.

Plan 013 owns:

```text
normalizedCoreSourceWeilFormDataRoot
normalizedCoreCCM25FinitePrimeArithmeticSourceDataRoot
```

Do not reopen support/visible wrappers, package read-off wrappers, evaluator
mass spellings, or route-symbol mass spellings as lower roots unless a named
Lean theorem rejects the canonical owner path.

Plan 013 Phase 0A produced that rejection for the current owner type. The
theorem

```text
CCM25SourceDataGuards.not_nonempty_concreteSourceWeilFormData
```

is axiom-free apart from `propext`, `Classical.choice`, and `Quot.sound`. It
uses a compact smooth bump with value `1` at `2`: the old global support
quantifier forces its finite-prime term at `2` to be zero, while the concrete
evaluator and `vonMangoldt(2) = log(2) > 0` make the same term positive. Thus
`normalizedCoreSourceWeilFormDataRoot` is an inconsistent root, not an
unfinished constructor target.

The replacement source bottom now compiles in three modules:

```text
CompactLogConvolution
  genuine f*(x) = star(f(-x)) and additive integral convolution

SelectedWeilSquare
  one compact test, its definitional square, support radius, exact finite
  global/restricted prime-power sets, and complex phase-preserving values

SelectedWeilFormula
  pole, archimedean, global-prime, and restricted-prime definitions on the
  same square owner
```

The remaining selected-CCM25 bottom in plan 016 Contract M1 is a proof that the
explicit archimedean integrand is integrable on `(0, infinity)`. The two roots
inherited from 013 remain active; no route consumer has been rewired yet.

### B3 and detector boundary

Detector-only coverage, QW/pole collapse, global mass cancellation, and the
selected final detector criterion have named equivalence guards at the
no-off-line-zero or RH level. They cannot close plan 016 from below.

Plan 016 Contracts M3-M6 must prove or reject the semilocal remainder normal
form, finite bad-space sign, conditioned detector, and global contradiction.
The RH-level detector outlet cannot serve as an input to those contracts.

The 2026-07-10 root audit proved the exact guards:

```text
normalizedRouteBackedCC20SquareRestrictedDetectorCriterionCoverage_iff_standardSourceRH
normalizedRouteBackedCC20SquareRestrictedDetectorCriterionCoverage_iff_mathlibRH
```

Their focused axiom output contains only `propext`, `Classical.choice`, and
`Quot.sound`. CC20 Proposition C.1 states the same global Weil-positivity/RH
equivalence. CCM25, the 2026 screw-function work, and the finite Guinand-Weil
dictionary do not supply the missing global positivity theorem. Plan 016 owns
the duplicate C1 root, hidden provider, and final detector root; the historical
014 audit supplies the rejection guards.

## 013 Windows Port

The selected CCM25 foundation from commit `07f946c` was ported file by file
into the Windows source of truth. Five new files match the remote blobs exactly;
the two existing files received only the reviewed import and guard additions.

The Windows snapshot passed these WSL ext4 targets:

```text
CompactLogConvolution
SelectedWeilSquare
SelectedWeilFormula
SelectedArchimedeanIntegrability
CCM25Concrete
CCM25SourceDataGuards
UnconditionalSkeleton
```

Both source-data rejection guards depend only on Mathlib foundations. The RH
skeleton still contains the same six project roots and the hidden provider.

## Rejected Shortcuts

Do not count any of these as proof progress:

```text
True or Set.univ producer fields
an arbitrary positiveTrace scalar
traceClass : Prop with no named operator
cyclicLegal : Prop with no per-move witnesses
stored Mellin or determinant rows
selected-test read-off presented as all-test coverage
SourceRH or no-off-line source-zero used as a producer
detector-only calibration used as 08A closure
equality of route symbols used to cast dependent canonical-owner data
moving between equivalent mass/package spellings
```

The accepted direction is data-bearing ownership followed by projection into
legacy route records.

## Lean Rules Worth Remembering

### Row-record destructuring

For an existential plus a conjunction whose final item is a structure, split
the outer pair before extracting the structure:

```lean
rcases h with ⟨r, hmatch⟩
have hr := hmatch.1
have rows := hmatch.2
```

A flat `rcases h with ⟨r, hr, rows⟩` can recursively destruct the final record.

### Type versus Prop

A data-bearing structure lives in `Type`. Use:

```text
P and Nonempty Rows
```

when only existence is needed, or use a Sigma/data structure when later code
must retain the witness. Do not write a `Type` record directly as a conjunct of
a proposition.

### Dependent owner transport

`owner.sameSymbols : routeSymbols = ownerSymbols` does not transport
certificate data that depends on the entire owner. Use a theorem that states
the required equality or `HEq` for every dependent component. Keep unproved
transport experiments outside compiled route APIs.

### Constructor names

When an inductive constructor has a mathematical name such as `rho`, use a
different local parameter name and write `.rho` at call sites.

### Import artifacts

Direct `lake env lean File.lean` can pass while imported `.olean` artifacts are
stale. Accepted verification requires an importing scratch file with `#check`
and `#print axioms`. If the import misses a new declaration after the smallest
build, remove only that module's stale artifacts and rebuild that target.

## Verification State

The unified 011 verification passed:

```text
WSL ext4 build targets: 5/5 passed
import-facing #check: passed
focused #print axioms: passed
sorryAx: absent from audited declarations
removed universal scalar root: absent
```

This verification applies to the current dirty Lean changes listed below. The
documentation compression and plan 016 do not change Lean, so they do not need
a new Lake build.

## Worktree State At Compression

The Windows repository is the sole source of truth. All source and document
edits, Git status decisions, commits, and pushes must happen there. WSL ext4
directories are disposable verification mirrors populated one way from the
Windows snapshot; WSL diffs and commits are not accepted project state.

As of 2026-07-10, Windows `main` is `c59e955` and `origin/main` is `07f946c`.
After fetching, `git rev-list --left-right --count HEAD...origin/main` reports
`6 179`. Do not resolve this divergence from WSL and do not overwrite Windows
with the remote branch. Any later reconciliation must preserve Windows as the
authority and inspect both histories before changing refs.

Completed 011 lane changes:

```text
ConnesWeilRH/Dev/UnconditionalSkeleton.lean
ConnesWeilRH/Route/CC20RouteRealization.lean
ConnesWeilRH/Route/TraceFrontEnd.lean
ConnesWeilRH/Source/ObjectTheoremBasePackage.lean
ConnesWeilRH/Source/S2B1TraceScale.lean
```

Pre-existing user changes must be preserved:

```text
ConnesWeilRH/Source/CCM25Concrete/FinitePrimeSourceDataBridge.lean
ConnesWeilRH/Source/CCM25Concrete/PrimePowerArithmetic.lean
```

Never reset, overwrite, or clean these paths as part of another lane.

## Verification Workflow

Edit and manage Git only in the Windows repository. Sync its source snapshot
one way into WSL2 on ext4 for Lean verification. Never run Lake with Windows
Lean or from `/mnt/c`, and never commit or push from a WSL verification mirror.

Preferred persistent mirror:

```text
/home/peter/verify/Connes-Weil-RH-Proof
```

Before reuse, run `git rev-parse --show-toplevel`. If it does not return the
project mirror itself, create a fresh ext4 verification directory, seed its
`.lake` from the persistent cache, and copy sources while excluding `.git` and
`.lake`.

All Lake commands use:

```text
flock -w 1800 /tmp/connes-weil-rh-lake.lock lake build <smallest-target>
```

Verification order:

```text
direct Lean check while editing
smallest owning module build
import-facing #check
focused #print axioms
route/Dev build only at a milestone
shortcut scan
git diff --check
```

## Public Hygiene

Before any commit or push, inspect staged file names and staged content. Root
workflow files are private unless the repository explicitly owns them as public
artifacts.

Do not publish local absolute paths, verification directory names, private
workflow artifacts, JSON escape fragments, or mojibake in GitHub text. Read
back every public body or comment after posting.

## Next Frontier

Execute:

```text
plan/016_2026-07-10_unified_remaining_gaps_plan.md
```




## Archived narrative (superseded; full text kept in git HEAD and docs/proofs)
Compressed 2026-08-10. Removed long sections whose full content is preserved
unchanged in committed git history (HEAD:MEMORY.md) and/or docs/proofs/:
  - the `# MEMORY.md` narrative body (dated recovery narrative back to ~2026-07-29);
  - the July 2026 blocks: Yoshida Model Rejection, Rejection-First Route Order,
    Plans 016/018/019/020/021/022, `## 2026-07-11 Qeasy Full-Product Positive Base`,
    and the two giants `Proof 541` (quantitative polar Julia slot bound) and
    `Proof 542` (non-polar gap factor bridge), ~26.5k lines combined.
Per AGENTS cadence MEMORY lines rot out on route-milestone merit scans; git + docs/
proofs own the full narrative. Current route state lives below (## Current Result ..
## Next Frontier) and in docs/proofs/925 (frontier), 926 (fork), 927 (Piece-2),
928 (route root), 929 (factor norm).



## Change Log (2026-08-09): 917 Hilbert CC20Interface layer build-verified axiom-clean
New Dev/BCC20InterfaceHilbertProbe917.lean: assembles `Source.CC20Interface` from
`HilbertTraceModelClosure.closedTraceModel` rows + Gate_nonempty, on
`RHDefinitionBridge.standard`, with the terminal finite-vanishing RH exit carried
as an argument. `#print axioms` = [propext, Classical.choice, Quot.sound], zero
sorry/axiom (WSL-verified, mirror lineage caveat). This closes the Hilbert
`RouteInputs.cc20` interface layer of the B re-route. True B door
(`fullWeilPositivity`) still needs a coherent Hilbert-backed route frame
(re-route 915 §4 steps 2-3) + full cold build. RH not claimed.


## Change Log (2026-08-09): Route-1 trusted baseline DONE; routes 2 & 3 verdict recorded
Route1: created isolated ext4 dir /home/peter/verify/cwr-b917, synced Windows HEAD
(b3e3fce+untracked), seeded .lake/packages from main mirror, `lake build
ConnesWeilRH.Dev.BCC20InterfaceHilbertProbe917` = 3187 jobs clean; axioms for
cc20InterfaceOfHilbertCarrier + gateSlotInInterface = [propext, Classical.choice,
Quot.sound], zero sorry. Fixed 917 docstring lint. Route2 (scan) NEGATIVE: the
only `fullWeilPositivity` producer is `Route.FullWeilPositivity`, gated by the
source model — no non-full-frame witness exists. Route3 (re-type to Hilbert) is
blocked at a documented false-premise source bottom: `UnconditionalSkeleton` L137
axiom `normalizedCoreSourceWeilFormDataRoot` vs L152 `not_nonempty` contradiction,
pointwise-additive (non-Mellin) convolution, plus L657/L1551 (docs 831/833/834).
Faking closure would violate the integrity guards; the fix is the ~31-file/200-edit
shared-type source-model refactor (831 blast), NOT a build-hack. RH not claimed.


## Change Log (2026-08-09): S1 L137 axiom REPLACED by real concrete SourceWeilFormData (build-verified)
New Dev/ConcreteP1SupportProbe.lean: builds a `PerCommonSourceFinitePrimeSupport`
on `concreteTestAlgebra` with exact index `{2}` (common bump, value 1 at t=2, prime
2 term strictly positive), lifted to `SourceWeilFormData concreteTestAlgebra`.
`#print axioms concreteWellForm` = [propext, Classical.choice, Quot.sound].
Replaced the false axiom `normalizedCoreSourceWeilFormDataRoot` (L137) in
`UnconditionalSkeleton` with `Source.Dev.ConcreteP1SupportProbe.concreteWeilForm`;
module builds (3500 jobs) on cwr-b917. Audit: `normalizedCoreSourceAnalyticCore
FromTheorems` = [propext, Classical.choice, Quot.sound] (L137 gone);
`normalizedCoreSourceModelConstructorCoreFromTheorems` still needs
`normalizedCoreCCM25FinitePrimeArithmeticSourceDataRoot` (= L657, a SEPARATE
source bottom, not addressed by S1). RH not claimed.


## Change Log (2026-08-09): L657 (CCM25 finite-prime arithmetic source data) assessed
`normalizedCoreCCM25FinitePrimeArithmeticSourceDataRoot` (UnconditionalSkeleton L657)
is `CommonFinitePrimeArithmeticSourceData W` (W = normalizedCoreSourceAnalyticCore
FromTheorems.toWeilFormSymbols, now real post-S1).  NOT a plain existence like L137:
it requires (a) `finitePrimeData` = ∀ test-pair lambda certs via
`FinitePrimeSourceDataBridge.ofSourceEvaluationVisibleCanonicalData`, and
(b) `scopedArchimedeanContributionBalance` = a real scalar equality (restricted
Welplicit formula == global formula).  No real `def : CommonFinitePrimeArithmeticSourceData`
exists yet in-repo (only statement probes Parallel09A/B).  Replacing L657 is the
next real S-construction: (1) finitePrimeData from the per-common prime-2 arithmetic
read-offs, (2) the scoped balance identity. Mutiana-obligation, not a seam. RH unclaimed.


## Change Log (2026-08-09): L657 Step-A is blocked by non-Mellin concrete convolution
Traced the `finitePrimeData` ship mile: `FinitePrimeArithmeticSourceData.certificateData`
is the `¥ f g lambda hlambda` finite-prime arithmetic family, built on
`W.convolutionStar`.  The concrete skeleton carrier has `convolutionStar = f + g`
(pointwise ADDITION), and `not_normalizedCC20MellinConvolutionLaw`
(CC20YoshidaConstruction:2727) proves the Mellin-convolution law fails on it
(doubles instead of squaring).  So a sound all-pair finite-prime family cannot be
built on the current concrete carrier.  L657/A roots back to the source-convolution
redefinition (the AGENTS '复合 carrier需重定义' root), not to a missing seam.  Forcing it
would be unsound. RH unclaimed.
