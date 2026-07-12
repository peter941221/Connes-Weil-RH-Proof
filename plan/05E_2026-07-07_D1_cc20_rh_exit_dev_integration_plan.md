# 05E D1 CC20 RH Exit Dev Integration Plan

Date: 2026-07-07

Status: final integration shard for Plan 05.  Do not start this shard until
05A and 05D are Good.

Execution correction, 2026-07-08:
  The accepted Dev integration direction is now the selected finite-vanishing
  route API, not the old all-input `CC20RHExitObjectPackage` C.1 field.  The
  final no-argument Dev outlets should consume:

  ```text
  Source.CC20FiniteVanishingWeilCriterion
    Source.normalizedCC20TestSpace Source.cc20TripleFiniteVanishingSet
  Route.normalizedCC20_source_rh_of_finite_vanishing_criterion
  ```

  with the concrete finite-vanishing criterion exposed as the explicit
  remaining root.  Do not close 05E by defining
  `CC20RHExitObjectPackage.propositionC1SourceCriterion` as a constant function
  returning selected SourceRH; that only disguises the selected route as the
  rejected all-input package.  Also do not recreate a selected
  `normalizedCC20FiniteVanishingWeilCriterionInput.tripleVanishing` root: for
  the current concrete carrier, that would assert all compact normalized CC20
  tests Mellin-vanish at `{0, 1/2, 1}`, which is the wrong semantic shape.

Execution correction, 2026-07-08, route-backed sign root:
  The previous forall-`g` half-density route is rejected as the active 05E
  root.  The counterexample guard is:

  ```text
  Source.CC20YoshidaInterpolationNode.exists_normalizedCC20_halfDensityPoleSum_counterexample
  Source.CC20YoshidaInterpolationNode.not_normalizedCC20FiniteVanishingToHalfDensityPoleSumNonnegative
  ```

  The current accepted root is route-backed/source-backed sign realization for
  each concrete Yoshida detector:

  ```text
  Dev.normalizedSelectedRouteBackedYoshidaDetectorTraceRealizerFromTheorems
    : Route.NormalizedRouteBackedYoshidaDetectorTraceRealizer
  ```

  This root is intentionally below the old sign-family wrapper.  The clean
  wrapper chain is:

  ```text
  normalizedSelectedRouteBackedYoshidaDetectorTraceRealizerFromTheorems
    -> Route.normalizedRouteBackedYoshidaDetectorRouteRealizer_of_trace_realizer
    -> normalizedSelectedRouteBackedYoshidaDetectorRouteRealizerFromTheorems
    -> Route.normalizedRouteBackedYoshidaDetectorSignRealizer_of_route_realizer
    -> normalizedSelectedRouteBackedYoshidaDetectorSignRealizerFromTheorems
    -> Route.normalizedRouteBackedYoshidaSignFamily_of_detector_realizer
    -> normalizedSelectedRouteBackedYoshidaSignFamilyFromTheorems
    -> Route.normalizedCC20_source_rh_of_routeBacked_yoshida_sign_family
    -> normalizedSelectedRouteBackedSourceRHFromTheorems
  ```

  Hard gate:

  ```text
  old weak path:
    Source.NormalizedCC20FiniteVanishingToHalfDensityPoleSumNonnegative
    Source.NormalizedCC20FiniteVanishingToPolePairingSign
    Source.CC20FiniteVanishingWeilCriterion
    old all-input CC20RHExitObjectPackage.propositionC1SourceCriterion

  new semantic owner/API:
    Route.NormalizedRouteBackedYoshidaDetectorTraceRealizer
    Route.NormalizedRouteBackedYoshidaDetectorTraceRealization detector
    Route.NormalizedRouteBackedYoshidaDetectorRouteRealizer
    Route.NormalizedRouteBackedYoshidaDetectorRouteRealization detector

  real consumer rewired:
    Dev.normalizedSelectedRouteBackedYoshidaSignFamilyFromTheorems
    Dev.normalizedSelectedRouteBackedSourceRHFromTheorems
    Dev.normalizedSelectedCC20ExitPackageFromTheorems
    Dev.normalizedNoArgumentRouteCertificatePackageFromTheorems
    Dev.unconditional_rh_skeleton

  same-object alias / wrapper rejection scan:
    Do not fill the new root from a selected fixed route certificate unless
    it is proven to use the same `detector.test`.
    Do not return stored SourceRH.
    Do not use accepted-source fields, `True`, `Set.univ`, the old all-input
    C.1 package, or the rejected forall-`g` half-density sign theorem.

  smallest WSL build:
    lake build ConnesWeilRH.Route.CC20RouteRealization
    lake build ConnesWeilRH.Dev.UnconditionalSkeleton

  focused axiom audit targets:
    Route.normalizedRouteBackedYoshidaDetectorSignRealizer_of_route_realizer
    Route.normalizedRouteBackedYoshidaDetectorRouteRealizer_of_trace_realizer
    Route.normalizedRouteBackedYoshidaSignFamily_of_detector_realizer
    Route.normalizedCC20_source_rh_of_routeBacked_yoshida_sign_family
    Dev.normalizedSelectedRouteBackedYoshidaDetectorTraceRealizerFromTheorems
    Dev.normalizedSelectedRouteBackedYoshidaDetectorRouteRealizerFromTheorems
    Dev.normalizedSelectedRouteBackedYoshidaDetectorSignRealizerFromTheorems
    Dev.normalizedSelectedRouteBackedSourceRHFromTheorems
    Dev.unconditional_rh_skeleton

  semantic sufficiency for next route/RH step:
    For every detector produced by 05C, the route layer must build a
    same-test source trace read-off and local-sum read-off after the now-clean
    detector-specific fixed-S construction. Then the existing Yoshida
    contradiction proves the no-argument SourceRH.
  ```

  Attack tree:

  ```text
  05E route-backed/source-backed sign theorem
  |
  +-- target root
  |   |
  |   +-- normalizedSelectedRouteBackedYoshidaDetectorTraceRealizerFromTheorems
  |       |
  |       +-- forall detector :
  |           YoshidaDetector normalizedCC20TestSpace cc20TripleFiniteVanishingSet rho
  |           produce Nonempty
  |             NormalizedRouteBackedYoshidaDetectorTraceRealization detector
  |
  +-- clean per-detector fixed-S layer
  |   |
  |   +-- inputs : RouteInputs
  |   |
  |   +-- baseSourceBackedTest : SourceBackedFixedSTest inputs
  |   |
  |   +-- finitePrimeSourceDataOwner :
  |   |     CommonFinitePrimeArithmeticSourceData inputs.ccm25.weilSymbols
  |   |
  |   +-- sourceBackedFixedSTestWithNormalizedYoshidaDetector
  |       |
  |       +-- same route test by rfl:
  |       |   normalizedCC20TestSpace.toRouteTest detector.test
  |       |
  |       +-- triple rows from detector.vanishesOnF
  |       |
  |       +-- finite-prime rows from
  |           fixedLambdaArithmeticSourceTestCertificatesForAllTests
  |
  +-- active per-detector trace realization fields
  |   |
  |   +-- sourceTraceReadOff : SourceRouteTraceData inputs
  |   |     (sourceBackedFixedSTestWithNormalizedYoshidaDetector ...)
  |   |
  |   +-- routeBackedLocalSumReadOff :
  |       normalizedCC20TestSpace.weilLocalSum
  |         (normalizedCC20TestSpace.starConvolution detector.test)
  |       =
  |       -inputs.cc20.archimedeanSymbols.positiveTrace archimedeanTest
  |
  +-- clean route wrapper
  |   |
  |   +-- RouteLedgerClearingData.ofSourceBacked
  |   |
  |   +-- source_common_test_tuple_contract_of_package
  |   |
  |   +-- normalizedRouteBackedYoshidaDetectorRouteRealization_of_trace_realization
  |   |
  |   +-- source_qw_nonnegative_to_cc20_nonpositive_of_common_test_parts
  |   |
  |   +-- route_bridge_certificate_of_sign_defect_classification
  |   |
  |   +-- route_backed_cc20_exit_input_data_of_route_bridge_certificate
  |   |
  |   +-- normalizedRouteBackedYoshidaDetectorSignWitness_of_route_realization
  |
  +-- current mathlib-bottom candidates
  |   |
  |   +-- detector-parametric archimedean trace realization:
  |   |     build `archimedeanTest` and prove the local-sum read-off
  |   |     for the actual `detector.test`
  |   |
  |   +-- missing API:
  |       map or realize each concrete CC20 detector test as an
        `inputs.cc20.archimedeanSymbols.Test`, then prove
        `SourceRouteTraceData` and the exact local-sum/positiveTrace identity
  |
  +-- rejected shortcuts
      |
      +-- old forall-g half-density/polePairing sign theorem
      +-- selected fixed route certificate for all detectors
      +-- old all-input C.1 package constant SourceRH
      +-- selected SourceRH field
      +-- accepted-source theorem/field
      +-- True / Set.univ / raw stored RH
  ```

  Execution result, 2026-07-08:

  ```text
  Clean without `sorryAx`:
    Route.sourceBackedFixedSTestWithNormalizedYoshidaDetector
    Route.normalizedRouteBackedYoshidaDetectorRouteRealization_of_trace_realization
    Route.normalizedRouteBackedYoshidaDetectorRouteRealizer_of_trace_realizer
    Route.normalizedRouteBackedYoshidaDetectorSignRealizer_of_route_realizer

  Remaining `sorryAx` root:
    Dev.normalizedSelectedRouteBackedYoshidaDetectorTraceRealizerFromTheorems

  Focused WSL build:
    lake build ConnesWeilRH.Route.CC20RouteRealization
      ConnesWeilRH.Dev.UnconditionalSkeleton
  ```

Execution correction, 2026-07-08, pole-pairing lowering:
  The selected finite-vanishing criterion is now lowered to the concrete
  half-density Mellin pole-sum provider:

  ```text
  Source.NormalizedCC20FiniteVanishingToHalfDensityPoleSumNonnegative
    -> Source.NormalizedCC20FiniteVanishingToPolePairingSign
    -> Source.NormalizedCC20PolePairingNonnegativeOnFiniteVanishing
    -> Source.CC20FiniteVanishingWeilCriterion
  ```

  The intermediate pole-pairing provider remains visible as a clean wrapper:

  ```text
  Source.NormalizedCC20FiniteVanishingToPolePairingSign
  ```

  The wrappers below this root are compatibility structure, not blockers:

  ```text
  normalizedSelectedCC20FiniteVanishingToHalfDensityPoleSumFromTheorems
    -> Source.normalizedCC20_finiteVanishingToPolePairingSign_of_halfDensityPoleSum
    -> normalizedSelectedCC20FiniteVanishingToPolePairingSignFromTheorems
    -> Source.normalizedCC20_polePairing_nonnegative_of_finiteVanishingToPolePairingSign
    -> normalizedSelectedCC20PolePairingNonnegativeOnFiniteVanishingFromTheorems
    -> Source.normalizedCC20_finite_vanishing_weil_criterion_of_polePairing_nonnegative
    -> normalizedSelectedCC20FiniteVanishingCriterionRowsFromTheorems
    -> Route.normalizedCC20_source_rh_of_finite_vanishing_criterion
    -> normalizedSelectedCC20SourceRHFromTheorems
  ```

  The active mathematical target is the forall-`g` half-density statement:

  ```lean
  ∀ g : Source.normalizedCC20ConcreteTestAlgebra.Test,
    HasCompactSupport
      (fun x : ℝ =>
        Source.normalizedCC20ConcreteTestAlgebra.legacy.encode g x) →
    (∀ p : Source.CriticalVanishingPoint,
      p ∈ Source.cc20TripleFiniteVanishingSet →
        Source.normalizedCC20ConcreteEvaluationData.mellinAt
          g (Source.criticalVanishingPointValue p) = 0) →
    0 ≤
      (Source.normalizedCC20ConcreteEvaluationData.mellinAt
        (Source.normalizedCC20ConcreteTestAlgebra.convolutionSquare
          (Source.normalizedCC20ConcreteTestAlgebra.convolutionSquare g))
        (Complex.I / 2)).re +
      (Source.normalizedCC20ConcreteEvaluationData.mellinAt
        (Source.normalizedCC20ConcreteTestAlgebra.convolutionSquare
          (Source.normalizedCC20ConcreteTestAlgebra.convolutionSquare g))
        (-Complex.I / 2)).re
  ```

  Static evidence:

  ```text
  ConnesWeilRH/Source/CC20TestSpace.lean:
    CC20FiniteVanishingWeilCriterion quantifies over every `g : C.Test`.

  ConnesWeilRH/Source/CC20ConcreteTestSpace.lean:
    normalizedCC20TestSpace.weilLocalSum g =
      -normalizedCC20ConcreteEvaluationData.polePairing g

  ConnesWeilRH/Source/AnalyticCoreBase.lean:
    SourceEvaluationData.polePairing E g =
      E.poleFunctional (A.convolutionSquare g)

  ConnesWeilRH/Route/Bridge.lean:
    SourceQWNonnegativeToCC20Nonpositive is indexed by a
    `SourceBackedFixedSTest inputs`, a lambda, a concrete `F_g`, and a package.
    It is fixed-tuple route evidence, not a proof for arbitrary concrete CC20
    carrier elements.
  ```

  Do not close this root from the fixed route certificate alone.  That would
  change the quantifier from:

  ```text
  forall concrete CC20 tests g
  ```

  to:

  ```text
  the selected source-backed common test in the existing route certificate
  ```

  and would not prove the CC20 finite-vanishing criterion.


## 1. Result First

Hard completion gate:

```text
Selected-route good:
  The final no-argument Dev outlets no longer obtain SourceRH through
  `cc20_source_rh_of_route_certificate` or the old all-input
  `CC20RHExitObjectPackage.propositionC1SourceCriterion`.

  They are built from:
    Route.normalizedCC20_source_rh_of_finite_vanishing_criterion
    Source.CC20YoshidaInterpolationNode.normalizedCC20YoshidaDetectorExists
    Source.cc20_triple_disjoint_from_standard_source_nontrivial_zeros
    Source.CC20FiniteVanishingWeilCriterion
      Source.normalizedCC20TestSpace Source.cc20TripleFiniteVanishingSet

  The remaining selected criterion root is explicit and audited:
    normalizedSelectedCC20FiniteVanishingToHalfDensityPoleSumFromTheorems

  The wrappers below that root are clean static rewrites:
    normalizedSelectedCC20FiniteVanishingToPolePairingSignFromTheorems
    normalizedSelectedCC20PolePairingNonnegativeOnFiniteVanishingFromTheorems
    normalizedSelectedCC20FiniteVanishingCriterionRowsFromTheorems

  The active Dev/source-object/route path consumes this package.

  The focused audit covers the complete Dev/source-object/route accessor chain,
  not only the local root.  A local root replacement without the chain audit is
  partial.

Full Plan 05 closure:
  Selected-route good plus no `sorryAx` in the concrete finite-vanishing
  pole-pairing sign root above.  The legacy
  `normalizedCoreCC20RHExitObjectPackageFromTheorems` may remain
  compatibility-only only if final no-argument outlets no longer use it as the
  SourceRH producer.

Rejected:
  The root is filled from `SourceFiniteVanishingCriterionPackage.ofCC20RHExitObjectPackage`,
  a stored SourceRH, stored Mathlib RH, `True`, `Set.univ`, a wrapper whose
  only field is `SourceFiniteVanishingCriterionPackage`, or any theorem with
  `sorryAx`.  Also rejected: filling the old all-input package by ignoring its
  C.1 input and returning selected SourceRH as a constant.  Also rejected:
  reusing the fixed route certificate as if it proved the forall-`g`
  `Source.NormalizedCC20FiniteVanishingToPolePairingSign`.
```

Attack tree:

```text
05E selected CC20 exit
|
+-- already clean / wrapper-only
|   |
|   +-- 05A: zeta-half nonvanishing and triple disjointness
|   |
|   +-- 05C: concrete Yoshida detector for normalized CC20 test space
|   |
|   +-- selected route theorem
|       |
|       +-- Route.normalizedCC20_source_rh_of_finite_vanishing_criterion
|
+-- active hard leaf
|   |
|   +-- normalizedSelectedCC20FiniteVanishingToHalfDensityPoleSumFromTheorems
|       |
|       +-- target:
|           forall compact normalized CC20 g,
|             Mellin(g) vanishes on {0,1/2,1}
|             -> 0 <= Re Mellin(convolutionSquare(convolutionSquare g), I/2)
|                     + Re Mellin(convolutionSquare(convolutionSquare g), -I/2)
|
+-- route A: formalize the real forall-g sign proof
|   |
|   +-- A1 identify CC20 finite vanishing with the concrete Mellin rows
|   +-- A2 expose QW(g,g) >= 0 for arbitrary source-backed g
|   +-- A3 prove QW(g,g) = -CC20 local Weil sum for the same convolution square
|   +-- A4 rewrite local Weil sum to the concrete polePairing expression
|
+-- route B: route API narrowing, only if A cannot be completed locally
|   |
|   +-- B1 introduce a selected source-backed common-test owner
|   +-- B2 prove every accepted concrete g enters that owner, or narrow C.Test
|   +-- B3 rerun Proposition C.1 over the narrowed owner
|   +-- B4 reject if any arbitrary concrete g is silently dropped
|
+-- rejected shortcuts
    |
    +-- old all-input CC20RHExitObjectPackage constant SourceRH
    +-- selected global tripleVanishing root
    +-- fixed route certificate as a forall-g proof
    +-- Yoshida detector positivity as the criterion sign proof
    +-- accepted-source field / True / Set.univ / raw SourceRH
```

Forced forall-g attack tree, 2026-07-08:

```text
Goal:
  prove Source.NormalizedCC20FiniteVanishingToHalfDensityPoleSumNonnegative

What it is:
  forall compact g in normalized concrete CC20 carrier,
    Mellin(g, 0) = Mellin(g, 1/2) = Mellin(g, 1) = 0
    ->
    0 <= Re Mellin(4*g, I/2) + Re Mellin(4*g, -I/2)

Why this is the last hard gate:
  Dev selected SourceRH now consumes exactly this root through:

    normalizedSelectedCC20FiniteVanishingToHalfDensityPoleSumFromTheorems
      -> Route.normalizedCC20_source_rh_of_halfDensityPoleSum_nonnegative
      -> normalizedSelectedCC20SourceRHFromTheorems
      -> cc20FiniteVanishingExitFromTheorems

How to attack:

  Root
  |
  +-- Gate 0: counterexample scan
  |   |
  |   +-- Try to build compact g with finite vanishing at {0,1/2,1}
  |   |   and half-density values -1 at I/2 and -I/2.
  |   |
  |   +-- If Lean can construct this g without assuming an off-line zeta zero,
  |       the forall-g statement is false for the current carrier.
  |
  +-- Gate 1: reduce expression
  |   |
  |   +-- use concreteTestAlgebra.convolutionSquare = g + g
  |   +-- use Mellin linearity
  |   +-- reduce target to:
  |         0 <= 4 * (Re Mellin(g, I/2) + Re Mellin(g, -I/2))
  |
  +-- Gate 2: identify missing analytic principle
  |   |
  |   +-- finite vanishing at real points {0,1/2,1}
  |   +-- must imply a sign bound at imaginary points {I/2,-I/2}
  |   +-- no route certificate may replace this implication
  |
  +-- Gate 3A: proof route, if Gate 0 fails
  |   |
  |   +-- find a real positivity theorem for Mellin transforms of compact tests
  |   +-- prove half-density sum nonnegative from finite vanishing
  |   +-- close Dev root
  |
  +-- Gate 3B: contradiction route, if Gate 0 succeeds
      |
      +-- prove theorem showing the current root contradicts a constructed
      |   compact finite-vanishing test
      +-- report that the carrier/API must be narrowed before this root can be
          proved honestly
```

Route-backed/source-backed replacement tree, 2026-07-08:

```text
Problem:
  The forall-g root is false for the current concrete carrier.

  Evidence:
    ConnesWeilRH.Source.CC20YoshidaInterpolationNode
      .not_normalizedCC20FiniteVanishingToHalfDensityPoleSumNonnegative

Replacement root:
  route-backed/source-backed sign family for every Yoshida detector test, not a
  theorem over every SchwartzMap and not one selected fixed test.

Object shape:

  Normalized route-backed Yoshida sign family
  |
  +-- forall rho
      |
      +-- standard source nontrivial zero rho
      +-- rho.re != 1/2
      |
      +-- YoshidaDetector normalizedCC20TestSpace F rho
      |   |
      |   +-- compact support
      |   +-- finite vanishing on F={0,1/2,1}
      |   +-- detects rho
      |   +-- positive local Weil sum if rho is off-line
      |
      +-- route-backed/source-backed sign for that same detector test
          |
          +-- CC20WeilNonpositive normalizedCC20TestSpace detector.test

Lean chain:

  normalizedSelectedRouteBackedYoshidaSignFamilyFromTheorems
    |
    +-- Route.normalizedCC20_source_rh_of_routeBacked_yoshida_sign_family
    |
    +-- normalizedSelectedRouteBackedSourceRHFromTheorems
    |
    +-- cc20FiniteVanishingExitFromTheorems
    |
    +-- rhDefinitionBridgeToMathlibFromTheorems

Hard gate:
  The final no-argument Dev outlet may consume:

    normalizedSelectedRouteBackedYoshidaSignFamilyFromTheorems
    normalizedSelectedRouteBackedSourceRHFromTheorems

  It must not consume:

    normalizedSelectedCC20FiniteVanishingToHalfDensityPoleSumFromTheorems
    Source.NormalizedCC20FiniteVanishingToHalfDensityPoleSumNonnegative
    Source.CC20FiniteVanishingWeilCriterion normalizedCC20TestSpace ...
    normalizedFinalExitPackageFromTheorems.sourceRH as the final SourceRH

Why this is honest:
  The root claims nonpositivity only for detector tests that carry
  route-backed/source-backed sign evidence.  It is strong enough for the
  Yoshida contradiction because it is a family over every off-line rho, but it
  does not quantify over arbitrary compact Schwartz tests, so it avoids the
  05C Mellin-surjectivity counterexample.

Rejected:
  Reintroducing the old all-input CC20 package as a fake selected proof;
  casting route-backed sign into forall-g concrete CC20 positivity;
  using one selected fixed-test RouteCertificate as if it handled every
  off-line rho; using the false half-density forall-g root after the
  counterexample theorem.
```

Route-backed sign theorem hard tree, 2026-07-08:

```text
Goal:
  remove the last 05E selected SourceRH root without returning to the false
  forall-g criterion.

Current Lean owner:
  Route.NormalizedRouteBackedYoshidaSignFamily

Required object shape:

  forall rho off the critical line
  |
  +-- Yoshida detector for rho
  |   |
  |   +-- detector.test is the concrete CC20 test
  |   +-- detector gives positive CC20 local Weil sum if rho is off-line
  |
  +-- route-backed/source-backed realization of the same test
  |   |
  |   +-- inputs : RouteInputs
  |   +-- sourceBackedTest : SourceBackedFixedSTest inputs
  |   +-- detectorMatchesRouteTest:
  |   |     normalizedCC20TestSpace.toRouteTest detector.test
  |   |       = sourceBackedTest.weilTest
  |   |
  |   +-- bridge : RouteBridgeCertificate inputs sourceBackedTest ledgers
  |   +-- routeBackedFinalSign :
  |       SourceQWNonnegativeToCC20Nonpositive inputs ... sourceBackedTest ...
  |
  +-- real final sign theorem
      |
      +-- input:
      |     routeBackedFinalSign for that same sourceBackedTest
      |
      +-- local read-off:
      |     normalizedCC20TestSpace.weilLocalSum
      |       (normalizedCC20TestSpace.starConvolution detector.test)
      |       =
      |     -inputs.cc20.archimedeanSymbols.positiveTrace
      |       bridge.sourceTraceReadOff.archimedeanTest
      |
      +-- output:
            CC20WeilNonpositive normalizedCC20TestSpace detector.test

Accepted closure:
  `NormalizedRouteBackedYoshidaSignWitness` may carry the same-test read-off

    NormalizedRouteBackedYoshidaLocalSumReadOff data

  because Lean proves:

    NormalizedRouteBackedYoshidaLocalSumReadOff data
      -> NormalizedRouteBackedYoshidaSignTheorem data

  by rewriting the CC20 local sum to `-positiveTrace` and using
  `routeBackedFinalSign.positiveTraceNonnegative`.

Next proof leaf:

  Dev.normalizedSelectedRouteBackedYoshidaDetectorSignRealizerFromTheorems

  whose target is:

    Route.NormalizedRouteBackedYoshidaDetectorSignRealizer

  i.e. for every concrete Yoshida detector test, construct a route-backed
  source-backed same-test witness carrying:

    detectorMatchesRouteTest
    Route.NormalizedRouteBackedYoshidaLocalSumReadOff data

This must be proved from:
  detectorMatchesRouteTest
  normalizedCC20TestSpace.toRouteTest_eq
  SourceQWEqualsNegCC20WeilSum / SourceQWNonnegativeToCC20Nonpositive
  the concrete CC20 local Weil sum definition

Rejected:
  using `detectorNonpositive` as a field;
  using arbitrary `routeBackedSignTheorem` as a field;
  using the selected route certificate for all rho;
  proving the family directly by `sorry` instead of composing 05C detector
  existence with the detector realizer;
  erasing the `detectorMatchesRouteTest` equality;
  filling the theorem from raw SourceRH, Mathlib RH, `True`, `Set.univ`,
  accepted-source text, or the old finite-vanishing forall-g root.
```

Static execution note, 2026-07-08, archimedean trace lowering:

```text
Result:
  Static-only lowering.  Not accepted proof progress because no build or
  focused axiom audit was run.

Route API added:
  Route.NormalizedRouteBackedYoshidaDetectorArchimedeanTraceRealization
  Route.NormalizedRouteBackedYoshidaDetectorArchimedeanTraceRealizer
  Route.normalizedRouteBackedYoshidaDetectorRouteTraceData_of_archimedean
  Route.normalizedRouteBackedYoshidaDetectorTraceRealization_of_archimedean
  Route.normalizedRouteBackedYoshidaDetectorTraceRealizer_of_archimedean_trace_realizer

Dev root moved:
  old broad root:
    normalizedSelectedRouteBackedYoshidaDetectorTraceRealizerFromTheorems

  new active root:
    normalizedSelectedRouteBackedYoshidaDetectorArchimedeanTraceRealizerFromTheorems

  wrapper:
    normalizedSelectedRouteBackedYoshidaDetectorTraceRealizerFromTheorems
      :=
    Route.normalizedRouteBackedYoshidaDetectorTraceRealizer_of_archimedean_trace_realizer
      normalizedSelectedRouteBackedYoshidaDetectorArchimedeanTraceRealizerFromTheorems

New hard bottom:
  For every concrete Yoshida detector, produce the same-test archimedean
  realization:

    inputs
    baseSourceBackedTest
    finitePrimeSourceDataOwner
    archimedeanTest
    hilbertSchmidtGate
    lambda / oneLtLambda
    ConcreteCCM25ArithmeticPackage for
      normalizedCC20TestSpace.toRouteTest detector.test
    exact local-sum/positiveTrace read-off

What is no longer the active blocker:
  testAndQuotientCompatibility
  fixedSSupportSquareTransport
  positiveTraceNonnegative
  detector route realization
  route realizer
  sign realizer

Reason:
  Those are reconstructed by the route wrapper from the archimedean realization
  using the existing package/source-backed APIs.  The remaining non-mechanical
  obligation is the same-test archimedean test and read-off.
```


## 2. File Ownership

Allowed files:

```text
ConnesWeilRH/Dev/UnconditionalSkeleton.lean
ConnesWeilRH/Route/CC20RouteRealization.lean
ConnesWeilRH/Source/CC20ConcreteTestSpace.lean
```

Read-only dependencies:

```text
ConnesWeilRH/Source/CC20RHExit.lean
ConnesWeilRH/Source/ZetaHalfNonvanishing.lean
ConnesWeilRH/Source/CC20PropositionC1.lean
ConnesWeilRH/Route/RouteTheorem.lean
```

Do not edit unrelated source theorem files in this shard.  If 05A or 05C is
missing, stop and report the missing theorem.  The current shard may edit
`CC20ConcreteTestSpace.lean` only to expose the concrete pole-pairing sign
target and clean wrappers.


## 3. Old Weak Path

Current hard root:

```lean
noncomputable def normalizedCoreCC20RHExitObjectPackageFromTheorems :
    Source.CC20RHExitObjectPackage
      normalizedCoreRHDefinitionBridgeFromTheorems := by
  sorry
```

Adapter loop to watch:

```text
SourceFiniteVanishingCriterionPackage.ofCC20RHExitObjectPackage
  normalizedSourceObjectCoreTheoremBaseDataFromTheorems.base.cc20RHExitObjectPackage
```

That adapter may remain only as downstream compatibility after the core package
is constructed from lower source facts.


## 4. Implementation Route

Add the selected source package in Dev:

```lean
def normalizedSelectedCC20FiniteVanishingCriterionRowsFromTheorems :
    Source.CC20FiniteVanishingWeilCriterion
      Source.normalizedCC20TestSpace Source.cc20TripleFiniteVanishingSet

def normalizedSelectedCC20SourceRHFromTheorems :
    Source.RHDefinitionBridge.standard.SourceRH :=
  Route.normalizedCC20_source_rh_of_finite_vanishing_criterion
    Source.CC20YoshidaInterpolationNode.normalizedCC20YoshidaDetectorExists
    Source.cc20_triple_disjoint_from_standard_source_nontrivial_zeros
    normalizedSelectedCC20FiniteVanishingCriterionRowsFromTheorems
```

Current lowering:

```lean
noncomputable def normalizedSelectedCC20FiniteVanishingToHalfDensityPoleSumFromTheorems :
    Source.NormalizedCC20FiniteVanishingToHalfDensityPoleSumNonnegative := by
  sorry

noncomputable def normalizedSelectedCC20FiniteVanishingToPolePairingSignFromTheorems :
    Source.NormalizedCC20FiniteVanishingToPolePairingSign :=
  Source.normalizedCC20_finiteVanishingToPolePairingSign_of_halfDensityPoleSum
    normalizedSelectedCC20FiniteVanishingToHalfDensityPoleSumFromTheorems

noncomputable def normalizedSelectedCC20PolePairingNonnegativeOnFiniteVanishingFromTheorems :
    Source.NormalizedCC20PolePairingNonnegativeOnFiniteVanishing :=
  Source.normalizedCC20_polePairing_nonnegative_of_finiteVanishingToPolePairingSign
    normalizedSelectedCC20FiniteVanishingToPolePairingSignFromTheorems

def normalizedSelectedCC20FiniteVanishingCriterionRowsFromTheorems :
    Source.CC20FiniteVanishingWeilCriterion
      Source.normalizedCC20TestSpace Source.cc20TripleFiniteVanishingSet :=
  Source.normalizedCC20_finite_vanishing_weil_criterion_of_polePairing_nonnegative
    normalizedSelectedCC20PolePairingNonnegativeOnFiniteVanishingFromTheorems
```


## 5. Rejection Scans

```text
rg -n "normalizedCoreCC20RHExitObjectPackageFromTheorems|normalizedCoreSourceFiniteVanishingCriterionPackageFromTheorems|SourceFiniteVanishingCriterionPackage\.ofCC20RHExitObjectPackage|SourceFiniteVanishingCriterionPackage\.toCC20RHExitObjectPackage|SourceRH\s*:=|mathlibRH\s*:|RiemannHypothesis\s*:=|Set\.univ|\bTrue\b|\bsorry\b|\badmit\b|^\s*(axiom|constant|opaque|unsafe)\b" ConnesWeilRH/Dev/UnconditionalSkeleton.lean
```

The scan must show `toCC20RHExitObjectPackage` consumes the new lower source
package, not a package recovered from the same CC20 exit object.

Additional sign-root rejection scan:

```text
rg -n "normalizedSelectedCC20FiniteVanishingToHalfDensityPoleSumFromTheorems|normalizedSelectedCC20FiniteVanishingToPolePairingSignFromTheorems|normalizedSelectedCC20PolePairingNonnegativeOnFiniteVanishingFromTheorems|SourceQWNonnegativeToCC20Nonpositive|final_sign_nonpositive_of_route_bridge_certificate|normalizedCC20FiniteVanishingWeilCriterionInput\.tripleVanishing|CC20RHExitObjectPackage|SourceRH\s*:=|Set\.univ|\bTrue\b|\bsorry\b|\badmit\b" ConnesWeilRH/Dev/UnconditionalSkeleton.lean ConnesWeilRH/Route ConnesWeilRH/Source/CC20ConcreteTestSpace.lean
```


## 6. WSL Build Gate

Do not run this gate from `/mnt/c`.  When Peter authorizes verification, use a
WSL ext4 mirror or fresh ext4 verification copy, and serialize the command with
`/tmp/connes-weil-rh-lake.lock`.

```text
wsl -d Ubuntu-24.04 -- bash -lc 'flock /tmp/connes-weil-rh-lake.lock -c "cd <ext4-connes-weil-rh-copy> && lake build ConnesWeilRH.Dev.UnconditionalSkeleton ConnesWeilRH.Route.CC20RouteRealization"'
```

Current user instruction, 2026-07-08: do not build.


## 7. Focused Axiom Audit

```lean
import ConnesWeilRH.Dev.UnconditionalSkeleton

#check ConnesWeilRH.Source.normalizedCC20_polePairing_nonnegative_of_finiteVanishingToPolePairingSign
#print axioms ConnesWeilRH.Source.normalizedCC20_polePairing_nonnegative_of_finiteVanishingToPolePairingSign

#check ConnesWeilRH.Source.normalizedCC20_finite_vanishing_weil_criterion_of_polePairing_nonnegative
#print axioms ConnesWeilRH.Source.normalizedCC20_finite_vanishing_weil_criterion_of_polePairing_nonnegative

#check ConnesWeilRH.Source.normalizedCC20_finiteVanishingToPolePairingSign_of_halfDensityPoleSum
#print axioms ConnesWeilRH.Source.normalizedCC20_finiteVanishingToPolePairingSign_of_halfDensityPoleSum

#check ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedCoreCC20RHExitObjectPackageFromTheorems
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedCoreCC20RHExitObjectPackageFromTheorems

#check ConnesWeilRH.Route.normalizedCC20_source_rh_of_finite_vanishing_criterion
#print axioms ConnesWeilRH.Route.normalizedCC20_source_rh_of_finite_vanishing_criterion

#check ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedSelectedCC20FiniteVanishingToHalfDensityPoleSumFromTheorems
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedSelectedCC20FiniteVanishingToHalfDensityPoleSumFromTheorems

#check ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedSelectedCC20FiniteVanishingToPolePairingSignFromTheorems
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedSelectedCC20FiniteVanishingToPolePairingSignFromTheorems

#check ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedSelectedCC20PolePairingNonnegativeOnFiniteVanishingFromTheorems
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedSelectedCC20PolePairingNonnegativeOnFiniteVanishingFromTheorems

#check ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedSelectedCC20FiniteVanishingCriterionRowsFromTheorems
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedSelectedCC20FiniteVanishingCriterionRowsFromTheorems

#check ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedSelectedCC20SourceRHFromTheorems
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedSelectedCC20SourceRHFromTheorems

#check ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedSourceObjectCoreBasePackageConstructorInputFromTheorems
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedSourceObjectCoreBasePackageConstructorInputFromTheorems

#check ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedSourceObjectCoreTheoremBaseDataFromTheorems
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedSourceObjectCoreTheoremBaseDataFromTheorems

#check ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedSourceObjectRHExitObjectFromTheorems
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedSourceObjectRHExitObjectFromTheorems

#check ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedRhExitFromTheorems
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedRhExitFromTheorems

#check ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedSourceObjectPackageFromTheorems
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedSourceObjectPackageFromTheorems

#check ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedRouteCertificateFromTheorems
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedRouteCertificateFromTheorems

#check ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedNoArgumentRouteCertificatePackageFromTheorems
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.normalizedNoArgumentRouteCertificatePackageFromTheorems

#check ConnesWeilRH.Dev.UnconditionalSkeleton.mathlib_rh_of_normalized_no_argument_route_certificate_package
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.mathlib_rh_of_normalized_no_argument_route_certificate_package

#check ConnesWeilRH.Dev.UnconditionalSkeleton.cc20FiniteVanishingExitFromTheorems
#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.cc20FiniteVanishingExitFromTheorems
```

The final route certificate may still show `sorryAx` from other D1 roots, but
the selected finite-vanishing producer audit must show exactly whether 05 still
contributes `sorryAx`.  If the accessor chain still reaches
`SourceFiniteVanishingCriterionPackage.ofCC20RHExitObjectPackage` as the source
of the 05 evidence, or if it recreates a selected global `tripleVanishing` row,
the result is partial or rejected.


## 8. Acceptance Text

```text
Result:
  Good / partial / rejected.

Old weak path removed:
  normalizedCoreCC20RHExitObjectPackageFromTheorems no longer uses `sorry`.

New semantic owner:
  normalizedSelectedCC20FiniteVanishingToHalfDensityPoleSumFromTheorems

Lower source theorems:
  Source.CC20YoshidaInterpolationNode.normalizedCC20YoshidaDetectorExists
  Source.cc20_triple_disjoint_from_standard_source_nontrivial_zeros
  Route.normalizedCC20_source_rh_of_finite_vanishing_criterion
  Source.normalizedCC20_finiteVanishingToPolePairingSign_of_halfDensityPoleSum
  Source.normalizedCC20_polePairing_nonnegative_of_finiteVanishingToPolePairingSign
  Source.normalizedCC20_finite_vanishing_weil_criterion_of_polePairing_nonnegative

Consumer rewires:
  normalizedSourceObjectCoreBasePackageConstructorInputFromTheorems
  normalizedSourceObjectCoreTheoremBaseDataFromTheorems
  normalizedSourceObjectRHExitObjectFromTheorems
  normalizedRhExitFromTheorems
  normalizedSourceObjectPackageFromTheorems
  normalizedRouteCertificateFromTheorems
  normalizedSelectedCC20ExitPackageFromTheorems
  normalizedNoArgumentRouteCertificatePackageFromTheorems
  mathlib_rh_of_normalized_no_argument_route_certificate_package

Build:
  <command and result>

Focused axiom audit:
  <output>

Remaining black box:
  <exact declaration/type, if any>
```
