/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Route.Exhaustion
import ConnesWeilRH.Route.Bridge
import ConnesWeilRH.Route.TraceFrontEnd

/-!
# Route theorem skeleton

The final theorem targets Mathlib's canonical `RiemannHypothesis`. Phase 1 uses
the CC20 exit as an explicit hypothesis, so this module has no hidden project
axioms.
-/

namespace ConnesWeilRH
namespace Route

open Source.SourceObjectPackageOfData

structure RouteCertificate (inputs : RouteInputs) where
  sourceBackedTest : SourceBackedFixedSTest inputs
  ledgers : RouteLedgers
  bridge : RouteBridgeCertificate inputs sourceBackedTest ledgers

structure RouteBackedCC20NonpositivityInputData
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (L : RouteLedgers) (bridge : RouteBridgeCertificate inputs g L)
    (input : WeilPositivityInput) where
  inputIsRouteInput : input = toWeilPositivityInput inputs g L
  sourceBackedFullPositivity : SourceBackedFullPositivity inputs g L
  finalSignBridge :
    FinalSignBridgeContract inputs bridge.sourceTraceReadOff.archimedeanTest g
      bridge.sourceTraceReadOff.lambda
      (inputs.ccm25.weilSymbols.convolutionStar g.weilTest g.weilTest)
      bridge.sourceTraceReadOff.ccm25ArithmeticPackage
  finalSignNonpositive :
    SourceQWNonnegativeToCC20Nonpositive inputs
      bridge.sourceTraceReadOff.archimedeanTest g
      bridge.sourceTraceReadOff.lambda
      (inputs.ccm25.weilSymbols.convolutionStar g.weilTest g.weilTest)
      bridge.sourceTraceReadOff.ccm25ArithmeticPackage
  fullWeilPositivity : input.fullWeilPositivity

structure RouteBackedCC20TripleVanishingInputData
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (L : RouteLedgers) (input : WeilPositivityInput) where
  inputIsRouteInput : input = toWeilPositivityInput inputs g L
  tripleVanishingSymbols : TripleVanishingSymbols
  symbolsAreSourceBacked : tripleVanishingSymbols = g.tripleVanishingSymbols
  sourceTripleVanishing :
    TripleVanishingSymbols.TripleVanishingStatement tripleVanishingSymbols
  routeTripleVanishing : g.test.tripleVanishing
  tripleVanishingMatchesMellin : input.tripleVanishing

structure RouteBackedCC20ExitInputData
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (L : RouteLedgers) (bridge : RouteBridgeCertificate inputs g L) where
  input : WeilPositivityInput
  inputIsRouteInput : input = toWeilPositivityInput inputs g L
  sourceBackedFullPositivity : SourceBackedFullPositivity inputs g L
  nonpositivityInput :
    RouteBackedCC20NonpositivityInputData inputs g L bridge input
  tripleVanishingInput :
    RouteBackedCC20TripleVanishingInputData inputs g L input
  finalSignBridge :
    FinalSignBridgeContract inputs bridge.sourceTraceReadOff.archimedeanTest g
      bridge.sourceTraceReadOff.lambda
      (inputs.ccm25.weilSymbols.convolutionStar g.weilTest g.weilTest)
      bridge.sourceTraceReadOff.ccm25ArithmeticPackage
  finalSignNonpositive :
    SourceQWNonnegativeToCC20Nonpositive inputs
      bridge.sourceTraceReadOff.archimedeanTest g
      bridge.sourceTraceReadOff.lambda
      (inputs.ccm25.weilSymbols.convolutionStar g.weilTest g.weilTest)
      bridge.sourceTraceReadOff.ccm25ArithmeticPackage
  tripleVanishing : input.tripleVanishing
  fullWeilPositivity : input.fullWeilPositivity
  propositionC1InputData :
    Source.CC20PropositionC1InputData
      inputs.cc20.rhDefinitionBridge
      inputs.cc20.cc20RHExitObjectPackage.finiteVanishingSet input

structure ExpandedSourceRouteCertificateFrontEnd
    (pkg : Source.SourceObject.SourceObjectPackage)
    (fixedFront : ExpandedSourceFixedSTestFrontEnd pkg)
    (traceFront : ExpandedSourceTraceReadOffFrontEnd pkg fixedFront) where
  ledgers : RouteLedgers
  commonTuple :
    SourceCommonTestTupleContract
      (RouteInputs.ofExpandedSourcePackage pkg)
      (SourceBackedFixedSTest.ofExpandedSourcePackage pkg fixedFront)
      traceFront.lambda
      pkg.commonTest.sourceConvolutionSquare
      traceFront.ccm25ArithmeticPackage
  signDefectClassification :
    SourceSignDefectClassification
      (RouteInputs.ofExpandedSourcePackage pkg)
      (SourceBackedFixedSTest.ofExpandedSourcePackage pkg fixedFront)
      traceFront.lambda ledgers
  restrictedToFullQWBridge :
    RestrictedToFullQWBridgeContract
      (RouteInputs.ofExpandedSourcePackage pkg)
      (SourceBackedFixedSTest.ofExpandedSourcePackage pkg fixedFront)
      traceFront.lambda
      pkg.commonTest.sourceConvolutionSquare
      ledgers traceFront.ccm25ArithmeticPackage
  sourceArchimedeanSignBridge :
    SourceArchimedeanSignBridge
      (RouteInputs.ofExpandedSourcePackage pkg)
      pkg.cc20Trace.sourceTraceTest
      (SourceBackedFixedSTest.ofExpandedSourcePackage pkg fixedFront)

theorem normalizedScalarFullTraceArchimedeanBalanceOfQWLambdaRestriction
    (base : Source.SourceObjectTheoremBasePackage)
    (common : Source.SourceObjectCommonData base)
    (ccm24 : Source.SourceObject.CCM24SemilocalObjectPackage)
    (normalizedSeed :
      Source.CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (remainders :
      Source.CC20Concrete.TraceScale.CC20TracePackageRemainderData
        normalizedSeed)
    (rhExit : Source.SourceObject.CC20RHExitObjectPackage)
    (bridges :
      Source.SourceObjectCrossObjectBridges base common
        (Source.SourceObjectExpandedRows.ofNormalizedCC20Trace
          ccm24 normalizedSeed remainders)
        rhExit)
    (fixedData :
      FixedSTestObligationData
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges))
    (traceData :
      TraceFrontEndData
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges)
        (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData))
    (hrestriction :
      let originalSourceTrace :=
        TraceFrontEndData.toSourceTraceReadOffDataOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges fixedData
          traceData
      let originalInputs :=
        RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges)
      let originalG :=
        FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges fixedData
      SourceQWLambdaIsRestrictionOfQW originalInputs originalG
        originalSourceTrace.lambda originalSourceTrace.ccm25ArithmeticPackage) :
    TraceFrontEndData.NormalizedScalarFullTraceArchimedeanBalance
      base common ccm24 normalizedSeed remainders rhExit bridges fixedData
      traceData := by
  dsimp [TraceFrontEndData.NormalizedScalarFullTraceArchimedeanBalance] at *
  exact archimedean_contribution_equality_of_qw_lambda_restriction
    hrestriction

theorem normalizedScalarFullTraceArchimedeanPoleBalanceOfQWLambdaRestriction
    (base : Source.SourceObjectTheoremBasePackage)
    (common : Source.SourceObjectCommonData base)
    (ccm24 : Source.SourceObject.CCM24SemilocalObjectPackage)
    (normalizedSeed :
      Source.CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (remainders :
      Source.CC20Concrete.TraceScale.CC20TracePackageRemainderData
        normalizedSeed)
    (rhExit : Source.SourceObject.CC20RHExitObjectPackage)
    (bridges :
      Source.SourceObjectCrossObjectBridges base common
        (Source.SourceObjectExpandedRows.ofNormalizedCC20Trace
          ccm24 normalizedSeed remainders)
        rhExit)
    (fixedData :
      FixedSTestObligationData
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges))
    (traceData :
      TraceFrontEndData
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges)
        (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData))
    (hrestriction :
      let originalSourceTrace :=
        TraceFrontEndData.toSourceTraceReadOffDataOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges fixedData
          traceData
      let originalInputs :=
        RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges)
      let originalG :=
        FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges fixedData
      SourceQWLambdaIsRestrictionOfQW originalInputs originalG
        originalSourceTrace.lambda originalSourceTrace.ccm25ArithmeticPackage) :
    TraceFrontEndData.NormalizedScalarFullTraceArchimedeanPoleBalance
      base common ccm24 normalizedSeed remainders rhExit bridges fixedData
      traceData := by
  dsimp [TraceFrontEndData.NormalizedScalarFullTraceArchimedeanPoleBalance] at *
  have hfull :=
    archimedean_contribution_equality_of_qw_lambda_restriction hrestriction
  dsimp at hfull
  rw [Source.CCM25Concrete.Package.source_restricted_finite_prime_evaluator_sum_eq_global] at hfull
  rwa [sub_left_inj] at hfull

theorem normalizedScalarFullTraceArchimedeanPoleBalanceOfRestrictedToFullContract
    (base : Source.SourceObjectTheoremBasePackage)
    (common : Source.SourceObjectCommonData base)
    (ccm24 : Source.SourceObject.CCM24SemilocalObjectPackage)
    (normalizedSeed :
      Source.CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (remainders :
      Source.CC20Concrete.TraceScale.CC20TracePackageRemainderData
        normalizedSeed)
    (rhExit : Source.SourceObject.CC20RHExitObjectPackage)
    (bridges :
      Source.SourceObjectCrossObjectBridges base common
        (Source.SourceObjectExpandedRows.ofNormalizedCC20Trace
          ccm24 normalizedSeed remainders)
        rhExit)
    (fixedData :
      FixedSTestObligationData
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges))
    (traceData :
      TraceFrontEndData
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges)
        (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData))
    (L : RouteLedgers)
    (hbridge :
      let originalSourceTrace :=
        TraceFrontEndData.toSourceTraceReadOffDataOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges fixedData
          traceData
      let originalInputs :=
        RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges)
      let originalG :=
        FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges fixedData
      RestrictedToFullQWBridgeContract originalInputs originalG
        originalSourceTrace.lambda
        (originalInputs.ccm25.weilSymbols.convolutionStar
          originalG.weilTest originalG.weilTest)
        L originalSourceTrace.ccm25ArithmeticPackage) :
    TraceFrontEndData.NormalizedScalarFullTraceArchimedeanPoleBalance
      base common ccm24 normalizedSeed remainders rhExit bridges fixedData
      traceData := by
  apply
    normalizedScalarFullTraceArchimedeanPoleBalanceOfQWLambdaRestriction
      base common ccm24 normalizedSeed remainders rhExit bridges fixedData
      traceData
  dsimp at hbridge ⊢
  exact source_qw_lambda_restriction_of_restricted_to_full_contract hbridge

theorem normalizedScalarFullTraceArchimedeanBalanceOfRestrictedToFullContract
    (base : Source.SourceObjectTheoremBasePackage)
    (common : Source.SourceObjectCommonData base)
    (ccm24 : Source.SourceObject.CCM24SemilocalObjectPackage)
    (normalizedSeed :
      Source.CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (remainders :
      Source.CC20Concrete.TraceScale.CC20TracePackageRemainderData
        normalizedSeed)
    (rhExit : Source.SourceObject.CC20RHExitObjectPackage)
    (bridges :
      Source.SourceObjectCrossObjectBridges base common
        (Source.SourceObjectExpandedRows.ofNormalizedCC20Trace
          ccm24 normalizedSeed remainders)
        rhExit)
    (fixedData :
      FixedSTestObligationData
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges))
    (traceData :
      TraceFrontEndData
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges)
        (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData))
    (L : RouteLedgers)
    (hbridge :
      let originalSourceTrace :=
        TraceFrontEndData.toSourceTraceReadOffDataOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges fixedData
          traceData
      let originalInputs :=
        RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges)
      let originalG :=
        FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges fixedData
      RestrictedToFullQWBridgeContract originalInputs originalG
        originalSourceTrace.lambda
        (originalInputs.ccm25.weilSymbols.convolutionStar
          originalG.weilTest originalG.weilTest)
        L originalSourceTrace.ccm25ArithmeticPackage) :
    TraceFrontEndData.NormalizedScalarFullTraceArchimedeanBalance
      base common ccm24 normalizedSeed remainders rhExit bridges fixedData
      traceData := by
  exact
    TraceFrontEndData.normalizedScalarFullTraceArchimedeanBalanceOfPoleBalance
      base common ccm24 normalizedSeed remainders rhExit bridges fixedData
      traceData
      (normalizedScalarFullTraceArchimedeanPoleBalanceOfRestrictedToFullContract
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData L hbridge)

def normalizedScalarTraceFrontFullTraceReadOffBridgeFromRestrictedToFullContract
    (base : Source.SourceObjectTheoremBasePackage)
    (common : Source.SourceObjectCommonData base)
    (ccm24 : Source.SourceObject.CCM24SemilocalObjectPackage)
    (normalizedSeed :
      Source.CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (remainders :
      Source.CC20Concrete.TraceScale.CC20TracePackageRemainderData
        normalizedSeed)
    (rhExit : Source.SourceObject.CC20RHExitObjectPackage)
    (bridges :
      Source.SourceObjectCrossObjectBridges base common
        (Source.SourceObjectExpandedRows.ofNormalizedCC20Trace
          ccm24 normalizedSeed remainders)
        rhExit)
    (fixedData :
      FixedSTestObligationData
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges))
    (traceData :
      TraceFrontEndData
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges)
        (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData))
    (scalarRemainders :
      Source.CC20Concrete.TraceScale.CC20TracePackageRemainderData
        (Source.CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
          (TraceFrontEndData.normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)))
    (scalarRhExit : Source.SourceObject.CC20RHExitObjectPackage)
    (scalarBridges :
      Source.SourceObjectCrossObjectBridges base common
        (Source.SourceObjectExpandedRows.ofNormalizedScalarCC20Trace
          ccm24
          (TraceFrontEndData.normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)
          scalarRemainders)
        scalarRhExit)
    (scalarFixedData :
      FixedSTestObligationData
        (Source.sourceObjectPackageOfNormalizedScalarCC20Trace
          base common ccm24
          (TraceFrontEndData.normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)
          scalarRemainders scalarRhExit scalarBridges))
    (L : RouteLedgers)
    (hbridge :
      let originalSourceTrace :=
        TraceFrontEndData.toSourceTraceReadOffDataOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges fixedData
          traceData
      let originalInputs :=
        RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges)
      let originalG :=
        FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges fixedData
      RestrictedToFullQWBridgeContract originalInputs originalG
        originalSourceTrace.lambda
        (originalInputs.ccm25.weilSymbols.convolutionStar
          originalG.weilTest originalG.weilTest)
        L originalSourceTrace.ccm25ArithmeticPackage) :
    let scalarInputs :=
      RouteInputs.ofExpandedSourcePackage
        (Source.sourceObjectPackageOfNormalizedScalarCC20Trace
          base common ccm24
          (TraceFrontEndData.normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)
          scalarRemainders scalarRhExit scalarBridges)
    let scalarG :=
      FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedScalarPackage
        base common ccm24
        (TraceFrontEndData.normalizedRestrictedScalarTraceSeedOfTraceData
          base common ccm24 normalizedSeed remainders rhExit bridges fixedData
          traceData)
        scalarRemainders scalarRhExit scalarBridges scalarFixedData
    FullTraceReadOffBridgeContract scalarInputs
      (Source.sourceObjectPackageOfNormalizedScalarCC20Trace
        base common ccm24
        (TraceFrontEndData.normalizedRestrictedScalarTraceSeedOfTraceData
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData traceData)
        scalarRemainders scalarRhExit scalarBridges).cc20Trace.sourceTraceTest
      scalarG := by
  intro scalarInputs scalarG
  let originalSourceTrace :=
    TraceFrontEndData.toSourceTraceReadOffDataOfNormalizedPackage
      base common ccm24 normalizedSeed remainders rhExit bridges fixedData
      traceData
  let originalInputs :=
    RouteInputs.ofExpandedSourcePackage
      (Source.sourceObjectPackageOfNormalizedCC20Trace
        base common ccm24 normalizedSeed remainders rhExit bridges)
  let originalG :=
    FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
      base common ccm24 normalizedSeed remainders rhExit bridges fixedData
  let hrestrictedToFull :
      originalInputs.ccm25.weilSymbols.qwLambda originalSourceTrace.lambda
          originalG.weilTest originalG.weilTest =
        originalInputs.ccm25.weilSymbols.qw originalG.weilTest
          originalG.weilTest :=
    Source.CCM25Concrete.Package.qw_lambda_eq_qw_of_archimedean_contribution
      originalSourceTrace.ccm25ArithmeticPackage
      (normalizedScalarFullTraceArchimedeanBalanceOfRestrictedToFullContract
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData L hbridge)
  let heq :
      FullTraceReadOffEquality scalarInputs
        (Source.sourceObjectPackageOfNormalizedScalarCC20Trace
          base common ccm24
          (TraceFrontEndData.normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)
          scalarRemainders scalarRhExit scalarBridges).cc20Trace.sourceTraceTest
        scalarG := by
    dsimp [FullTraceReadOffEquality]
    let hsource :
        scalarInputs.cc20.archimedeanSymbols.sourceNoDefectTrace
            (Source.sourceObjectPackageOfNormalizedScalarCC20Trace
              base common ccm24
              (TraceFrontEndData.normalizedRestrictedScalarTraceSeedOfTraceData
                base common ccm24 normalizedSeed remainders rhExit bridges
                fixedData traceData)
              scalarRemainders scalarRhExit
              scalarBridges).cc20Trace.sourceTraceTest =
          TraceFrontEndData.NormalizedRestrictedScalarNormalForm
            base common ccm24 normalizedSeed remainders rhExit bridges fixedData
            traceData :=
      normalized_scalar_cc20_trace_package_source_no_defect_eq_scalar
        base common ccm24
        (TraceFrontEndData.normalizedRestrictedScalarTraceSeedOfTraceData
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData traceData)
        scalarRemainders scalarRhExit scalarBridges
        (Source.sourceObjectPackageOfNormalizedScalarCC20Trace
          base common ccm24
          (TraceFrontEndData.normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)
          scalarRemainders scalarRhExit scalarBridges).cc20Trace.sourceTraceTest
    calc
      scalarInputs.cc20.archimedeanSymbols.sourceNoDefectTrace
          (Source.sourceObjectPackageOfNormalizedScalarCC20Trace
            base common ccm24
            (TraceFrontEndData.normalizedRestrictedScalarTraceSeedOfTraceData
              base common ccm24 normalizedSeed remainders rhExit bridges
              fixedData traceData)
            scalarRemainders scalarRhExit scalarBridges).cc20Trace.sourceTraceTest =
        TraceFrontEndData.NormalizedRestrictedScalarNormalForm
          base common ccm24 normalizedSeed remainders rhExit bridges fixedData
          traceData := hsource
      _ =
        originalInputs.ccm25.weilSymbols.qwLambda originalSourceTrace.lambda
          originalG.weilTest originalG.weilTest :=
          (TraceFrontEndData.normalized_qw_lambda_reduces_to_normal_form
            base common ccm24 normalizedSeed remainders rhExit bridges fixedData
            traceData).symm
      _ =
        originalInputs.ccm25.weilSymbols.qw originalG.weilTest
          originalG.weilTest := hrestrictedToFull
      _ =
        scalarInputs.ccm25.weilSymbols.qw scalarG.weilTest scalarG.weilTest :=
          rfl
  exact
    { build := fun hnoDefect hfull =>
        full_trace_read_off_source_of_parts hnoDefect hfull heq
      preservesNoDefect := by
        intro hnoDefect hfull
        rfl
      preservesFullQW := by
        intro hnoDefect hfull
        rfl }

/--
Goal 4D staging data for a route front end whose sign/defect evidence is tied
to the Goal 4C trace-scale no-missing-bulk ledger.
-/
structure TraceScaleRouteFrontEndData
    (pkg : Source.SourceObject.SourceObjectPackage)
    (fixedFront : ExpandedSourceFixedSTestFrontEnd pkg)
    (traceData : TraceFrontEndData pkg fixedFront) where
  ledgers : RouteLedgers
  traceScaleNoMissingBulk :
    TraceScaleNoMissingBulkData pkg fixedFront traceData.lambda
      traceData.ccm25ArithmeticPackage
  traceScaleMatchesTraceData :
    traceScaleNoMissingBulk = traceData.traceScaleNoMissingBulk
  commonTuple :
    SourceCommonTestTupleContract
      (RouteInputs.ofExpandedSourcePackage pkg)
      (SourceBackedFixedSTest.ofExpandedSourcePackage pkg fixedFront)
      traceData.lambda
      pkg.commonTest.sourceConvolutionSquare
      traceData.ccm25ArithmeticPackage
  signDefectClassification :
    SourceSignDefectClassification
      (RouteInputs.ofExpandedSourcePackage pkg)
      (SourceBackedFixedSTest.ofExpandedSourcePackage pkg fixedFront)
      traceData.lambda ledgers
  traceScaleOwnsSignDefectRemainder :
    traceScaleNoMissingBulk.rankPoleCdefOwnEveryRemainder
      ledgers signDefectClassification
  restrictedToFullQWBridge :
    RestrictedToFullQWBridgeContract
      (RouteInputs.ofExpandedSourcePackage pkg)
      (SourceBackedFixedSTest.ofExpandedSourcePackage pkg fixedFront)
      traceData.lambda
      pkg.commonTest.sourceConvolutionSquare
      ledgers traceData.ccm25ArithmeticPackage
  sourceArchimedeanSignBridge :
    SourceArchimedeanSignBridge
      (RouteInputs.ofExpandedSourcePackage pkg)
      pkg.cc20Trace.sourceTraceTest
      (SourceBackedFixedSTest.ofExpandedSourcePackage pkg fixedFront)

namespace TraceScaleRouteFrontEndData

def ofTraceData
    (pkg : Source.SourceObject.SourceObjectPackage)
    (fixedFront : ExpandedSourceFixedSTestFrontEnd pkg)
    (traceData : TraceFrontEndData pkg fixedFront)
    (ledgers : RouteLedgers)
    (commonTuple :
      SourceCommonTestTupleContract
        (RouteInputs.ofExpandedSourcePackage pkg)
        (SourceBackedFixedSTest.ofExpandedSourcePackage pkg fixedFront)
        traceData.lambda
        pkg.commonTest.sourceConvolutionSquare
        traceData.ccm25ArithmeticPackage)
    (signDefectClassification :
      SourceSignDefectClassification
        (RouteInputs.ofExpandedSourcePackage pkg)
        (SourceBackedFixedSTest.ofExpandedSourcePackage pkg fixedFront)
        traceData.lambda ledgers)
    (traceScaleOwnsSignDefectRemainder :
      traceData.traceScaleNoMissingBulk.rankPoleCdefOwnEveryRemainder
        ledgers signDefectClassification)
    (restrictedToFullQWBridge :
      RestrictedToFullQWBridgeContract
        (RouteInputs.ofExpandedSourcePackage pkg)
        (SourceBackedFixedSTest.ofExpandedSourcePackage pkg fixedFront)
        traceData.lambda
        pkg.commonTest.sourceConvolutionSquare
        ledgers traceData.ccm25ArithmeticPackage)
    (sourceArchimedeanSignBridge :
      SourceArchimedeanSignBridge
        (RouteInputs.ofExpandedSourcePackage pkg)
        pkg.cc20Trace.sourceTraceTest
        (SourceBackedFixedSTest.ofExpandedSourcePackage pkg fixedFront)) :
    TraceScaleRouteFrontEndData pkg fixedFront traceData where
  ledgers := ledgers
  traceScaleNoMissingBulk := traceData.traceScaleNoMissingBulk
  traceScaleMatchesTraceData := rfl
  commonTuple := commonTuple
  signDefectClassification := signDefectClassification
  traceScaleOwnsSignDefectRemainder := traceScaleOwnsSignDefectRemainder
  restrictedToFullQWBridge := restrictedToFullQWBridge
  sourceArchimedeanSignBridge := sourceArchimedeanSignBridge

def toExpandedSourceRouteCertificateFrontEnd
    (pkg : Source.SourceObject.SourceObjectPackage)
    (fixedFront : ExpandedSourceFixedSTestFrontEnd pkg)
    (traceData : TraceFrontEndData pkg fixedFront)
    (routeData : TraceScaleRouteFrontEndData pkg fixedFront traceData) :
    ExpandedSourceRouteCertificateFrontEnd pkg fixedFront
      (traceData.toExpandedSourceTraceReadOffFrontEnd pkg fixedFront) where
  ledgers := routeData.ledgers
  commonTuple := routeData.commonTuple
  signDefectClassification := routeData.signDefectClassification
  restrictedToFullQWBridge := routeData.restrictedToFullQWBridge
  sourceArchimedeanSignBridge := routeData.sourceArchimedeanSignBridge

theorem route_front_trace_scale_matches_trace_data
    (pkg : Source.SourceObject.SourceObjectPackage)
    (fixedFront : ExpandedSourceFixedSTestFrontEnd pkg)
    (traceData : TraceFrontEndData pkg fixedFront)
    (routeData : TraceScaleRouteFrontEndData pkg fixedFront traceData) :
    routeData.traceScaleNoMissingBulk = traceData.traceScaleNoMissingBulk :=
  routeData.traceScaleMatchesTraceData

theorem of_trace_data_trace_scale_matches_trace_data
    (pkg : Source.SourceObject.SourceObjectPackage)
    (fixedFront : ExpandedSourceFixedSTestFrontEnd pkg)
    (traceData : TraceFrontEndData pkg fixedFront)
    (ledgers : RouteLedgers)
    (commonTuple :
      SourceCommonTestTupleContract
        (RouteInputs.ofExpandedSourcePackage pkg)
        (SourceBackedFixedSTest.ofExpandedSourcePackage pkg fixedFront)
        traceData.lambda
        pkg.commonTest.sourceConvolutionSquare
        traceData.ccm25ArithmeticPackage)
    (signDefectClassification :
      SourceSignDefectClassification
        (RouteInputs.ofExpandedSourcePackage pkg)
        (SourceBackedFixedSTest.ofExpandedSourcePackage pkg fixedFront)
        traceData.lambda ledgers)
    (traceScaleOwnsSignDefectRemainder :
      traceData.traceScaleNoMissingBulk.rankPoleCdefOwnEveryRemainder
        ledgers signDefectClassification)
    (restrictedToFullQWBridge :
      RestrictedToFullQWBridgeContract
        (RouteInputs.ofExpandedSourcePackage pkg)
        (SourceBackedFixedSTest.ofExpandedSourcePackage pkg fixedFront)
        traceData.lambda
        pkg.commonTest.sourceConvolutionSquare
        ledgers traceData.ccm25ArithmeticPackage)
    (sourceArchimedeanSignBridge :
      SourceArchimedeanSignBridge
        (RouteInputs.ofExpandedSourcePackage pkg)
        pkg.cc20Trace.sourceTraceTest
        (SourceBackedFixedSTest.ofExpandedSourcePackage pkg fixedFront)) :
    (ofTraceData pkg fixedFront traceData ledgers commonTuple
      signDefectClassification traceScaleOwnsSignDefectRemainder
      restrictedToFullQWBridge sourceArchimedeanSignBridge).traceScaleNoMissingBulk =
      traceData.traceScaleNoMissingBulk :=
  rfl

theorem route_front_no_extra_bulk
    (pkg : Source.SourceObject.SourceObjectPackage)
    (fixedFront : ExpandedSourceFixedSTestFrontEnd pkg)
    (traceData : TraceFrontEndData pkg fixedFront)
    (routeData : TraceScaleRouteFrontEndData pkg fixedFront traceData) :
    routeData.traceScaleNoMissingBulk.noExtraBulkScaleTerm :=
  routeData.traceScaleNoMissingBulk.noExtraBulkScaleTermHolds

theorem route_front_trace_scale_owns_sign_defect
    (pkg : Source.SourceObject.SourceObjectPackage)
    (fixedFront : ExpandedSourceFixedSTestFrontEnd pkg)
    (traceData : TraceFrontEndData pkg fixedFront)
    (routeData : TraceScaleRouteFrontEndData pkg fixedFront traceData) :
    routeData.traceScaleNoMissingBulk.rankPoleCdefOwnEveryRemainder
      routeData.ledgers routeData.signDefectClassification :=
  routeData.traceScaleOwnsSignDefectRemainder

theorem route_front_ledgers
    (pkg : Source.SourceObject.SourceObjectPackage)
    (fixedFront : ExpandedSourceFixedSTestFrontEnd pkg)
    (traceData : TraceFrontEndData pkg fixedFront)
    (routeData : TraceScaleRouteFrontEndData pkg fixedFront traceData) :
    (routeData.toExpandedSourceRouteCertificateFrontEnd
      pkg fixedFront traceData).ledgers = routeData.ledgers :=
  rfl

theorem route_front_sign_defect_classification
    (pkg : Source.SourceObject.SourceObjectPackage)
    (fixedFront : ExpandedSourceFixedSTestFrontEnd pkg)
    (traceData : TraceFrontEndData pkg fixedFront)
    (routeData : TraceScaleRouteFrontEndData pkg fixedFront traceData) :
    (routeData.toExpandedSourceRouteCertificateFrontEnd
      pkg fixedFront traceData).signDefectClassification =
      routeData.signDefectClassification :=
  rfl

end TraceScaleRouteFrontEndData

theorem expanded_source_package_convolution_square_read_off
    (pkg : Source.SourceObject.SourceObjectPackage)
    (fixedFront : ExpandedSourceFixedSTestFrontEnd pkg) :
    pkg.commonTest.sourceConvolutionSquare =
      (RouteInputs.ofExpandedSourcePackage pkg).ccm25.weilSymbols.convolutionStar
        (SourceBackedFixedSTest.ofExpandedSourcePackage pkg fixedFront).weilTest
        (SourceBackedFixedSTest.ofExpandedSourcePackage pkg fixedFront).weilTest := by
  exact pkg.commonTest.sourceConvolutionSquareReadOff

theorem expanded_source_common_test_eq_ccm25_arithmetic_source_test
    (pkg : Source.SourceObject.SourceObjectPackage) :
    Source.SourceObject.SourceObjectPackage.toCCM25CommonSourceTest pkg =
      Source.CCM25Concrete.Rows.source_test_of_arithmetic_rows
        pkg.ccm25.concreteArithmeticRows
        pkg.commonTest.sourceTest pkg.commonTest.sourceTest :=
  Source.SourceObject.SourceObjectPackage.common_ccm25_source_test_eq_arithmetic_rows
    pkg

theorem expanded_source_common_square_eq_ccm25_source_test_square
    (pkg : Source.SourceObject.SourceObjectPackage) :
    pkg.commonTest.sourceConvolutionSquare =
      (Source.SourceObject.SourceObjectPackage.toCCM25CommonSourceTest
        pkg).sourceConvolutionSquare :=
  Source.SourceObject.SourceObjectPackage.common_convolution_square_eq_ccm25_source_test_square
    pkg

def expanded_source_common_test_involution_bridge
    (pkg : Source.SourceObject.SourceObjectPackage) :
    Source.SourceObject.CommonTestInvolutionBridge
      (RouteInputs.ofExpandedSourcePackage pkg).ccm25.weilSymbols
      pkg.commonTest :=
  Source.SourceObject.SourceObjectPackage.commonTestInvolutionBridge pkg

def expanded_source_ccm24_common_test_bridge
    (pkg : Source.SourceObject.SourceObjectPackage) :
    Source.SourceObject.CCM24CommonTestBridge
      (RouteInputs.ofExpandedSourcePackage pkg).ccm25.weilSymbols
      pkg.commonTest pkg.ccm24 :=
  Source.SourceObject.SourceObjectPackage.ccm24CommonTestBridge pkg

def expanded_source_cc20_common_test_bridge
    (pkg : Source.SourceObject.SourceObjectPackage) :
    Source.SourceObject.CC20CommonTestBridge
      (RouteInputs.ofExpandedSourcePackage pkg).ccm25.weilSymbols
      pkg.commonTest pkg.cc20Trace :=
  Source.SourceObject.SourceObjectPackage.cc20CommonTestBridge pkg

theorem expanded_source_ccm24_common_support_window
    (pkg : Source.SourceObject.SourceObjectPackage) :
    pkg.ccm24.semilocalSymbols.supportInWindow
      pkg.ccm24.sourceTestLeg pkg.ccm24.sourceSupportWindow :=
  Source.SourceObject.SourceObjectPackage.ccm24_common_support_window pkg

theorem expanded_source_ccm24_common_convolution_support
    (pkg : Source.SourceObject.SourceObjectPackage) :
    pkg.ccm24.semilocalSymbols.convolutionSupportTransported
      pkg.ccm24.sourceTestLeg pkg.ccm24.sourceSupportWindow :=
  Source.SourceObject.SourceObjectPackage.ccm24_common_convolution_support_transported
    pkg

theorem expanded_source_cc20_common_mellin_half_density
    (pkg : Source.SourceObject.SourceObjectPackage) :
    ArchimedeanTraceSymbols.MellinHalfDensityConventionStatement
      pkg.cc20Trace.archimedeanSymbols :=
  Source.SourceObject.SourceObjectPackage.cc20_common_mellin_half_density pkg

def expanded_source_convolution_square_compatibility
    (pkg : Source.SourceObject.SourceObjectPackage)
    (fixedFront : ExpandedSourceFixedSTestFrontEnd pkg)
    (traceFront : ExpandedSourceTraceReadOffFrontEnd pkg fixedFront) :
    SourceConvolutionSquareCompatibility
      (RouteInputs.ofExpandedSourcePackage pkg)
      (SourceBackedFixedSTest.ofExpandedSourcePackage pkg fixedFront)
      traceFront.lambda
      pkg.commonTest.sourceConvolutionSquare
      traceFront.ccm25ArithmeticPackage :=
  source_convolution_square_compatibility_of_package
    (expanded_source_package_convolution_square_read_off pkg fixedFront)

def expanded_source_route_common_test
    (pkg : Source.SourceObject.SourceObjectPackage)
    (fixedFront : ExpandedSourceFixedSTestFrontEnd pkg)
    (traceFront : ExpandedSourceTraceReadOffFrontEnd pkg fixedFront)
    (routeFront :
      ExpandedSourceRouteCertificateFrontEnd pkg fixedFront traceFront) :
    SourceQWUsesCommonTest
      (RouteInputs.ofExpandedSourcePackage pkg)
      (SourceBackedFixedSTest.ofExpandedSourcePackage pkg fixedFront)
      traceFront.lambda
      pkg.commonTest.sourceConvolutionSquare
      traceFront.ccm25ArithmeticPackage :=
  source_qw_uses_common_test_of_common_tuple routeFront.commonTuple

def expanded_source_route_common_tuple_on_route_square
    (pkg : Source.SourceObject.SourceObjectPackage)
    (fixedFront : ExpandedSourceFixedSTestFrontEnd pkg)
    (traceFront : ExpandedSourceTraceReadOffFrontEnd pkg fixedFront)
    (routeFront :
      ExpandedSourceRouteCertificateFrontEnd pkg fixedFront traceFront) :
    SourceCommonTestTupleContract
      (RouteInputs.ofExpandedSourcePackage pkg)
      (SourceBackedFixedSTest.ofExpandedSourcePackage pkg fixedFront)
      traceFront.lambda
      ((RouteInputs.ofExpandedSourcePackage pkg).ccm25.weilSymbols.convolutionStar
        (SourceBackedFixedSTest.ofExpandedSourcePackage pkg fixedFront).weilTest
        (SourceBackedFixedSTest.ofExpandedSourcePackage pkg fixedFront).weilTest)
      traceFront.ccm25ArithmeticPackage := by
  rw [← expanded_source_package_convolution_square_read_off pkg fixedFront]
  exact routeFront.commonTuple

def expanded_source_route_common_test_on_route_square
    (pkg : Source.SourceObject.SourceObjectPackage)
    (fixedFront : ExpandedSourceFixedSTestFrontEnd pkg)
    (traceFront : ExpandedSourceTraceReadOffFrontEnd pkg fixedFront)
    (routeFront :
      ExpandedSourceRouteCertificateFrontEnd pkg fixedFront traceFront) :
    SourceQWUsesCommonTest
      (RouteInputs.ofExpandedSourcePackage pkg)
      (SourceBackedFixedSTest.ofExpandedSourcePackage pkg fixedFront)
      traceFront.lambda
      ((RouteInputs.ofExpandedSourcePackage pkg).ccm25.weilSymbols.convolutionStar
        (SourceBackedFixedSTest.ofExpandedSourcePackage pkg fixedFront).weilTest
        (SourceBackedFixedSTest.ofExpandedSourcePackage pkg fixedFront).weilTest)
      traceFront.ccm25ArithmeticPackage :=
  source_qw_uses_common_test_of_common_tuple
    (expanded_source_route_common_tuple_on_route_square
      pkg fixedFront traceFront routeFront)

def expanded_source_restricted_to_full_bridge_on_route_square
    (pkg : Source.SourceObject.SourceObjectPackage)
    (fixedFront : ExpandedSourceFixedSTestFrontEnd pkg)
    (traceFront : ExpandedSourceTraceReadOffFrontEnd pkg fixedFront)
    (routeFront :
      ExpandedSourceRouteCertificateFrontEnd pkg fixedFront traceFront) :
    RestrictedToFullQWBridgeContract
      (RouteInputs.ofExpandedSourcePackage pkg)
      (SourceBackedFixedSTest.ofExpandedSourcePackage pkg fixedFront)
      traceFront.lambda
      ((RouteInputs.ofExpandedSourcePackage pkg).ccm25.weilSymbols.convolutionStar
        (SourceBackedFixedSTest.ofExpandedSourcePackage pkg fixedFront).weilTest
        (SourceBackedFixedSTest.ofExpandedSourcePackage pkg fixedFront).weilTest)
      routeFront.ledgers traceFront.ccm25ArithmeticPackage := by
  rw [← expanded_source_package_convolution_square_read_off pkg fixedFront]
  exact routeFront.restrictedToFullQWBridge

def expanded_source_route_final_sign_bridge
    (pkg : Source.SourceObject.SourceObjectPackage)
    (fixedFront : ExpandedSourceFixedSTestFrontEnd pkg)
    (traceFront : ExpandedSourceTraceReadOffFrontEnd pkg fixedFront)
    (routeFront :
      ExpandedSourceRouteCertificateFrontEnd pkg fixedFront traceFront) :
    FinalSignBridgeContract
      (RouteInputs.ofExpandedSourcePackage pkg)
      pkg.cc20Trace.sourceTraceTest
      (SourceBackedFixedSTest.ofExpandedSourcePackage pkg fixedFront)
      traceFront.lambda
      ((RouteInputs.ofExpandedSourcePackage pkg).ccm25.weilSymbols.convolutionStar
        (SourceBackedFixedSTest.ofExpandedSourcePackage pkg fixedFront).weilTest
        (SourceBackedFixedSTest.ofExpandedSourcePackage pkg fixedFront).weilTest)
      traceFront.ccm25ArithmeticPackage :=
  final_sign_bridge_data_of_common_test
    (expanded_source_route_common_test_on_route_square
      pkg fixedFront traceFront routeFront)
    routeFront.sourceArchimedeanSignBridge

noncomputable def route_backed_cc20_nonpositivity_input_data_of_route_bridge_certificate
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {L : RouteLedgers}
    (bridge : RouteBridgeCertificate inputs g L) :
    RouteBackedCC20NonpositivityInputData inputs g L bridge
      (toWeilPositivityInput inputs g L) where
  inputIsRouteInput := rfl
  sourceBackedFullPositivity :=
    source_backed_full_positivity_of_route_bridge_certificate bridge
  finalSignBridge :=
    final_sign_bridge_of_route_bridge_certificate bridge
  finalSignNonpositive :=
    final_sign_nonnegative_to_nonpositive_of_contract
      (final_sign_bridge_of_route_bridge_certificate bridge)
  fullWeilPositivity :=
    full_weil_positivity_input_holds
      (full_weil_positivity_of_source_backed
        (source_backed_full_positivity_of_route_bridge_certificate bridge))

def route_backed_cc20_triple_vanishing_input_data_of_source_backed
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {L : RouteLedgers} :
    RouteBackedCC20TripleVanishingInputData inputs g L
      (toWeilPositivityInput inputs g L) where
  inputIsRouteInput := rfl
  tripleVanishingSymbols := g.tripleVanishingSymbols
  symbolsAreSourceBacked := rfl
  sourceTripleVanishing := g.tripleVanishingSourceHolds
  routeTripleVanishing := triple_vanishing_of_source_backed g
  tripleVanishingMatchesMellin :=
    triple_vanishing_input_holds
      (triple_vanishing_of_source_backed g)

noncomputable def route_backed_cc20_exit_input_data_of_route_bridge_certificate
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {L : RouteLedgers}
    (bridge : RouteBridgeCertificate inputs g L) :
    RouteBackedCC20ExitInputData inputs g L bridge where
  input := toWeilPositivityInput inputs g L
  inputIsRouteInput := rfl
  sourceBackedFullPositivity :=
    source_backed_full_positivity_of_route_bridge_certificate bridge
  nonpositivityInput :=
    route_backed_cc20_nonpositivity_input_data_of_route_bridge_certificate
      bridge
  tripleVanishingInput :=
    route_backed_cc20_triple_vanishing_input_data_of_source_backed
  finalSignBridge :=
    (route_backed_cc20_nonpositivity_input_data_of_route_bridge_certificate
      bridge).finalSignBridge
  finalSignNonpositive :=
    (route_backed_cc20_nonpositivity_input_data_of_route_bridge_certificate
      bridge).finalSignNonpositive
  tripleVanishing :=
    (route_backed_cc20_triple_vanishing_input_data_of_source_backed
      : RouteBackedCC20TripleVanishingInputData inputs g L
          (toWeilPositivityInput inputs g L)).tripleVanishingMatchesMellin
  fullWeilPositivity :=
    (route_backed_cc20_nonpositivity_input_data_of_route_bridge_certificate
      bridge).fullWeilPositivity
  propositionC1InputData :=
    let hroute :=
      Source.cc20_proposition_c1_input_data
        inputs.cc20.cc20RHExitObjectPackage.finiteSetAdmissible
        inputs.cc20.cc20RHExitObjectPackage.finiteSetDisjointFromNontrivialZeros
        ((route_backed_cc20_triple_vanishing_input_data_of_source_backed
          : RouteBackedCC20TripleVanishingInputData inputs g L
              (toWeilPositivityInput inputs g L)).tripleVanishingMatchesMellin)
        ((route_backed_cc20_nonpositivity_input_data_of_route_bridge_certificate
          bridge).fullWeilPositivity)
    hroute.c1InputData

def nonpositivity_input_of_route_backed_cc20_exit_input_data
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {L : RouteLedgers} {bridge : RouteBridgeCertificate inputs g L}
    (h : RouteBackedCC20ExitInputData inputs g L bridge) :
    RouteBackedCC20NonpositivityInputData inputs g L bridge h.input :=
  h.nonpositivityInput

def final_sign_nonpositive_of_route_backed_cc20_exit_input_data
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {L : RouteLedgers} {bridge : RouteBridgeCertificate inputs g L}
    (h : RouteBackedCC20ExitInputData inputs g L bridge) :
    SourceQWNonnegativeToCC20Nonpositive inputs
      bridge.sourceTraceReadOff.archimedeanTest g
      bridge.sourceTraceReadOff.lambda
      (inputs.ccm25.weilSymbols.convolutionStar g.weilTest g.weilTest)
      bridge.sourceTraceReadOff.ccm25ArithmeticPackage :=
  h.nonpositivityInput.finalSignNonpositive

theorem route_triple_vanishing_of_route_backed_cc20_exit_input_data
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {L : RouteLedgers} {bridge : RouteBridgeCertificate inputs g L}
    (h : RouteBackedCC20ExitInputData inputs g L bridge) :
    TripleVanishingSymbols.TripleVanishingStatement
      h.tripleVanishingInput.tripleVanishingSymbols :=
  h.tripleVanishingInput.sourceTripleVanishing

theorem c1_triple_vanishing_row_of_route_backed_cc20_exit_input_data
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {L : RouteLedgers} {bridge : RouteBridgeCertificate inputs g L}
    (h : RouteBackedCC20ExitInputData inputs g L bridge) :
    h.input.tripleVanishing :=
  Source.triple_vanishing_of_c1_input_data h.propositionC1InputData

theorem c1_finite_set_disjoint_row_of_route_backed_cc20_exit_input_data
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {L : RouteLedgers} {bridge : RouteBridgeCertificate inputs g L}
    (h : RouteBackedCC20ExitInputData inputs g L bridge) :
    Source.SourceFiniteSetDisjointFromNontrivialZeros
      inputs.cc20.rhDefinitionBridge
      inputs.cc20.cc20RHExitObjectPackage.finiteVanishingSet :=
  Source.finite_set_disjoint_of_c1_input_data h.propositionC1InputData

theorem c1_zero_not_source_nontrivial_zero_of_route_backed_cc20_exit_input_data
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {L : RouteLedgers} {bridge : RouteBridgeCertificate inputs g L}
    (h : RouteBackedCC20ExitInputData inputs g L bridge) :
    ¬inputs.cc20.rhDefinitionBridge.sourceNontrivialZero
      (Source.criticalVanishingPointValue CriticalVanishingPoint.zero) :=
  Source.zero_not_source_nontrivial_zero_of_c1_input_data
    inputs.cc20.cc20RHExitObjectPackage.finiteSetAdmissible
    h.propositionC1InputData

theorem c1_half_not_source_nontrivial_zero_of_route_backed_cc20_exit_input_data
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {L : RouteLedgers} {bridge : RouteBridgeCertificate inputs g L}
    (h : RouteBackedCC20ExitInputData inputs g L bridge) :
    ¬inputs.cc20.rhDefinitionBridge.sourceNontrivialZero
      (Source.criticalVanishingPointValue CriticalVanishingPoint.half) :=
  Source.half_not_source_nontrivial_zero_of_c1_input_data
    inputs.cc20.cc20RHExitObjectPackage.finiteSetAdmissible
    h.propositionC1InputData

theorem c1_one_not_source_nontrivial_zero_of_route_backed_cc20_exit_input_data
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {L : RouteLedgers} {bridge : RouteBridgeCertificate inputs g L}
    (h : RouteBackedCC20ExitInputData inputs g L bridge) :
    ¬inputs.cc20.rhDefinitionBridge.sourceNontrivialZero
      (Source.criticalVanishingPointValue CriticalVanishingPoint.one) :=
  Source.one_not_source_nontrivial_zero_of_c1_input_data
    inputs.cc20.cc20RHExitObjectPackage.finiteSetAdmissible
    h.propositionC1InputData

theorem c1_triple_vanishing_row_uses_route_triple_input
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {L : RouteLedgers} {bridge : RouteBridgeCertificate inputs g L}
    (h : RouteBackedCC20ExitInputData inputs g L bridge) :
    Source.triple_vanishing_of_c1_input_data h.propositionC1InputData =
      h.tripleVanishingInput.tripleVanishingMatchesMellin := by
  rfl

def c1_full_positivity_row_of_route_backed_cc20_exit_input_data
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {L : RouteLedgers} {bridge : RouteBridgeCertificate inputs g L}
    (h : RouteBackedCC20ExitInputData inputs g L bridge) :
    h.input.fullWeilPositivity :=
  Source.full_positivity_of_c1_input_data h.propositionC1InputData

theorem c1_full_positivity_row_uses_route_nonpositivity_input
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {L : RouteLedgers} {bridge : RouteBridgeCertificate inputs g L}
    (h : RouteBackedCC20ExitInputData inputs g L bridge) :
  Source.full_positivity_of_c1_input_data h.propositionC1InputData =
      c1_full_positivity_row_of_route_backed_cc20_exit_input_data h := by
  rfl

def route_certificate_of_sign_defect_classification
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {L : RouteLedgers}
    (sourceTraceReadOff : SourceTraceReadOffData inputs g)
    (signDefectClassification :
      SourceSignDefectClassification inputs g sourceTraceReadOff.lambda L)
    (restrictedToFullQWBridge :
      RestrictedToFullQWBridgeContract inputs g sourceTraceReadOff.lambda
        (inputs.ccm25.weilSymbols.convolutionStar g.weilTest g.weilTest)
        L sourceTraceReadOff.ccm25ArithmeticPackage)
    (finalSignBridge :
      FinalSignBridgeContract inputs sourceTraceReadOff.archimedeanTest g
        sourceTraceReadOff.lambda
        (inputs.ccm25.weilSymbols.convolutionStar g.weilTest g.weilTest)
        sourceTraceReadOff.ccm25ArithmeticPackage) :
    RouteCertificate inputs where
  sourceBackedTest := g
  ledgers := L
  bridge :=
    route_bridge_certificate_of_sign_defect_classification
      sourceTraceReadOff signDefectClassification
      restrictedToFullQWBridge finalSignBridge

def route_certificate_of_expanded_source_package
    (pkg : Source.SourceObject.SourceObjectPackage)
    (fixedFront : ExpandedSourceFixedSTestFrontEnd pkg)
    (traceFront : ExpandedSourceTraceReadOffFrontEnd pkg fixedFront)
    (routeFront :
      ExpandedSourceRouteCertificateFrontEnd pkg fixedFront traceFront) :
    RouteCertificate (RouteInputs.ofExpandedSourcePackage pkg) :=
  route_certificate_of_sign_defect_classification
    (SourceTraceReadOffData.ofExpandedSourcePackage pkg fixedFront traceFront)
    routeFront.signDefectClassification
    (expanded_source_restricted_to_full_bridge_on_route_square
      pkg fixedFront traceFront routeFront)
    (expanded_source_route_final_sign_bridge pkg fixedFront traceFront routeFront)

def route_front_end_of_trace_scale_data
    (pkg : Source.SourceObject.SourceObjectPackage)
    (fixedFront : ExpandedSourceFixedSTestFrontEnd pkg)
    (traceData : TraceFrontEndData pkg fixedFront)
    (routeData : TraceScaleRouteFrontEndData pkg fixedFront traceData) :
    ExpandedSourceRouteCertificateFrontEnd pkg fixedFront
      (traceData.toExpandedSourceTraceReadOffFrontEnd pkg fixedFront) :=
  routeData.toExpandedSourceRouteCertificateFrontEnd pkg fixedFront traceData

def route_certificate_of_trace_scale_data
    (pkg : Source.SourceObject.SourceObjectPackage)
    (fixedFront : ExpandedSourceFixedSTestFrontEnd pkg)
    (traceData : TraceFrontEndData pkg fixedFront)
    (routeData : TraceScaleRouteFrontEndData pkg fixedFront traceData) :
    RouteCertificate (RouteInputs.ofExpandedSourcePackage pkg) :=
  route_certificate_of_expanded_source_package
    pkg fixedFront
    (traceData.toExpandedSourceTraceReadOffFrontEnd pkg fixedFront)
    (route_front_end_of_trace_scale_data pkg fixedFront traceData routeData)

def trace_scale_route_front_end_of_normalized_comparison
    (base : Source.SourceObjectTheoremBasePackage)
    (common : Source.SourceObjectCommonData base)
    (ccm24 : Source.SourceObject.CCM24SemilocalObjectPackage)
    (normalizedSeed :
      Source.CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (remainders :
      Source.CC20Concrete.TraceScale.CC20TracePackageRemainderData
        normalizedSeed)
    (rhExit : Source.SourceObject.CC20RHExitObjectPackage)
    (bridges :
      Source.SourceObjectCrossObjectBridges base common
        (Source.SourceObjectExpandedRows.ofNormalizedCC20Trace
          ccm24 normalizedSeed remainders)
        rhExit)
    (fixedData :
      FixedSTestObligationData
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges))
    (traceData :
      TraceFrontEndData
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges)
        (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData))
    (comparison :
      TraceFrontEndData.NormalizedSupportSquareQWLambdaSourceComparison
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData)
    (ledgers : RouteLedgers)
    (commonTuple :
      SourceCommonTestTupleContract
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)
        traceData.lambda
        (Source.SourceObject.CommonTestObject.sourceConvolutionSquare
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges).commonTest)
        traceData.ccm25ArithmeticPackage)
    (signDefectClassification :
      SourceSignDefectClassification
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)
        traceData.lambda ledgers)
    (traceScaleMatchesComparison :
      traceData.traceScaleNoMissingBulk =
        TraceFrontEndData.traceScaleNoMissingBulkOfNormalizedPackageFromComparison
          base common ccm24 normalizedSeed remainders rhExit bridges fixedData
          traceData comparison
          (fun L _h =>
            SourceSignDefectClassification
              (RouteInputs.ofExpandedSourcePackage
                (Source.sourceObjectPackageOfNormalizedCC20Trace
                  base common ccm24 normalizedSeed remainders rhExit bridges))
              (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
                base common ccm24 normalizedSeed remainders rhExit bridges
                fixedData)
              traceData.lambda L)
          True trivial)
    (traceScaleOwnsSignDefectRemainder :
      (TraceFrontEndData.traceScaleNoMissingBulkOfNormalizedPackageFromComparison
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData comparison
        (fun L _h =>
          SourceSignDefectClassification
            (RouteInputs.ofExpandedSourcePackage
              (Source.sourceObjectPackageOfNormalizedCC20Trace
                base common ccm24 normalizedSeed remainders rhExit bridges))
            (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
              base common ccm24 normalizedSeed remainders rhExit bridges
              fixedData)
            traceData.lambda L)
        True trivial).rankPoleCdefOwnEveryRemainder
        ledgers signDefectClassification)
    (restrictedToFullQWBridge :
      RestrictedToFullQWBridgeContract
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)
        traceData.lambda
        (Source.SourceObject.CommonTestObject.sourceConvolutionSquare
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges).commonTest)
        ledgers traceData.ccm25ArithmeticPackage)
    (sourceArchimedeanSignBridge :
      SourceArchimedeanSignBridge
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges).cc20Trace.sourceTraceTest
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)) :
    TraceScaleRouteFrontEndData
      (Source.sourceObjectPackageOfNormalizedCC20Trace
        base common ccm24 normalizedSeed remainders rhExit bridges)
      (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData)
      traceData :=
  TraceScaleRouteFrontEndData.ofTraceData
    (Source.sourceObjectPackageOfNormalizedCC20Trace
      base common ccm24 normalizedSeed remainders rhExit bridges)
    (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
      base common ccm24 normalizedSeed remainders rhExit bridges fixedData)
    traceData ledgers commonTuple signDefectClassification
    (by
      rw [traceScaleMatchesComparison]
      exact traceScaleOwnsSignDefectRemainder)
    restrictedToFullQWBridge sourceArchimedeanSignBridge

def trace_scale_route_front_end_of_normalized_package_bridge
    (base : Source.SourceObjectTheoremBasePackage)
    (common : Source.SourceObjectCommonData base)
    (ccm24 : Source.SourceObject.CCM24SemilocalObjectPackage)
    (normalizedSeed :
      Source.CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (remainders :
      Source.CC20Concrete.TraceScale.CC20TracePackageRemainderData
        normalizedSeed)
    (rhExit : Source.SourceObject.CC20RHExitObjectPackage)
    (bridges :
      Source.SourceObjectCrossObjectBridges base common
        (Source.SourceObjectExpandedRows.ofNormalizedCC20Trace
          ccm24 normalizedSeed remainders)
        rhExit)
    (fixedData :
      FixedSTestObligationData
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges))
    (traceData :
      TraceFrontEndData
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges)
        (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData))
    (ledgers : RouteLedgers)
    (commonTuple :
      SourceCommonTestTupleContract
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)
        traceData.lambda
        (Source.SourceObject.CommonTestObject.sourceConvolutionSquare
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges).commonTest)
        traceData.ccm25ArithmeticPackage)
    (signDefectClassification :
      SourceSignDefectClassification
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)
        traceData.lambda ledgers)
    (traceScaleMatchesBridge :
      traceData.traceScaleNoMissingBulk =
        TraceFrontEndData.traceScaleNoMissingBulkOfNormalizedPackageFromComparison
          base common ccm24 normalizedSeed remainders rhExit bridges fixedData
          traceData
          (TraceFrontEndData.normalizedSupportSquareQWLambdaSourceComparisonOfPackageBridge
            base common ccm24 normalizedSeed remainders rhExit bridges fixedData
            traceData)
          (fun L _h =>
            SourceSignDefectClassification
              (RouteInputs.ofExpandedSourcePackage
                (Source.sourceObjectPackageOfNormalizedCC20Trace
                  base common ccm24 normalizedSeed remainders rhExit bridges))
              (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
                base common ccm24 normalizedSeed remainders rhExit bridges
                fixedData)
              traceData.lambda L)
          True trivial)
    (traceScaleOwnsSignDefectRemainder :
      (TraceFrontEndData.traceScaleNoMissingBulkOfNormalizedPackageFromComparison
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData
        (TraceFrontEndData.normalizedSupportSquareQWLambdaSourceComparisonOfPackageBridge
          base common ccm24 normalizedSeed remainders rhExit bridges fixedData
          traceData)
        (fun L _h =>
          SourceSignDefectClassification
            (RouteInputs.ofExpandedSourcePackage
              (Source.sourceObjectPackageOfNormalizedCC20Trace
                base common ccm24 normalizedSeed remainders rhExit bridges))
            (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
              base common ccm24 normalizedSeed remainders rhExit bridges
              fixedData)
            traceData.lambda L)
        True trivial).rankPoleCdefOwnEveryRemainder
        ledgers signDefectClassification)
    (restrictedToFullQWBridge :
      RestrictedToFullQWBridgeContract
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)
        traceData.lambda
        (Source.SourceObject.CommonTestObject.sourceConvolutionSquare
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges).commonTest)
        ledgers traceData.ccm25ArithmeticPackage)
    (sourceArchimedeanSignBridge :
      SourceArchimedeanSignBridge
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges).cc20Trace.sourceTraceTest
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)) :
    TraceScaleRouteFrontEndData
      (Source.sourceObjectPackageOfNormalizedCC20Trace
        base common ccm24 normalizedSeed remainders rhExit bridges)
      (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData)
      traceData :=
  trace_scale_route_front_end_of_normalized_comparison
    base common ccm24 normalizedSeed remainders rhExit bridges fixedData
    traceData
    (TraceFrontEndData.normalizedSupportSquareQWLambdaSourceComparisonOfPackageBridge
      base common ccm24 normalizedSeed remainders rhExit bridges fixedData
      traceData)
    ledgers commonTuple signDefectClassification traceScaleMatchesBridge
    traceScaleOwnsSignDefectRemainder restrictedToFullQWBridge
    sourceArchimedeanSignBridge

/--
Route front-end constructor that first replaces the stored trace-scale ledger
by the normalized comparison-backed ledger.

Compared with `trace_scale_route_front_end_of_normalized_comparison`, this
does not ask the caller to prove that the old stored ledger equals the
comparison-generated one.  The replacement trace data stores that ledger by
definition, while all trace/read-off bridge fields are copied from the supplied
trace front end.
-/
def trace_scale_route_front_end_of_normalized_comparison_replacement
    (base : Source.SourceObjectTheoremBasePackage)
    (common : Source.SourceObjectCommonData base)
    (ccm24 : Source.SourceObject.CCM24SemilocalObjectPackage)
    (normalizedSeed :
      Source.CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (remainders :
      Source.CC20Concrete.TraceScale.CC20TracePackageRemainderData
        normalizedSeed)
    (rhExit : Source.SourceObject.CC20RHExitObjectPackage)
    (bridges :
      Source.SourceObjectCrossObjectBridges base common
        (Source.SourceObjectExpandedRows.ofNormalizedCC20Trace
          ccm24 normalizedSeed remainders)
        rhExit)
    (fixedData :
      FixedSTestObligationData
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges))
    (traceData :
      TraceFrontEndData
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges)
        (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData))
    (comparison :
      TraceFrontEndData.NormalizedSupportSquareQWLambdaSourceComparison
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData)
    (ledgers : RouteLedgers)
    (commonTuple :
      SourceCommonTestTupleContract
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)
        traceData.lambda
        (Source.SourceObject.CommonTestObject.sourceConvolutionSquare
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges).commonTest)
        traceData.ccm25ArithmeticPackage)
    (signDefectClassification :
      SourceSignDefectClassification
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)
        traceData.lambda ledgers)
    (restrictedToFullQWBridge :
      RestrictedToFullQWBridgeContract
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)
        traceData.lambda
        (Source.SourceObject.CommonTestObject.sourceConvolutionSquare
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges).commonTest)
        ledgers traceData.ccm25ArithmeticPackage)
    (sourceArchimedeanSignBridge :
      SourceArchimedeanSignBridge
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges).cc20Trace.sourceTraceTest
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)) :
    TraceScaleRouteFrontEndData
      (Source.sourceObjectPackageOfNormalizedCC20Trace
        base common ccm24 normalizedSeed remainders rhExit bridges)
      (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData)
      (TraceFrontEndData.withTraceScaleNoMissingBulkOfNormalizedComparison
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData comparison) :=
  let normalizedTraceData :=
    TraceFrontEndData.withTraceScaleNoMissingBulkOfNormalizedComparison
      base common ccm24 normalizedSeed remainders rhExit bridges fixedData
      traceData comparison
  TraceScaleRouteFrontEndData.ofTraceData
    (Source.sourceObjectPackageOfNormalizedCC20Trace
      base common ccm24 normalizedSeed remainders rhExit bridges)
    (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
      base common ccm24 normalizedSeed remainders rhExit bridges fixedData)
    normalizedTraceData ledgers commonTuple signDefectClassification
    (TraceFrontEndData.normalized_comparison_trace_scale_replacement_owns_sign_defect
      base common ccm24 normalizedSeed remainders rhExit bridges fixedData
      traceData comparison ledgers signDefectClassification)
    restrictedToFullQWBridge sourceArchimedeanSignBridge

def route_certificate_of_normalized_comparison_replacement
    (base : Source.SourceObjectTheoremBasePackage)
    (common : Source.SourceObjectCommonData base)
    (ccm24 : Source.SourceObject.CCM24SemilocalObjectPackage)
    (normalizedSeed :
      Source.CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (remainders :
      Source.CC20Concrete.TraceScale.CC20TracePackageRemainderData
        normalizedSeed)
    (rhExit : Source.SourceObject.CC20RHExitObjectPackage)
    (bridges :
      Source.SourceObjectCrossObjectBridges base common
        (Source.SourceObjectExpandedRows.ofNormalizedCC20Trace
          ccm24 normalizedSeed remainders)
        rhExit)
    (fixedData :
      FixedSTestObligationData
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges))
    (traceData :
      TraceFrontEndData
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges)
        (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData))
    (comparison :
      TraceFrontEndData.NormalizedSupportSquareQWLambdaSourceComparison
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData)
    (ledgers : RouteLedgers)
    (commonTuple :
      SourceCommonTestTupleContract
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)
        traceData.lambda
        (Source.SourceObject.CommonTestObject.sourceConvolutionSquare
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges).commonTest)
        traceData.ccm25ArithmeticPackage)
    (signDefectClassification :
      SourceSignDefectClassification
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)
        traceData.lambda ledgers)
    (restrictedToFullQWBridge :
      RestrictedToFullQWBridgeContract
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)
        traceData.lambda
        (Source.SourceObject.CommonTestObject.sourceConvolutionSquare
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges).commonTest)
        ledgers traceData.ccm25ArithmeticPackage)
    (sourceArchimedeanSignBridge :
      SourceArchimedeanSignBridge
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges).cc20Trace.sourceTraceTest
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)) :
    RouteCertificate
      (RouteInputs.ofExpandedSourcePackage
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges)) :=
  let normalizedTraceData :=
    TraceFrontEndData.withTraceScaleNoMissingBulkOfNormalizedComparison
      base common ccm24 normalizedSeed remainders rhExit bridges fixedData
      traceData comparison
  route_certificate_of_trace_scale_data
    (Source.sourceObjectPackageOfNormalizedCC20Trace
      base common ccm24 normalizedSeed remainders rhExit bridges)
    (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
      base common ccm24 normalizedSeed remainders rhExit bridges fixedData)
    normalizedTraceData
    (trace_scale_route_front_end_of_normalized_comparison_replacement
      base common ccm24 normalizedSeed remainders rhExit bridges fixedData
      traceData comparison ledgers commonTuple signDefectClassification
      restrictedToFullQWBridge sourceArchimedeanSignBridge)

def trace_scale_route_front_end_of_normalized_comparison_contract_replacement
    (base : Source.SourceObjectTheoremBasePackage)
    (common : Source.SourceObjectCommonData base)
    (ccm24 : Source.SourceObject.CCM24SemilocalObjectPackage)
    (normalizedSeed :
      Source.CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (remainders :
      Source.CC20Concrete.TraceScale.CC20TracePackageRemainderData
        normalizedSeed)
    (rhExit : Source.SourceObject.CC20RHExitObjectPackage)
    (bridges :
      Source.SourceObjectCrossObjectBridges base common
        (Source.SourceObjectExpandedRows.ofNormalizedCC20Trace
          ccm24 normalizedSeed remainders)
        rhExit)
    (fixedData :
      FixedSTestObligationData
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges))
    (traceData :
      TraceFrontEndData
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges)
        (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData))
    (comparison :
      TraceFrontEndData.NormalizedSupportSquareQWLambdaSourceComparison
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData)
    (noExtraBulk :
      TraceFrontEndData.TraceScaleNoExtraBulkContract
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges)
        (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges fixedData)
        traceData.lambda traceData.ccm25ArithmeticPackage)
    (ledgers : RouteLedgers)
    (commonTuple :
      SourceCommonTestTupleContract
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)
        traceData.lambda
        (Source.SourceObject.CommonTestObject.sourceConvolutionSquare
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges).commonTest)
        traceData.ccm25ArithmeticPackage)
    (signDefectClassification :
      SourceSignDefectClassification
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)
        traceData.lambda ledgers)
    (restrictedToFullQWBridge :
      RestrictedToFullQWBridgeContract
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)
        traceData.lambda
        (Source.SourceObject.CommonTestObject.sourceConvolutionSquare
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges).commonTest)
        ledgers traceData.ccm25ArithmeticPackage)
    (sourceArchimedeanSignBridge :
      SourceArchimedeanSignBridge
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges).cc20Trace.sourceTraceTest
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)) :
    TraceScaleRouteFrontEndData
      (Source.sourceObjectPackageOfNormalizedCC20Trace
        base common ccm24 normalizedSeed remainders rhExit bridges)
      (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData)
      (TraceFrontEndData.withTraceScaleNoMissingBulkOfNormalizedComparisonFromContract
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData comparison noExtraBulk) := by
  let normalizedTraceData :=
    TraceFrontEndData.withTraceScaleNoMissingBulkOfNormalizedComparisonFromContract
      base common ccm24 normalizedSeed remainders rhExit bridges fixedData
      traceData comparison noExtraBulk
  exact
    TraceScaleRouteFrontEndData.ofTraceData
      (Source.sourceObjectPackageOfNormalizedCC20Trace
        base common ccm24 normalizedSeed remainders rhExit bridges)
      (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData)
      normalizedTraceData ledgers commonTuple signDefectClassification
      (TraceFrontEndData.normalized_comparison_trace_scale_contract_replacement_owns_sign_defect
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData comparison noExtraBulk ledgers signDefectClassification)
      restrictedToFullQWBridge sourceArchimedeanSignBridge

def route_certificate_of_normalized_comparison_contract_replacement
    (base : Source.SourceObjectTheoremBasePackage)
    (common : Source.SourceObjectCommonData base)
    (ccm24 : Source.SourceObject.CCM24SemilocalObjectPackage)
    (normalizedSeed :
      Source.CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (remainders :
      Source.CC20Concrete.TraceScale.CC20TracePackageRemainderData
        normalizedSeed)
    (rhExit : Source.SourceObject.CC20RHExitObjectPackage)
    (bridges :
      Source.SourceObjectCrossObjectBridges base common
        (Source.SourceObjectExpandedRows.ofNormalizedCC20Trace
          ccm24 normalizedSeed remainders)
        rhExit)
    (fixedData :
      FixedSTestObligationData
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges))
    (traceData :
      TraceFrontEndData
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges)
        (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData))
    (comparison :
      TraceFrontEndData.NormalizedSupportSquareQWLambdaSourceComparison
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData)
    (noExtraBulk :
      TraceFrontEndData.TraceScaleNoExtraBulkContract
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges)
        (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges fixedData)
        traceData.lambda traceData.ccm25ArithmeticPackage)
    (ledgers : RouteLedgers)
    (commonTuple :
      SourceCommonTestTupleContract
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)
        traceData.lambda
        (Source.SourceObject.CommonTestObject.sourceConvolutionSquare
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges).commonTest)
        traceData.ccm25ArithmeticPackage)
    (signDefectClassification :
      SourceSignDefectClassification
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)
        traceData.lambda ledgers)
    (restrictedToFullQWBridge :
      RestrictedToFullQWBridgeContract
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)
        traceData.lambda
        (Source.SourceObject.CommonTestObject.sourceConvolutionSquare
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges).commonTest)
        ledgers traceData.ccm25ArithmeticPackage)
    (sourceArchimedeanSignBridge :
      SourceArchimedeanSignBridge
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges).cc20Trace.sourceTraceTest
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)) :
    RouteCertificate
      (RouteInputs.ofExpandedSourcePackage
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges)) := by
  let normalizedTraceData :=
    TraceFrontEndData.withTraceScaleNoMissingBulkOfNormalizedComparisonFromContract
      base common ccm24 normalizedSeed remainders rhExit bridges fixedData
      traceData comparison noExtraBulk
  exact
    route_certificate_of_trace_scale_data
      (Source.sourceObjectPackageOfNormalizedCC20Trace
        base common ccm24 normalizedSeed remainders rhExit bridges)
      (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData)
      normalizedTraceData
      (trace_scale_route_front_end_of_normalized_comparison_contract_replacement
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData comparison noExtraBulk ledgers commonTuple
        signDefectClassification restrictedToFullQWBridge
        sourceArchimedeanSignBridge)

noncomputable def route_certificate_of_normalized_comparison_current_cutoff_binding
    (base : Source.SourceObjectTheoremBasePackage)
    (common : Source.SourceObjectCommonData base)
    (ccm24 : Source.SourceObject.CCM24SemilocalObjectPackage)
    (normalizedSeed :
      Source.CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (remainders :
      Source.CC20Concrete.TraceScale.CC20TracePackageRemainderData
        normalizedSeed)
    (rhExit : Source.SourceObject.CC20RHExitObjectPackage)
    (bridges :
      Source.SourceObjectCrossObjectBridges base common
        (Source.SourceObjectExpandedRows.ofNormalizedCC20Trace
          ccm24 normalizedSeed remainders)
        rhExit)
    (fixedData :
      FixedSTestObligationData
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges))
    (traceData :
      TraceFrontEndData
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges)
        (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData))
    (comparison :
      TraceFrontEndData.NormalizedSupportSquareQWLambdaSourceComparison
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData)
    (noExtraBulk :
      TraceFrontEndData.TraceScaleNoExtraBulkContract
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges)
        (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges fixedData)
        traceData.lambda traceData.ccm25ArithmeticPackage)
    (ledgers : RouteLedgers)
    (signDefectClassification :
      SourceSignDefectClassification
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)
        traceData.lambda ledgers)
    (currentCutoff :
      RestrictedToFullCurrentCutoffBinding
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)
        traceData.lambda
        (Source.SourceObject.CommonTestObject.sourceConvolutionSquare
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges).commonTest)
        ledgers traceData.ccm25ArithmeticPackage)
    (sourceArchimedeanSignBridge :
      SourceArchimedeanSignBridge
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges).cc20Trace.sourceTraceTest
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)) :
    RouteCertificate
      (RouteInputs.ofExpandedSourcePackage
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges)) :=
  route_certificate_of_normalized_comparison_contract_replacement
    base common ccm24 normalizedSeed remainders rhExit bridges fixedData
    traceData comparison noExtraBulk ledgers currentCutoff.commonTuple
    signDefectClassification
    (restricted_to_full_bridge_contract_of_current_cutoff_binding
      currentCutoff)
    sourceArchimedeanSignBridge

def route_certificate_of_normalized_comparison
    (base : Source.SourceObjectTheoremBasePackage)
    (common : Source.SourceObjectCommonData base)
    (ccm24 : Source.SourceObject.CCM24SemilocalObjectPackage)
    (normalizedSeed :
      Source.CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (remainders :
      Source.CC20Concrete.TraceScale.CC20TracePackageRemainderData
        normalizedSeed)
    (rhExit : Source.SourceObject.CC20RHExitObjectPackage)
    (bridges :
      Source.SourceObjectCrossObjectBridges base common
        (Source.SourceObjectExpandedRows.ofNormalizedCC20Trace
          ccm24 normalizedSeed remainders)
        rhExit)
    (fixedData :
      FixedSTestObligationData
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges))
    (traceData :
      TraceFrontEndData
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges)
        (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData))
    (comparison :
      TraceFrontEndData.NormalizedSupportSquareQWLambdaSourceComparison
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData)
    (ledgers : RouteLedgers)
    (commonTuple :
      SourceCommonTestTupleContract
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)
        traceData.lambda
        (Source.SourceObject.CommonTestObject.sourceConvolutionSquare
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges).commonTest)
        traceData.ccm25ArithmeticPackage)
    (signDefectClassification :
      SourceSignDefectClassification
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)
        traceData.lambda ledgers)
    (traceScaleMatchesComparison :
      traceData.traceScaleNoMissingBulk =
        TraceFrontEndData.traceScaleNoMissingBulkOfNormalizedPackageFromComparison
          base common ccm24 normalizedSeed remainders rhExit bridges fixedData
          traceData comparison
          (fun L _h =>
            SourceSignDefectClassification
              (RouteInputs.ofExpandedSourcePackage
                (Source.sourceObjectPackageOfNormalizedCC20Trace
                  base common ccm24 normalizedSeed remainders rhExit bridges))
              (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
                base common ccm24 normalizedSeed remainders rhExit bridges
                fixedData)
              traceData.lambda L)
          True trivial)
    (traceScaleOwnsSignDefectRemainder :
      (TraceFrontEndData.traceScaleNoMissingBulkOfNormalizedPackageFromComparison
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData comparison
        (fun L _h =>
          SourceSignDefectClassification
            (RouteInputs.ofExpandedSourcePackage
              (Source.sourceObjectPackageOfNormalizedCC20Trace
                base common ccm24 normalizedSeed remainders rhExit bridges))
            (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
              base common ccm24 normalizedSeed remainders rhExit bridges
              fixedData)
            traceData.lambda L)
        True trivial).rankPoleCdefOwnEveryRemainder
        ledgers signDefectClassification)
    (restrictedToFullQWBridge :
      RestrictedToFullQWBridgeContract
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)
        traceData.lambda
        (Source.SourceObject.CommonTestObject.sourceConvolutionSquare
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges).commonTest)
        ledgers traceData.ccm25ArithmeticPackage)
    (sourceArchimedeanSignBridge :
      SourceArchimedeanSignBridge
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges).cc20Trace.sourceTraceTest
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)) :
    RouteCertificate
      (RouteInputs.ofExpandedSourcePackage
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges)) :=
  route_certificate_of_trace_scale_data
    (Source.sourceObjectPackageOfNormalizedCC20Trace
      base common ccm24 normalizedSeed remainders rhExit bridges)
    (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
      base common ccm24 normalizedSeed remainders rhExit bridges fixedData)
    traceData
    (trace_scale_route_front_end_of_normalized_comparison
      base common ccm24 normalizedSeed remainders rhExit bridges fixedData
      traceData comparison ledgers commonTuple signDefectClassification
      traceScaleMatchesComparison traceScaleOwnsSignDefectRemainder
      restrictedToFullQWBridge sourceArchimedeanSignBridge)

def route_certificate_of_normalized_package_bridge
    (base : Source.SourceObjectTheoremBasePackage)
    (common : Source.SourceObjectCommonData base)
    (ccm24 : Source.SourceObject.CCM24SemilocalObjectPackage)
    (normalizedSeed :
      Source.CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (remainders :
      Source.CC20Concrete.TraceScale.CC20TracePackageRemainderData
        normalizedSeed)
    (rhExit : Source.SourceObject.CC20RHExitObjectPackage)
    (bridges :
      Source.SourceObjectCrossObjectBridges base common
        (Source.SourceObjectExpandedRows.ofNormalizedCC20Trace
          ccm24 normalizedSeed remainders)
        rhExit)
    (fixedData :
      FixedSTestObligationData
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges))
    (traceData :
      TraceFrontEndData
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges)
        (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData))
    (ledgers : RouteLedgers)
    (commonTuple :
      SourceCommonTestTupleContract
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)
        traceData.lambda
        (Source.SourceObject.CommonTestObject.sourceConvolutionSquare
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges).commonTest)
        traceData.ccm25ArithmeticPackage)
    (signDefectClassification :
      SourceSignDefectClassification
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)
        traceData.lambda ledgers)
    (traceScaleMatchesBridge :
      traceData.traceScaleNoMissingBulk =
        TraceFrontEndData.traceScaleNoMissingBulkOfNormalizedPackageFromComparison
          base common ccm24 normalizedSeed remainders rhExit bridges fixedData
          traceData
          (TraceFrontEndData.normalizedSupportSquareQWLambdaSourceComparisonOfPackageBridge
            base common ccm24 normalizedSeed remainders rhExit bridges fixedData
            traceData)
          (fun L _h =>
            SourceSignDefectClassification
              (RouteInputs.ofExpandedSourcePackage
                (Source.sourceObjectPackageOfNormalizedCC20Trace
                  base common ccm24 normalizedSeed remainders rhExit bridges))
              (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
                base common ccm24 normalizedSeed remainders rhExit bridges
                fixedData)
              traceData.lambda L)
          True trivial)
    (traceScaleOwnsSignDefectRemainder :
      (TraceFrontEndData.traceScaleNoMissingBulkOfNormalizedPackageFromComparison
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData
        (TraceFrontEndData.normalizedSupportSquareQWLambdaSourceComparisonOfPackageBridge
          base common ccm24 normalizedSeed remainders rhExit bridges fixedData
          traceData)
        (fun L _h =>
          SourceSignDefectClassification
            (RouteInputs.ofExpandedSourcePackage
              (Source.sourceObjectPackageOfNormalizedCC20Trace
                base common ccm24 normalizedSeed remainders rhExit bridges))
            (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
              base common ccm24 normalizedSeed remainders rhExit bridges
              fixedData)
            traceData.lambda L)
        True trivial).rankPoleCdefOwnEveryRemainder
        ledgers signDefectClassification)
    (restrictedToFullQWBridge :
      RestrictedToFullQWBridgeContract
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)
        traceData.lambda
        (Source.SourceObject.CommonTestObject.sourceConvolutionSquare
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges).commonTest)
        ledgers traceData.ccm25ArithmeticPackage)
    (sourceArchimedeanSignBridge :
      SourceArchimedeanSignBridge
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges).cc20Trace.sourceTraceTest
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)) :
    RouteCertificate
      (RouteInputs.ofExpandedSourcePackage
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges)) :=
  route_certificate_of_trace_scale_data
    (Source.sourceObjectPackageOfNormalizedCC20Trace
      base common ccm24 normalizedSeed remainders rhExit bridges)
    (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
      base common ccm24 normalizedSeed remainders rhExit bridges fixedData)
    traceData
    (trace_scale_route_front_end_of_normalized_package_bridge
      base common ccm24 normalizedSeed remainders rhExit bridges fixedData
      traceData ledgers commonTuple signDefectClassification
      traceScaleMatchesBridge traceScaleOwnsSignDefectRemainder
      restrictedToFullQWBridge sourceArchimedeanSignBridge)

theorem cc20_source_rh_of_route_certificate
    {inputs : RouteInputs} (cert : RouteCertificate inputs) :
    inputs.cc20.rhDefinitionBridge.SourceRH := by
  let exitInput : RouteBackedCC20ExitInputData inputs
      cert.sourceBackedTest cert.ledgers cert.bridge :=
    route_backed_cc20_exit_input_data_of_route_bridge_certificate
      cert.bridge
  exact Source.CC20Interface.finite_vanishing_source_rh_of_c1_input_data
    inputs.cc20
    exitInput.input
    exitInput.propositionC1InputData

theorem final_connes_weil_rh
    {inputs : RouteInputs} (cert : RouteCertificate inputs) :
    _root_.RiemannHypothesis := by
  let _ := restricted_to_full_qw_bridge_of_route_bridge_certificate cert.bridge
  let _ := final_sign_bridge_of_route_bridge_certificate cert.bridge
  exact Source.RHDefinitionBridge.source_rh_to_mathlib_rh
    inputs.cc20.rhDefinitionBridge
    (cc20_source_rh_of_route_certificate cert)

theorem final_rh_of_normalized_comparison
    (base : Source.SourceObjectTheoremBasePackage)
    (common : Source.SourceObjectCommonData base)
    (ccm24 : Source.SourceObject.CCM24SemilocalObjectPackage)
    (normalizedSeed :
      Source.CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (remainders :
      Source.CC20Concrete.TraceScale.CC20TracePackageRemainderData
        normalizedSeed)
    (rhExit : Source.SourceObject.CC20RHExitObjectPackage)
    (bridges :
      Source.SourceObjectCrossObjectBridges base common
        (Source.SourceObjectExpandedRows.ofNormalizedCC20Trace
          ccm24 normalizedSeed remainders)
        rhExit)
    (fixedData :
      FixedSTestObligationData
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges))
    (traceData :
      TraceFrontEndData
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges)
        (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData))
    (comparison :
      TraceFrontEndData.NormalizedSupportSquareQWLambdaSourceComparison
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData)
    (ledgers : RouteLedgers)
    (commonTuple :
      SourceCommonTestTupleContract
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)
        traceData.lambda
        (Source.SourceObject.CommonTestObject.sourceConvolutionSquare
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges).commonTest)
        traceData.ccm25ArithmeticPackage)
    (signDefectClassification :
      SourceSignDefectClassification
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)
        traceData.lambda ledgers)
    (traceScaleMatchesComparison :
      traceData.traceScaleNoMissingBulk =
        TraceFrontEndData.traceScaleNoMissingBulkOfNormalizedPackageFromComparison
          base common ccm24 normalizedSeed remainders rhExit bridges fixedData
          traceData comparison
          (fun L _h =>
            SourceSignDefectClassification
              (RouteInputs.ofExpandedSourcePackage
                (Source.sourceObjectPackageOfNormalizedCC20Trace
                  base common ccm24 normalizedSeed remainders rhExit bridges))
              (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
                base common ccm24 normalizedSeed remainders rhExit bridges
                fixedData)
              traceData.lambda L)
          True trivial)
    (traceScaleOwnsSignDefectRemainder :
      (TraceFrontEndData.traceScaleNoMissingBulkOfNormalizedPackageFromComparison
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData comparison
        (fun L _h =>
          SourceSignDefectClassification
            (RouteInputs.ofExpandedSourcePackage
              (Source.sourceObjectPackageOfNormalizedCC20Trace
                base common ccm24 normalizedSeed remainders rhExit bridges))
            (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
              base common ccm24 normalizedSeed remainders rhExit bridges
              fixedData)
            traceData.lambda L)
        True trivial).rankPoleCdefOwnEveryRemainder
        ledgers signDefectClassification)
    (restrictedToFullQWBridge :
      RestrictedToFullQWBridgeContract
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)
        traceData.lambda
        (Source.SourceObject.CommonTestObject.sourceConvolutionSquare
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges).commonTest)
        ledgers traceData.ccm25ArithmeticPackage)
    (sourceArchimedeanSignBridge :
      SourceArchimedeanSignBridge
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges).cc20Trace.sourceTraceTest
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)) :
    _root_.RiemannHypothesis := by
  exact
    final_connes_weil_rh
      (route_certificate_of_normalized_comparison
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData comparison ledgers commonTuple signDefectClassification
        traceScaleMatchesComparison traceScaleOwnsSignDefectRemainder
        restrictedToFullQWBridge sourceArchimedeanSignBridge)

theorem final_rh_of_normalized_package_bridge
    (base : Source.SourceObjectTheoremBasePackage)
    (common : Source.SourceObjectCommonData base)
    (ccm24 : Source.SourceObject.CCM24SemilocalObjectPackage)
    (normalizedSeed :
      Source.CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (remainders :
      Source.CC20Concrete.TraceScale.CC20TracePackageRemainderData
        normalizedSeed)
    (rhExit : Source.SourceObject.CC20RHExitObjectPackage)
    (bridges :
      Source.SourceObjectCrossObjectBridges base common
        (Source.SourceObjectExpandedRows.ofNormalizedCC20Trace
          ccm24 normalizedSeed remainders)
        rhExit)
    (fixedData :
      FixedSTestObligationData
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges))
    (traceData :
      TraceFrontEndData
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges)
        (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData))
    (ledgers : RouteLedgers)
    (commonTuple :
      SourceCommonTestTupleContract
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)
        traceData.lambda
        (Source.SourceObject.CommonTestObject.sourceConvolutionSquare
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges).commonTest)
        traceData.ccm25ArithmeticPackage)
    (signDefectClassification :
      SourceSignDefectClassification
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)
        traceData.lambda ledgers)
    (traceScaleMatchesBridge :
      traceData.traceScaleNoMissingBulk =
        TraceFrontEndData.traceScaleNoMissingBulkOfNormalizedPackageFromComparison
          base common ccm24 normalizedSeed remainders rhExit bridges fixedData
          traceData
          (TraceFrontEndData.normalizedSupportSquareQWLambdaSourceComparisonOfPackageBridge
            base common ccm24 normalizedSeed remainders rhExit bridges fixedData
            traceData)
          (fun L _h =>
            SourceSignDefectClassification
              (RouteInputs.ofExpandedSourcePackage
                (Source.sourceObjectPackageOfNormalizedCC20Trace
                  base common ccm24 normalizedSeed remainders rhExit bridges))
              (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
                base common ccm24 normalizedSeed remainders rhExit bridges
                fixedData)
              traceData.lambda L)
          True trivial)
    (traceScaleOwnsSignDefectRemainder :
      (TraceFrontEndData.traceScaleNoMissingBulkOfNormalizedPackageFromComparison
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData
        (TraceFrontEndData.normalizedSupportSquareQWLambdaSourceComparisonOfPackageBridge
          base common ccm24 normalizedSeed remainders rhExit bridges fixedData
          traceData)
        (fun L _h =>
          SourceSignDefectClassification
            (RouteInputs.ofExpandedSourcePackage
              (Source.sourceObjectPackageOfNormalizedCC20Trace
                base common ccm24 normalizedSeed remainders rhExit bridges))
            (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
              base common ccm24 normalizedSeed remainders rhExit bridges
              fixedData)
            traceData.lambda L)
        True trivial).rankPoleCdefOwnEveryRemainder
        ledgers signDefectClassification)
    (restrictedToFullQWBridge :
      RestrictedToFullQWBridgeContract
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)
        traceData.lambda
        (Source.SourceObject.CommonTestObject.sourceConvolutionSquare
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges).commonTest)
        ledgers traceData.ccm25ArithmeticPackage)
    (sourceArchimedeanSignBridge :
      SourceArchimedeanSignBridge
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges).cc20Trace.sourceTraceTest
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)) :
    _root_.RiemannHypothesis := by
  exact
    final_connes_weil_rh
      (route_certificate_of_normalized_package_bridge
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData ledgers commonTuple signDefectClassification
        traceScaleMatchesBridge traceScaleOwnsSignDefectRemainder
        restrictedToFullQWBridge sourceArchimedeanSignBridge)

theorem final_rh_of_normalized_comparison_replacement
    (base : Source.SourceObjectTheoremBasePackage)
    (common : Source.SourceObjectCommonData base)
    (ccm24 : Source.SourceObject.CCM24SemilocalObjectPackage)
    (normalizedSeed :
      Source.CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (remainders :
      Source.CC20Concrete.TraceScale.CC20TracePackageRemainderData
        normalizedSeed)
    (rhExit : Source.SourceObject.CC20RHExitObjectPackage)
    (bridges :
      Source.SourceObjectCrossObjectBridges base common
        (Source.SourceObjectExpandedRows.ofNormalizedCC20Trace
          ccm24 normalizedSeed remainders)
        rhExit)
    (fixedData :
      FixedSTestObligationData
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges))
    (traceData :
      TraceFrontEndData
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges)
        (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData))
    (comparison :
      TraceFrontEndData.NormalizedSupportSquareQWLambdaSourceComparison
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData)
    (ledgers : RouteLedgers)
    (commonTuple :
      SourceCommonTestTupleContract
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)
        traceData.lambda
        (Source.SourceObject.CommonTestObject.sourceConvolutionSquare
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges).commonTest)
        traceData.ccm25ArithmeticPackage)
    (signDefectClassification :
      SourceSignDefectClassification
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)
        traceData.lambda ledgers)
    (restrictedToFullQWBridge :
      RestrictedToFullQWBridgeContract
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)
        traceData.lambda
        (Source.SourceObject.CommonTestObject.sourceConvolutionSquare
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges).commonTest)
        ledgers traceData.ccm25ArithmeticPackage)
    (sourceArchimedeanSignBridge :
      SourceArchimedeanSignBridge
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges).cc20Trace.sourceTraceTest
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)) :
    _root_.RiemannHypothesis := by
  exact
    final_connes_weil_rh
      (route_certificate_of_normalized_comparison_replacement
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData comparison ledgers commonTuple signDefectClassification
        restrictedToFullQWBridge sourceArchimedeanSignBridge)

theorem final_rh_of_normalized_comparison_contract_replacement
    (base : Source.SourceObjectTheoremBasePackage)
    (common : Source.SourceObjectCommonData base)
    (ccm24 : Source.SourceObject.CCM24SemilocalObjectPackage)
    (normalizedSeed :
      Source.CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (remainders :
      Source.CC20Concrete.TraceScale.CC20TracePackageRemainderData
        normalizedSeed)
    (rhExit : Source.SourceObject.CC20RHExitObjectPackage)
    (bridges :
      Source.SourceObjectCrossObjectBridges base common
        (Source.SourceObjectExpandedRows.ofNormalizedCC20Trace
          ccm24 normalizedSeed remainders)
        rhExit)
    (fixedData :
      FixedSTestObligationData
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges))
    (traceData :
      TraceFrontEndData
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges)
        (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData))
    (comparison :
      TraceFrontEndData.NormalizedSupportSquareQWLambdaSourceComparison
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData)
    (noExtraBulk :
      TraceFrontEndData.TraceScaleNoExtraBulkContract
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges)
        (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges fixedData)
        traceData.lambda traceData.ccm25ArithmeticPackage)
    (ledgers : RouteLedgers)
    (commonTuple :
      SourceCommonTestTupleContract
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)
        traceData.lambda
        (Source.SourceObject.CommonTestObject.sourceConvolutionSquare
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges).commonTest)
        traceData.ccm25ArithmeticPackage)
    (signDefectClassification :
      SourceSignDefectClassification
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)
        traceData.lambda ledgers)
    (restrictedToFullQWBridge :
      RestrictedToFullQWBridgeContract
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)
        traceData.lambda
        (Source.SourceObject.CommonTestObject.sourceConvolutionSquare
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges).commonTest)
        ledgers traceData.ccm25ArithmeticPackage)
    (sourceArchimedeanSignBridge :
      SourceArchimedeanSignBridge
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges).cc20Trace.sourceTraceTest
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)) :
    _root_.RiemannHypothesis := by
  exact
    final_connes_weil_rh
      (route_certificate_of_normalized_comparison_contract_replacement
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData comparison noExtraBulk ledgers commonTuple
        signDefectClassification restrictedToFullQWBridge
        sourceArchimedeanSignBridge)

theorem final_rh_of_normalized_comparison_current_cutoff_binding
    (base : Source.SourceObjectTheoremBasePackage)
    (common : Source.SourceObjectCommonData base)
    (ccm24 : Source.SourceObject.CCM24SemilocalObjectPackage)
    (normalizedSeed :
      Source.CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (remainders :
      Source.CC20Concrete.TraceScale.CC20TracePackageRemainderData
        normalizedSeed)
    (rhExit : Source.SourceObject.CC20RHExitObjectPackage)
    (bridges :
      Source.SourceObjectCrossObjectBridges base common
        (Source.SourceObjectExpandedRows.ofNormalizedCC20Trace
          ccm24 normalizedSeed remainders)
        rhExit)
    (fixedData :
      FixedSTestObligationData
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges))
    (traceData :
      TraceFrontEndData
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges)
        (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData))
    (comparison :
      TraceFrontEndData.NormalizedSupportSquareQWLambdaSourceComparison
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData)
    (noExtraBulk :
      TraceFrontEndData.TraceScaleNoExtraBulkContract
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges)
        (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges fixedData)
        traceData.lambda traceData.ccm25ArithmeticPackage)
    (ledgers : RouteLedgers)
    (signDefectClassification :
      SourceSignDefectClassification
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)
        traceData.lambda ledgers)
    (currentCutoff :
      RestrictedToFullCurrentCutoffBinding
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)
        traceData.lambda
        (Source.SourceObject.CommonTestObject.sourceConvolutionSquare
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges).commonTest)
        ledgers traceData.ccm25ArithmeticPackage)
    (sourceArchimedeanSignBridge :
      SourceArchimedeanSignBridge
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges).cc20Trace.sourceTraceTest
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)) :
    _root_.RiemannHypothesis := by
  exact
    final_connes_weil_rh
      (route_certificate_of_normalized_comparison_current_cutoff_binding
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData comparison noExtraBulk ledgers signDefectClassification
        currentCutoff sourceArchimedeanSignBridge)

theorem route_certificate_of_trace_scale_data_ledgers
    (pkg : Source.SourceObject.SourceObjectPackage)
    (fixedFront : ExpandedSourceFixedSTestFrontEnd pkg)
    (traceData : TraceFrontEndData pkg fixedFront)
    (routeData : TraceScaleRouteFrontEndData pkg fixedFront traceData) :
    (route_certificate_of_trace_scale_data pkg fixedFront traceData routeData).ledgers =
      routeData.ledgers :=
  rfl

theorem route_certificate_of_trace_scale_data_source_backed_test
    (pkg : Source.SourceObject.SourceObjectPackage)
    (fixedFront : ExpandedSourceFixedSTestFrontEnd pkg)
    (traceData : TraceFrontEndData pkg fixedFront)
    (routeData : TraceScaleRouteFrontEndData pkg fixedFront traceData) :
    (route_certificate_of_trace_scale_data
      pkg fixedFront traceData routeData).sourceBackedTest =
      SourceBackedFixedSTest.ofExpandedSourcePackage pkg fixedFront :=
  rfl

def route_front_end_of_package_data
    (base : Source.SourceObjectTheoremBasePackage)
    (common : Source.SourceObjectCommonData base)
    (rows : Source.SourceObjectExpandedRows base common)
    (rhExit : Source.SourceObject.CC20RHExitObjectPackage)
    (bridges : Source.SourceObjectCrossObjectBridges base common rows rhExit)
    (fixedData :
      FixedSTestObligationData
        (Source.sourceObjectPackageOfData base common rows rhExit bridges))
    (traceData :
      TraceFrontEndData
        (Source.sourceObjectPackageOfData base common rows rhExit bridges)
        (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfPackageData
          base common rows rhExit bridges fixedData))
    (routeData :
      TraceScaleRouteFrontEndData
        (Source.sourceObjectPackageOfData base common rows rhExit bridges)
        (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfPackageData
          base common rows rhExit bridges fixedData)
        traceData) :
    ExpandedSourceRouteCertificateFrontEnd
      (Source.sourceObjectPackageOfData base common rows rhExit bridges)
      (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfPackageData
        base common rows rhExit bridges fixedData)
      (TraceFrontEndData.toExpandedSourceTraceReadOffFrontEndOfPackageData
        base common rows rhExit bridges fixedData traceData) :=
  route_front_end_of_trace_scale_data
    (Source.sourceObjectPackageOfData base common rows rhExit bridges)
    (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfPackageData
      base common rows rhExit bridges fixedData)
    traceData routeData

def route_certificate_of_package_data
    (base : Source.SourceObjectTheoremBasePackage)
    (common : Source.SourceObjectCommonData base)
    (rows : Source.SourceObjectExpandedRows base common)
    (rhExit : Source.SourceObject.CC20RHExitObjectPackage)
    (bridges : Source.SourceObjectCrossObjectBridges base common rows rhExit)
    (fixedData :
      FixedSTestObligationData
        (Source.sourceObjectPackageOfData base common rows rhExit bridges))
    (traceData :
      TraceFrontEndData
        (Source.sourceObjectPackageOfData base common rows rhExit bridges)
        (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfPackageData
          base common rows rhExit bridges fixedData))
    (routeData :
      TraceScaleRouteFrontEndData
        (Source.sourceObjectPackageOfData base common rows rhExit bridges)
        (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfPackageData
          base common rows rhExit bridges fixedData)
        traceData) :
    RouteCertificate
      (RouteInputs.ofExpandedSourcePackage
        (Source.sourceObjectPackageOfData base common rows rhExit bridges)) :=
  route_certificate_of_trace_scale_data
    (Source.sourceObjectPackageOfData base common rows rhExit bridges)
    (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfPackageData
      base common rows rhExit bridges fixedData)
    traceData routeData

theorem route_certificate_ledgers_of_expanded_source_package
    (pkg : Source.SourceObject.SourceObjectPackage)
    (fixedFront : ExpandedSourceFixedSTestFrontEnd pkg)
    (traceFront : ExpandedSourceTraceReadOffFrontEnd pkg fixedFront)
    (routeFront :
      ExpandedSourceRouteCertificateFrontEnd pkg fixedFront traceFront) :
    (route_certificate_of_expanded_source_package
      pkg fixedFront traceFront routeFront).ledgers =
      routeFront.ledgers := by
  rfl

theorem route_certificate_source_trace_lambda_of_expanded_source_package
    (pkg : Source.SourceObject.SourceObjectPackage)
    (fixedFront : ExpandedSourceFixedSTestFrontEnd pkg)
    (traceFront : ExpandedSourceTraceReadOffFrontEnd pkg fixedFront)
    (routeFront :
      ExpandedSourceRouteCertificateFrontEnd pkg fixedFront traceFront) :
    (route_certificate_of_expanded_source_package
      pkg fixedFront traceFront routeFront).bridge.sourceTraceReadOff.lambda =
      traceFront.lambda := by
  rfl

end Route
end ConnesWeilRH
