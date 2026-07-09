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
  exact scoped_archimedean_contribution_equality_of_qw_lambda_restriction
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
  exact scoped_archimedean_contribution_equality_of_qw_lambda_restriction
    hrestriction

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
    Source.CCM25Concrete.Package.qw_lambda_eq_qw_of_scoped_archimedean_contribution
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
        ledgers traceData.ccm25ArithmeticPackage) :
    TraceScaleRouteFrontEndData pkg fixedFront traceData where
  ledgers := ledgers
  traceScaleNoMissingBulk := traceData.traceScaleNoMissingBulk
  traceScaleMatchesTraceData := rfl
  commonTuple := commonTuple
  signDefectClassification := signDefectClassification
  traceScaleOwnsSignDefectRemainder := traceScaleOwnsSignDefectRemainder
  restrictedToFullQWBridge := restrictedToFullQWBridge

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
        ledgers traceData.ccm25ArithmeticPackage) :
    (ofTraceData pkg fixedFront traceData ledgers commonTuple
      signDefectClassification traceScaleOwnsSignDefectRemainder
      restrictedToFullQWBridge).traceScaleNoMissingBulk =
      traceData.traceScaleNoMissingBulk :=
  rfl

theorem route_front_no_extra_bulk
    (pkg : Source.SourceObject.SourceObjectPackage)
    (fixedFront : ExpandedSourceFixedSTestFrontEnd pkg)
    (traceData : TraceFrontEndData pkg fixedFront)
    (routeData : TraceScaleRouteFrontEndData pkg fixedFront traceData) :
    routeData.traceScaleNoMissingBulk.noExtraBulkScaleTerm :=
  routeData.traceScaleNoMissingBulk.noExtraBulkScaleTermHolds

theorem route_front_trace_scale_source_term_statement
    (pkg : Source.SourceObject.SourceObjectPackage)
    (fixedFront : ExpandedSourceFixedSTestFrontEnd pkg)
    (traceData : TraceFrontEndData pkg fixedFront)
    (routeData : TraceScaleRouteFrontEndData pkg fixedFront traceData) :
    TraceFrontEndData.TraceScaleNoExtraBulkSourceTermStatement
      (TraceFrontEndData.no_extra_bulk_source_term_data_of_trace_scale_no_missing_bulk
        routeData.traceScaleNoMissingBulk) :=
  TraceFrontEndData.trace_scale_no_missing_bulk_source_term_statement_holds
    routeData.traceScaleNoMissingBulk

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

structure NormalizedRestrictedToFullAsymptoticRowsProvider
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
          fixedData)) where
  rows :
    RestrictedToFullAsymptoticRows
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

structure NormalizedRestrictedToFullArchimedeanBalanceRowsProvider
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
          fixedData)) where
  archimedeanBalanceRowsAtLarge :
    ∀ lambda : ℝ,
      traceData.lambda ≤ lambda →
        ∀ pkg :
          Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
            (RouteInputs.ofExpandedSourcePackage
              (Source.sourceObjectPackageOfNormalizedCC20Trace
                base common ccm24 normalizedSeed remainders rhExit bridges)).ccm25.weilSymbols
            (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
              base common ccm24 normalizedSeed remainders rhExit bridges
              fixedData).weilTest
            lambda,
          SourceCommonTestTupleContract
            (RouteInputs.ofExpandedSourcePackage
              (Source.sourceObjectPackageOfNormalizedCC20Trace
                base common ccm24 normalizedSeed remainders rhExit bridges))
            (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
              base common ccm24 normalizedSeed remainders rhExit bridges
              fixedData)
            lambda
            (Source.SourceObject.CommonTestObject.sourceConvolutionSquare
              (Source.sourceObjectPackageOfNormalizedCC20Trace
                base common ccm24 normalizedSeed remainders rhExit bridges).commonTest)
            pkg →
            SourceArchimedeanContributionBalanceRows
              (RouteInputs.ofExpandedSourcePackage
                (Source.sourceObjectPackageOfNormalizedCC20Trace
                  base common ccm24 normalizedSeed remainders rhExit bridges))
              (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
                base common ccm24 normalizedSeed remainders rhExit bridges
                fixedData)
              lambda
              pkg

noncomputable def normalized_restricted_to_full_asymptotic_rows_of_archimedean_balance
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
    (provider :
      NormalizedRestrictedToFullArchimedeanBalanceRowsProvider
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData) :
    NormalizedRestrictedToFullAsymptoticRowsProvider
      base common ccm24 normalizedSeed remainders rhExit bridges fixedData
      traceData where
  rows :=
    { supportThresholdAtLarge := by
        intro lambda habove
        exact
          fixed_test_support_threshold_at_large_of_source_backed
            (lt_of_lt_of_le traceData.oneLtLambda habove)
      primePowerAtomStabilizationAtLarge :=
        by
          intro lambda _habove pkg hcommon
          exact prime_power_atom_stabilization_of_common_tuple hcommon
      archimedeanContributionAtLarge :=
        by
          intro lambda habove pkg hcommon
          exact
            source_archimedean_contribution_matches_of_balance_rows
              (provider.archimedeanBalanceRowsAtLarge lambda habove pkg hcommon) }

noncomputable def normalized_restricted_to_full_threshold_of_asymptotic_rows
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
    (provider :
      NormalizedRestrictedToFullAsymptoticRowsProvider
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData) :
    RestrictedToFullQWLargeLambdaThreshold
      (RouteInputs.ofExpandedSourcePackage
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges))
      (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
        base common ccm24 normalizedSeed remainders rhExit bridges
        fixedData)
      (Source.SourceObject.CommonTestObject.sourceConvolutionSquare
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges).commonTest) :=
  restricted_to_full_large_lambda_threshold_of_asymptotic_rows
    traceData.oneLtLambda
    traceData.ccm25ArithmeticPackage
    (source_common_test_tuple_contract_of_package
      (fixed_test_support_cutoff_data_of_source_backed
        (g := FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)
        traceData.oneLtLambda).windowLambdaCompatibility
      (expanded_source_package_convolution_square_read_off
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges)
        (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)))
    provider.rows

noncomputable def normalized_restricted_to_full_current_cutoff_binding_of_asymptotic_rows
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
    (provider :
      NormalizedRestrictedToFullAsymptoticRowsProvider
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData)
    (mellinHalfDensityConvention :
      (Source.cc20MellinHalfDensityConvention
        (Source.CC20Interface.archimedeanSymbols
          (RouteInputs.ofExpandedSourcePackage
            (Source.sourceObjectPackageOfNormalizedCC20Trace
              base common ccm24 normalizedSeed remainders rhExit bridges)).cc20)).Holds)
    (supportInWindow :
      SemilocalModelSymbols.supportInWindow
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges)).ccm24
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData).semilocalTest
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData).window)
    (fourierSupportInWindow :
      SemilocalModelSymbols.fourierSupportInWindow
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges)).ccm24
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData).semilocalTest
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData).window)
    (convolutionSupportTransported :
      SemilocalModelSymbols.convolutionSupportTransported
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges)).ccm24
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData).semilocalTest
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData).window)
    (windowContainedInLambda :
      SemilocalModelSymbols.windowContainedInLambda
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges)).ccm24
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData).window traceData.lambda)
    (lambdaCompatible :
      SemilocalModelSymbols.lambdaCompatible
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges)).ccm24
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData).window traceData.lambda)
    (boundedComparisonMap :
      SemilocalModelSymbols.boundedComparisonMap
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges)).ccm24
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData).placeSet)
    (boundedComparisonInverse :
      SemilocalModelSymbols.boundedComparisonInverse
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges)).ccm24
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData).placeSet)
    (fixedWindowExhaustionCompatible :
      SemilocalModelSymbols.fixedWindowExhaustionCompatible
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges)).ccm24
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData).window)
    (rankKilled : ledgers.rankKilled)
    (poleKilled : ledgers.poleKilled)
    (cdefExhausts : ledgers.cdefExhausts) :
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
      ledgers traceData.ccm25ArithmeticPackage :=
  let windowSupportContainment :
      WindowSupportContainment
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)
        traceData.lambda :=
    ⟨supportInWindow, fourierSupportInWindow,
      convolutionSupportTransported, windowContainedInLambda⟩
  let postQSeriesTailBoundedComparison :
      PostQSeriesTailBoundedComparison
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)
        traceData.lambda :=
    ⟨boundedComparisonMap, boundedComparisonInverse⟩
  let sourceRemainderNoStripProjectionSplit :
      SourceRemainderNoStripProjectionSplit
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)
        traceData.lambda :=
    ⟨⟨mellinHalfDensityConvention,
        ⟨windowSupportContainment, lambdaCompatible⟩,
        postQSeriesTailBoundedComparison⟩,
      lambdaCompatible⟩
  let row4EndpointStripInput :
      SourceProjectionOrderEndpointStripNormalForm
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)
        traceData.lambda :=
    ⟨sourceRemainderNoStripProjectionSplit,
      fixedWindowExhaustionCompatible⟩
  let rankLedgerIdentification :
      SourceRankLedgerIdentification
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)
        traceData.lambda ledgers :=
    ⟨sourceRemainderNoStripProjectionSplit, rankKilled⟩
  let poleLedgerIdentification :
      SourcePoleLedgerIdentification
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)
        traceData.lambda ledgers :=
    ⟨sourceRemainderNoStripProjectionSplit, poleKilled⟩
  let noExtraNoStripChannel :
      SourceNoExtraNoStripChannel
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)
        traceData.lambda :=
    ⟨sourceRemainderNoStripProjectionSplit, row4EndpointStripInput⟩
  restricted_to_full_current_cutoff_binding_of_common_tuple
    (normalized_restricted_to_full_threshold_of_asymptotic_rows
      base common ccm24 normalizedSeed remainders rhExit bridges fixedData
      traceData provider)
    le_rfl
    (source_common_test_tuple_contract_of_package
      { oneLtLambda := traceData.oneLtLambda
        windowSupportContainment := windowSupportContainment
        lambdaCompatible := lambdaCompatible }
      (expanded_source_package_convolution_square_read_off
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges)
        (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)))
    (source_endpoint_strip_remainder_cdef_domination_of_parts
      row4EndpointStripInput windowSupportContainment
      postQSeriesTailBoundedComparison
      ⟨rankLedgerIdentification, poleLedgerIdentification,
        noExtraNoStripChannel⟩
      cdefExhausts)

noncomputable def
    normalized_restricted_to_full_current_cutoff_binding_of_source_backed_asymptotic_rows
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
    (provider :
      NormalizedRestrictedToFullAsymptoticRowsProvider
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData)
    (rankKilled : ledgers.rankKilled)
    (poleKilled : ledgers.poleKilled)
    (cdefExhausts : ledgers.cdefExhausts) :
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
      ledgers traceData.ccm25ArithmeticPackage :=
  let pkg :=
    Source.sourceObjectPackageOfNormalizedCC20Trace
      base common ccm24 normalizedSeed remainders rhExit bridges
  let inputs := RouteInputs.ofExpandedSourcePackage pkg
  let g :=
    FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
      base common ccm24 normalizedSeed remainders rhExit bridges fixedData
  let hWindow :=
    window_support_containment_of_source_backed g traceData.oneLtLambda
  let hBounded :=
    bounded_comparison_of_source_backed g
  normalized_restricted_to_full_current_cutoff_binding_of_asymptotic_rows
    base common ccm24 normalizedSeed remainders rhExit bridges fixedData
    traceData ledgers provider
    inputs.cc20.mellinHalfDensityConvention
    hWindow.1
    hWindow.2.1
    hWindow.2.2.1
    hWindow.2.2.2
    (lambda_compatible_of_source_backed g traceData.oneLtLambda)
    hBounded.1
    hBounded.2
    (sonin_exhaustion_of_source_backed g)
    rankKilled poleKilled cdefExhausts

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
    (RouteInputs.ofExpandedSourcePackage pkg).ccm24.supportInWindow
      pkg.ccm24.semilocalSymbols.sourceTest pkg.ccm24.sourceSupportWindow :=
  Source.SourceObject.SourceObjectPackage.ccm24_common_support_window pkg

theorem expanded_source_ccm24_common_convolution_support
    (pkg : Source.SourceObject.SourceObjectPackage) :
    (RouteInputs.ofExpandedSourcePackage pkg).ccm24.convolutionSupportTransported
      pkg.ccm24.semilocalSymbols.sourceTest pkg.ccm24.sourceSupportWindow :=
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

noncomputable def expanded_source_route_final_sign_nonpositive
    (pkg : Source.SourceObject.SourceObjectPackage)
    (fixedFront : ExpandedSourceFixedSTestFrontEnd pkg)
    (traceFront : ExpandedSourceTraceReadOffFrontEnd pkg fixedFront)
    (routeFront :
      ExpandedSourceRouteCertificateFrontEnd pkg fixedFront traceFront) :
    SourceQWNonnegativeToCC20Nonpositive
      (RouteInputs.ofExpandedSourcePackage pkg)
      pkg.cc20Trace.sourceTraceTest
      (SourceBackedFixedSTest.ofExpandedSourcePackage pkg fixedFront)
      traceFront.lambda
      ((RouteInputs.ofExpandedSourcePackage pkg).ccm25.weilSymbols.convolutionStar
        (SourceBackedFixedSTest.ofExpandedSourcePackage pkg fixedFront).weilTest
        (SourceBackedFixedSTest.ofExpandedSourcePackage pkg fixedFront).weilTest)
      traceFront.ccm25ArithmeticPackage :=
  by
    let sourceTrace :=
      SourceTraceReadOffData.ofExpandedSourcePackage pkg fixedFront traceFront
    let commonTuple :=
      expanded_source_route_common_tuple_on_route_square
        pkg fixedFront traceFront routeFront
    exact source_qw_nonnegative_to_cc20_nonpositive_of_common_test_parts
      commonTuple.windowLambdaCompatibility
      commonTuple.packageReadOff
      commonTuple.squareCompatibility
      sourceTrace.hilbertSchmidtGate
      (RouteInputs.ofExpandedSourcePackage pkg).cc20.signsAndNormalizations
      (RouteInputs.ofExpandedSourcePackage pkg).cc20.mellinHalfDensityConvention

noncomputable def route_backed_cc20_nonpositivity_input_data_of_route_bridge_certificate
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {L : RouteLedgers}
    (bridge : RouteBridgeCertificate inputs g L) :
    RouteBackedCC20NonpositivityInputData inputs g L bridge
      (toWeilPositivityInput inputs g L) where
  inputIsRouteInput := rfl
  sourceBackedFullPositivity :=
    source_backed_full_positivity_of_route_bridge_certificate bridge
  finalSignNonpositive :=
    final_sign_nonpositive_of_route_bridge_certificate bridge
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
  sourceTripleVanishing := g.tripleVanishingRouteRows.sourceTripleVanishing
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

structure RouteFinalExitPackage
    (inputs : RouteInputs) where
  certificate : RouteCertificate inputs
  exitInput :
    RouteBackedCC20ExitInputData inputs
      certificate.sourceBackedTest certificate.ledgers certificate.bridge
  sourceRH : inputs.cc20.rhDefinitionBridge.SourceRH
  sourceRHMatchesC1 :
    sourceRH =
      inputs.cc20.cc20RHExitObjectPackage.propositionC1SourceCriterion
        exitInput.input exitInput.propositionC1InputData

noncomputable def route_final_exit_package_of_certificate
    {inputs : RouteInputs} (cert : RouteCertificate inputs) :
    RouteFinalExitPackage inputs where
  certificate := cert
  exitInput :=
    route_backed_cc20_exit_input_data_of_route_bridge_certificate
      cert.bridge
  sourceRH :=
    inputs.cc20.cc20RHExitObjectPackage.propositionC1SourceCriterion
        (route_backed_cc20_exit_input_data_of_route_bridge_certificate
          cert.bridge).input
        (route_backed_cc20_exit_input_data_of_route_bridge_certificate
            cert.bridge).propositionC1InputData
  sourceRHMatchesC1 := rfl

noncomputable def route_final_exit_package_of_route_bridge_certificate
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {L : RouteLedgers}
    (bridge : RouteBridgeCertificate inputs g L) :
    RouteFinalExitPackage inputs :=
  route_final_exit_package_of_certificate
    { sourceBackedTest := g
      ledgers := L
      bridge := bridge }

def cc20_source_rh_of_route_final_exit_package
    {inputs : RouteInputs} (h : RouteFinalExitPackage inputs) :
    inputs.cc20.rhDefinitionBridge.SourceRH :=
  h.sourceRH

def mathlib_rh_of_route_final_exit_package
    {inputs : RouteInputs} (h : RouteFinalExitPackage inputs) :
    _root_.RiemannHypothesis :=
  Source.RHDefinitionBridge.source_rh_to_mathlib_rh
    inputs.cc20.rhDefinitionBridge
    (cc20_source_rh_of_route_final_exit_package h)

theorem route_final_exit_mathlib_rh_uses_source_bridge
    {inputs : RouteInputs} (h : RouteFinalExitPackage inputs) :
    mathlib_rh_of_route_final_exit_package h =
      Source.RHDefinitionBridge.source_rh_to_mathlib_rh
        inputs.cc20.rhDefinitionBridge
        (cc20_source_rh_of_route_final_exit_package h) :=
  rfl

def route_certificate_of_sign_defect_classification
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {L : RouteLedgers}
    (sourceTraceReadOff : SourceRouteTraceData inputs g)
    (signDefectClassification :
      SourceSignDefectClassification inputs g sourceTraceReadOff.lambda L)
    (finalSignNonpositive :
      SourceQWNonnegativeToCC20Nonpositive inputs sourceTraceReadOff.archimedeanTest g
        sourceTraceReadOff.lambda
        (inputs.ccm25.weilSymbols.convolutionStar g.weilTest g.weilTest)
        sourceTraceReadOff.ccm25ArithmeticPackage) :
    RouteCertificate inputs where
  sourceBackedTest := g
  ledgers := L
  bridge :=
    route_bridge_certificate_of_sign_defect_classification
      sourceTraceReadOff signDefectClassification
      finalSignNonpositive

noncomputable def route_certificate_of_expanded_source_package
    (pkg : Source.SourceObject.SourceObjectPackage)
    (fixedFront : ExpandedSourceFixedSTestFrontEnd pkg)
    (traceFront : ExpandedSourceTraceReadOffFrontEnd pkg fixedFront)
    (routeFront :
      ExpandedSourceRouteCertificateFrontEnd pkg fixedFront traceFront) :
    RouteCertificate (RouteInputs.ofExpandedSourcePackage pkg) :=
  route_certificate_of_sign_defect_classification
    (SourceRouteTraceData.ofExpandedSourcePackage pkg fixedFront traceFront)
    routeFront.signDefectClassification
    (expanded_source_route_final_sign_nonpositive pkg fixedFront traceFront routeFront)

def route_front_end_of_trace_scale_data
    (pkg : Source.SourceObject.SourceObjectPackage)
    (fixedFront : ExpandedSourceFixedSTestFrontEnd pkg)
    (traceData : TraceFrontEndData pkg fixedFront)
    (routeData : TraceScaleRouteFrontEndData pkg fixedFront traceData) :
    ExpandedSourceRouteCertificateFrontEnd pkg fixedFront
      (traceData.toExpandedSourceTraceReadOffFrontEnd pkg fixedFront) :=
  routeData.toExpandedSourceRouteCertificateFrontEnd pkg fixedFront traceData

noncomputable def route_certificate_of_trace_scale_data
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
          traceData.traceScaleNoMissingBulk.noExtraBulkScaleTerm
          traceData.traceScaleNoMissingBulk.noExtraBulkScaleTermHolds)
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
        traceData.traceScaleNoMissingBulk.noExtraBulkScaleTerm
        traceData.traceScaleNoMissingBulk.noExtraBulkScaleTermHolds).rankPoleCdefOwnEveryRemainder
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
        ledgers traceData.ccm25ArithmeticPackage) :
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
    restrictedToFullQWBridge

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
    (ledgerPackage :
      LedgerSignDefectPackage
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)
        traceData.lambda)
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
          traceData.traceScaleNoMissingBulk.noExtraBulkScaleTerm
          traceData.traceScaleNoMissingBulk.noExtraBulkScaleTermHolds)
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
        traceData.traceScaleNoMissingBulk.noExtraBulkScaleTerm
        traceData.traceScaleNoMissingBulk.noExtraBulkScaleTermHolds).rankPoleCdefOwnEveryRemainder
        ledgerPackage.ledgers ledgerPackage.signDefectClassification)
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
        ledgerPackage.ledgers traceData.ccm25ArithmeticPackage) :
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
    ledgerPackage.ledgers commonTuple ledgerPackage.signDefectClassification
    traceScaleMatchesBridge traceScaleOwnsSignDefectRemainder
    restrictedToFullQWBridge

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
        ledgers traceData.ccm25ArithmeticPackage) :
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
    restrictedToFullQWBridge

noncomputable def route_certificate_of_normalized_comparison_replacement
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
    (signDefectClassification :
      SourceSignDefectClassification
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)
        traceData.lambda ledgers)
    (currentThresholdData :
      RestrictedToFullCurrentThresholdData
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
    (endpointStripInput :
      SourceProjectionOrderEndpointStripNormalForm
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)
        traceData.lambda)
    (windowSupportContainment :
      WindowSupportContainment
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)
        traceData.lambda)
    (postQSeriesTailBoundedComparison :
      PostQSeriesTailBoundedComparison
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)
        traceData.lambda)
    (rankPoleVanishing :
      SourceRankPoleLedgerVanishingGate
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)
        traceData.lambda ledgers)
    (cdefExhausts : ledgers.cdefExhausts) :
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
      traceData comparison ledgers currentThresholdData.commonTuple
      signDefectClassification
      (restricted_to_full_bridge_contract_of_current_threshold_data
        currentThresholdData
        (currentThresholdData.largeLambdaThreshold.scalarRestrictionAtLarge
          traceData.lambda currentThresholdData.currentAboveThreshold
          traceData.ccm25ArithmeticPackage currentThresholdData.commonTuple)
        (source_endpoint_strip_remainder_cdef_domination_of_parts
          endpointStripInput windowSupportContainment
          postQSeriesTailBoundedComparison rankPoleVanishing
          cdefExhausts)))

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
    (ledgerPackage :
      LedgerSignDefectPackage
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)
        traceData.lambda)
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
        ledgerPackage.ledgers traceData.ccm25ArithmeticPackage) :
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
      normalizedTraceData ledgerPackage.ledgers commonTuple
      ledgerPackage.signDefectClassification
      (TraceFrontEndData.normalized_comparison_trace_scale_contract_replacement_owns_sign_defect
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData comparison noExtraBulk ledgerPackage.ledgers
        ledgerPackage.signDefectClassification)
      restrictedToFullQWBridge

noncomputable def trace_scale_route_front_end_of_normalized_boundary_rows_contract_replacement
    (base : Source.SourceObjectTheoremBasePackage)
    (data : Source.SourceObjectConcreteCommonData base)
    (ccm24 : Source.SourceObject.CCM24SemilocalObjectPackage)
    (normalizedSeed :
      Source.CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (remainders :
      Source.CC20Concrete.TraceScale.CC20TracePackageRemainderData
        normalizedSeed)
    (rhExit : Source.SourceObject.CC20RHExitObjectPackage)
    (bridges :
      Source.SourceObjectCrossObjectBridges base data.toSourceObjectCommonData
        (Source.SourceObjectExpandedRows.ofNormalizedCC20Trace
          ccm24 normalizedSeed remainders)
        rhExit)
    (fixedData :
      FixedSTestObligationData
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges))
    (traceData :
      TraceFrontEndData
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges)
        (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges fixedData))
    (boundary :
      Source.SourceObjectConcreteCommonData.SourceEvaluationVisibleFinitePrimeBoundary
        data traceData.lambda)
    (hseed : normalizedSeed = base.s2b1NormalizedSeed)
    (noExtraBulk :
      TraceFrontEndData.TraceScaleNoExtraBulkContract
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges)
        (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges fixedData)
        traceData.lambda traceData.ccm25ArithmeticPackage)
    (ledgerPackage :
      LedgerSignDefectPackage
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
            rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges fixedData)
        traceData.lambda)
    (commonTuple :
      SourceCommonTestTupleContract
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
            rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges fixedData)
        traceData.lambda
        (Source.SourceObject.CommonTestObject.sourceConvolutionSquare
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
            rhExit bridges).commonTest)
        traceData.ccm25ArithmeticPackage)
    (restrictedToFullQWBridge :
      RestrictedToFullQWBridgeContract
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
            rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges fixedData)
        traceData.lambda
        (Source.SourceObject.CommonTestObject.sourceConvolutionSquare
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
            rhExit bridges).commonTest)
        ledgerPackage.ledgers traceData.ccm25ArithmeticPackage) :
    TraceScaleRouteFrontEndData
      (Source.sourceObjectPackageOfNormalizedCC20Trace
        base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
        rhExit bridges)
      (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
        base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
        rhExit bridges fixedData)
      (TraceFrontEndData.withTraceScaleNoMissingBulkOfNormalizedBoundaryRowsFromContract
        base data ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData boundary hseed noExtraBulk) := by
  let boundaryTraceData :=
    TraceFrontEndData.withTraceScaleNoMissingBulkOfNormalizedBoundaryRowsFromContract
      base data ccm24 normalizedSeed remainders rhExit bridges fixedData
      traceData boundary hseed noExtraBulk
  exact
    TraceScaleRouteFrontEndData.ofTraceData
      (Source.sourceObjectPackageOfNormalizedCC20Trace
        base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
        rhExit bridges)
      (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
        base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
        rhExit bridges fixedData)
      boundaryTraceData ledgerPackage.ledgers commonTuple
      ledgerPackage.signDefectClassification
      (TraceFrontEndData.normalized_boundary_trace_scale_contract_replacement_owns_sign_defect
        base data ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData boundary hseed noExtraBulk ledgerPackage.ledgers
        ledgerPackage.signDefectClassification)
      restrictedToFullQWBridge

noncomputable def trace_scale_route_front_end_of_normalized_certificate_boundary_rows_contract_replacement
    (base : Source.SourceObjectTheoremBasePackage)
    (data : Source.SourceObjectConcreteCommonData base)
    (ccm24 : Source.SourceObject.CCM24SemilocalObjectPackage)
    (normalizedSeed :
      Source.CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (remainders :
      Source.CC20Concrete.TraceScale.CC20TracePackageRemainderData
        normalizedSeed)
    (rhExit : Source.SourceObject.CC20RHExitObjectPackage)
    (bridges :
      Source.SourceObjectCrossObjectBridges base data.toSourceObjectCommonData
        (Source.SourceObjectExpandedRows.ofNormalizedCC20Trace
          ccm24 normalizedSeed remainders)
        rhExit)
    (fixedData :
      FixedSTestObligationData
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges))
    (traceData :
      TraceFrontEndData
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges)
        (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges fixedData))
    (boundary :
      Source.SourceObjectConcreteCommonData.CommonFinitePrimeCertificateBoundary
        data traceData.lambda)
    (hseed : normalizedSeed = base.s2b1NormalizedSeed)
    (noExtraBulk :
      TraceFrontEndData.TraceScaleNoExtraBulkContract
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges)
        (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges fixedData)
        traceData.lambda traceData.ccm25ArithmeticPackage)
    (ledgerPackage :
      LedgerSignDefectPackage
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
            rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges fixedData)
        traceData.lambda)
    (commonTuple :
      SourceCommonTestTupleContract
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
            rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges fixedData)
        traceData.lambda
        (Source.SourceObject.CommonTestObject.sourceConvolutionSquare
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
            rhExit bridges).commonTest)
        traceData.ccm25ArithmeticPackage)
    (restrictedToFullQWBridge :
      RestrictedToFullQWBridgeContract
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
            rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges fixedData)
        traceData.lambda
        (Source.SourceObject.CommonTestObject.sourceConvolutionSquare
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
            rhExit bridges).commonTest)
        ledgerPackage.ledgers traceData.ccm25ArithmeticPackage) :
    TraceScaleRouteFrontEndData
      (Source.sourceObjectPackageOfNormalizedCC20Trace
        base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
        rhExit bridges)
      (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
        base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
        rhExit bridges fixedData)
      (TraceFrontEndData.withTraceScaleNoMissingBulkOfNormalizedCertificateBoundaryRowsFromContract
        base data ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData boundary hseed noExtraBulk) := by
  let boundaryTraceData :=
    TraceFrontEndData.withTraceScaleNoMissingBulkOfNormalizedCertificateBoundaryRowsFromContract
      base data ccm24 normalizedSeed remainders rhExit bridges fixedData
      traceData boundary hseed noExtraBulk
  exact
    TraceScaleRouteFrontEndData.ofTraceData
      (Source.sourceObjectPackageOfNormalizedCC20Trace
        base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
        rhExit bridges)
      (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
        base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
        rhExit bridges fixedData)
      boundaryTraceData ledgerPackage.ledgers commonTuple
      ledgerPackage.signDefectClassification
      (by
        dsimp [boundaryTraceData,
          TraceFrontEndData.withTraceScaleNoMissingBulkOfNormalizedCertificateBoundaryRowsFromContract,
          TraceFrontEndData.traceScaleNoMissingBulkOfNormalizedPackageFromCertificateBoundaryRows]
        exact
          TraceFrontEndData.trace_scale_owns_sign_defect_remainder_holds
            ledgerPackage.signDefectClassification)
      restrictedToFullQWBridge

noncomputable def route_certificate_of_normalized_comparison_contract_replacement
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
        ledgers traceData.ccm25ArithmeticPackage) :
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
        traceData comparison noExtraBulk
        (ledger_sign_defect_package_of_source_backed_ledgers
          (source_backed_ledgers_of_sign_defect_classification
            signDefectClassification))
        currentCutoff.commonTuple
        (restricted_to_full_bridge_contract_of_current_cutoff_binding
          currentCutoff))

noncomputable def route_certificate_of_normalized_boundary_rows_contract_replacement
    (base : Source.SourceObjectTheoremBasePackage)
    (data : Source.SourceObjectConcreteCommonData base)
    (ccm24 : Source.SourceObject.CCM24SemilocalObjectPackage)
    (normalizedSeed :
      Source.CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (remainders :
      Source.CC20Concrete.TraceScale.CC20TracePackageRemainderData
        normalizedSeed)
    (rhExit : Source.SourceObject.CC20RHExitObjectPackage)
    (bridges :
      Source.SourceObjectCrossObjectBridges base data.toSourceObjectCommonData
        (Source.SourceObjectExpandedRows.ofNormalizedCC20Trace
          ccm24 normalizedSeed remainders)
        rhExit)
    (fixedData :
      FixedSTestObligationData
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges))
    (traceData :
      TraceFrontEndData
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges)
        (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges fixedData))
    (boundary :
      Source.SourceObjectConcreteCommonData.SourceEvaluationVisibleFinitePrimeBoundary
        data traceData.lambda)
    (hseed : normalizedSeed = base.s2b1NormalizedSeed)
    (noExtraBulk :
      TraceFrontEndData.TraceScaleNoExtraBulkContract
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges)
        (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges fixedData)
        traceData.lambda traceData.ccm25ArithmeticPackage)
    (ledgers : RouteLedgers)
    (signDefectClassification :
      SourceSignDefectClassification
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
            rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges fixedData)
        traceData.lambda ledgers)
    (currentCutoff :
      RestrictedToFullCurrentCutoffBinding
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
            rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges fixedData)
        traceData.lambda
        (Source.SourceObject.CommonTestObject.sourceConvolutionSquare
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
            rhExit bridges).commonTest)
        ledgers traceData.ccm25ArithmeticPackage) :
    RouteCertificate
      (RouteInputs.ofExpandedSourcePackage
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges)) := by
  let boundaryTraceData :=
    TraceFrontEndData.withTraceScaleNoMissingBulkOfNormalizedBoundaryRowsFromContract
      base data ccm24 normalizedSeed remainders rhExit bridges fixedData
      traceData boundary hseed noExtraBulk
  exact
    route_certificate_of_trace_scale_data
      (Source.sourceObjectPackageOfNormalizedCC20Trace
        base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
        rhExit bridges)
      (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
        base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
        rhExit bridges fixedData)
      boundaryTraceData
      (trace_scale_route_front_end_of_normalized_boundary_rows_contract_replacement
        base data ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData boundary hseed noExtraBulk
        (ledger_sign_defect_package_of_source_backed_ledgers
          (source_backed_ledgers_of_sign_defect_classification
            signDefectClassification))
        currentCutoff.commonTuple
        (restricted_to_full_bridge_contract_of_current_cutoff_binding
          currentCutoff))

noncomputable def route_certificate_of_normalized_boundary_rows_current_cutoff_binding
    (base : Source.SourceObjectTheoremBasePackage)
    (data : Source.SourceObjectConcreteCommonData base)
    (ccm24 : Source.SourceObject.CCM24SemilocalObjectPackage)
    (normalizedSeed :
      Source.CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (remainders :
      Source.CC20Concrete.TraceScale.CC20TracePackageRemainderData
        normalizedSeed)
    (rhExit : Source.SourceObject.CC20RHExitObjectPackage)
    (bridges :
      Source.SourceObjectCrossObjectBridges base data.toSourceObjectCommonData
        (Source.SourceObjectExpandedRows.ofNormalizedCC20Trace
          ccm24 normalizedSeed remainders)
        rhExit)
    (fixedData :
      FixedSTestObligationData
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges))
    (traceData :
      TraceFrontEndData
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges)
        (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges fixedData))
    (boundary :
      Source.SourceObjectConcreteCommonData.SourceEvaluationVisibleFinitePrimeBoundary
        data traceData.lambda)
    (hseed : normalizedSeed = base.s2b1NormalizedSeed)
    (noExtraBulk :
      TraceFrontEndData.TraceScaleNoExtraBulkContract
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges)
        (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges fixedData)
        traceData.lambda traceData.ccm25ArithmeticPackage)
    (ledgerPackage :
      LedgerSignDefectPackage
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
            rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges fixedData)
        traceData.lambda)
    (currentCutoff :
      RestrictedToFullCurrentCutoffBinding
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
            rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges fixedData)
        traceData.lambda
        (Source.SourceObject.CommonTestObject.sourceConvolutionSquare
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
            rhExit bridges).commonTest)
        ledgerPackage.ledgers traceData.ccm25ArithmeticPackage) :
    RouteCertificate
      (RouteInputs.ofExpandedSourcePackage
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges)) :=
  route_certificate_of_normalized_boundary_rows_contract_replacement
    base data ccm24 normalizedSeed remainders rhExit bridges fixedData
    traceData boundary hseed noExtraBulk ledgerPackage.ledgers
    ledgerPackage.signDefectClassification currentCutoff

noncomputable def route_certificate_of_normalized_boundary_rows_ledger_restricted_package
    (base : Source.SourceObjectTheoremBasePackage)
    (data : Source.SourceObjectConcreteCommonData base)
    (ccm24 : Source.SourceObject.CCM24SemilocalObjectPackage)
    (normalizedSeed :
      Source.CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (remainders :
      Source.CC20Concrete.TraceScale.CC20TracePackageRemainderData
        normalizedSeed)
    (rhExit : Source.SourceObject.CC20RHExitObjectPackage)
    (bridges :
      Source.SourceObjectCrossObjectBridges base data.toSourceObjectCommonData
        (Source.SourceObjectExpandedRows.ofNormalizedCC20Trace
          ccm24 normalizedSeed remainders)
        rhExit)
    (fixedData :
      FixedSTestObligationData
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges))
    (traceData :
      TraceFrontEndData
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges)
        (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges fixedData))
    (boundary :
      Source.SourceObjectConcreteCommonData.SourceEvaluationVisibleFinitePrimeBoundary
        data traceData.lambda)
    (hseed : normalizedSeed = base.s2b1NormalizedSeed)
    (noExtraBulk :
      TraceFrontEndData.TraceScaleNoExtraBulkContract
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges)
        (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges fixedData)
        traceData.lambda traceData.ccm25ArithmeticPackage)
    (ledgerPackage :
      LedgerSignDefectPackage
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
            rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges fixedData)
        traceData.lambda)
    (restrictedToFullPackage :
      RestrictedToFullThresholdBridgePackage
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
            rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges fixedData)
        traceData.lambda
        (Source.SourceObject.CommonTestObject.sourceConvolutionSquare
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
            rhExit bridges).commonTest)
        ledgerPackage.ledgers traceData.ccm25ArithmeticPackage) :
    RouteCertificate
      (RouteInputs.ofExpandedSourcePackage
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges)) :=
  route_certificate_of_normalized_boundary_rows_current_cutoff_binding
    base data ccm24 normalizedSeed remainders rhExit bridges fixedData
    traceData boundary hseed noExtraBulk ledgerPackage
    restrictedToFullPackage.currentCutoff

noncomputable def route_certificate_of_normalized_source_weil_form_boundary_current_cutoff_binding
    (base : Source.SourceObjectTheoremBasePackage)
    (data : Source.SourceObjectConcreteCommonData base)
    (ccm24 : Source.SourceObject.CCM24SemilocalObjectPackage)
    (normalizedSeed :
      Source.CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (remainders :
      Source.CC20Concrete.TraceScale.CC20TracePackageRemainderData
        normalizedSeed)
    (rhExit : Source.SourceObject.CC20RHExitObjectPackage)
    (bridges :
      Source.SourceObjectCrossObjectBridges base data.toSourceObjectCommonData
        (Source.SourceObjectExpandedRows.ofNormalizedCC20Trace
          ccm24 normalizedSeed remainders)
        rhExit)
    (fixedData :
      FixedSTestObligationData
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges))
    (traceData :
      TraceFrontEndData
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges)
        (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges fixedData))
    {sourceAlgebra : Source.AnalyticCore.SourceTestAlgebra}
    (sourceWeilForm : Source.AnalyticCore.SourceWeilFormData sourceAlgebra)
    (sourceSymbols_eq :
      base.ccm25Model.toWeilFormSymbols =
        sourceWeilForm.toWeilFormSymbols)
    (hseed : normalizedSeed = base.s2b1NormalizedSeed)
    (noExtraBulk :
      TraceFrontEndData.TraceScaleNoExtraBulkContract
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges)
        (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges fixedData)
        traceData.lambda traceData.ccm25ArithmeticPackage)
    (ledgerPackage :
      LedgerSignDefectPackage
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
            rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges fixedData)
        traceData.lambda)
    (currentCutoff :
      RestrictedToFullCurrentCutoffBinding
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
            rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges fixedData)
        traceData.lambda
        (Source.SourceObject.CommonTestObject.sourceConvolutionSquare
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
            rhExit bridges).commonTest)
        ledgerPackage.ledgers traceData.ccm25ArithmeticPackage) :
    RouteCertificate
      (RouteInputs.ofExpandedSourcePackage
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges)) :=
  let boundary :=
    Source.SourceObjectConcreteCommonData.SourceEvaluationVisibleFinitePrimeBoundary.ofSourceWeilForm
      data sourceWeilForm sourceSymbols_eq traceData.lambda
      traceData.oneLtLambda
  route_certificate_of_normalized_boundary_rows_current_cutoff_binding
    base data ccm24 normalizedSeed remainders rhExit bridges fixedData
    traceData boundary hseed noExtraBulk ledgerPackage currentCutoff

noncomputable def route_certificate_of_normalized_source_weil_form_boundary_ledger_restricted_package
    (base : Source.SourceObjectTheoremBasePackage)
    (data : Source.SourceObjectConcreteCommonData base)
    (ccm24 : Source.SourceObject.CCM24SemilocalObjectPackage)
    (normalizedSeed :
      Source.CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (remainders :
      Source.CC20Concrete.TraceScale.CC20TracePackageRemainderData
        normalizedSeed)
    (rhExit : Source.SourceObject.CC20RHExitObjectPackage)
    (bridges :
      Source.SourceObjectCrossObjectBridges base data.toSourceObjectCommonData
        (Source.SourceObjectExpandedRows.ofNormalizedCC20Trace
          ccm24 normalizedSeed remainders)
        rhExit)
    (fixedData :
      FixedSTestObligationData
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges))
    (traceData :
      TraceFrontEndData
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges)
        (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges fixedData))
    {sourceAlgebra : Source.AnalyticCore.SourceTestAlgebra}
    (sourceWeilForm : Source.AnalyticCore.SourceWeilFormData sourceAlgebra)
    (sourceSymbols_eq :
      base.ccm25Model.toWeilFormSymbols =
        sourceWeilForm.toWeilFormSymbols)
    (hseed : normalizedSeed = base.s2b1NormalizedSeed)
    (noExtraBulk :
      TraceFrontEndData.TraceScaleNoExtraBulkContract
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges)
        (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges fixedData)
        traceData.lambda traceData.ccm25ArithmeticPackage)
    (ledgerPackage :
      LedgerSignDefectPackage
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
            rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges fixedData)
        traceData.lambda)
    (restrictedToFullPackage :
      RestrictedToFullThresholdBridgePackage
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
            rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges fixedData)
        traceData.lambda
        (Source.SourceObject.CommonTestObject.sourceConvolutionSquare
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
            rhExit bridges).commonTest)
        ledgerPackage.ledgers traceData.ccm25ArithmeticPackage) :
    RouteCertificate
      (RouteInputs.ofExpandedSourcePackage
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges)) :=
  route_certificate_of_normalized_source_weil_form_boundary_current_cutoff_binding
    base data ccm24 normalizedSeed remainders rhExit bridges fixedData
    traceData sourceWeilForm sourceSymbols_eq hseed
    noExtraBulk ledgerPackage restrictedToFullPackage.currentCutoff

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
    (ledgerPackage :
      LedgerSignDefectPackage
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)
        traceData.lambda)
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
        ledgerPackage.ledgers traceData.ccm25ArithmeticPackage) :
    RouteCertificate
      (RouteInputs.ofExpandedSourcePackage
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges)) :=
  route_certificate_of_normalized_comparison_contract_replacement
    base common ccm24 normalizedSeed remainders rhExit bridges fixedData
    traceData comparison noExtraBulk ledgerPackage.ledgers
    ledgerPackage.signDefectClassification currentCutoff

noncomputable def route_certificate_of_normalized_comparison_ledger_package_current_cutoff
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
    (ledgerPackage :
      LedgerSignDefectPackage
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)
        traceData.lambda)
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
        ledgerPackage.ledgers traceData.ccm25ArithmeticPackage) :
    RouteCertificate
      (RouteInputs.ofExpandedSourcePackage
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges)) :=
  route_certificate_of_normalized_comparison_current_cutoff_binding
    base common ccm24 normalizedSeed remainders rhExit bridges fixedData
    traceData comparison noExtraBulk ledgerPackage currentCutoff

noncomputable def route_certificate_of_normalized_comparison_ledger_package_source_backed_cutoff
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
    (ledgerPackage :
      LedgerSignDefectPackage
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)
        traceData.lambda)
    (provider :
      NormalizedRestrictedToFullAsymptoticRowsProvider
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData) :
    RouteCertificate
      (RouteInputs.ofExpandedSourcePackage
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges)) :=
  route_certificate_of_normalized_comparison_current_cutoff_binding
    base common ccm24 normalizedSeed remainders rhExit bridges fixedData
    traceData comparison noExtraBulk ledgerPackage
    (normalized_restricted_to_full_current_cutoff_binding_of_source_backed_asymptotic_rows
      base common ccm24 normalizedSeed remainders rhExit bridges fixedData
      traceData ledgerPackage.ledgers provider
      ledgerPackage.ledgersCleared.rankKilled
      ledgerPackage.ledgersCleared.poleKilled
      ledgerPackage.ledgersCleared.cdefExhausts)

noncomputable def route_certificate_of_normalized_certificate_boundary_rows_current_cutoff_binding
    (base : Source.SourceObjectTheoremBasePackage)
    (data : Source.SourceObjectConcreteCommonData base)
    (ccm24 : Source.SourceObject.CCM24SemilocalObjectPackage)
    (normalizedSeed :
      Source.CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (remainders :
      Source.CC20Concrete.TraceScale.CC20TracePackageRemainderData
        normalizedSeed)
    (rhExit : Source.SourceObject.CC20RHExitObjectPackage)
    (bridges :
      Source.SourceObjectCrossObjectBridges base data.toSourceObjectCommonData
        (Source.SourceObjectExpandedRows.ofNormalizedCC20Trace
          ccm24 normalizedSeed remainders)
        rhExit)
    (fixedData :
      FixedSTestObligationData
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges))
    (traceData :
      TraceFrontEndData
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges)
        (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges fixedData))
    (boundary :
      Source.SourceObjectConcreteCommonData.CommonFinitePrimeCertificateBoundary
        data traceData.lambda)
    (hseed : normalizedSeed = base.s2b1NormalizedSeed)
    (noExtraBulk :
      TraceFrontEndData.TraceScaleNoExtraBulkContract
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges)
        (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges fixedData)
        traceData.lambda traceData.ccm25ArithmeticPackage)
    (ledgerPackage :
      LedgerSignDefectPackage
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
            rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges fixedData)
        traceData.lambda)
    (traceScaleOwnsSignDefectRemainder :
      traceData.traceScaleNoMissingBulk.rankPoleCdefOwnEveryRemainder
        ledgerPackage.ledgers ledgerPackage.signDefectClassification)
    (currentCutoff :
      RestrictedToFullCurrentCutoffBinding
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
            rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges fixedData)
        traceData.lambda
        (Source.SourceObject.CommonTestObject.sourceConvolutionSquare
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
            rhExit bridges).commonTest)
        ledgerPackage.ledgers traceData.ccm25ArithmeticPackage) :
    RouteCertificate
      (RouteInputs.ofExpandedSourcePackage
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges)) := by
  exact
    route_certificate_of_trace_scale_data
      (Source.sourceObjectPackageOfNormalizedCC20Trace
        base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
        rhExit bridges)
      (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
        base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
        rhExit bridges fixedData)
      traceData
      (TraceScaleRouteFrontEndData.ofTraceData
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges)
        (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges fixedData)
        traceData
        ledgerPackage.ledgers
        currentCutoff.commonTuple
        ledgerPackage.signDefectClassification
        traceScaleOwnsSignDefectRemainder
        (restricted_to_full_bridge_contract_of_current_cutoff_binding
          currentCutoff))

noncomputable def route_certificate_of_normalized_certificate_boundary_rows_ledger_package_source_backed_cutoff
    (base : Source.SourceObjectTheoremBasePackage)
    (data : Source.SourceObjectConcreteCommonData base)
    (ccm24 : Source.SourceObject.CCM24SemilocalObjectPackage)
    (normalizedSeed :
      Source.CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (remainders :
      Source.CC20Concrete.TraceScale.CC20TracePackageRemainderData
        normalizedSeed)
    (rhExit : Source.SourceObject.CC20RHExitObjectPackage)
    (bridges :
      Source.SourceObjectCrossObjectBridges base data.toSourceObjectCommonData
        (Source.SourceObjectExpandedRows.ofNormalizedCC20Trace
          ccm24 normalizedSeed remainders)
        rhExit)
    (fixedData :
      FixedSTestObligationData
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges))
    (traceData :
      TraceFrontEndData
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges)
        (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges fixedData))
    (boundary :
      Source.SourceObjectConcreteCommonData.CommonFinitePrimeCertificateBoundary
        data traceData.lambda)
    (hseed : normalizedSeed = base.s2b1NormalizedSeed)
    (noExtraBulk :
      TraceFrontEndData.TraceScaleNoExtraBulkContract
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges)
        (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges fixedData)
        traceData.lambda traceData.ccm25ArithmeticPackage)
    (ledgerPackage :
      LedgerSignDefectPackage
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
            rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges fixedData)
        traceData.lambda)
    (traceScaleOwnsSignDefectRemainder :
      traceData.traceScaleNoMissingBulk.rankPoleCdefOwnEveryRemainder
        ledgerPackage.ledgers ledgerPackage.signDefectClassification)
    (provider :
      NormalizedRestrictedToFullAsymptoticRowsProvider
        base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
        rhExit bridges fixedData traceData) :
    RouteCertificate
      (RouteInputs.ofExpandedSourcePackage
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges)) :=
  route_certificate_of_normalized_certificate_boundary_rows_current_cutoff_binding
    base data ccm24 normalizedSeed remainders rhExit bridges fixedData
    traceData boundary hseed noExtraBulk ledgerPackage
    traceScaleOwnsSignDefectRemainder
    (normalized_restricted_to_full_current_cutoff_binding_of_source_backed_asymptotic_rows
      base data.toSourceObjectCommonData ccm24 normalizedSeed remainders rhExit
      bridges fixedData traceData ledgerPackage.ledgers provider
      ledgerPackage.ledgersCleared.rankKilled
      ledgerPackage.ledgersCleared.poleKilled
      ledgerPackage.ledgersCleared.cdefExhausts)

noncomputable def route_certificate_of_normalized_comparison_ledger_restricted_package
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
    (ledgerPackage :
      LedgerSignDefectPackage
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)
        traceData.lambda)
    (restrictedToFullPackage :
      RestrictedToFullThresholdBridgePackage
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
        ledgerPackage.ledgers traceData.ccm25ArithmeticPackage) :
    RouteCertificate
      (RouteInputs.ofExpandedSourcePackage
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges)) :=
  route_certificate_of_normalized_comparison_ledger_package_current_cutoff
    base common ccm24 normalizedSeed remainders rhExit bridges fixedData
    traceData comparison noExtraBulk ledgerPackage
    restrictedToFullPackage.currentCutoff

noncomputable def route_certificate_of_normalized_comparison
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
          traceData.traceScaleNoMissingBulk.noExtraBulkScaleTerm
          traceData.traceScaleNoMissingBulk.noExtraBulkScaleTermHolds)
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
        traceData.traceScaleNoMissingBulk.noExtraBulkScaleTerm
        traceData.traceScaleNoMissingBulk.noExtraBulkScaleTermHolds).rankPoleCdefOwnEveryRemainder
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
        ledgers traceData.ccm25ArithmeticPackage) :
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
      restrictedToFullQWBridge)

noncomputable def route_certificate_of_normalized_package_bridge
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
    (ledgerPackage :
      LedgerSignDefectPackage
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)
        traceData.lambda)
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
          traceData.traceScaleNoMissingBulk.noExtraBulkScaleTerm
          traceData.traceScaleNoMissingBulk.noExtraBulkScaleTermHolds)
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
        traceData.traceScaleNoMissingBulk.noExtraBulkScaleTerm
        traceData.traceScaleNoMissingBulk.noExtraBulkScaleTermHolds).rankPoleCdefOwnEveryRemainder
        ledgerPackage.ledgers ledgerPackage.signDefectClassification)
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
        ledgerPackage.ledgers traceData.ccm25ArithmeticPackage) :
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
      traceData ledgerPackage commonTuple traceScaleMatchesBridge
      traceScaleOwnsSignDefectRemainder restrictedToFullQWBridge)

theorem cc20_source_rh_of_route_certificate
    {inputs : RouteInputs} (cert : RouteCertificate inputs) :
    inputs.cc20.rhDefinitionBridge.SourceRH :=
  cc20_source_rh_of_route_final_exit_package
    (route_final_exit_package_of_certificate cert)

theorem final_connes_weil_rh
    {inputs : RouteInputs} (cert : RouteCertificate inputs) :
    _root_.RiemannHypothesis := by
  let _ := final_sign_nonpositive_of_route_bridge_certificate cert.bridge
  exact
    Source.RHDefinitionBridge.source_rh_to_mathlib_rh
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
    (ledgerPackage :
      LedgerSignDefectPackage
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)
        traceData.lambda)
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
          traceData.traceScaleNoMissingBulk.noExtraBulkScaleTerm
          traceData.traceScaleNoMissingBulk.noExtraBulkScaleTermHolds)
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
        traceData.traceScaleNoMissingBulk.noExtraBulkScaleTerm
        traceData.traceScaleNoMissingBulk.noExtraBulkScaleTermHolds).rankPoleCdefOwnEveryRemainder
        ledgerPackage.ledgers ledgerPackage.signDefectClassification)
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
        ledgerPackage.ledgers traceData.ccm25ArithmeticPackage) :
    _root_.RiemannHypothesis := by
  exact
    final_connes_weil_rh
      (route_certificate_of_normalized_comparison
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData comparison ledgerPackage.ledgers commonTuple
        ledgerPackage.signDefectClassification
        traceScaleMatchesComparison traceScaleOwnsSignDefectRemainder
        restrictedToFullQWBridge)

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
    (ledgerPackage :
      LedgerSignDefectPackage
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)
        traceData.lambda)
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
          traceData.traceScaleNoMissingBulk.noExtraBulkScaleTerm
          traceData.traceScaleNoMissingBulk.noExtraBulkScaleTermHolds)
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
        traceData.traceScaleNoMissingBulk.noExtraBulkScaleTerm
        traceData.traceScaleNoMissingBulk.noExtraBulkScaleTermHolds).rankPoleCdefOwnEveryRemainder
        ledgerPackage.ledgers ledgerPackage.signDefectClassification)
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
        ledgerPackage.ledgers traceData.ccm25ArithmeticPackage) :
    _root_.RiemannHypothesis := by
  exact
    final_connes_weil_rh
      (route_certificate_of_normalized_package_bridge
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData ledgerPackage commonTuple traceScaleMatchesBridge
        traceScaleOwnsSignDefectRemainder restrictedToFullQWBridge)

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
    (signDefectClassification :
      SourceSignDefectClassification
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)
        traceData.lambda ledgers)
    (currentThresholdData :
      RestrictedToFullCurrentThresholdData
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
    (endpointStripInput :
      SourceProjectionOrderEndpointStripNormalForm
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)
        traceData.lambda)
    (windowSupportContainment :
      WindowSupportContainment
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)
        traceData.lambda)
    (postQSeriesTailBoundedComparison :
      PostQSeriesTailBoundedComparison
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)
        traceData.lambda)
    (rankPoleVanishing :
      SourceRankPoleLedgerVanishingGate
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)
        traceData.lambda ledgers)
    (cdefExhausts : ledgers.cdefExhausts) :
    _root_.RiemannHypothesis := by
  exact
    final_connes_weil_rh
      (route_certificate_of_normalized_comparison_replacement
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData comparison ledgers signDefectClassification
        currentThresholdData endpointStripInput windowSupportContainment
        postQSeriesTailBoundedComparison rankPoleVanishing cdefExhausts)

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
    (ledgerPackage :
      LedgerSignDefectPackage
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)
        traceData.lambda)
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
        ledgerPackage.ledgers traceData.ccm25ArithmeticPackage) :
    _root_.RiemannHypothesis := by
  exact
    final_connes_weil_rh
      (route_certificate_of_normalized_comparison_contract_replacement
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData comparison noExtraBulk ledgerPackage.ledgers
        ledgerPackage.signDefectClassification currentCutoff)

theorem final_rh_of_normalized_boundary_rows_contract_replacement
    (base : Source.SourceObjectTheoremBasePackage)
    (data : Source.SourceObjectConcreteCommonData base)
    (ccm24 : Source.SourceObject.CCM24SemilocalObjectPackage)
    (normalizedSeed :
      Source.CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (remainders :
      Source.CC20Concrete.TraceScale.CC20TracePackageRemainderData
        normalizedSeed)
    (rhExit : Source.SourceObject.CC20RHExitObjectPackage)
    (bridges :
      Source.SourceObjectCrossObjectBridges base data.toSourceObjectCommonData
        (Source.SourceObjectExpandedRows.ofNormalizedCC20Trace
          ccm24 normalizedSeed remainders)
        rhExit)
    (fixedData :
      FixedSTestObligationData
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges))
    (traceData :
      TraceFrontEndData
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges)
        (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges fixedData))
    (boundary :
      Source.SourceObjectConcreteCommonData.SourceEvaluationVisibleFinitePrimeBoundary
        data traceData.lambda)
    (hseed : normalizedSeed = base.s2b1NormalizedSeed)
    (noExtraBulk :
      TraceFrontEndData.TraceScaleNoExtraBulkContract
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges)
        (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges fixedData)
        traceData.lambda traceData.ccm25ArithmeticPackage)
    (ledgerPackage :
      LedgerSignDefectPackage
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
            rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges fixedData)
        traceData.lambda)
    (currentCutoff :
      RestrictedToFullCurrentCutoffBinding
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
            rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges fixedData)
        traceData.lambda
        (Source.SourceObject.CommonTestObject.sourceConvolutionSquare
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
            rhExit bridges).commonTest)
        ledgerPackage.ledgers traceData.ccm25ArithmeticPackage) :
    _root_.RiemannHypothesis := by
  exact
    final_connes_weil_rh
      (route_certificate_of_normalized_boundary_rows_contract_replacement
        base data ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData boundary hseed noExtraBulk ledgerPackage.ledgers
        ledgerPackage.signDefectClassification currentCutoff)

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
    (ledgerPackage :
      LedgerSignDefectPackage
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)
        traceData.lambda)
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
        ledgerPackage.ledgers traceData.ccm25ArithmeticPackage) :
    _root_.RiemannHypothesis := by
  exact
    final_connes_weil_rh
      (route_certificate_of_normalized_comparison_current_cutoff_binding
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData comparison noExtraBulk ledgerPackage currentCutoff)

theorem final_rh_of_normalized_boundary_rows_current_cutoff_binding
    (base : Source.SourceObjectTheoremBasePackage)
    (data : Source.SourceObjectConcreteCommonData base)
    (ccm24 : Source.SourceObject.CCM24SemilocalObjectPackage)
    (normalizedSeed :
      Source.CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (remainders :
      Source.CC20Concrete.TraceScale.CC20TracePackageRemainderData
        normalizedSeed)
    (rhExit : Source.SourceObject.CC20RHExitObjectPackage)
    (bridges :
      Source.SourceObjectCrossObjectBridges base data.toSourceObjectCommonData
        (Source.SourceObjectExpandedRows.ofNormalizedCC20Trace
          ccm24 normalizedSeed remainders)
        rhExit)
    (fixedData :
      FixedSTestObligationData
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges))
    (traceData :
      TraceFrontEndData
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges)
        (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges fixedData))
    (boundary :
      Source.SourceObjectConcreteCommonData.SourceEvaluationVisibleFinitePrimeBoundary
        data traceData.lambda)
    (hseed : normalizedSeed = base.s2b1NormalizedSeed)
    (noExtraBulk :
      TraceFrontEndData.TraceScaleNoExtraBulkContract
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges)
        (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges fixedData)
        traceData.lambda traceData.ccm25ArithmeticPackage)
    (ledgerPackage :
      LedgerSignDefectPackage
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
            rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges fixedData)
        traceData.lambda)
    (currentCutoff :
      RestrictedToFullCurrentCutoffBinding
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
            rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges fixedData)
        traceData.lambda
        (Source.SourceObject.CommonTestObject.sourceConvolutionSquare
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
            rhExit bridges).commonTest)
        ledgerPackage.ledgers traceData.ccm25ArithmeticPackage) :
    _root_.RiemannHypothesis := by
  exact
    final_connes_weil_rh
      (route_certificate_of_normalized_boundary_rows_current_cutoff_binding
        base data ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData boundary hseed noExtraBulk ledgerPackage currentCutoff)

theorem final_rh_of_normalized_comparison_ledger_package_current_cutoff
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
    (ledgerPackage :
      LedgerSignDefectPackage
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)
        traceData.lambda)
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
        ledgerPackage.ledgers traceData.ccm25ArithmeticPackage) :
    _root_.RiemannHypothesis := by
  exact
    final_connes_weil_rh
      (route_certificate_of_normalized_comparison_ledger_package_current_cutoff
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData comparison noExtraBulk ledgerPackage currentCutoff)

theorem final_rh_of_normalized_comparison_ledger_package_source_backed_cutoff
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
    (ledgerPackage :
      LedgerSignDefectPackage
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)
        traceData.lambda)
    (provider :
      NormalizedRestrictedToFullAsymptoticRowsProvider
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData) :
    _root_.RiemannHypothesis := by
  exact
    final_connes_weil_rh
      (route_certificate_of_normalized_comparison_ledger_package_source_backed_cutoff
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData comparison noExtraBulk ledgerPackage provider)

theorem final_rh_of_normalized_comparison_ledger_restricted_package
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
    (ledgerPackage :
      LedgerSignDefectPackage
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)
        traceData.lambda)
    (restrictedToFullPackage :
      RestrictedToFullThresholdBridgePackage
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
        ledgerPackage.ledgers traceData.ccm25ArithmeticPackage) :
    _root_.RiemannHypothesis := by
  exact
    final_connes_weil_rh
      (route_certificate_of_normalized_comparison_ledger_restricted_package
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData comparison noExtraBulk ledgerPackage restrictedToFullPackage)

theorem final_rh_of_normalized_boundary_rows_ledger_restricted_package
    (base : Source.SourceObjectTheoremBasePackage)
    (data : Source.SourceObjectConcreteCommonData base)
    (ccm24 : Source.SourceObject.CCM24SemilocalObjectPackage)
    (normalizedSeed :
      Source.CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (remainders :
      Source.CC20Concrete.TraceScale.CC20TracePackageRemainderData
        normalizedSeed)
    (rhExit : Source.SourceObject.CC20RHExitObjectPackage)
    (bridges :
      Source.SourceObjectCrossObjectBridges base data.toSourceObjectCommonData
        (Source.SourceObjectExpandedRows.ofNormalizedCC20Trace
          ccm24 normalizedSeed remainders)
        rhExit)
    (fixedData :
      FixedSTestObligationData
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges))
    (traceData :
      TraceFrontEndData
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges)
        (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges fixedData))
    (boundary :
      Source.SourceObjectConcreteCommonData.SourceEvaluationVisibleFinitePrimeBoundary
        data traceData.lambda)
    (hseed : normalizedSeed = base.s2b1NormalizedSeed)
    (noExtraBulk :
      TraceFrontEndData.TraceScaleNoExtraBulkContract
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges)
        (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges fixedData)
        traceData.lambda traceData.ccm25ArithmeticPackage)
    (ledgerPackage :
      LedgerSignDefectPackage
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
            rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges fixedData)
        traceData.lambda)
    (restrictedToFullPackage :
      RestrictedToFullThresholdBridgePackage
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
            rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges fixedData)
        traceData.lambda
        (Source.SourceObject.CommonTestObject.sourceConvolutionSquare
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
            rhExit bridges).commonTest)
        ledgerPackage.ledgers traceData.ccm25ArithmeticPackage) :
    _root_.RiemannHypothesis := by
  exact
    final_connes_weil_rh
      (route_certificate_of_normalized_boundary_rows_ledger_restricted_package
        base data ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData boundary hseed noExtraBulk ledgerPackage restrictedToFullPackage)

theorem final_rh_of_normalized_source_weil_form_boundary_ledger_restricted_package
    (base : Source.SourceObjectTheoremBasePackage)
    (data : Source.SourceObjectConcreteCommonData base)
    (ccm24 : Source.SourceObject.CCM24SemilocalObjectPackage)
    (normalizedSeed :
      Source.CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (remainders :
      Source.CC20Concrete.TraceScale.CC20TracePackageRemainderData
        normalizedSeed)
    (rhExit : Source.SourceObject.CC20RHExitObjectPackage)
    (bridges :
      Source.SourceObjectCrossObjectBridges base data.toSourceObjectCommonData
        (Source.SourceObjectExpandedRows.ofNormalizedCC20Trace
          ccm24 normalizedSeed remainders)
        rhExit)
    (fixedData :
      FixedSTestObligationData
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges))
    (traceData :
      TraceFrontEndData
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges)
        (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges fixedData))
    {sourceAlgebra : Source.AnalyticCore.SourceTestAlgebra}
    (sourceWeilForm : Source.AnalyticCore.SourceWeilFormData sourceAlgebra)
    (sourceSymbols_eq :
      base.ccm25Model.toWeilFormSymbols =
        sourceWeilForm.toWeilFormSymbols)
    (hseed : normalizedSeed = base.s2b1NormalizedSeed)
    (noExtraBulk :
      TraceFrontEndData.TraceScaleNoExtraBulkContract
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges)
        (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges fixedData)
        traceData.lambda traceData.ccm25ArithmeticPackage)
    (ledgerPackage :
      LedgerSignDefectPackage
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
            rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges fixedData)
        traceData.lambda)
    (restrictedToFullPackage :
      RestrictedToFullThresholdBridgePackage
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
            rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
          rhExit bridges fixedData)
        traceData.lambda
        (Source.SourceObject.CommonTestObject.sourceConvolutionSquare
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base data.toSourceObjectCommonData ccm24 normalizedSeed remainders
            rhExit bridges).commonTest)
        ledgerPackage.ledgers traceData.ccm25ArithmeticPackage) :
    _root_.RiemannHypothesis := by
  exact
    final_connes_weil_rh
      (route_certificate_of_normalized_source_weil_form_boundary_ledger_restricted_package
        base data ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData sourceWeilForm sourceSymbols_eq hseed
        noExtraBulk ledgerPackage restrictedToFullPackage)

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

noncomputable def route_certificate_of_package_data
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
