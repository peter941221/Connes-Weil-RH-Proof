/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Route.Theorem1
import ConnesWeilRH.Route.FixedTestFrontEnd

/-!
# Trace-front-end staging

Goal 4A builds the expanded trace front end from the Goal 2D source package
and the Goal 3 fixed-test front end.  It keeps trace legality, support-square
transport, full trace read-off, and restricted trace read-off as explicit
inputs.

Goal 4C keeps the S2-B1 no-missing-bulk check as data, not as a loose marker
proposition.  Downstream route-certificate staging can require this data before
it consumes sign/defect and restricted-to-full evidence.
-/

namespace ConnesWeilRH
namespace Route

/--
Goal 4C data for the S2-B1 trace-scale no-missing-bulk target.

The fields are intentionally propositional at this stage: the current slice
does not prove the CC20/CCM25 analytic scalar identities.  It does, however,
force the next route-front-end constructor to carry a named ledger of the exact
trace-scale obligations that must be proved before positive trace can feed
`QW_lambda`.
-/
structure TraceScaleNoMissingBulkData
    (pkg : Source.SourceObject.SourceObjectPackage)
    (fixedFront : ExpandedSourceFixedSTestFrontEnd pkg)
    (lambda : ℝ)
    (ccm25ArithmeticPackage :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        (RouteInputs.ofExpandedSourcePackage pkg).ccm25.weilSymbols
        pkg.commonTest.sourceTest lambda) where
  ordinaryTraceMatchesSupportSquare : Prop
  supportSquareMatchesNoDefectSource : Prop
  noDefectSourceMatchesQWLambda : Prop
  rankPoleCdefOwnEveryRemainder :
    (L : RouteLedgers) ->
      SourceSignDefectClassification
        (RouteInputs.ofExpandedSourcePackage pkg)
        (SourceBackedFixedSTest.ofExpandedSourcePackage pkg fixedFront)
        lambda L -> Prop
  noExtraBulkScaleTerm : Prop
  ordinaryTraceMatchesSupportSquareHolds : ordinaryTraceMatchesSupportSquare
  supportSquareMatchesNoDefectSourceHolds : supportSquareMatchesNoDefectSource
  noDefectSourceMatchesQWLambdaHolds : noDefectSourceMatchesQWLambda
  noExtraBulkScaleTermHolds : noExtraBulkScaleTerm

/--
Goal 4E data for the first S2-B1 scalar leg: ordinary positive trace and the
support-square trace must be the same finite-lambda scalar.
-/
structure OrdinaryTraceSupportSquareTheoremData
    (pkg : Source.SourceObject.SourceObjectPackage)
    (fixedFront : ExpandedSourceFixedSTestFrontEnd pkg)
    (lambda : ℝ)
    (ccm25ArithmeticPackage :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        (RouteInputs.ofExpandedSourcePackage pkg).ccm25.weilSymbols
        pkg.commonTest.sourceTest lambda) where
  ordinaryTraceMatchesSupportSquare : Prop
  ordinaryTraceMatchesSupportSquareHolds : ordinaryTraceMatchesSupportSquare

/--
Source-shaped Goal 4E evidence for the ordinary-trace/support-square scalar
handoff.  This keeps the missing analytic theorem tied to the exact trace data,
trace-class/cyclicity legality, and support-square read-off used by the route.
-/
structure CC20OrdinaryTraceSupportSquareTheoremData
    (inputs : RouteInputs)
    (g : SourceBackedFixedSTest inputs)
    (traceData : SourceTraceReadOffData inputs g) where
  traceLegality : CC20TraceLegality inputs traceData.archimedeanTest
  traceSquareReadOff : CC20TraceSquareReadOff inputs traceData.archimedeanTest
  ordinaryTraceMatchesSupportSquare : Prop
  ordinaryTraceMatchesSupportSquareHolds : ordinaryTraceMatchesSupportSquare
  traceLegalityMatchesData :
    traceLegality = cc20_trace_legality_of_source_trace_data traceData
  traceSquareMatchesData :
    traceSquareReadOff = cc20_trace_square_of_source_trace_data traceData

/--
Goal 4F data for the S2-B1 no-defect-to-`QW_lambda` scalar leg.
-/
structure NoDefectQWLambdaTheoremData
    (pkg : Source.SourceObject.SourceObjectPackage)
    (fixedFront : ExpandedSourceFixedSTestFrontEnd pkg)
    (lambda : ℝ)
    (ccm25ArithmeticPackage :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        (RouteInputs.ofExpandedSourcePackage pkg).ccm25.weilSymbols
        pkg.commonTest.sourceTest lambda) where
  supportSquareMatchesNoDefectSource : Prop
  noDefectSourceMatchesQWLambda : Prop
  supportSquareMatchesNoDefectSourceHolds : supportSquareMatchesNoDefectSource
  noDefectSourceMatchesQWLambdaHolds : noDefectSourceMatchesQWLambda

/--
Source-shaped Goal 4F evidence for support-square/no-defect/`QW_lambda`
compatibility.  The restricted bridge source is kept visible because this is the
normalization point where hidden finite-part subtraction or bulk drift would
break the route.
-/
structure CC20NoDefectQWLambdaTheoremData
    (inputs : RouteInputs)
    (g : SourceBackedFixedSTest inputs)
    (traceData : SourceTraceReadOffData inputs g) where
  traceSquareReadOff : CC20TraceSquareReadOff inputs traceData.archimedeanTest
  restrictedTraceReadOffSource :
    RestrictedTraceReadOffSource inputs traceData.archimedeanTest g
      traceData.lambda
  supportSquareMatchesNoDefectSource : Prop
  noDefectSourceMatchesQWLambda : Prop
  supportSquareMatchesNoDefectSourceHolds : supportSquareMatchesNoDefectSource
  noDefectSourceMatchesQWLambdaHolds : noDefectSourceMatchesQWLambda
  traceSquareMatchesData :
    traceSquareReadOff = cc20_trace_square_of_source_trace_data traceData

def trace_scale_no_missing_bulk_of_scalar_theorem_data
    {pkg : Source.SourceObject.SourceObjectPackage}
    {fixedFront : ExpandedSourceFixedSTestFrontEnd pkg}
    {lambda : ℝ}
    {ccm25ArithmeticPackage :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        (RouteInputs.ofExpandedSourcePackage pkg).ccm25.weilSymbols
        pkg.commonTest.sourceTest lambda}
    (ordinary :
      OrdinaryTraceSupportSquareTheoremData pkg fixedFront lambda
        ccm25ArithmeticPackage)
    (noDefect :
      NoDefectQWLambdaTheoremData pkg fixedFront lambda
        ccm25ArithmeticPackage)
    (rankPoleCdefOwnEveryRemainder :
      (L : RouteLedgers) ->
        SourceSignDefectClassification
          (RouteInputs.ofExpandedSourcePackage pkg)
          (SourceBackedFixedSTest.ofExpandedSourcePackage pkg fixedFront)
          lambda L -> Prop)
    (noExtraBulkScaleTerm : Prop)
    (noExtraBulkScaleTermHolds : noExtraBulkScaleTerm) :
    TraceScaleNoMissingBulkData pkg fixedFront lambda ccm25ArithmeticPackage where
  ordinaryTraceMatchesSupportSquare :=
    ordinary.ordinaryTraceMatchesSupportSquare
  supportSquareMatchesNoDefectSource :=
    noDefect.supportSquareMatchesNoDefectSource
  noDefectSourceMatchesQWLambda :=
    noDefect.noDefectSourceMatchesQWLambda
  rankPoleCdefOwnEveryRemainder := rankPoleCdefOwnEveryRemainder
  noExtraBulkScaleTerm := noExtraBulkScaleTerm
  ordinaryTraceMatchesSupportSquareHolds :=
    ordinary.ordinaryTraceMatchesSupportSquareHolds
  supportSquareMatchesNoDefectSourceHolds :=
    noDefect.supportSquareMatchesNoDefectSourceHolds
  noDefectSourceMatchesQWLambdaHolds :=
    noDefect.noDefectSourceMatchesQWLambdaHolds
  noExtraBulkScaleTermHolds := noExtraBulkScaleTermHolds

theorem ordinary_trace_matches_support_square_of_scalar_theorem_data
    {pkg : Source.SourceObject.SourceObjectPackage}
    {fixedFront : ExpandedSourceFixedSTestFrontEnd pkg}
    {lambda : ℝ}
    {ccm25ArithmeticPackage :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        (RouteInputs.ofExpandedSourcePackage pkg).ccm25.weilSymbols
        pkg.commonTest.sourceTest lambda}
    (ordinary :
      OrdinaryTraceSupportSquareTheoremData pkg fixedFront lambda
        ccm25ArithmeticPackage)
    (noDefect :
      NoDefectQWLambdaTheoremData pkg fixedFront lambda
        ccm25ArithmeticPackage)
    (rankPoleCdefOwnEveryRemainder :
      (L : RouteLedgers) ->
        SourceSignDefectClassification
          (RouteInputs.ofExpandedSourcePackage pkg)
          (SourceBackedFixedSTest.ofExpandedSourcePackage pkg fixedFront)
          lambda L -> Prop)
    (noExtraBulkScaleTerm : Prop)
    (noExtraBulkScaleTermHolds : noExtraBulkScaleTerm) :
    (trace_scale_no_missing_bulk_of_scalar_theorem_data
      ordinary noDefect rankPoleCdefOwnEveryRemainder noExtraBulkScaleTerm
      noExtraBulkScaleTermHolds).ordinaryTraceMatchesSupportSquare :=
  ordinary.ordinaryTraceMatchesSupportSquareHolds

theorem ordinary_trace_support_square_theorem_holds
    {pkg : Source.SourceObject.SourceObjectPackage}
    {fixedFront : ExpandedSourceFixedSTestFrontEnd pkg}
    {lambda : ℝ}
    {ccm25ArithmeticPackage :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        (RouteInputs.ofExpandedSourcePackage pkg).ccm25.weilSymbols
        pkg.commonTest.sourceTest lambda}
    (ordinary :
      OrdinaryTraceSupportSquareTheoremData pkg fixedFront lambda
        ccm25ArithmeticPackage) :
    ordinary.ordinaryTraceMatchesSupportSquare :=
  ordinary.ordinaryTraceMatchesSupportSquareHolds

theorem support_square_matches_no_defect_of_scalar_theorem_data
    {pkg : Source.SourceObject.SourceObjectPackage}
    {fixedFront : ExpandedSourceFixedSTestFrontEnd pkg}
    {lambda : ℝ}
    {ccm25ArithmeticPackage :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        (RouteInputs.ofExpandedSourcePackage pkg).ccm25.weilSymbols
        pkg.commonTest.sourceTest lambda}
    (ordinary :
      OrdinaryTraceSupportSquareTheoremData pkg fixedFront lambda
        ccm25ArithmeticPackage)
    (noDefect :
      NoDefectQWLambdaTheoremData pkg fixedFront lambda
        ccm25ArithmeticPackage)
    (rankPoleCdefOwnEveryRemainder :
      (L : RouteLedgers) ->
        SourceSignDefectClassification
          (RouteInputs.ofExpandedSourcePackage pkg)
          (SourceBackedFixedSTest.ofExpandedSourcePackage pkg fixedFront)
          lambda L -> Prop)
    (noExtraBulkScaleTerm : Prop)
    (noExtraBulkScaleTermHolds : noExtraBulkScaleTerm) :
    (trace_scale_no_missing_bulk_of_scalar_theorem_data
      ordinary noDefect rankPoleCdefOwnEveryRemainder noExtraBulkScaleTerm
      noExtraBulkScaleTermHolds).supportSquareMatchesNoDefectSource :=
  noDefect.supportSquareMatchesNoDefectSourceHolds

theorem no_defect_matches_qw_lambda_of_scalar_theorem_data
    {pkg : Source.SourceObject.SourceObjectPackage}
    {fixedFront : ExpandedSourceFixedSTestFrontEnd pkg}
    {lambda : ℝ}
    {ccm25ArithmeticPackage :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        (RouteInputs.ofExpandedSourcePackage pkg).ccm25.weilSymbols
        pkg.commonTest.sourceTest lambda}
    (ordinary :
      OrdinaryTraceSupportSquareTheoremData pkg fixedFront lambda
        ccm25ArithmeticPackage)
    (noDefect :
      NoDefectQWLambdaTheoremData pkg fixedFront lambda
        ccm25ArithmeticPackage)
    (rankPoleCdefOwnEveryRemainder :
      (L : RouteLedgers) ->
        SourceSignDefectClassification
          (RouteInputs.ofExpandedSourcePackage pkg)
          (SourceBackedFixedSTest.ofExpandedSourcePackage pkg fixedFront)
          lambda L -> Prop)
    (noExtraBulkScaleTerm : Prop)
    (noExtraBulkScaleTermHolds : noExtraBulkScaleTerm) :
    (trace_scale_no_missing_bulk_of_scalar_theorem_data
      ordinary noDefect rankPoleCdefOwnEveryRemainder noExtraBulkScaleTerm
      noExtraBulkScaleTermHolds).noDefectSourceMatchesQWLambda :=
  noDefect.noDefectSourceMatchesQWLambdaHolds

theorem support_square_no_defect_theorem_holds
    {pkg : Source.SourceObject.SourceObjectPackage}
    {fixedFront : ExpandedSourceFixedSTestFrontEnd pkg}
    {lambda : ℝ}
    {ccm25ArithmeticPackage :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        (RouteInputs.ofExpandedSourcePackage pkg).ccm25.weilSymbols
        pkg.commonTest.sourceTest lambda}
    (noDefect :
      NoDefectQWLambdaTheoremData pkg fixedFront lambda
        ccm25ArithmeticPackage) :
    noDefect.supportSquareMatchesNoDefectSource :=
  noDefect.supportSquareMatchesNoDefectSourceHolds

theorem no_defect_qw_lambda_theorem_holds
    {pkg : Source.SourceObject.SourceObjectPackage}
    {fixedFront : ExpandedSourceFixedSTestFrontEnd pkg}
    {lambda : ℝ}
    {ccm25ArithmeticPackage :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        (RouteInputs.ofExpandedSourcePackage pkg).ccm25.weilSymbols
        pkg.commonTest.sourceTest lambda}
    (noDefect :
      NoDefectQWLambdaTheoremData pkg fixedFront lambda
        ccm25ArithmeticPackage) :
    noDefect.noDefectSourceMatchesQWLambda :=
  noDefect.noDefectSourceMatchesQWLambdaHolds

/--
Goal 4A data for the trace front end.

This record does not prove trace legality or trace read-off.  It packages the
exact trace/read-off bridge inputs required by `ExpandedSourceTraceReadOffFrontEnd`
and pins them to the fixed package, fixed-test front end, and fixed lambda.

The `traceScaleNoMissingBulk` field is the Goal 4C target: it must stay separate
from trace legality and positive trace nonnegativity.
-/
structure TraceFrontEndData
    (pkg : Source.SourceObject.SourceObjectPackage)
    (fixedFront : ExpandedSourceFixedSTestFrontEnd pkg) where
  lambda : ℝ
  oneLtLambda : 1 < lambda
  ccm25ArithmeticPackage :
    Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
      (RouteInputs.ofExpandedSourcePackage pkg).ccm25.weilSymbols
      pkg.commonTest.sourceTest lambda
  testAndQuotientCompatibility :
    TestAndQuotientCompatibility
      (RouteInputs.ofExpandedSourcePackage pkg)
      (SourceBackedFixedSTest.ofExpandedSourcePackage pkg fixedFront)
  fixedSSupportSquareTransport :
    FixedSQuantizedSupportSquareTransport
      (RouteInputs.ofExpandedSourcePackage pkg)
      pkg.cc20Trace.sourceTraceTest
      (SourceBackedFixedSTest.ofExpandedSourcePackage pkg fixedFront)
      lambda
  fullTraceReadOffBridge :
    FullTraceReadOffBridgeContract
      (RouteInputs.ofExpandedSourcePackage pkg)
      pkg.cc20Trace.sourceTraceTest
      (SourceBackedFixedSTest.ofExpandedSourcePackage pkg fixedFront)
  restrictedTraceReadOffBridge :
    RestrictedTraceReadOffBridgeContract
      (RouteInputs.ofExpandedSourcePackage pkg)
      pkg.cc20Trace.sourceTraceTest
      (SourceBackedFixedSTest.ofExpandedSourcePackage pkg fixedFront)
      lambda
  traceScaleNoMissingBulk :
    TraceScaleNoMissingBulkData pkg fixedFront lambda ccm25ArithmeticPackage

namespace TraceFrontEndData

namespace SOData

theorem normalized_scalar_source_no_defect_eq_scalar
    (base : Source.SourceObjectTheoremBasePackage)
    (common : Source.SourceObjectCommonData base)
    (ccm24 : Source.SourceObject.CCM24SemilocalObjectPackage)
    (scalarSeed :
      Source.CC20Concrete.TraceScale.NormalizedScalarTraceScaleSymbols)
    (remainders :
      Source.CC20Concrete.TraceScale.CC20TracePackageRemainderData
        (Source.CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
          scalarSeed))
    (rhExit : Source.SourceObject.CC20RHExitObjectPackage)
    (bridges :
      Source.SourceObjectCrossObjectBridges base common
        (Source.SourceObjectExpandedRows.ofNormalizedScalarCC20Trace
          ccm24 scalarSeed remainders)
        rhExit)
    (g : scalarSeed.Test) :
    let pkg :=
      Source.sourceObjectPackageOfNormalizedScalarCC20Trace
        base common ccm24 scalarSeed remainders rhExit bridges
    pkg.cc20Trace.archimedeanSymbols.sourceNoDefectTrace g =
      scalarSeed.scalarTrace g :=
  Source.SourceObjectPackageOfData.normalized_scalar_cc20_trace_package_source_no_defect_eq_scalar
    base common ccm24 scalarSeed remainders rhExit bridges g

theorem normalized_scalar_trace_amplitude_sq_eq_scalar
    (base : Source.SourceObjectTheoremBasePackage)
    (common : Source.SourceObjectCommonData base)
    (ccm24 : Source.SourceObject.CCM24SemilocalObjectPackage)
    (scalarSeed :
      Source.CC20Concrete.TraceScale.NormalizedScalarTraceScaleSymbols)
    (remainders :
      Source.CC20Concrete.TraceScale.CC20TracePackageRemainderData
        (Source.CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
          scalarSeed))
    (rhExit : Source.SourceObject.CC20RHExitObjectPackage)
    (bridges :
      Source.SourceObjectCrossObjectBridges base common
        (Source.SourceObjectExpandedRows.ofNormalizedScalarCC20Trace
          ccm24 scalarSeed remainders)
        rhExit)
    (g : scalarSeed.Test) :
    let pkg :=
      Source.sourceObjectPackageOfNormalizedScalarCC20Trace
        base common ccm24 scalarSeed remainders rhExit bridges
    pkg.cc20Trace.archimedeanSymbols.supportSquareTrace g =
      scalarSeed.scalarTrace g := by
  exact
    Source.SourceObjectPackageOfData.normalized_scalar_cc20_trace_package_support_square_eq_scalar
      base common ccm24 scalarSeed remainders rhExit bridges g

end SOData

def toExpandedSourceTraceReadOffFrontEnd
    (pkg : Source.SourceObject.SourceObjectPackage)
    (fixedFront : ExpandedSourceFixedSTestFrontEnd pkg)
    (data : TraceFrontEndData pkg fixedFront) :
    ExpandedSourceTraceReadOffFrontEnd pkg fixedFront where
  lambda := data.lambda
  oneLtLambda := data.oneLtLambda
  ccm25ArithmeticPackage := data.ccm25ArithmeticPackage
  testAndQuotientCompatibility := data.testAndQuotientCompatibility
  fixedSSupportSquareTransport := data.fixedSSupportSquareTransport
  fullTraceReadOffBridge := data.fullTraceReadOffBridge
  restrictedTraceReadOffBridge := data.restrictedTraceReadOffBridge

def toSourceTraceReadOffData
    (pkg : Source.SourceObject.SourceObjectPackage)
    (fixedFront : ExpandedSourceFixedSTestFrontEnd pkg)
    (data : TraceFrontEndData pkg fixedFront) :
    SourceTraceReadOffData
      (RouteInputs.ofExpandedSourcePackage pkg)
      (SourceBackedFixedSTest.ofExpandedSourcePackage pkg fixedFront) :=
  SourceTraceReadOffData.ofExpandedSourcePackage pkg fixedFront
    (data.toExpandedSourceTraceReadOffFrontEnd pkg fixedFront)

theorem trace_front_lambda
    (pkg : Source.SourceObject.SourceObjectPackage)
    (fixedFront : ExpandedSourceFixedSTestFrontEnd pkg)
    (data : TraceFrontEndData pkg fixedFront) :
    (data.toExpandedSourceTraceReadOffFrontEnd pkg fixedFront).lambda =
      data.lambda :=
  rfl

theorem trace_front_arithmetic_package
    (pkg : Source.SourceObject.SourceObjectPackage)
    (fixedFront : ExpandedSourceFixedSTestFrontEnd pkg)
    (data : TraceFrontEndData pkg fixedFront) :
    (data.toExpandedSourceTraceReadOffFrontEnd
      pkg fixedFront).ccm25ArithmeticPackage =
      data.ccm25ArithmeticPackage :=
  rfl

theorem source_trace_archimedean_test
    (pkg : Source.SourceObject.SourceObjectPackage)
    (fixedFront : ExpandedSourceFixedSTestFrontEnd pkg)
    (data : TraceFrontEndData pkg fixedFront) :
    (data.toSourceTraceReadOffData pkg fixedFront).archimedeanTest =
      pkg.cc20Trace.sourceTraceTest :=
  rfl

theorem source_trace_lambda
    (pkg : Source.SourceObject.SourceObjectPackage)
    (fixedFront : ExpandedSourceFixedSTestFrontEnd pkg)
    (data : TraceFrontEndData pkg fixedFront) :
    (data.toSourceTraceReadOffData pkg fixedFront).lambda =
      data.lambda :=
  rfl

theorem source_trace_arithmetic_package
    (pkg : Source.SourceObject.SourceObjectPackage)
    (fixedFront : ExpandedSourceFixedSTestFrontEnd pkg)
    (data : TraceFrontEndData pkg fixedFront) :
    (data.toSourceTraceReadOffData pkg fixedFront).ccm25ArithmeticPackage =
      data.ccm25ArithmeticPackage :=
  rfl

theorem source_trace_test_and_quotient_compatibility
    (pkg : Source.SourceObject.SourceObjectPackage)
    (fixedFront : ExpandedSourceFixedSTestFrontEnd pkg)
    (data : TraceFrontEndData pkg fixedFront) :
    (data.toSourceTraceReadOffData
      pkg fixedFront).testAndQuotientCompatibility =
      data.testAndQuotientCompatibility :=
  rfl

theorem source_trace_support_square_transport
    (pkg : Source.SourceObject.SourceObjectPackage)
    (fixedFront : ExpandedSourceFixedSTestFrontEnd pkg)
    (data : TraceFrontEndData pkg fixedFront) :
    (data.toSourceTraceReadOffData
      pkg fixedFront).fixedSSupportSquareTransport =
      data.fixedSSupportSquareTransport :=
  rfl

theorem source_trace_full_trace_bridge
    (pkg : Source.SourceObject.SourceObjectPackage)
    (fixedFront : ExpandedSourceFixedSTestFrontEnd pkg)
    (data : TraceFrontEndData pkg fixedFront) :
    (data.toSourceTraceReadOffData pkg fixedFront).fullTraceReadOffBridge =
      data.fullTraceReadOffBridge :=
  rfl

theorem source_trace_restricted_trace_bridge
    (pkg : Source.SourceObject.SourceObjectPackage)
    (fixedFront : ExpandedSourceFixedSTestFrontEnd pkg)
    (data : TraceFrontEndData pkg fixedFront) :
    (data.toSourceTraceReadOffData
      pkg fixedFront).restrictedTraceReadOffBridge =
      data.restrictedTraceReadOffBridge :=
  rfl

def trace_scale_no_missing_bulk
    (pkg : Source.SourceObject.SourceObjectPackage)
    (fixedFront : ExpandedSourceFixedSTestFrontEnd pkg)
    (data : TraceFrontEndData pkg fixedFront) :
    TraceScaleNoMissingBulkData pkg fixedFront data.lambda
      data.ccm25ArithmeticPackage :=
  data.traceScaleNoMissingBulk

theorem trace_scale_no_missing_bulk_ordinary_trace
    (pkg : Source.SourceObject.SourceObjectPackage)
    (fixedFront : ExpandedSourceFixedSTestFrontEnd pkg)
    (data : TraceFrontEndData pkg fixedFront) :
    (trace_scale_no_missing_bulk pkg fixedFront data).ordinaryTraceMatchesSupportSquare =
      data.traceScaleNoMissingBulk.ordinaryTraceMatchesSupportSquare :=
  rfl

theorem trace_scale_no_missing_bulk_support_square
    (pkg : Source.SourceObject.SourceObjectPackage)
    (fixedFront : ExpandedSourceFixedSTestFrontEnd pkg)
    (data : TraceFrontEndData pkg fixedFront) :
    (trace_scale_no_missing_bulk pkg fixedFront data).supportSquareMatchesNoDefectSource =
      data.traceScaleNoMissingBulk.supportSquareMatchesNoDefectSource :=
  rfl

theorem trace_scale_no_missing_bulk_no_defect_qw_lambda
    (pkg : Source.SourceObject.SourceObjectPackage)
    (fixedFront : ExpandedSourceFixedSTestFrontEnd pkg)
    (data : TraceFrontEndData pkg fixedFront) :
    (trace_scale_no_missing_bulk pkg fixedFront data).noDefectSourceMatchesQWLambda =
      data.traceScaleNoMissingBulk.noDefectSourceMatchesQWLambda :=
  rfl

theorem trace_scale_no_missing_bulk_rank_pole_cdef
    (pkg : Source.SourceObject.SourceObjectPackage)
    (fixedFront : ExpandedSourceFixedSTestFrontEnd pkg)
    (data : TraceFrontEndData pkg fixedFront) :
    (trace_scale_no_missing_bulk pkg fixedFront data).rankPoleCdefOwnEveryRemainder =
      data.traceScaleNoMissingBulk.rankPoleCdefOwnEveryRemainder :=
  rfl

theorem trace_scale_no_missing_bulk_no_extra_bulk
    (pkg : Source.SourceObject.SourceObjectPackage)
    (fixedFront : ExpandedSourceFixedSTestFrontEnd pkg)
    (data : TraceFrontEndData pkg fixedFront) :
    (trace_scale_no_missing_bulk pkg fixedFront data).noExtraBulkScaleTerm =
      data.traceScaleNoMissingBulk.noExtraBulkScaleTerm :=
  rfl

theorem trace_scale_no_missing_bulk_no_extra_bulk_holds
    (pkg : Source.SourceObject.SourceObjectPackage)
    (fixedFront : ExpandedSourceFixedSTestFrontEnd pkg)
    (data : TraceFrontEndData pkg fixedFront) :
    (trace_scale_no_missing_bulk pkg fixedFront data).noExtraBulkScaleTerm :=
  data.traceScaleNoMissingBulk.noExtraBulkScaleTermHolds

def TraceScaleRankPoleCdefOwnership
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) (L : RouteLedgers) : Prop :=
  NoHiddenPositiveDefectOutsideCdef inputs g lambda L

theorem trace_scale_rank_pole_cdef_ownership_of_sign_defect_classification
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {L : RouteLedgers}
    (h : SourceSignDefectClassification inputs g lambda L) :
    TraceScaleRankPoleCdefOwnership inputs g lambda L :=
  h.noHiddenPositiveDefect

theorem trace_scale_rank_pole_identification_of_ownership
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {L : RouteLedgers}
    (h : TraceScaleRankPoleCdefOwnership inputs g lambda L) :
    SourceRankPoleLedgerIdentification inputs g lambda L :=
  row7_rank_pole_identification_of_no_hidden_positive_defect h

theorem trace_scale_cdef_domination_of_ownership
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {L : RouteLedgers}
    (h : TraceScaleRankPoleCdefOwnership inputs g lambda L) :
    SourceEndpointStripRemainderCdefDomination inputs g lambda L :=
  row7_endpoint_strip_cdef_domination_of_no_hidden_positive_defect h

theorem trace_scale_ledgers_cleared_of_ownership
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {L : RouteLedgers}
    (h : TraceScaleRankPoleCdefOwnership inputs g lambda L) :
    L.rankKilled ∧ L.poleKilled ∧ L.cdefExhausts :=
  ⟨row5_rank_ledger_of_rank_pole_identification
      (trace_scale_rank_pole_identification_of_ownership h),
    row5_pole_ledger_of_rank_pole_identification
      (trace_scale_rank_pole_identification_of_ownership h),
    row6_cdef_exhausts_of_cdef_domination
      (trace_scale_cdef_domination_of_ownership h)⟩

def trace_scale_owns_sign_defect_remainder
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {L : RouteLedgers}
    (_h : SourceSignDefectClassification inputs g lambda L) : Prop :=
  TraceScaleRankPoleCdefOwnership inputs g lambda L

theorem trace_scale_owns_sign_defect_remainder_holds
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {L : RouteLedgers}
    (h : SourceSignDefectClassification inputs g lambda L) :
    trace_scale_owns_sign_defect_remainder h :=
  trace_scale_rank_pole_cdef_ownership_of_sign_defect_classification h

structure TraceScaleNoExtraBulkContract
    (pkg : Source.SourceObject.SourceObjectPackage)
    (fixedFront : ExpandedSourceFixedSTestFrontEnd pkg)
    (lambda : ℝ)
    (ccm25ArithmeticPackage :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        (RouteInputs.ofExpandedSourcePackage pkg).ccm25.weilSymbols
        pkg.commonTest.sourceTest lambda) where
  traceScaleOwnership :
    ∀ (L : RouteLedgers),
      ∀ signDefectClassification :
        SourceSignDefectClassification
          (RouteInputs.ofExpandedSourcePackage pkg)
          (SourceBackedFixedSTest.ofExpandedSourcePackage pkg fixedFront)
          lambda L,
        trace_scale_owns_sign_defect_remainder signDefectClassification
  noExtraBulkScaleTerm : Prop
  noExtraBulkScaleTermHolds : noExtraBulkScaleTerm

def no_extra_bulk_contract_of_parts
    {pkg : Source.SourceObject.SourceObjectPackage}
    {fixedFront : ExpandedSourceFixedSTestFrontEnd pkg}
    {lambda : ℝ}
    {ccm25ArithmeticPackage :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        (RouteInputs.ofExpandedSourcePackage pkg).ccm25.weilSymbols
        pkg.commonTest.sourceTest lambda}
    (noExtraBulkScaleTerm : Prop)
    (noExtraBulkScaleTermHolds : noExtraBulkScaleTerm) :
    TraceScaleNoExtraBulkContract pkg fixedFront lambda ccm25ArithmeticPackage where
  traceScaleOwnership := by
    intro L signDefectClassification
    exact trace_scale_owns_sign_defect_remainder_holds signDefectClassification
  noExtraBulkScaleTerm := noExtraBulkScaleTerm
  noExtraBulkScaleTermHolds := noExtraBulkScaleTermHolds

theorem no_extra_bulk_contract_owns_sign_defect
    {pkg : Source.SourceObject.SourceObjectPackage}
    {fixedFront : ExpandedSourceFixedSTestFrontEnd pkg}
    {lambda : ℝ}
    {ccm25ArithmeticPackage :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        (RouteInputs.ofExpandedSourcePackage pkg).ccm25.weilSymbols
        pkg.commonTest.sourceTest lambda}
    {L : RouteLedgers}
    {signDefectClassification :
      SourceSignDefectClassification
        (RouteInputs.ofExpandedSourcePackage pkg)
        (SourceBackedFixedSTest.ofExpandedSourcePackage pkg fixedFront)
        lambda L}
    (h :
      TraceScaleNoExtraBulkContract pkg fixedFront lambda
        ccm25ArithmeticPackage) :
    trace_scale_owns_sign_defect_remainder signDefectClassification :=
  h.traceScaleOwnership L signDefectClassification

theorem no_extra_bulk_contract_holds
    {pkg : Source.SourceObject.SourceObjectPackage}
    {fixedFront : ExpandedSourceFixedSTestFrontEnd pkg}
    {lambda : ℝ}
    {ccm25ArithmeticPackage :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        (RouteInputs.ofExpandedSourcePackage pkg).ccm25.weilSymbols
        pkg.commonTest.sourceTest lambda}
    (h :
      TraceScaleNoExtraBulkContract pkg fixedFront lambda
        ccm25ArithmeticPackage) :
    h.noExtraBulkScaleTerm :=
  h.noExtraBulkScaleTermHolds

theorem source_trace_weil_test_eq_fixed_front
    (pkg : Source.SourceObject.SourceObjectPackage)
    (fixedFront : ExpandedSourceFixedSTestFrontEnd pkg)
    (_data : TraceFrontEndData pkg fixedFront) :
    (SourceBackedFixedSTest.ofExpandedSourcePackage
      pkg fixedFront).weilTest =
      pkg.commonTest.sourceTest :=
  rfl

def ordinary_trace_support_square_theorem_data_of_cc20
    {pkg : Source.SourceObject.SourceObjectPackage}
    {fixedFront : ExpandedSourceFixedSTestFrontEnd pkg}
    {traceData : TraceFrontEndData pkg fixedFront}
    (h :
      CC20OrdinaryTraceSupportSquareTheoremData
        (RouteInputs.ofExpandedSourcePackage pkg)
        (SourceBackedFixedSTest.ofExpandedSourcePackage pkg fixedFront)
        (traceData.toSourceTraceReadOffData pkg fixedFront)) :
    OrdinaryTraceSupportSquareTheoremData pkg fixedFront traceData.lambda
      traceData.ccm25ArithmeticPackage where
  ordinaryTraceMatchesSupportSquare := h.ordinaryTraceMatchesSupportSquare
  ordinaryTraceMatchesSupportSquareHolds :=
    h.ordinaryTraceMatchesSupportSquareHolds

def ordinary_trace_support_square_theorem_data_of_source_interface
    {pkg : Source.SourceObject.SourceObjectPackage}
    {fixedFront : ExpandedSourceFixedSTestFrontEnd pkg}
    {traceData : TraceFrontEndData pkg fixedFront} :
    OrdinaryTraceSupportSquareTheoremData pkg fixedFront traceData.lambda
      traceData.ccm25ArithmeticPackage where
  ordinaryTraceMatchesSupportSquare :=
    (RouteInputs.ofExpandedSourcePackage pkg).cc20.archimedeanSymbols.positiveTrace
      (traceData.toSourceTraceReadOffData pkg fixedFront).archimedeanTest =
    (RouteInputs.ofExpandedSourcePackage pkg).cc20.archimedeanSymbols.supportSquareTrace
      (traceData.toSourceTraceReadOffData pkg fixedFront).archimedeanTest
  ordinaryTraceMatchesSupportSquareHolds :=
    (RouteInputs.ofExpandedSourcePackage pkg).cc20.ordinaryTraceSupportSquare
      (traceData.toSourceTraceReadOffData pkg fixedFront).archimedeanTest
      (cc20_trace_legality_of_source_trace_data
        (traceData.toSourceTraceReadOffData pkg fixedFront)).traceClass
      (cc20_trace_legality_of_source_trace_data
        (traceData.toSourceTraceReadOffData pkg fixedFront)).cyclicLegal

theorem ordinary_trace_support_square_source_interface_holds
    {pkg : Source.SourceObject.SourceObjectPackage}
    {fixedFront : ExpandedSourceFixedSTestFrontEnd pkg}
    {traceData : TraceFrontEndData pkg fixedFront} :
    (ordinary_trace_support_square_theorem_data_of_source_interface
      (pkg := pkg) (fixedFront := fixedFront)
      (traceData := traceData)).ordinaryTraceMatchesSupportSquare :=
  (ordinary_trace_support_square_theorem_data_of_source_interface
    (pkg := pkg) (fixedFront := fixedFront)
    (traceData := traceData)).ordinaryTraceMatchesSupportSquareHolds

theorem ordinary_trace_support_square_constructor_uses_cc20_statement
    {pkg : Source.SourceObject.SourceObjectPackage}
    {fixedFront : ExpandedSourceFixedSTestFrontEnd pkg}
    {traceData : TraceFrontEndData pkg fixedFront}
    (h :
      CC20OrdinaryTraceSupportSquareTheoremData
        (RouteInputs.ofExpandedSourcePackage pkg)
        (SourceBackedFixedSTest.ofExpandedSourcePackage pkg fixedFront)
        (traceData.toSourceTraceReadOffData pkg fixedFront)) :
    (ordinary_trace_support_square_theorem_data_of_cc20 h).ordinaryTraceMatchesSupportSquare =
      h.ordinaryTraceMatchesSupportSquare :=
  rfl

theorem ordinary_trace_support_square_constructor_holds
    {pkg : Source.SourceObject.SourceObjectPackage}
    {fixedFront : ExpandedSourceFixedSTestFrontEnd pkg}
    {traceData : TraceFrontEndData pkg fixedFront}
    (h :
      CC20OrdinaryTraceSupportSquareTheoremData
        (RouteInputs.ofExpandedSourcePackage pkg)
        (SourceBackedFixedSTest.ofExpandedSourcePackage pkg fixedFront)
        (traceData.toSourceTraceReadOffData pkg fixedFront)) :
    (ordinary_trace_support_square_theorem_data_of_cc20 h).ordinaryTraceMatchesSupportSquare :=
  h.ordinaryTraceMatchesSupportSquareHolds

def no_defect_qw_lambda_theorem_data_of_cc20
    {pkg : Source.SourceObject.SourceObjectPackage}
    {fixedFront : ExpandedSourceFixedSTestFrontEnd pkg}
    {traceData : TraceFrontEndData pkg fixedFront}
    (h :
      CC20NoDefectQWLambdaTheoremData
        (RouteInputs.ofExpandedSourcePackage pkg)
        (SourceBackedFixedSTest.ofExpandedSourcePackage pkg fixedFront)
        (traceData.toSourceTraceReadOffData pkg fixedFront)) :
    NoDefectQWLambdaTheoremData pkg fixedFront traceData.lambda
      traceData.ccm25ArithmeticPackage where
  supportSquareMatchesNoDefectSource := h.supportSquareMatchesNoDefectSource
  noDefectSourceMatchesQWLambda := h.noDefectSourceMatchesQWLambda
  supportSquareMatchesNoDefectSourceHolds :=
    h.supportSquareMatchesNoDefectSourceHolds
  noDefectSourceMatchesQWLambdaHolds :=
    h.noDefectSourceMatchesQWLambdaHolds

def no_defect_qw_lambda_theorem_data_of_source_trace_square
    {pkg : Source.SourceObject.SourceObjectPackage}
    {fixedFront : ExpandedSourceFixedSTestFrontEnd pkg}
    {traceData : TraceFrontEndData pkg fixedFront}
    (noDefectSourceMatchesQWLambda : Prop)
    (noDefectSourceMatchesQWLambdaHolds : noDefectSourceMatchesQWLambda) :
    NoDefectQWLambdaTheoremData pkg fixedFront traceData.lambda
      traceData.ccm25ArithmeticPackage where
  supportSquareMatchesNoDefectSource :=
    CC20NoDefectSourceReadOff
      (RouteInputs.ofExpandedSourcePackage pkg)
      (traceData.toSourceTraceReadOffData pkg fixedFront).archimedeanTest
  noDefectSourceMatchesQWLambda := noDefectSourceMatchesQWLambda
  supportSquareMatchesNoDefectSourceHolds :=
    (cc20_trace_square_of_source_trace_data
      (traceData.toSourceTraceReadOffData pkg fixedFront)).noDefectSourceReadOff
  noDefectSourceMatchesQWLambdaHolds := noDefectSourceMatchesQWLambdaHolds

theorem support_square_no_defect_source_interface_holds
    {pkg : Source.SourceObject.SourceObjectPackage}
    {fixedFront : ExpandedSourceFixedSTestFrontEnd pkg}
    {traceData : TraceFrontEndData pkg fixedFront}
    {noDefectSourceMatchesQWLambda : Prop}
    (noDefectSourceMatchesQWLambdaHolds : noDefectSourceMatchesQWLambda) :
    (no_defect_qw_lambda_theorem_data_of_source_trace_square
      (pkg := pkg) (fixedFront := fixedFront) (traceData := traceData)
      noDefectSourceMatchesQWLambda
      noDefectSourceMatchesQWLambdaHolds).supportSquareMatchesNoDefectSource :=
  (no_defect_qw_lambda_theorem_data_of_source_trace_square
    (pkg := pkg) (fixedFront := fixedFront) (traceData := traceData)
    noDefectSourceMatchesQWLambda
    noDefectSourceMatchesQWLambdaHolds).supportSquareMatchesNoDefectSourceHolds

theorem no_defect_qw_lambda_source_trace_square_keeps_qw_lambda_obligation
    {pkg : Source.SourceObject.SourceObjectPackage}
    {fixedFront : ExpandedSourceFixedSTestFrontEnd pkg}
    {traceData : TraceFrontEndData pkg fixedFront}
    {noDefectSourceMatchesQWLambda : Prop}
    (noDefectSourceMatchesQWLambdaHolds : noDefectSourceMatchesQWLambda) :
    (no_defect_qw_lambda_theorem_data_of_source_trace_square
      (pkg := pkg) (fixedFront := fixedFront) (traceData := traceData)
      noDefectSourceMatchesQWLambda
      noDefectSourceMatchesQWLambdaHolds).noDefectSourceMatchesQWLambda =
      noDefectSourceMatchesQWLambda :=
  rfl

def cc20_no_defect_qw_lambda_theorem_data_of_source_interface
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    (traceData : SourceTraceReadOffData inputs g) :
    CC20NoDefectQWLambdaTheoremData inputs g traceData where
  traceSquareReadOff := cc20_trace_square_of_source_trace_data traceData
  restrictedTraceReadOffSource :=
    restricted_trace_read_off_of_source_trace_data traceData
  supportSquareMatchesNoDefectSource :=
    CC20NoDefectSourceReadOff inputs traceData.archimedeanTest
  noDefectSourceMatchesQWLambda :=
    inputs.cc20.archimedeanSymbols.sourceNoDefectTrace
        traceData.archimedeanTest =
      inputs.ccm25.weilSymbols.qwLambda traceData.lambda g.weilTest
        g.weilTest
  supportSquareMatchesNoDefectSourceHolds :=
    (cc20_trace_square_of_source_trace_data traceData).noDefectSourceReadOff
  noDefectSourceMatchesQWLambdaHolds :=
    (cc20_trace_square_of_source_trace_data
      traceData).noDefectSourceReadOff.symm.trans
      (restricted_trace_read_off_of_source_trace_data
        traceData).restrictedTraceReadOffEquality
  traceSquareMatchesData := rfl

def no_defect_qw_lambda_theorem_data_of_source_interface
    {pkg : Source.SourceObject.SourceObjectPackage}
    {fixedFront : ExpandedSourceFixedSTestFrontEnd pkg}
    {traceData : TraceFrontEndData pkg fixedFront} :
    NoDefectQWLambdaTheoremData pkg fixedFront traceData.lambda
      traceData.ccm25ArithmeticPackage :=
  no_defect_qw_lambda_theorem_data_of_cc20
    (cc20_no_defect_qw_lambda_theorem_data_of_source_interface
      (traceData.toSourceTraceReadOffData pkg fixedFront))

theorem support_square_no_defect_source_interface_full_holds
    {pkg : Source.SourceObject.SourceObjectPackage}
    {fixedFront : ExpandedSourceFixedSTestFrontEnd pkg}
    {traceData : TraceFrontEndData pkg fixedFront} :
    (no_defect_qw_lambda_theorem_data_of_source_interface
      (pkg := pkg) (fixedFront := fixedFront)
      (traceData := traceData)).supportSquareMatchesNoDefectSource :=
  (no_defect_qw_lambda_theorem_data_of_source_interface
    (pkg := pkg) (fixedFront := fixedFront)
    (traceData := traceData)).supportSquareMatchesNoDefectSourceHolds

theorem no_defect_qw_lambda_source_interface_holds
    {pkg : Source.SourceObject.SourceObjectPackage}
    {fixedFront : ExpandedSourceFixedSTestFrontEnd pkg}
    {traceData : TraceFrontEndData pkg fixedFront} :
    (no_defect_qw_lambda_theorem_data_of_source_interface
      (pkg := pkg) (fixedFront := fixedFront)
      (traceData := traceData)).noDefectSourceMatchesQWLambda :=
  (no_defect_qw_lambda_theorem_data_of_source_interface
    (pkg := pkg) (fixedFront := fixedFront)
    (traceData := traceData)).noDefectSourceMatchesQWLambdaHolds

theorem no_defect_qw_lambda_constructor_uses_support_square_statement
    {pkg : Source.SourceObject.SourceObjectPackage}
    {fixedFront : ExpandedSourceFixedSTestFrontEnd pkg}
    {traceData : TraceFrontEndData pkg fixedFront}
    (h :
      CC20NoDefectQWLambdaTheoremData
        (RouteInputs.ofExpandedSourcePackage pkg)
        (SourceBackedFixedSTest.ofExpandedSourcePackage pkg fixedFront)
        (traceData.toSourceTraceReadOffData pkg fixedFront)) :
    (no_defect_qw_lambda_theorem_data_of_cc20 h).supportSquareMatchesNoDefectSource =
      h.supportSquareMatchesNoDefectSource :=
  rfl

theorem no_defect_qw_lambda_constructor_uses_qw_lambda_statement
    {pkg : Source.SourceObject.SourceObjectPackage}
    {fixedFront : ExpandedSourceFixedSTestFrontEnd pkg}
    {traceData : TraceFrontEndData pkg fixedFront}
    (h :
      CC20NoDefectQWLambdaTheoremData
        (RouteInputs.ofExpandedSourcePackage pkg)
        (SourceBackedFixedSTest.ofExpandedSourcePackage pkg fixedFront)
        (traceData.toSourceTraceReadOffData pkg fixedFront)) :
    (no_defect_qw_lambda_theorem_data_of_cc20 h).noDefectSourceMatchesQWLambda =
      h.noDefectSourceMatchesQWLambda :=
  rfl

/--
Package-data specialization of the Goal 4A constructor.
-/
def toExpandedSourceTraceReadOffFrontEndOfPackageData
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
          base common rows rhExit bridges fixedData)) :
    ExpandedSourceTraceReadOffFrontEnd
      (Source.sourceObjectPackageOfData base common rows rhExit bridges)
      (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfPackageData
        base common rows rhExit bridges fixedData) :=
  traceData.toExpandedSourceTraceReadOffFrontEnd
    (Source.sourceObjectPackageOfData base common rows rhExit bridges)
    (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfPackageData
      base common rows rhExit bridges fixedData)

def toSourceTraceReadOffDataOfPackageData
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
          base common rows rhExit bridges fixedData)) :
    SourceTraceReadOffData
      (RouteInputs.ofExpandedSourcePackage
        (Source.sourceObjectPackageOfData base common rows rhExit bridges))
      (SourceBackedFixedSTest.ofExpandedSourcePackage
        (Source.sourceObjectPackageOfData base common rows rhExit bridges)
        (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfPackageData
          base common rows rhExit bridges fixedData)) :=
  traceData.toSourceTraceReadOffData
    (Source.sourceObjectPackageOfData base common rows rhExit bridges)
    (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfPackageData
      base common rows rhExit bridges fixedData)

theorem package_data_source_trace_archimedean_test
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
          base common rows rhExit bridges fixedData)) :
    (toSourceTraceReadOffDataOfPackageData
      base common rows rhExit bridges fixedData traceData).archimedeanTest =
      rows.cc20Trace.sourceTraceTest :=
  rfl

theorem package_data_source_trace_lambda
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
          base common rows rhExit bridges fixedData)) :
    (toSourceTraceReadOffDataOfPackageData
      base common rows rhExit bridges fixedData traceData).lambda =
      traceData.lambda :=
  rfl

theorem package_data_source_trace_arithmetic_package
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
          base common rows rhExit bridges fixedData)) :
    (toSourceTraceReadOffDataOfPackageData
      base common rows rhExit bridges fixedData traceData).ccm25ArithmeticPackage =
      traceData.ccm25ArithmeticPackage :=
  rfl

theorem package_data_source_trace_weil_test_eq_common
    (base : Source.SourceObjectTheoremBasePackage)
    (common : Source.SourceObjectCommonData base)
    (rows : Source.SourceObjectExpandedRows base common)
    (rhExit : Source.SourceObject.CC20RHExitObjectPackage)
    (bridges : Source.SourceObjectCrossObjectBridges base common rows rhExit)
    (fixedData :
      FixedSTestObligationData
        (Source.sourceObjectPackageOfData base common rows rhExit bridges))
    (_traceData :
      TraceFrontEndData
        (Source.sourceObjectPackageOfData base common rows rhExit bridges)
        (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfPackageData
          base common rows rhExit bridges fixedData)) :
    (SourceBackedFixedSTest.ofExpandedSourcePackage
      (Source.sourceObjectPackageOfData base common rows rhExit bridges)
      (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfPackageData
        base common rows rhExit bridges fixedData)).weilTest =
      common.commonTest.sourceTest :=
  rfl

def toExpandedSourceTraceReadOffFrontEndOfNormalizedPackage
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
          fixedData)) :
    ExpandedSourceTraceReadOffFrontEnd
      (Source.sourceObjectPackageOfNormalizedCC20Trace
        base common ccm24 normalizedSeed remainders rhExit bridges)
      (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
        base common ccm24 normalizedSeed remainders rhExit bridges
        fixedData) :=
  traceData.toExpandedSourceTraceReadOffFrontEnd
    (Source.sourceObjectPackageOfNormalizedCC20Trace
      base common ccm24 normalizedSeed remainders rhExit bridges)
    (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
      base common ccm24 normalizedSeed remainders rhExit bridges fixedData)

noncomputable def toExpandedSourceTraceReadOffFrontEndOfNormalizedScalarPackage
    (base : Source.SourceObjectTheoremBasePackage)
    (common : Source.SourceObjectCommonData base)
    (ccm24 : Source.SourceObject.CCM24SemilocalObjectPackage)
    (scalarSeed :
      Source.CC20Concrete.TraceScale.NormalizedScalarTraceScaleSymbols)
    (remainders :
      Source.CC20Concrete.TraceScale.CC20TracePackageRemainderData
        (Source.CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
          scalarSeed))
    (rhExit : Source.SourceObject.CC20RHExitObjectPackage)
    (bridges :
      Source.SourceObjectCrossObjectBridges base common
        (Source.SourceObjectExpandedRows.ofNormalizedScalarCC20Trace
          ccm24 scalarSeed remainders)
        rhExit)
    (fixedData :
      FixedSTestObligationData
        (Source.sourceObjectPackageOfNormalizedScalarCC20Trace
          base common ccm24 scalarSeed remainders rhExit bridges))
    (traceData :
      TraceFrontEndData
        (Source.sourceObjectPackageOfNormalizedScalarCC20Trace
          base common ccm24 scalarSeed remainders rhExit bridges)
        (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedScalarPackage
          base common ccm24 scalarSeed remainders rhExit bridges
          fixedData)) :
    ExpandedSourceTraceReadOffFrontEnd
      (Source.sourceObjectPackageOfNormalizedScalarCC20Trace
        base common ccm24 scalarSeed remainders rhExit bridges)
      (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedScalarPackage
        base common ccm24 scalarSeed remainders rhExit bridges
        fixedData) :=
  traceData.toExpandedSourceTraceReadOffFrontEnd
    (Source.sourceObjectPackageOfNormalizedScalarCC20Trace
      base common ccm24 scalarSeed remainders rhExit bridges)
    (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedScalarPackage
      base common ccm24 scalarSeed remainders rhExit bridges fixedData)

def toSourceTraceReadOffDataOfNormalizedPackage
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
          fixedData)) :
    SourceTraceReadOffData
      (RouteInputs.ofExpandedSourcePackage
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges))
      (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
        base common ccm24 normalizedSeed remainders rhExit bridges
        fixedData) :=
  traceData.toSourceTraceReadOffData
    (Source.sourceObjectPackageOfNormalizedCC20Trace
      base common ccm24 normalizedSeed remainders rhExit bridges)
    (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
      base common ccm24 normalizedSeed remainders rhExit bridges fixedData)

noncomputable def toSourceTraceReadOffDataOfNormalizedScalarPackage
    (base : Source.SourceObjectTheoremBasePackage)
    (common : Source.SourceObjectCommonData base)
    (ccm24 : Source.SourceObject.CCM24SemilocalObjectPackage)
    (scalarSeed :
      Source.CC20Concrete.TraceScale.NormalizedScalarTraceScaleSymbols)
    (remainders :
      Source.CC20Concrete.TraceScale.CC20TracePackageRemainderData
        (Source.CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
          scalarSeed))
    (rhExit : Source.SourceObject.CC20RHExitObjectPackage)
    (bridges :
      Source.SourceObjectCrossObjectBridges base common
        (Source.SourceObjectExpandedRows.ofNormalizedScalarCC20Trace
          ccm24 scalarSeed remainders)
        rhExit)
    (fixedData :
      FixedSTestObligationData
        (Source.sourceObjectPackageOfNormalizedScalarCC20Trace
          base common ccm24 scalarSeed remainders rhExit bridges))
    (traceData :
      TraceFrontEndData
        (Source.sourceObjectPackageOfNormalizedScalarCC20Trace
          base common ccm24 scalarSeed remainders rhExit bridges)
        (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedScalarPackage
          base common ccm24 scalarSeed remainders rhExit bridges
          fixedData)) :
    SourceTraceReadOffData
      (RouteInputs.ofExpandedSourcePackage
        (Source.sourceObjectPackageOfNormalizedScalarCC20Trace
          base common ccm24 scalarSeed remainders rhExit bridges))
      (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedScalarPackage
        base common ccm24 scalarSeed remainders rhExit bridges
        fixedData) :=
  traceData.toSourceTraceReadOffData
    (Source.sourceObjectPackageOfNormalizedScalarCC20Trace
      base common ccm24 scalarSeed remainders rhExit bridges)
    (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedScalarPackage
      base common ccm24 scalarSeed remainders rhExit bridges fixedData)

theorem normalized_scalar_package_source_trace_source_no_defect_eq_scalar
    (base : Source.SourceObjectTheoremBasePackage)
    (common : Source.SourceObjectCommonData base)
    (ccm24 : Source.SourceObject.CCM24SemilocalObjectPackage)
    (scalarSeed :
      Source.CC20Concrete.TraceScale.NormalizedScalarTraceScaleSymbols)
    (remainders :
      Source.CC20Concrete.TraceScale.CC20TracePackageRemainderData
        (Source.CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
          scalarSeed))
    (rhExit : Source.SourceObject.CC20RHExitObjectPackage)
    (bridges :
      Source.SourceObjectCrossObjectBridges base common
        (Source.SourceObjectExpandedRows.ofNormalizedScalarCC20Trace
          ccm24 scalarSeed remainders)
        rhExit)
    (fixedData :
      FixedSTestObligationData
        (Source.sourceObjectPackageOfNormalizedScalarCC20Trace
          base common ccm24 scalarSeed remainders rhExit bridges))
    (traceData :
      TraceFrontEndData
        (Source.sourceObjectPackageOfNormalizedScalarCC20Trace
          base common ccm24 scalarSeed remainders rhExit bridges)
        (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedScalarPackage
          base common ccm24 scalarSeed remainders rhExit bridges
          fixedData)) :
    let sourceTrace :=
      toSourceTraceReadOffDataOfNormalizedScalarPackage
        base common ccm24 scalarSeed remainders rhExit bridges fixedData
        traceData
    let inputs :=
      RouteInputs.ofExpandedSourcePackage
        (Source.sourceObjectPackageOfNormalizedScalarCC20Trace
          base common ccm24 scalarSeed remainders rhExit bridges)
    inputs.cc20.archimedeanSymbols.sourceNoDefectTrace
        sourceTrace.archimedeanTest =
      scalarSeed.scalarTrace sourceTrace.archimedeanTest := by
  intro sourceTrace inputs
  rfl

theorem normalized_scalar_package_source_trace_support_square_eq_scalar
    (base : Source.SourceObjectTheoremBasePackage)
    (common : Source.SourceObjectCommonData base)
    (ccm24 : Source.SourceObject.CCM24SemilocalObjectPackage)
    (scalarSeed :
      Source.CC20Concrete.TraceScale.NormalizedScalarTraceScaleSymbols)
    (remainders :
      Source.CC20Concrete.TraceScale.CC20TracePackageRemainderData
        (Source.CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
          scalarSeed))
    (rhExit : Source.SourceObject.CC20RHExitObjectPackage)
    (bridges :
      Source.SourceObjectCrossObjectBridges base common
        (Source.SourceObjectExpandedRows.ofNormalizedScalarCC20Trace
          ccm24 scalarSeed remainders)
        rhExit)
    (fixedData :
      FixedSTestObligationData
        (Source.sourceObjectPackageOfNormalizedScalarCC20Trace
          base common ccm24 scalarSeed remainders rhExit bridges))
    (traceData :
      TraceFrontEndData
        (Source.sourceObjectPackageOfNormalizedScalarCC20Trace
          base common ccm24 scalarSeed remainders rhExit bridges)
        (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedScalarPackage
          base common ccm24 scalarSeed remainders rhExit bridges
          fixedData)) :
    let sourceTrace :=
      toSourceTraceReadOffDataOfNormalizedScalarPackage
        base common ccm24 scalarSeed remainders rhExit bridges fixedData
        traceData
    let inputs :=
      RouteInputs.ofExpandedSourcePackage
        (Source.sourceObjectPackageOfNormalizedScalarCC20Trace
          base common ccm24 scalarSeed remainders rhExit bridges)
    inputs.cc20.archimedeanSymbols.supportSquareTrace
        sourceTrace.archimedeanTest =
      scalarSeed.scalarTrace sourceTrace.archimedeanTest := by
  intro sourceTrace inputs
  rfl

def ordinaryTraceSupportSquareTheoremDataOfNormalizedPackage
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
          fixedData)) :
    OrdinaryTraceSupportSquareTheoremData
      (Source.sourceObjectPackageOfNormalizedCC20Trace
        base common ccm24 normalizedSeed remainders rhExit bridges)
      (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData)
      traceData.lambda traceData.ccm25ArithmeticPackage where
  ordinaryTraceMatchesSupportSquare :=
    let pkg :=
      Source.sourceObjectPackageOfNormalizedCC20Trace
        base common ccm24 normalizedSeed remainders rhExit bridges
    let fixedFront :=
      FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
    let sourceTrace := traceData.toSourceTraceReadOffData pkg fixedFront
    let inputs := RouteInputs.ofExpandedSourcePackage pkg
    inputs.cc20.archimedeanSymbols.positiveTrace sourceTrace.archimedeanTest =
      inputs.cc20.archimedeanSymbols.supportSquareTrace
        sourceTrace.archimedeanTest
  ordinaryTraceMatchesSupportSquareHolds :=
    let sourceTrace :=
      toSourceTraceReadOffDataOfNormalizedPackage
        base common ccm24 normalizedSeed remainders rhExit bridges
        fixedData traceData
    let legality := cc20_trace_legality_of_source_trace_data sourceTrace
    Source.SourceObjectPackageOfData.normalized_cc20_trace_package_ordinary_trace_support_square
      base common ccm24 normalizedSeed remainders rhExit bridges
      sourceTrace.archimedeanTest legality.traceClass legality.cyclicLegal

theorem normalized_package_ordinary_trace_support_square_holds
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
          fixedData)) :
    (ordinaryTraceSupportSquareTheoremDataOfNormalizedPackage
      base common ccm24 normalizedSeed remainders rhExit bridges
      fixedData traceData).ordinaryTraceMatchesSupportSquare :=
  (ordinaryTraceSupportSquareTheoremDataOfNormalizedPackage
    base common ccm24 normalizedSeed remainders rhExit bridges
    fixedData traceData).ordinaryTraceMatchesSupportSquareHolds

def noDefectQWLambdaTheoremDataOfNormalizedPackageSupportSquare
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
    (noDefectSourceMatchesQWLambda : Prop)
    (noDefectSourceMatchesQWLambdaHolds :
      noDefectSourceMatchesQWLambda) :
    NoDefectQWLambdaTheoremData
      (Source.sourceObjectPackageOfNormalizedCC20Trace
        base common ccm24 normalizedSeed remainders rhExit bridges)
      (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData)
      traceData.lambda traceData.ccm25ArithmeticPackage where
  supportSquareMatchesNoDefectSource :=
    let sourceTrace :=
      toSourceTraceReadOffDataOfNormalizedPackage
        base common ccm24 normalizedSeed remainders rhExit bridges
        fixedData traceData
    let inputs :=
      RouteInputs.ofExpandedSourcePackage
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges)
    inputs.cc20.archimedeanSymbols.supportSquareTrace
        sourceTrace.archimedeanTest =
      inputs.cc20.archimedeanSymbols.sourceNoDefectTrace
        sourceTrace.archimedeanTest
  noDefectSourceMatchesQWLambda := noDefectSourceMatchesQWLambda
  supportSquareMatchesNoDefectSourceHolds :=
    let sourceTrace :=
      toSourceTraceReadOffDataOfNormalizedPackage
        base common ccm24 normalizedSeed remainders rhExit bridges
        fixedData traceData
    let legality := cc20_trace_legality_of_source_trace_data sourceTrace
    Source.SourceObjectPackageOfData.normalized_cc20_trace_package_support_square_no_defect
      base common ccm24 normalizedSeed remainders rhExit bridges
      sourceTrace.archimedeanTest legality.traceClass legality.cyclicLegal
  noDefectSourceMatchesQWLambdaHolds := noDefectSourceMatchesQWLambdaHolds

theorem normalized_package_support_square_no_defect_holds
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
    {noDefectSourceMatchesQWLambda : Prop}
    (noDefectSourceMatchesQWLambdaHolds :
      noDefectSourceMatchesQWLambda) :
    (noDefectQWLambdaTheoremDataOfNormalizedPackageSupportSquare
      base common ccm24 normalizedSeed remainders rhExit bridges
      fixedData traceData noDefectSourceMatchesQWLambda
      noDefectSourceMatchesQWLambdaHolds).supportSquareMatchesNoDefectSource :=
  (noDefectQWLambdaTheoremDataOfNormalizedPackageSupportSquare
    base common ccm24 normalizedSeed remainders rhExit bridges
    fixedData traceData noDefectSourceMatchesQWLambda
    noDefectSourceMatchesQWLambdaHolds).supportSquareMatchesNoDefectSourceHolds

theorem normalized_package_no_defect_qw_lambda_obligation_preserved
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
    {noDefectSourceMatchesQWLambda : Prop}
    (noDefectSourceMatchesQWLambdaHolds :
      noDefectSourceMatchesQWLambda) :
    (noDefectQWLambdaTheoremDataOfNormalizedPackageSupportSquare
      base common ccm24 normalizedSeed remainders rhExit bridges
      fixedData traceData noDefectSourceMatchesQWLambda
      noDefectSourceMatchesQWLambdaHolds).noDefectSourceMatchesQWLambda =
      noDefectSourceMatchesQWLambda := by
  rfl

/--
Checklist item 3 early skeleton in package-form coordinates.

`restrictedTraceReadOffSourceOfNormalizedPackage` appears before the named
`NormalizedRestrictedScalarNormalForm`, so this theorem states the same
no-comparison bridge against the unfolded CCM25 package expression. The later
normal-form theorem gives the roadmap-facing name.
-/
theorem normalized_source_no_defect_reduces_to_package_formula
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
          fixedData)) :
    let sourceTrace :=
      toSourceTraceReadOffDataOfNormalizedPackage
        base common ccm24 normalizedSeed remainders rhExit bridges
        fixedData traceData
    let inputs :=
      RouteInputs.ofExpandedSourcePackage
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges)
    let g :=
      FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
    inputs.cc20.archimedeanSymbols.sourceNoDefectTrace
        sourceTrace.archimedeanTest =
      inputs.ccm25.weilSymbols.archimedeanTerm
          (inputs.ccm25.weilSymbols.convolutionStar g.weilTest g.weilTest) +
        inputs.ccm25.weilSymbols.polePairing g.weilTest -
          Source.CCM25Concrete.Package.source_restricted_finite_prime_evaluator_sum
            sourceTrace.ccm25ArithmeticPackage := by
  intro sourceTrace inputs g
  calc
    inputs.cc20.archimedeanSymbols.sourceNoDefectTrace
        sourceTrace.archimedeanTest =
      inputs.cc20.archimedeanSymbols.supportSquareTrace
        sourceTrace.archimedeanTest := by
        exact
          (Source.SourceObjectPackageOfData.normalized_cc20_trace_package_support_square_no_defect
            base common ccm24 normalizedSeed remainders rhExit bridges
            sourceTrace.archimedeanTest
            (cc20_trace_legality_of_source_trace_data sourceTrace).traceClass
            (cc20_trace_legality_of_source_trace_data sourceTrace).cyclicLegal).symm
    _ = inputs.ccm25.weilSymbols.qwLambda sourceTrace.lambda
          g.weilTest g.weilTest := by
        exact
          (restricted_trace_read_off_of_source_trace_data
            sourceTrace).restrictedTraceReadOffEquality
    _ = inputs.ccm25.weilSymbols.archimedeanTerm
          (inputs.ccm25.weilSymbols.convolutionStar g.weilTest g.weilTest) +
        inputs.ccm25.weilSymbols.polePairing g.weilTest -
          Source.CCM25Concrete.Package.source_restricted_finite_prime_evaluator_sum
            sourceTrace.ccm25ArithmeticPackage := by
        exact
          Source.CCM25Concrete.Package.qw_lambda_formula_source_evaluator_of_package_components
            sourceTrace.ccm25ArithmeticPackage

def restrictedTraceReadOffSourceOfNormalizedPackage
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
          fixedData)) :
    let sourceTrace :=
      toSourceTraceReadOffDataOfNormalizedPackage
        base common ccm24 normalizedSeed remainders rhExit bridges
        fixedData traceData
    RestrictedTraceReadOffSource
      (RouteInputs.ofExpandedSourcePackage
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges))
      sourceTrace.archimedeanTest
      (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData)
      sourceTrace.lambda :=
  let sourceTrace :=
    toSourceTraceReadOffDataOfNormalizedPackage
      base common ccm24 normalizedSeed remainders rhExit bridges
      fixedData traceData
  restricted_trace_read_off_source_of_parts
    (ccm25_restricted_qw_read_off_of_package
      sourceTrace.ccm25ArithmeticPackage
      (window_lambda_compatibility_of_source_backed sourceTrace.oneLtLambda))
    (by
      dsimp [RestrictedTraceReadOffEquality]
      let inputs :=
        RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges)
      let g :=
        FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges fixedData
      calc
        inputs.cc20.archimedeanSymbols.supportSquareTrace
            sourceTrace.archimedeanTest =
          inputs.cc20.archimedeanSymbols.sourceNoDefectTrace
            sourceTrace.archimedeanTest :=
            Source.SourceObjectPackageOfData.normalized_cc20_trace_package_support_square_no_defect
              base common ccm24 normalizedSeed remainders rhExit bridges
              sourceTrace.archimedeanTest
              (cc20_trace_legality_of_source_trace_data sourceTrace).traceClass
              (cc20_trace_legality_of_source_trace_data sourceTrace).cyclicLegal
        _ = inputs.ccm25.weilSymbols.archimedeanTerm
              (inputs.ccm25.weilSymbols.convolutionStar
                g.weilTest g.weilTest) +
            inputs.ccm25.weilSymbols.polePairing g.weilTest -
              Source.CCM25Concrete.Package.source_restricted_finite_prime_evaluator_sum
                sourceTrace.ccm25ArithmeticPackage :=
            normalized_source_no_defect_reduces_to_package_formula
              base common ccm24 normalizedSeed remainders rhExit bridges
              fixedData traceData
        _ = inputs.ccm25.weilSymbols.qwLambda sourceTrace.lambda
            g.weilTest g.weilTest := by
            exact
              (Source.CCM25Concrete.Package.qw_lambda_formula_source_evaluator_of_package_components
                sourceTrace.ccm25ArithmeticPackage).symm)

theorem normalized_package_restricted_trace_preserves_package_qw
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
          fixedData)) :
    let sourceTrace :=
      toSourceTraceReadOffDataOfNormalizedPackage
        base common ccm24 normalizedSeed remainders rhExit bridges
        fixedData traceData
    (restrictedTraceReadOffSourceOfNormalizedPackage
      base common ccm24 normalizedSeed remainders rhExit bridges
      fixedData traceData).ccm25RestrictedQWReadOff =
      ccm25_restricted_qw_read_off_of_package
        sourceTrace.ccm25ArithmeticPackage
        (window_lambda_compatibility_of_source_backed sourceTrace.oneLtLambda) :=
  rfl

theorem normalized_package_restricted_trace_read_off_equality
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
          fixedData)) :
    let sourceTrace :=
      toSourceTraceReadOffDataOfNormalizedPackage
        base common ccm24 normalizedSeed remainders rhExit bridges
        fixedData traceData
    RestrictedTraceReadOffEquality
      (RouteInputs.ofExpandedSourcePackage
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges))
      sourceTrace.archimedeanTest
      (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData)
      sourceTrace.lambda :=
  (restrictedTraceReadOffSourceOfNormalizedPackage
    base common ccm24 normalizedSeed remainders rhExit bridges
    fixedData traceData).restrictedTraceReadOffEquality

structure NormalizedRestrictedTraceEqualityContract
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
  sourceTrace :
    SourceTraceReadOffData
      (RouteInputs.ofExpandedSourcePackage
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges))
      (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData)
  sourceTrace_eq_normalized :
    sourceTrace =
      toSourceTraceReadOffDataOfNormalizedPackage
        base common ccm24 normalizedSeed remainders rhExit bridges
        fixedData traceData
  packageRestrictedQW :
    CCM25RestrictedQWReadOff
      (RouteInputs.ofExpandedSourcePackage
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges))
      (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData)
      sourceTrace.lambda
  packageRestrictedQW_eq :
    packageRestrictedQW =
      ccm25_restricted_qw_read_off_of_package
        sourceTrace.ccm25ArithmeticPackage
        (window_lambda_compatibility_of_source_backed sourceTrace.oneLtLambda)
  restrictedSource :
    RestrictedTraceReadOffSource
      (RouteInputs.ofExpandedSourcePackage
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges))
      sourceTrace.archimedeanTest
      (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData)
      sourceTrace.lambda
  restrictedSource_eq_bridge :
    restrictedSource =
      sourceTrace.restrictedTraceReadOffBridge.build packageRestrictedQW
  restrictedTraceReadOffEquality :
    RestrictedTraceReadOffEquality
      (RouteInputs.ofExpandedSourcePackage
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges))
      sourceTrace.archimedeanTest
      (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData)
      sourceTrace.lambda
  restrictedTraceReadOffEquality_eq_bridge :
    restrictedTraceReadOffEquality =
      restrictedSource.restrictedTraceReadOffEquality

/--
Narrow source comparison needed to replace the broad restricted trace bridge on
the normalized package path.

This is still an assumption-bearing target: it asks for the CC20 support-square
trace to match the concrete CCM25 restricted evaluator expression attached to
the exact normalized arithmetic package.
-/
structure NormalizedSupportSquareQWLambdaSourceComparison
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
  supportSquareMatchesPackageQWLambdaFormula :
    let sourceTrace :=
      toSourceTraceReadOffDataOfNormalizedPackage
        base common ccm24 normalizedSeed remainders rhExit bridges
        fixedData traceData
    let inputs :=
      RouteInputs.ofExpandedSourcePackage
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges)
    let g :=
      FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
    inputs.cc20.archimedeanSymbols.supportSquareTrace
        sourceTrace.archimedeanTest =
      inputs.ccm25.weilSymbols.archimedeanTerm
          (inputs.ccm25.weilSymbols.convolutionStar g.weilTest g.weilTest) +
        inputs.ccm25.weilSymbols.polePairing g.weilTest -
          Source.CCM25Concrete.Package.source_restricted_finite_prime_evaluator_sum
            sourceTrace.ccm25ArithmeticPackage

/--
Bridge-backed constructor for the normalized support-square/`QW_lambda`
comparison.

This is useful wiring, not analytic discharge: the proof still goes through the
existing restricted trace read-off bridge carried by `SourceTraceReadOffData`.
The future hard theorem should replace this constructor at the call site.
-/
def normalizedSupportSquareQWLambdaSourceComparisonOfPackageBridge
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
          fixedData)) :
    NormalizedSupportSquareQWLambdaSourceComparison
      base common ccm24 normalizedSeed remainders rhExit bridges fixedData
      traceData where
  supportSquareMatchesPackageQWLambdaFormula := by
    intro sourceTrace inputs g
    calc
      inputs.cc20.archimedeanSymbols.supportSquareTrace
          sourceTrace.archimedeanTest =
        inputs.ccm25.weilSymbols.qwLambda sourceTrace.lambda
          g.weilTest g.weilTest := by
          exact
            (restricted_trace_read_off_of_source_trace_data
              sourceTrace).restrictedTraceReadOffEquality
      _ = inputs.ccm25.weilSymbols.archimedeanTerm
            (inputs.ccm25.weilSymbols.convolutionStar
              g.weilTest g.weilTest) +
          inputs.ccm25.weilSymbols.polePairing g.weilTest -
            Source.CCM25Concrete.Package.source_restricted_finite_prime_evaluator_sum
              sourceTrace.ccm25ArithmeticPackage := by
          exact
            Source.CCM25Concrete.Package.qw_lambda_formula_source_evaluator_of_package_components
              sourceTrace.ccm25ArithmeticPackage

theorem normalized_support_square_qw_lambda_package_bridge_holds
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
          fixedData)) :
    let sourceTrace :=
      toSourceTraceReadOffDataOfNormalizedPackage
        base common ccm24 normalizedSeed remainders rhExit bridges
        fixedData traceData
    let inputs :=
      RouteInputs.ofExpandedSourcePackage
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges)
    let g :=
      FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
    inputs.cc20.archimedeanSymbols.supportSquareTrace
        sourceTrace.archimedeanTest =
      inputs.ccm25.weilSymbols.archimedeanTerm
          (inputs.ccm25.weilSymbols.convolutionStar g.weilTest g.weilTest) +
        inputs.ccm25.weilSymbols.polePairing g.weilTest -
          Source.CCM25Concrete.Package.source_restricted_finite_prime_evaluator_sum
            sourceTrace.ccm25ArithmeticPackage := by
  exact
    (normalizedSupportSquareQWLambdaSourceComparisonOfPackageBridge
      base common ccm24 normalizedSeed remainders rhExit bridges fixedData
      traceData).supportSquareMatchesPackageQWLambdaFormula

/--
The CC20 side of the normalized support-square comparison reduces to the
support-square scalar already carried by the normalized trace-scale seed.

This is a concrete CC20-side read-off; it does not identify that scalar with
the CCM25 restricted `QW_lambda` evaluator.
-/
noncomputable def NormalizedCC20SupportSquareNormalForm
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
          fixedData)) : ℝ :=
  let sourceTrace :=
    toSourceTraceReadOffDataOfNormalizedPackage
      base common ccm24 normalizedSeed remainders rhExit bridges
      fixedData traceData
  Source.CC20Concrete.TraceScale.normalizedSeedSupportSquareTrace
    normalizedSeed sourceTrace.archimedeanTest

theorem normalized_seed_support_square_eq_trace_amplitude_sq
    (A : Source.CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (g : A.Test) :
    Source.CC20Concrete.TraceScale.normalizedSeedSupportSquareTrace A g =
      A.traceAmplitude g ^ 2 := by
  open Source.CC20Concrete.TraceScale in
  dsimp [normalizedSeedSupportSquareTrace, normalizedSeedConcreteSymbols,
    NormalizedLegalSquareTraceScaleSymbols.toLegalSquareTraceScaleSymbols,
    LegalSquareTraceScaleSymbols.toSquareTraceScaleSymbols,
    SquareTraceScaleSymbols.toConcreteTraceScaleSymbols,
    SquareTraceScaleSymbols.supportSquareTrace]

theorem normalized_support_square_reduces_to_cc20_normal_form
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
          fixedData)) :
    let sourceTrace :=
      toSourceTraceReadOffDataOfNormalizedPackage
        base common ccm24 normalizedSeed remainders rhExit bridges
        fixedData traceData
    let inputs :=
      RouteInputs.ofExpandedSourcePackage
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges)
    inputs.cc20.archimedeanSymbols.supportSquareTrace
        sourceTrace.archimedeanTest =
      NormalizedCC20SupportSquareNormalForm
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData := by
  dsimp [NormalizedCC20SupportSquareNormalForm,
    toSourceTraceReadOffDataOfNormalizedPackage, toSourceTraceReadOffData,
    TraceFrontEndData.toExpandedSourceTraceReadOffFrontEnd,
    SourceTraceReadOffData.ofExpandedSourcePackage,
    RouteInputs.ofExpandedSourcePackage]
  rfl

noncomputable def NormalizedCC20TraceAmplitudeSquareNormalForm
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
          fixedData)) : ℝ :=
  let sourceTrace :=
    toSourceTraceReadOffDataOfNormalizedPackage
      base common ccm24 normalizedSeed remainders rhExit bridges
      fixedData traceData
  normalizedSeed.traceAmplitude sourceTrace.archimedeanTest ^ 2

theorem normalized_cc20_support_square_normal_form_eq_trace_amplitude_square
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
          fixedData)) :
    NormalizedCC20SupportSquareNormalForm
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData =
      NormalizedCC20TraceAmplitudeSquareNormalForm
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData := by
  simpa [NormalizedCC20SupportSquareNormalForm,
    NormalizedCC20TraceAmplitudeSquareNormalForm,
    Source.CC20Concrete.TraceScale.normalizedSeedSupportSquareTrace] using
    normalized_seed_support_square_eq_trace_amplitude_sq normalizedSeed
      ((toSourceTraceReadOffDataOfNormalizedPackage
        base common ccm24 normalizedSeed remainders rhExit bridges
        fixedData traceData).archimedeanTest)

/--
The shared scalar target for the normalized restricted trace bridge.

This names the CCM25 package expression already exposed by the normalized
source trace package. It does not assert that the CC20 no-defect trace reduces
to this scalar; that analytic equality remains the next proof target.
-/
noncomputable def NormalizedRestrictedScalarNormalForm
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
          fixedData)) : ℝ :=
  let sourceTrace :=
    toSourceTraceReadOffDataOfNormalizedPackage
      base common ccm24 normalizedSeed remainders rhExit bridges
      fixedData traceData
  let inputs :=
    RouteInputs.ofExpandedSourcePackage
      (Source.sourceObjectPackageOfNormalizedCC20Trace
        base common ccm24 normalizedSeed remainders rhExit bridges)
  let g :=
    FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
      base common ccm24 normalizedSeed remainders rhExit bridges fixedData
  inputs.ccm25.weilSymbols.archimedeanTerm
      (inputs.ccm25.weilSymbols.convolutionStar g.weilTest g.weilTest) +
    inputs.ccm25.weilSymbols.polePairing g.weilTest -
      Source.CCM25Concrete.Package.source_restricted_finite_prime_evaluator_sum
        sourceTrace.ccm25ArithmeticPackage

structure NormalizedSupportSquareScalarNormalFormContract
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
  cc20SupportSquareEqualsRestrictedScalar :
    NormalizedCC20SupportSquareNormalForm
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData =
      NormalizedRestrictedScalarNormalForm
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData

structure NormalizedTraceAmplitudeSquareScalarContract
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
  traceAmplitudeSquareEqualsRestrictedScalar :
    NormalizedCC20TraceAmplitudeSquareNormalForm
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData =
      NormalizedRestrictedScalarNormalForm
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData

def normalizedSupportSquareScalarNormalFormContractOfTraceAmplitudeSquare
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
    (h :
      NormalizedTraceAmplitudeSquareScalarContract
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData) :
    NormalizedSupportSquareScalarNormalFormContract
      base common ccm24 normalizedSeed remainders rhExit bridges fixedData
      traceData where
  cc20SupportSquareEqualsRestrictedScalar :=
    (normalized_cc20_support_square_normal_form_eq_trace_amplitude_square
      base common ccm24 normalizedSeed remainders rhExit bridges fixedData
      traceData).trans h.traceAmplitudeSquareEqualsRestrictedScalar

def normalizedSupportSquareQWLambdaSourceComparisonOfScalarNormalForms
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
    (h :
      NormalizedSupportSquareScalarNormalFormContract
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData) :
    NormalizedSupportSquareQWLambdaSourceComparison
      base common ccm24 normalizedSeed remainders rhExit bridges fixedData
      traceData where
  supportSquareMatchesPackageQWLambdaFormula := by
    intro sourceTrace inputs g
    calc
      inputs.cc20.archimedeanSymbols.supportSquareTrace
          sourceTrace.archimedeanTest =
        NormalizedCC20SupportSquareNormalForm
          base common ccm24 normalizedSeed remainders rhExit bridges fixedData
          traceData := by
          exact
            normalized_support_square_reduces_to_cc20_normal_form
              base common ccm24 normalizedSeed remainders rhExit bridges
              fixedData traceData
      _ =
        NormalizedRestrictedScalarNormalForm
          base common ccm24 normalizedSeed remainders rhExit bridges fixedData
          traceData := h.cc20SupportSquareEqualsRestrictedScalar
      _ = inputs.ccm25.weilSymbols.archimedeanTerm
            (inputs.ccm25.weilSymbols.convolutionStar g.weilTest
              g.weilTest) +
          inputs.ccm25.weilSymbols.polePairing g.weilTest -
            Source.CCM25Concrete.Package.source_restricted_finite_prime_evaluator_sum
              sourceTrace.ccm25ArithmeticPackage := by
          dsimp [NormalizedRestrictedScalarNormalForm]

theorem normalized_qw_lambda_reduces_to_normal_form
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
          fixedData)) :
    let sourceTrace :=
      toSourceTraceReadOffDataOfNormalizedPackage
        base common ccm24 normalizedSeed remainders rhExit bridges
        fixedData traceData
    let inputs :=
      RouteInputs.ofExpandedSourcePackage
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges)
    let g :=
      FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
    inputs.ccm25.weilSymbols.qwLambda sourceTrace.lambda g.weilTest
        g.weilTest =
      NormalizedRestrictedScalarNormalForm
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData := by
  dsimp [NormalizedRestrictedScalarNormalForm]
  exact
    Source.CCM25Concrete.Package.qw_lambda_formula_source_evaluator_of_package_components
      (toSourceTraceReadOffDataOfNormalizedPackage
        base common ccm24 normalizedSeed remainders rhExit bridges
        fixedData traceData).ccm25ArithmeticPackage

/--
Route-level scalar seed whose trace scalar is the CCM25 restricted normal form.

The only mathematical input kept here is nonnegativity of that scalar, because
`NormalizedScalarTraceScaleSymbols` builds a positive trace package. This marks
the next hard proof if we want to replace the bridge-backed normalized package
by a scalar-built package.
-/
noncomputable def normalizedRestrictedScalarTraceSeed
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
    (normalForm_nonnegative :
      0 ≤
        NormalizedRestrictedScalarNormalForm
          base common ccm24 normalizedSeed remainders rhExit bridges fixedData
          traceData) :
    Source.CC20Concrete.TraceScale.NormalizedScalarTraceScaleSymbols where
  Test :=
    let inputs :=
      RouteInputs.ofExpandedSourcePackage
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges)
    inputs.cc20.archimedeanSymbols.Test
  scalarTrace :=
    fun _ =>
      NormalizedRestrictedScalarNormalForm
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData
  scalarTrace_nonnegative := fun _ => normalForm_nonnegative
  traceClass :=
    let inputs :=
      RouteInputs.ofExpandedSourcePackage
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges)
    inputs.cc20.archimedeanSymbols.traceClass
  cyclicLegal :=
    let inputs :=
      RouteInputs.ofExpandedSourcePackage
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges)
    inputs.cc20.archimedeanSymbols.cyclicLegal

theorem normalized_restricted_scalar_seed_source_no_defect_eq_normal_form
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
    (normalForm_nonnegative :
      0 ≤
        NormalizedRestrictedScalarNormalForm
          base common ccm24 normalizedSeed remainders rhExit bridges fixedData
          traceData)
    (a :
      (normalizedRestrictedScalarTraceSeed
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData normalForm_nonnegative).Test) :
    let scalarSeed :=
      normalizedRestrictedScalarTraceSeed
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData normalForm_nonnegative
    scalarSeed.toArchimedeanTraceSymbols.sourceNoDefectTrace a =
      NormalizedRestrictedScalarNormalForm
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData := by
  intro scalarSeed
  open Source.CC20Concrete.TraceScale.NormalizedScalarTraceScaleSymbols in
  exact source_no_defect_trace_eq_scalar scalarSeed a

/--
Checklist item 3 skeleton: the no-comparison CC20-to-CCM25 scalar bridge.

This is the theorem that must eventually replace
`NormalizedSupportSquareQWLambdaSourceComparison` on the normalized package
path.  The current proof factors through the normalized package's restricted
trace read-off path, so it closes the route-level syntax target but not the
deeper analytic discharge of that read-off bridge.
-/
theorem normalized_source_no_defect_reduces_to_normal_form
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
          fixedData)) :
    let sourceTrace :=
      toSourceTraceReadOffDataOfNormalizedPackage
        base common ccm24 normalizedSeed remainders rhExit bridges
        fixedData traceData
    let inputs :=
      RouteInputs.ofExpandedSourcePackage
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges)
    inputs.cc20.archimedeanSymbols.sourceNoDefectTrace
        sourceTrace.archimedeanTest =
      NormalizedRestrictedScalarNormalForm
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData := by
  dsimp [NormalizedRestrictedScalarNormalForm]
  exact
    normalized_source_no_defect_reduces_to_package_formula
      base common ccm24 normalizedSeed remainders rhExit bridges
      fixedData traceData

theorem normalized_restricted_scalar_normal_form_nonnegative
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
          fixedData)) :
    0 ≤
      NormalizedRestrictedScalarNormalForm
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData := by
  let sourceTrace :=
    toSourceTraceReadOffDataOfNormalizedPackage
      base common ccm24 normalizedSeed remainders rhExit bridges
      fixedData traceData
  let inputs :=
    RouteInputs.ofExpandedSourcePackage
      (Source.sourceObjectPackageOfNormalizedCC20Trace
        base common ccm24 normalizedSeed remainders rhExit bridges)
  let hpositive :
      0 ≤ inputs.cc20.archimedeanSymbols.positiveTrace
        sourceTrace.archimedeanTest :=
    sourceTrace.positiveTraceNonnegative
  let hordinary :
      inputs.cc20.archimedeanSymbols.positiveTrace
          sourceTrace.archimedeanTest =
        inputs.cc20.archimedeanSymbols.supportSquareTrace
          sourceTrace.archimedeanTest :=
    (ordinaryTraceSupportSquareTheoremDataOfNormalizedPackage
      base common ccm24 normalizedSeed remainders rhExit bridges fixedData
      traceData).ordinaryTraceMatchesSupportSquareHolds
  let hsupport :
      inputs.cc20.archimedeanSymbols.supportSquareTrace
          sourceTrace.archimedeanTest =
        inputs.cc20.archimedeanSymbols.sourceNoDefectTrace
          sourceTrace.archimedeanTest :=
    Source.SourceObjectPackageOfData.normalized_cc20_trace_package_support_square_no_defect
      base common ccm24 normalizedSeed remainders rhExit bridges
      sourceTrace.archimedeanTest
      (cc20_trace_legality_of_source_trace_data sourceTrace).traceClass
      (cc20_trace_legality_of_source_trace_data sourceTrace).cyclicLegal
  let hnormal :
      inputs.cc20.archimedeanSymbols.sourceNoDefectTrace
          sourceTrace.archimedeanTest =
        NormalizedRestrictedScalarNormalForm
          base common ccm24 normalizedSeed remainders rhExit bridges fixedData
          traceData :=
    normalized_source_no_defect_reduces_to_normal_form
      base common ccm24 normalizedSeed remainders rhExit bridges fixedData
      traceData
  exact (hordinary.trans (hsupport.trans hnormal)) ▸ hpositive

noncomputable def normalizedRestrictedScalarTraceSeedOfTraceData
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
          fixedData)) :
    Source.CC20Concrete.TraceScale.NormalizedScalarTraceScaleSymbols :=
  normalizedRestrictedScalarTraceSeed
    base common ccm24 normalizedSeed remainders rhExit bridges fixedData
    traceData
    (normalized_restricted_scalar_normal_form_nonnegative
      base common ccm24 normalizedSeed remainders rhExit bridges fixedData
      traceData)

theorem normalized_restricted_scalar_package_source_no_defect_eq_normal_form
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
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)))
    (scalarRhExit : Source.SourceObject.CC20RHExitObjectPackage)
    (scalarBridges :
      Source.SourceObjectCrossObjectBridges base common
        (Source.SourceObjectExpandedRows.ofNormalizedScalarCC20Trace
          ccm24
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)
          scalarRemainders)
        scalarRhExit)
    (a :
      (RouteInputs.ofExpandedSourcePackage
        (Source.sourceObjectPackageOfNormalizedScalarCC20Trace
          base common ccm24
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)
          scalarRemainders scalarRhExit scalarBridges)).cc20.archimedeanSymbols.Test) :
    (RouteInputs.ofExpandedSourcePackage
      (Source.sourceObjectPackageOfNormalizedScalarCC20Trace
        base common ccm24
        (normalizedRestrictedScalarTraceSeedOfTraceData
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData traceData)
        scalarRemainders scalarRhExit scalarBridges)).cc20.archimedeanSymbols.sourceNoDefectTrace
        a =
      NormalizedRestrictedScalarNormalForm
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData := by
  exact
    normalized_restricted_scalar_seed_source_no_defect_eq_normal_form
      base common ccm24 normalizedSeed remainders rhExit bridges fixedData
      traceData
      (normalized_restricted_scalar_normal_form_nonnegative
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData)
      a

theorem normalized_restricted_scalar_package_support_square_eq_original_qw_lambda_formula
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
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)))
    (scalarRhExit : Source.SourceObject.CC20RHExitObjectPackage)
    (scalarBridges :
      Source.SourceObjectCrossObjectBridges base common
        (Source.SourceObjectExpandedRows.ofNormalizedScalarCC20Trace
          ccm24
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)
          scalarRemainders)
        scalarRhExit)
    (a :
      (RouteInputs.ofExpandedSourcePackage
        (Source.sourceObjectPackageOfNormalizedScalarCC20Trace
          base common ccm24
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)
          scalarRemainders scalarRhExit scalarBridges)).cc20.archimedeanSymbols.Test) :
    let scalarInputs :=
      RouteInputs.ofExpandedSourcePackage
        (Source.sourceObjectPackageOfNormalizedScalarCC20Trace
          base common ccm24
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)
          scalarRemainders scalarRhExit scalarBridges)
    let originalInputs :=
      RouteInputs.ofExpandedSourcePackage
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges)
    let originalG :=
      FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
    let originalSourceTrace :=
      toSourceTraceReadOffDataOfNormalizedPackage
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData
    scalarInputs.cc20.archimedeanSymbols.supportSquareTrace
        a =
      originalInputs.ccm25.weilSymbols.archimedeanTerm
          (originalInputs.ccm25.weilSymbols.convolutionStar
            originalG.weilTest originalG.weilTest) +
        originalInputs.ccm25.weilSymbols.polePairing originalG.weilTest -
          Source.CCM25Concrete.Package.source_restricted_finite_prime_evaluator_sum
            originalSourceTrace.ccm25ArithmeticPackage := by
  intro scalarInputs originalInputs originalG originalSourceTrace
  let originalSourceTrace :=
    toSourceTraceReadOffDataOfNormalizedPackage
      base common ccm24 normalizedSeed remainders rhExit bridges fixedData
      traceData
  let originalInputs :=
    RouteInputs.ofExpandedSourcePackage
      (Source.sourceObjectPackageOfNormalizedCC20Trace
        base common ccm24 normalizedSeed remainders rhExit bridges)
  let originalG :=
    FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
      base common ccm24 normalizedSeed remainders rhExit bridges fixedData
  let hsupport :
      scalarInputs.cc20.archimedeanSymbols.supportSquareTrace
          a =
        NormalizedRestrictedScalarNormalForm
          base common ccm24 normalizedSeed remainders rhExit bridges fixedData
          traceData := by
    exact
      Source.SourceObjectPackageOfData.normalized_scalar_cc20_trace_package_support_square_eq_scalar
        base common ccm24
        (normalizedRestrictedScalarTraceSeedOfTraceData
          base common ccm24 normalizedSeed remainders rhExit bridges fixedData
          traceData)
        scalarRemainders scalarRhExit scalarBridges a
  let hformula :
      originalInputs.ccm25.weilSymbols.qwLambda originalSourceTrace.lambda
          originalG.weilTest originalG.weilTest =
        NormalizedRestrictedScalarNormalForm
          base common ccm24 normalizedSeed remainders rhExit bridges fixedData
          traceData :=
    normalized_qw_lambda_reduces_to_normal_form
      base common ccm24 normalizedSeed remainders rhExit bridges fixedData
      traceData
  let hpackage :
      originalInputs.ccm25.weilSymbols.qwLambda originalSourceTrace.lambda
          originalG.weilTest originalG.weilTest =
        originalInputs.ccm25.weilSymbols.archimedeanTerm
            (originalInputs.ccm25.weilSymbols.convolutionStar
              originalG.weilTest originalG.weilTest) +
          originalInputs.ccm25.weilSymbols.polePairing originalG.weilTest -
            Source.CCM25Concrete.Package.source_restricted_finite_prime_evaluator_sum
              originalSourceTrace.ccm25ArithmeticPackage :=
    Source.CCM25Concrete.Package.qw_lambda_formula_source_evaluator_of_package_components
      originalSourceTrace.ccm25ArithmeticPackage
  calc
    scalarInputs.cc20.archimedeanSymbols.supportSquareTrace
        a =
      NormalizedRestrictedScalarNormalForm
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData := hsupport
    _ =
      originalInputs.ccm25.weilSymbols.qwLambda originalSourceTrace.lambda
        originalG.weilTest originalG.weilTest := hformula.symm
    _ =
      originalInputs.ccm25.weilSymbols.archimedeanTerm
          (originalInputs.ccm25.weilSymbols.convolutionStar
            originalG.weilTest originalG.weilTest) +
        originalInputs.ccm25.weilSymbols.polePairing originalG.weilTest -
          Source.CCM25Concrete.Package.source_restricted_finite_prime_evaluator_sum
            originalSourceTrace.ccm25ArithmeticPackage := hpackage

theorem normalizedScalarTestAndQuotientCompatibilityFromOriginalCCM25
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
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)))
    (scalarRhExit : Source.SourceObject.CC20RHExitObjectPackage)
    (scalarBridges :
      Source.SourceObjectCrossObjectBridges base common
        (Source.SourceObjectExpandedRows.ofNormalizedScalarCC20Trace
          ccm24
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)
          scalarRemainders)
        scalarRhExit)
    (scalarFixedData :
      FixedSTestObligationData
        (Source.sourceObjectPackageOfNormalizedScalarCC20Trace
          base common ccm24
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)
          scalarRemainders scalarRhExit scalarBridges)) :
    let scalarInputs :=
      RouteInputs.ofExpandedSourcePackage
        (Source.sourceObjectPackageOfNormalizedScalarCC20Trace
          base common ccm24
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)
          scalarRemainders scalarRhExit scalarBridges)
    let scalarG :=
      FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedScalarPackage
        base common ccm24
        (normalizedRestrictedScalarTraceSeedOfTraceData
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData traceData)
        scalarRemainders scalarRhExit scalarBridges scalarFixedData
    TestAndQuotientCompatibility scalarInputs scalarG := by
  intro scalarInputs scalarG
  exact
    test_and_quotient_compatibility_of_package
      (inputs := scalarInputs) (g := scalarG) (lambda := traceData.lambda)
      traceData.ccm25ArithmeticPackage

theorem normalizedScalarFixedSNoDefectSupportSquareTemplate
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
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)))
    (scalarRhExit : Source.SourceObject.CC20RHExitObjectPackage)
    (scalarBridges :
      Source.SourceObjectCrossObjectBridges base common
        (Source.SourceObjectExpandedRows.ofNormalizedScalarCC20Trace
          ccm24
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)
          scalarRemainders)
        scalarRhExit) :
    let scalarPkg :=
      Source.sourceObjectPackageOfNormalizedScalarCC20Trace
        base common ccm24
        (normalizedRestrictedScalarTraceSeedOfTraceData
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData traceData)
        scalarRemainders scalarRhExit scalarBridges
    let scalarInputs := RouteInputs.ofExpandedSourcePackage scalarPkg
    FixedSNoDefectSupportSquareTemplate scalarInputs
      scalarPkg.cc20Trace.sourceTraceTest := by
  intro scalarPkg scalarInputs
  dsimp [FixedSNoDefectSupportSquareTemplate, CC20NoDefectSourceReadOff]
  let hlegal :=
    scalarPkg.cc20Trace.sourceTraceClassCyclicityTemplate
      scalarPkg.cc20Trace.sourceTraceTest
      (scalarPkg.cc20Trace.sourceHilbertSchmidtGate
        scalarPkg.cc20Trace.sourceTraceTest)
  exact
    Source.SourceObjectPackageOfData.normalized_scalar_cc20_trace_package_support_square_no_defect
      base common ccm24
      (normalizedRestrictedScalarTraceSeedOfTraceData
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData)
      scalarRemainders scalarRhExit scalarBridges
      scalarPkg.cc20Trace.sourceTraceTest
      hlegal.1 hlegal.2

theorem normalizedScalarTraceClassCyclicSupportSquareIdentity
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
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)))
    (scalarRhExit : Source.SourceObject.CC20RHExitObjectPackage)
    (scalarBridges :
      Source.SourceObjectCrossObjectBridges base common
        (Source.SourceObjectExpandedRows.ofNormalizedScalarCC20Trace
          ccm24
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)
          scalarRemainders)
        scalarRhExit) :
    let scalarPkg :=
      Source.sourceObjectPackageOfNormalizedScalarCC20Trace
        base common ccm24
        (normalizedRestrictedScalarTraceSeedOfTraceData
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData traceData)
        scalarRemainders scalarRhExit scalarBridges
    let scalarInputs := RouteInputs.ofExpandedSourcePackage scalarPkg
    TraceClassCyclicSupportSquareIdentity scalarInputs
      scalarPkg.cc20Trace.sourceTraceTest := by
  intro scalarPkg scalarInputs
  dsimp [TraceClassCyclicSupportSquareIdentity]
  let hlegal :=
    scalarPkg.cc20Trace.sourceTraceClassCyclicityTemplate
      scalarPkg.cc20Trace.sourceTraceTest
      (scalarPkg.cc20Trace.sourceHilbertSchmidtGate
        scalarPkg.cc20Trace.sourceTraceTest)
  exact
    { traceClass := hlegal.1
      cyclicLegal := hlegal.2 }

theorem normalizedScalarFixedSSupportSquareTransportFromOriginalCCM25
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
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)))
    (scalarRhExit : Source.SourceObject.CC20RHExitObjectPackage)
    (scalarBridges :
      Source.SourceObjectCrossObjectBridges base common
        (Source.SourceObjectExpandedRows.ofNormalizedScalarCC20Trace
          ccm24
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)
          scalarRemainders)
        scalarRhExit)
    (scalarFixedData :
      FixedSTestObligationData
        (Source.sourceObjectPackageOfNormalizedScalarCC20Trace
          base common ccm24
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)
          scalarRemainders scalarRhExit scalarBridges)) :
    let scalarPkg :=
      Source.sourceObjectPackageOfNormalizedScalarCC20Trace
        base common ccm24
        (normalizedRestrictedScalarTraceSeedOfTraceData
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData traceData)
        scalarRemainders scalarRhExit scalarBridges
    let scalarInputs := RouteInputs.ofExpandedSourcePackage scalarPkg
    let scalarG :=
      FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedScalarPackage
        base common ccm24
        (normalizedRestrictedScalarTraceSeedOfTraceData
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData traceData)
        scalarRemainders scalarRhExit scalarBridges scalarFixedData
    FixedSQuantizedSupportSquareTransport scalarInputs
      scalarPkg.cc20Trace.sourceTraceTest scalarG traceData.lambda := by
  intro scalarPkg scalarInputs scalarG
  exact
    fixed_s_quantized_support_square_transport_of_parts
      (inputs := scalarInputs) (a := scalarPkg.cc20Trace.sourceTraceTest)
      (g := scalarG) (lambda := traceData.lambda) traceData.oneLtLambda
      (normalizedScalarFixedSNoDefectSupportSquareTemplate
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData scalarRemainders scalarRhExit scalarBridges)
      (normalizedScalarTraceClassCyclicSupportSquareIdentity
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData scalarRemainders scalarRhExit scalarBridges)

/--
Build scalar trace-front-end data while reusing the original normalized
package's cutoff and CCM25 arithmetic package.

Only the CC20-facing legality and trace-read-off contracts remain scalar
package inputs.  This is the precise synchronization layer needed before the
scalar-built package can replace the square-seeded normalized package in the
route.
-/
noncomputable def traceFrontEndDataOfNormalizedScalarPackageFromOriginalCCM25
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
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)))
    (scalarRhExit : Source.SourceObject.CC20RHExitObjectPackage)
    (scalarBridges :
      Source.SourceObjectCrossObjectBridges base common
        (Source.SourceObjectExpandedRows.ofNormalizedScalarCC20Trace
          ccm24
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)
          scalarRemainders)
        scalarRhExit)
    (scalarFixedData :
      FixedSTestObligationData
        (Source.sourceObjectPackageOfNormalizedScalarCC20Trace
          base common ccm24
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)
          scalarRemainders scalarRhExit scalarBridges))
    (scalarTestAndQuotientCompatibility :
      TestAndQuotientCompatibility
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedScalarCC20Trace
            base common ccm24
            (normalizedRestrictedScalarTraceSeedOfTraceData
              base common ccm24 normalizedSeed remainders rhExit bridges
              fixedData traceData)
            scalarRemainders scalarRhExit scalarBridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedScalarPackage
          base common ccm24
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)
          scalarRemainders scalarRhExit scalarBridges scalarFixedData))
    (scalarFixedSSupportSquareTransport :
      FixedSQuantizedSupportSquareTransport
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedScalarCC20Trace
            base common ccm24
            (normalizedRestrictedScalarTraceSeedOfTraceData
              base common ccm24 normalizedSeed remainders rhExit bridges
              fixedData traceData)
            scalarRemainders scalarRhExit scalarBridges))
        (Source.sourceObjectPackageOfNormalizedScalarCC20Trace
          base common ccm24
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)
          scalarRemainders scalarRhExit scalarBridges).cc20Trace.sourceTraceTest
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedScalarPackage
          base common ccm24
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)
          scalarRemainders scalarRhExit scalarBridges scalarFixedData)
        traceData.lambda)
    (scalarFullTraceReadOffBridge :
      FullTraceReadOffBridgeContract
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedScalarCC20Trace
            base common ccm24
            (normalizedRestrictedScalarTraceSeedOfTraceData
              base common ccm24 normalizedSeed remainders rhExit bridges
              fixedData traceData)
            scalarRemainders scalarRhExit scalarBridges))
        (Source.sourceObjectPackageOfNormalizedScalarCC20Trace
          base common ccm24
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)
          scalarRemainders scalarRhExit scalarBridges).cc20Trace.sourceTraceTest
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedScalarPackage
          base common ccm24
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)
          scalarRemainders scalarRhExit scalarBridges scalarFixedData))
    (scalarRestrictedTraceReadOffBridge :
      RestrictedTraceReadOffBridgeContract
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedScalarCC20Trace
            base common ccm24
            (normalizedRestrictedScalarTraceSeedOfTraceData
              base common ccm24 normalizedSeed remainders rhExit bridges
              fixedData traceData)
            scalarRemainders scalarRhExit scalarBridges))
        (Source.sourceObjectPackageOfNormalizedScalarCC20Trace
          base common ccm24
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)
          scalarRemainders scalarRhExit scalarBridges).cc20Trace.sourceTraceTest
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedScalarPackage
          base common ccm24
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)
          scalarRemainders scalarRhExit scalarBridges scalarFixedData)
        traceData.lambda)
    (scalarTraceScaleNoMissingBulk :
      TraceScaleNoMissingBulkData
        (Source.sourceObjectPackageOfNormalizedScalarCC20Trace
          base common ccm24
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)
          scalarRemainders scalarRhExit scalarBridges)
        (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedScalarPackage
          base common ccm24
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)
          scalarRemainders scalarRhExit scalarBridges scalarFixedData)
        traceData.lambda
        (by
          exact traceData.ccm25ArithmeticPackage)) :
    TraceFrontEndData
      (Source.sourceObjectPackageOfNormalizedScalarCC20Trace
        base common ccm24
        (normalizedRestrictedScalarTraceSeedOfTraceData
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData traceData)
        scalarRemainders scalarRhExit scalarBridges)
      (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedScalarPackage
        base common ccm24
        (normalizedRestrictedScalarTraceSeedOfTraceData
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData traceData)
        scalarRemainders scalarRhExit scalarBridges scalarFixedData) where
  lambda := traceData.lambda
  oneLtLambda := traceData.oneLtLambda
  ccm25ArithmeticPackage := traceData.ccm25ArithmeticPackage
  testAndQuotientCompatibility := scalarTestAndQuotientCompatibility
  fixedSSupportSquareTransport := scalarFixedSSupportSquareTransport
  fullTraceReadOffBridge := scalarFullTraceReadOffBridge
  restrictedTraceReadOffBridge := scalarRestrictedTraceReadOffBridge
  traceScaleNoMissingBulk := scalarTraceScaleNoMissingBulk

theorem normalized_scalar_trace_front_from_original_lambda
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
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)))
    (scalarRhExit : Source.SourceObject.CC20RHExitObjectPackage)
    (scalarBridges :
      Source.SourceObjectCrossObjectBridges base common
        (Source.SourceObjectExpandedRows.ofNormalizedScalarCC20Trace
          ccm24
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)
          scalarRemainders)
        scalarRhExit)
    (scalarFixedData :
      FixedSTestObligationData
        (Source.sourceObjectPackageOfNormalizedScalarCC20Trace
          base common ccm24
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)
          scalarRemainders scalarRhExit scalarBridges))
    (scalarTestAndQuotientCompatibility)
    (scalarFixedSSupportSquareTransport)
    (scalarFullTraceReadOffBridge)
    (scalarRestrictedTraceReadOffBridge)
    (scalarTraceScaleNoMissingBulk) :
    (traceFrontEndDataOfNormalizedScalarPackageFromOriginalCCM25
      base common ccm24 normalizedSeed remainders rhExit bridges fixedData
      traceData scalarRemainders scalarRhExit scalarBridges scalarFixedData
      scalarTestAndQuotientCompatibility scalarFixedSSupportSquareTransport
      scalarFullTraceReadOffBridge scalarRestrictedTraceReadOffBridge
      scalarTraceScaleNoMissingBulk).lambda =
      traceData.lambda :=
  rfl

theorem normalized_scalar_trace_front_trace_amplitude_square_eq_original_normal_form
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
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)))
    (scalarRhExit : Source.SourceObject.CC20RHExitObjectPackage)
    (scalarBridges :
      Source.SourceObjectCrossObjectBridges base common
        (Source.SourceObjectExpandedRows.ofNormalizedScalarCC20Trace
          ccm24
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)
          scalarRemainders)
        scalarRhExit)
    (scalarFixedData :
      FixedSTestObligationData
        (Source.sourceObjectPackageOfNormalizedScalarCC20Trace
          base common ccm24
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)
          scalarRemainders scalarRhExit scalarBridges))
    (scalarTestAndQuotientCompatibility)
    (scalarFixedSSupportSquareTransport)
    (scalarFullTraceReadOffBridge)
    (scalarRestrictedTraceReadOffBridge)
    (scalarTraceScaleNoMissingBulk) :
    let scalarSeed :=
      normalizedRestrictedScalarTraceSeedOfTraceData
        base common ccm24 normalizedSeed remainders rhExit bridges
        fixedData traceData
    let scalarTraceData :=
      traceFrontEndDataOfNormalizedScalarPackageFromOriginalCCM25
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData scalarRemainders scalarRhExit scalarBridges scalarFixedData
        scalarTestAndQuotientCompatibility scalarFixedSSupportSquareTransport
        scalarFullTraceReadOffBridge scalarRestrictedTraceReadOffBridge
        scalarTraceScaleNoMissingBulk
    let scalarSourceTrace :=
      toSourceTraceReadOffDataOfNormalizedScalarPackage
        base common ccm24 scalarSeed scalarRemainders scalarRhExit
        scalarBridges scalarFixedData scalarTraceData
    (Source.CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
        scalarSeed).traceAmplitude scalarSourceTrace.archimedeanTest ^ 2 =
      NormalizedRestrictedScalarNormalForm
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData := by
  intro scalarSeed scalarTraceData scalarSourceTrace
  simpa [normalizedRestrictedScalarTraceSeedOfTraceData,
    normalizedRestrictedScalarTraceSeed,
    Source.CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed] using
    Real.sq_sqrt
      (normalized_restricted_scalar_normal_form_nonnegative
        base common ccm24 normalizedSeed remainders rhExit bridges
        fixedData traceData)

def ordinaryTraceSupportSquareTheoremDataOfNormalizedScalarTraceFront
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
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)))
    (scalarRhExit : Source.SourceObject.CC20RHExitObjectPackage)
    (scalarBridges :
      Source.SourceObjectCrossObjectBridges base common
        (Source.SourceObjectExpandedRows.ofNormalizedScalarCC20Trace
          ccm24
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)
          scalarRemainders)
        scalarRhExit)
    (scalarFixedData :
      FixedSTestObligationData
        (Source.sourceObjectPackageOfNormalizedScalarCC20Trace
          base common ccm24
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)
          scalarRemainders scalarRhExit scalarBridges))
    (scalarTraceData :
      TraceFrontEndData
        (Source.sourceObjectPackageOfNormalizedScalarCC20Trace
          base common ccm24
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)
          scalarRemainders scalarRhExit scalarBridges)
        (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedScalarPackage
          base common ccm24
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)
          scalarRemainders scalarRhExit scalarBridges scalarFixedData)) :
    OrdinaryTraceSupportSquareTheoremData
      (Source.sourceObjectPackageOfNormalizedScalarCC20Trace
        base common ccm24
        (normalizedRestrictedScalarTraceSeedOfTraceData
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData traceData)
        scalarRemainders scalarRhExit scalarBridges)
      (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedScalarPackage
        base common ccm24
        (normalizedRestrictedScalarTraceSeedOfTraceData
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData traceData)
        scalarRemainders scalarRhExit scalarBridges scalarFixedData)
      scalarTraceData.lambda scalarTraceData.ccm25ArithmeticPackage where
  ordinaryTraceMatchesSupportSquare :=
    let scalarSourceTrace :=
      toSourceTraceReadOffDataOfNormalizedScalarPackage
        base common ccm24
        (normalizedRestrictedScalarTraceSeedOfTraceData
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData traceData)
        scalarRemainders scalarRhExit scalarBridges scalarFixedData
        scalarTraceData
    let scalarInputs :=
      RouteInputs.ofExpandedSourcePackage
        (Source.sourceObjectPackageOfNormalizedScalarCC20Trace
          base common ccm24
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)
          scalarRemainders scalarRhExit scalarBridges)
    scalarInputs.cc20.archimedeanSymbols.positiveTrace
        scalarSourceTrace.archimedeanTest =
      scalarInputs.cc20.archimedeanSymbols.supportSquareTrace
        scalarSourceTrace.archimedeanTest
  ordinaryTraceMatchesSupportSquareHolds := by
    let scalarSourceTrace :=
      toSourceTraceReadOffDataOfNormalizedScalarPackage
        base common ccm24
        (normalizedRestrictedScalarTraceSeedOfTraceData
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData traceData)
        scalarRemainders scalarRhExit scalarBridges scalarFixedData
        scalarTraceData
    let legality := cc20_trace_legality_of_source_trace_data scalarSourceTrace
    exact
      (RouteInputs.ofExpandedSourcePackage
        (Source.sourceObjectPackageOfNormalizedScalarCC20Trace
          base common ccm24
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)
          scalarRemainders scalarRhExit scalarBridges)).cc20.ordinaryTraceSupportSquare
        scalarSourceTrace.archimedeanTest legality.traceClass legality.cyclicLegal

def noDefectQWLambdaTheoremDataOfNormalizedScalarTraceFront
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
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)))
    (scalarRhExit : Source.SourceObject.CC20RHExitObjectPackage)
    (scalarBridges :
      Source.SourceObjectCrossObjectBridges base common
        (Source.SourceObjectExpandedRows.ofNormalizedScalarCC20Trace
          ccm24
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)
          scalarRemainders)
        scalarRhExit)
    (scalarFixedData :
      FixedSTestObligationData
        (Source.sourceObjectPackageOfNormalizedScalarCC20Trace
          base common ccm24
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)
          scalarRemainders scalarRhExit scalarBridges))
    (scalarTraceData :
      TraceFrontEndData
        (Source.sourceObjectPackageOfNormalizedScalarCC20Trace
          base common ccm24
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)
          scalarRemainders scalarRhExit scalarBridges)
        (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedScalarPackage
          base common ccm24
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)
          scalarRemainders scalarRhExit scalarBridges scalarFixedData))
    (scalarTraceData_lambda : scalarTraceData.lambda = traceData.lambda) :
    NoDefectQWLambdaTheoremData
      (Source.sourceObjectPackageOfNormalizedScalarCC20Trace
        base common ccm24
        (normalizedRestrictedScalarTraceSeedOfTraceData
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData traceData)
        scalarRemainders scalarRhExit scalarBridges)
      (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedScalarPackage
        base common ccm24
        (normalizedRestrictedScalarTraceSeedOfTraceData
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData traceData)
        scalarRemainders scalarRhExit scalarBridges scalarFixedData)
      scalarTraceData.lambda scalarTraceData.ccm25ArithmeticPackage where
  supportSquareMatchesNoDefectSource :=
    let scalarSourceTrace :=
      toSourceTraceReadOffDataOfNormalizedScalarPackage
        base common ccm24
        (normalizedRestrictedScalarTraceSeedOfTraceData
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData traceData)
        scalarRemainders scalarRhExit scalarBridges scalarFixedData
        scalarTraceData
    let scalarInputs :=
      RouteInputs.ofExpandedSourcePackage
        (Source.sourceObjectPackageOfNormalizedScalarCC20Trace
          base common ccm24
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)
          scalarRemainders scalarRhExit scalarBridges)
    scalarInputs.cc20.archimedeanSymbols.supportSquareTrace
        scalarSourceTrace.archimedeanTest =
      scalarInputs.cc20.archimedeanSymbols.sourceNoDefectTrace
        scalarSourceTrace.archimedeanTest
  noDefectSourceMatchesQWLambda :=
    let scalarSourceTrace :=
      toSourceTraceReadOffDataOfNormalizedScalarPackage
        base common ccm24
        (normalizedRestrictedScalarTraceSeedOfTraceData
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData traceData)
        scalarRemainders scalarRhExit scalarBridges scalarFixedData
        scalarTraceData
    let scalarInputs :=
      RouteInputs.ofExpandedSourcePackage
        (Source.sourceObjectPackageOfNormalizedScalarCC20Trace
          base common ccm24
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)
          scalarRemainders scalarRhExit scalarBridges)
    let scalarG :=
      FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedScalarPackage
        base common ccm24
        (normalizedRestrictedScalarTraceSeedOfTraceData
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData traceData)
        scalarRemainders scalarRhExit scalarBridges scalarFixedData
    scalarInputs.cc20.archimedeanSymbols.sourceNoDefectTrace
        scalarSourceTrace.archimedeanTest =
      scalarInputs.ccm25.weilSymbols.qwLambda scalarTraceData.lambda
        scalarG.weilTest scalarG.weilTest
  supportSquareMatchesNoDefectSourceHolds := by
    let scalarSourceTrace :=
      toSourceTraceReadOffDataOfNormalizedScalarPackage
        base common ccm24
        (normalizedRestrictedScalarTraceSeedOfTraceData
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData traceData)
        scalarRemainders scalarRhExit scalarBridges scalarFixedData
        scalarTraceData
    exact
      (cc20_trace_square_of_source_trace_data
        scalarSourceTrace).noDefectSourceReadOff
  noDefectSourceMatchesQWLambdaHolds := by
    let scalarSourceTrace :=
      toSourceTraceReadOffDataOfNormalizedScalarPackage
        base common ccm24
        (normalizedRestrictedScalarTraceSeedOfTraceData
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData traceData)
        scalarRemainders scalarRhExit scalarBridges scalarFixedData
        scalarTraceData
    let scalarInputs :=
      RouteInputs.ofExpandedSourcePackage
        (Source.sourceObjectPackageOfNormalizedScalarCC20Trace
          base common ccm24
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)
          scalarRemainders scalarRhExit scalarBridges)
    let scalarG :=
      FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedScalarPackage
        base common ccm24
        (normalizedRestrictedScalarTraceSeedOfTraceData
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData traceData)
        scalarRemainders scalarRhExit scalarBridges scalarFixedData
    let hsource :
        scalarInputs.cc20.archimedeanSymbols.sourceNoDefectTrace
            scalarSourceTrace.archimedeanTest =
          NormalizedRestrictedScalarNormalForm
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData :=
      SOData.normalized_scalar_source_no_defect_eq_scalar
        base common ccm24
        (normalizedRestrictedScalarTraceSeedOfTraceData
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData traceData)
        scalarRemainders scalarRhExit scalarBridges
        scalarSourceTrace.archimedeanTest
    calc
      scalarInputs.cc20.archimedeanSymbols.sourceNoDefectTrace
          scalarSourceTrace.archimedeanTest =
        NormalizedRestrictedScalarNormalForm
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData traceData := hsource
      _ =
        scalarInputs.ccm25.weilSymbols.qwLambda traceData.lambda
          scalarG.weilTest scalarG.weilTest := by
          exact
            (normalized_qw_lambda_reduces_to_normal_form
              base common ccm24 normalizedSeed remainders rhExit bridges
              fixedData traceData).symm
      _ =
        scalarInputs.ccm25.weilSymbols.qwLambda scalarTraceData.lambda
          scalarG.weilTest scalarG.weilTest := by
          rw [scalarTraceData_lambda]

noncomputable def traceScaleNoMissingBulkOfNormalizedScalarTraceFront
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
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)))
    (scalarRhExit : Source.SourceObject.CC20RHExitObjectPackage)
    (scalarBridges :
      Source.SourceObjectCrossObjectBridges base common
        (Source.SourceObjectExpandedRows.ofNormalizedScalarCC20Trace
          ccm24
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)
          scalarRemainders)
        scalarRhExit)
    (scalarFixedData :
      FixedSTestObligationData
        (Source.sourceObjectPackageOfNormalizedScalarCC20Trace
          base common ccm24
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)
          scalarRemainders scalarRhExit scalarBridges))
    (scalarTraceData :
      TraceFrontEndData
        (Source.sourceObjectPackageOfNormalizedScalarCC20Trace
          base common ccm24
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)
          scalarRemainders scalarRhExit scalarBridges)
        (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedScalarPackage
          base common ccm24
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)
          scalarRemainders scalarRhExit scalarBridges scalarFixedData))
    (scalarTraceData_lambda : scalarTraceData.lambda = traceData.lambda)
    (rankPoleCdefOwnEveryRemainder :
      (L : RouteLedgers) ->
        SourceSignDefectClassification
          (RouteInputs.ofExpandedSourcePackage
            (Source.sourceObjectPackageOfNormalizedScalarCC20Trace
              base common ccm24
              (normalizedRestrictedScalarTraceSeedOfTraceData
                base common ccm24 normalizedSeed remainders rhExit bridges
                fixedData traceData)
              scalarRemainders scalarRhExit scalarBridges))
          (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedScalarPackage
            base common ccm24
            (normalizedRestrictedScalarTraceSeedOfTraceData
              base common ccm24 normalizedSeed remainders rhExit bridges
              fixedData traceData)
            scalarRemainders scalarRhExit scalarBridges scalarFixedData)
          scalarTraceData.lambda L -> Prop)
    (noExtraBulkScaleTerm : Prop)
    (noExtraBulkScaleTermHolds : noExtraBulkScaleTerm) :
    TraceScaleNoMissingBulkData
      (Source.sourceObjectPackageOfNormalizedScalarCC20Trace
        base common ccm24
        (normalizedRestrictedScalarTraceSeedOfTraceData
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData traceData)
        scalarRemainders scalarRhExit scalarBridges)
      (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedScalarPackage
        base common ccm24
        (normalizedRestrictedScalarTraceSeedOfTraceData
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData traceData)
        scalarRemainders scalarRhExit scalarBridges scalarFixedData)
      scalarTraceData.lambda scalarTraceData.ccm25ArithmeticPackage :=
  trace_scale_no_missing_bulk_of_scalar_theorem_data
    (ordinaryTraceSupportSquareTheoremDataOfNormalizedScalarTraceFront
      base common ccm24 normalizedSeed remainders rhExit bridges fixedData
      traceData scalarRemainders scalarRhExit scalarBridges scalarFixedData
      scalarTraceData)
    (noDefectQWLambdaTheoremDataOfNormalizedScalarTraceFront
      base common ccm24 normalizedSeed remainders rhExit bridges fixedData
      traceData scalarRemainders scalarRhExit scalarBridges scalarFixedData
      scalarTraceData scalarTraceData_lambda)
    rankPoleCdefOwnEveryRemainder noExtraBulkScaleTerm
    noExtraBulkScaleTermHolds

noncomputable def traceScaleNoMissingBulkOfNormalizedScalarTraceFrontFromSignDefect
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
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)))
    (scalarRhExit : Source.SourceObject.CC20RHExitObjectPackage)
    (scalarBridges :
      Source.SourceObjectCrossObjectBridges base common
        (Source.SourceObjectExpandedRows.ofNormalizedScalarCC20Trace
          ccm24
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)
          scalarRemainders)
        scalarRhExit)
    (scalarFixedData :
      FixedSTestObligationData
        (Source.sourceObjectPackageOfNormalizedScalarCC20Trace
          base common ccm24
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)
          scalarRemainders scalarRhExit scalarBridges))
    (scalarTraceData :
      TraceFrontEndData
        (Source.sourceObjectPackageOfNormalizedScalarCC20Trace
          base common ccm24
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)
          scalarRemainders scalarRhExit scalarBridges)
        (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedScalarPackage
          base common ccm24
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)
          scalarRemainders scalarRhExit scalarBridges scalarFixedData))
    (scalarTraceData_lambda : scalarTraceData.lambda = traceData.lambda)
    (noExtraBulkScaleTerm : Prop)
    (noExtraBulkScaleTermHolds : noExtraBulkScaleTerm) :
    TraceScaleNoMissingBulkData
      (Source.sourceObjectPackageOfNormalizedScalarCC20Trace
        base common ccm24
        (normalizedRestrictedScalarTraceSeedOfTraceData
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData traceData)
        scalarRemainders scalarRhExit scalarBridges)
      (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedScalarPackage
        base common ccm24
        (normalizedRestrictedScalarTraceSeedOfTraceData
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData traceData)
        scalarRemainders scalarRhExit scalarBridges scalarFixedData)
      scalarTraceData.lambda scalarTraceData.ccm25ArithmeticPackage :=
  traceScaleNoMissingBulkOfNormalizedScalarTraceFront
    base common ccm24 normalizedSeed remainders rhExit bridges fixedData
    traceData scalarRemainders scalarRhExit scalarBridges scalarFixedData
    scalarTraceData scalarTraceData_lambda
    (fun _L h =>
      trace_scale_owns_sign_defect_remainder h)
    noExtraBulkScaleTerm noExtraBulkScaleTermHolds

theorem normalized_scalar_trace_scale_owns_sign_defect
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
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)))
    (scalarRhExit : Source.SourceObject.CC20RHExitObjectPackage)
    (scalarBridges :
      Source.SourceObjectCrossObjectBridges base common
        (Source.SourceObjectExpandedRows.ofNormalizedScalarCC20Trace
          ccm24
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)
          scalarRemainders)
        scalarRhExit)
    (scalarFixedData :
      FixedSTestObligationData
        (Source.sourceObjectPackageOfNormalizedScalarCC20Trace
          base common ccm24
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)
          scalarRemainders scalarRhExit scalarBridges))
    (scalarTraceData :
      TraceFrontEndData
        (Source.sourceObjectPackageOfNormalizedScalarCC20Trace
          base common ccm24
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)
          scalarRemainders scalarRhExit scalarBridges)
        (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedScalarPackage
          base common ccm24
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)
          scalarRemainders scalarRhExit scalarBridges scalarFixedData))
    (scalarTraceData_lambda : scalarTraceData.lambda = traceData.lambda)
    (noExtraBulkScaleTerm : Prop)
    (noExtraBulkScaleTermHolds : noExtraBulkScaleTerm)
    (L : RouteLedgers)
    (h :
      SourceSignDefectClassification
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedScalarCC20Trace
            base common ccm24
            (normalizedRestrictedScalarTraceSeedOfTraceData
              base common ccm24 normalizedSeed remainders rhExit bridges
              fixedData traceData)
            scalarRemainders scalarRhExit scalarBridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedScalarPackage
          base common ccm24
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)
          scalarRemainders scalarRhExit scalarBridges scalarFixedData)
        scalarTraceData.lambda L) :
    (traceScaleNoMissingBulkOfNormalizedScalarTraceFrontFromSignDefect
      base common ccm24 normalizedSeed remainders rhExit bridges fixedData
      traceData scalarRemainders scalarRhExit scalarBridges scalarFixedData
      scalarTraceData scalarTraceData_lambda noExtraBulkScaleTerm
      noExtraBulkScaleTermHolds).rankPoleCdefOwnEveryRemainder L h := by
  exact trace_scale_owns_sign_defect_remainder_holds h

noncomputable def traceScaleNoMissingBulkOfNormalizedScalarTraceFrontFromContract
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
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)))
    (scalarRhExit : Source.SourceObject.CC20RHExitObjectPackage)
    (scalarBridges :
      Source.SourceObjectCrossObjectBridges base common
        (Source.SourceObjectExpandedRows.ofNormalizedScalarCC20Trace
          ccm24
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)
          scalarRemainders)
        scalarRhExit)
    (scalarFixedData :
      FixedSTestObligationData
        (Source.sourceObjectPackageOfNormalizedScalarCC20Trace
          base common ccm24
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)
          scalarRemainders scalarRhExit scalarBridges))
    (scalarTraceData :
      TraceFrontEndData
        (Source.sourceObjectPackageOfNormalizedScalarCC20Trace
          base common ccm24
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)
          scalarRemainders scalarRhExit scalarBridges)
        (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedScalarPackage
          base common ccm24
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)
          scalarRemainders scalarRhExit scalarBridges scalarFixedData))
    (scalarTraceData_lambda : scalarTraceData.lambda = traceData.lambda)
    (noExtraBulk :
      TraceScaleNoExtraBulkContract
        (Source.sourceObjectPackageOfNormalizedScalarCC20Trace
          base common ccm24
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)
          scalarRemainders scalarRhExit scalarBridges)
        (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedScalarPackage
          base common ccm24
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)
          scalarRemainders scalarRhExit scalarBridges scalarFixedData)
        scalarTraceData.lambda scalarTraceData.ccm25ArithmeticPackage) :
    TraceScaleNoMissingBulkData
      (Source.sourceObjectPackageOfNormalizedScalarCC20Trace
        base common ccm24
        (normalizedRestrictedScalarTraceSeedOfTraceData
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData traceData)
        scalarRemainders scalarRhExit scalarBridges)
      (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedScalarPackage
        base common ccm24
        (normalizedRestrictedScalarTraceSeedOfTraceData
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData traceData)
        scalarRemainders scalarRhExit scalarBridges scalarFixedData)
      scalarTraceData.lambda scalarTraceData.ccm25ArithmeticPackage :=
  traceScaleNoMissingBulkOfNormalizedScalarTraceFront
    base common ccm24 normalizedSeed remainders rhExit bridges fixedData
    traceData scalarRemainders scalarRhExit scalarBridges scalarFixedData
    scalarTraceData scalarTraceData_lambda
    (fun _L h => trace_scale_owns_sign_defect_remainder h)
    noExtraBulk.noExtraBulkScaleTerm
    noExtraBulk.noExtraBulkScaleTermHolds

theorem normalized_scalar_trace_front_restricted_trace_equality_from_original
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
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)))
    (scalarRhExit : Source.SourceObject.CC20RHExitObjectPackage)
    (scalarBridges :
      Source.SourceObjectCrossObjectBridges base common
        (Source.SourceObjectExpandedRows.ofNormalizedScalarCC20Trace
          ccm24
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)
          scalarRemainders)
        scalarRhExit)
    (scalarFixedData :
      FixedSTestObligationData
        (Source.sourceObjectPackageOfNormalizedScalarCC20Trace
          base common ccm24
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)
          scalarRemainders scalarRhExit scalarBridges))
    (scalarTestAndQuotientCompatibility)
    (scalarFixedSSupportSquareTransport)
    (scalarFullTraceReadOffBridge)
    (scalarRestrictedTraceReadOffBridge)
    (scalarTraceScaleNoMissingBulk) :
    let scalarTraceData :=
      traceFrontEndDataOfNormalizedScalarPackageFromOriginalCCM25
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData scalarRemainders scalarRhExit scalarBridges scalarFixedData
        scalarTestAndQuotientCompatibility scalarFixedSSupportSquareTransport
        scalarFullTraceReadOffBridge scalarRestrictedTraceReadOffBridge
        scalarTraceScaleNoMissingBulk
    let scalarSourceTrace :=
      toSourceTraceReadOffDataOfNormalizedScalarPackage
        base common ccm24
        (normalizedRestrictedScalarTraceSeedOfTraceData
          base common ccm24 normalizedSeed remainders rhExit bridges fixedData
          traceData)
        scalarRemainders scalarRhExit scalarBridges scalarFixedData
        scalarTraceData
    let scalarInputs :=
      RouteInputs.ofExpandedSourcePackage
        (Source.sourceObjectPackageOfNormalizedScalarCC20Trace
          base common ccm24
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)
          scalarRemainders scalarRhExit scalarBridges)
    let scalarG :=
      FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedScalarPackage
        base common ccm24
        (normalizedRestrictedScalarTraceSeedOfTraceData
          base common ccm24 normalizedSeed remainders rhExit bridges fixedData
          traceData)
        scalarRemainders scalarRhExit scalarBridges scalarFixedData
    RestrictedTraceReadOffEquality scalarInputs
      scalarSourceTrace.archimedeanTest scalarG scalarSourceTrace.lambda := by
  intro scalarTraceData scalarSourceTrace scalarInputs scalarG
  dsimp [RestrictedTraceReadOffEquality]
  let originalSourceTrace :=
    toSourceTraceReadOffDataOfNormalizedPackage
      base common ccm24 normalizedSeed remainders rhExit bridges fixedData
      traceData
  let originalInputs :=
    RouteInputs.ofExpandedSourcePackage
      (Source.sourceObjectPackageOfNormalizedCC20Trace
        base common ccm24 normalizedSeed remainders rhExit bridges)
  let originalG :=
    FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
      base common ccm24 normalizedSeed remainders rhExit bridges fixedData
  let hsupport :
      scalarInputs.cc20.archimedeanSymbols.supportSquareTrace
          scalarSourceTrace.archimedeanTest =
        NormalizedRestrictedScalarNormalForm
          base common ccm24 normalizedSeed remainders rhExit bridges fixedData
          traceData :=
    Source.SourceObjectPackageOfData.normalized_scalar_cc20_trace_package_support_square_eq_scalar
      base common ccm24
      (normalizedRestrictedScalarTraceSeedOfTraceData
        base common ccm24 normalizedSeed remainders rhExit bridges
        fixedData traceData)
      scalarRemainders scalarRhExit scalarBridges
      scalarSourceTrace.archimedeanTest
  calc
    scalarInputs.cc20.archimedeanSymbols.supportSquareTrace
        scalarSourceTrace.archimedeanTest =
      NormalizedRestrictedScalarNormalForm
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData := hsupport
    _ =
      originalInputs.ccm25.weilSymbols.qwLambda originalSourceTrace.lambda
        originalG.weilTest originalG.weilTest :=
        (normalized_qw_lambda_reduces_to_normal_form
          base common ccm24 normalizedSeed remainders rhExit bridges fixedData
          traceData).symm
    _ =
      scalarInputs.ccm25.weilSymbols.qwLambda scalarSourceTrace.lambda
        scalarG.weilTest scalarG.weilTest := rfl

def normalizedScalarTraceFrontRestrictedTraceReadOffBridgeFromOriginal
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
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)))
    (scalarRhExit : Source.SourceObject.CC20RHExitObjectPackage)
    (scalarBridges :
      Source.SourceObjectCrossObjectBridges base common
        (Source.SourceObjectExpandedRows.ofNormalizedScalarCC20Trace
          ccm24
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)
          scalarRemainders)
        scalarRhExit)
    (scalarFixedData :
      FixedSTestObligationData
        (Source.sourceObjectPackageOfNormalizedScalarCC20Trace
          base common ccm24
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)
          scalarRemainders scalarRhExit scalarBridges))
    (scalarTestAndQuotientCompatibility)
    (scalarFixedSSupportSquareTransport)
    (scalarFullTraceReadOffBridge)
    (scalarRestrictedTraceReadOffBridge)
    (scalarTraceScaleNoMissingBulk) :
    let scalarTraceData :=
      traceFrontEndDataOfNormalizedScalarPackageFromOriginalCCM25
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData scalarRemainders scalarRhExit scalarBridges scalarFixedData
        scalarTestAndQuotientCompatibility scalarFixedSSupportSquareTransport
        scalarFullTraceReadOffBridge scalarRestrictedTraceReadOffBridge
        scalarTraceScaleNoMissingBulk
    let scalarSourceTrace :=
      toSourceTraceReadOffDataOfNormalizedScalarPackage
        base common ccm24
        (normalizedRestrictedScalarTraceSeedOfTraceData
          base common ccm24 normalizedSeed remainders rhExit bridges fixedData
          traceData)
        scalarRemainders scalarRhExit scalarBridges scalarFixedData
        scalarTraceData
    let scalarInputs :=
      RouteInputs.ofExpandedSourcePackage
        (Source.sourceObjectPackageOfNormalizedScalarCC20Trace
          base common ccm24
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)
          scalarRemainders scalarRhExit scalarBridges)
    let scalarG :=
      FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedScalarPackage
        base common ccm24
        (normalizedRestrictedScalarTraceSeedOfTraceData
          base common ccm24 normalizedSeed remainders rhExit bridges fixedData
          traceData)
        scalarRemainders scalarRhExit scalarBridges scalarFixedData
    RestrictedTraceReadOffBridgeContract scalarInputs
      scalarSourceTrace.archimedeanTest scalarG scalarSourceTrace.lambda := by
  intro scalarTraceData scalarSourceTrace scalarInputs scalarG
  exact
    { build := fun hrestricted =>
        restricted_trace_read_off_source_of_parts hrestricted
          (normalized_scalar_trace_front_restricted_trace_equality_from_original
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData scalarRemainders scalarRhExit scalarBridges
            scalarFixedData scalarTestAndQuotientCompatibility
            scalarFixedSSupportSquareTransport scalarFullTraceReadOffBridge
            scalarRestrictedTraceReadOffBridge scalarTraceScaleNoMissingBulk)
      preservesRestrictedQW := by
        intro hrestricted
        rfl }

def normalizedScalarRestrictedTraceReadOffBridgeFromOriginalCCM25
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
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)))
    (scalarRhExit : Source.SourceObject.CC20RHExitObjectPackage)
    (scalarBridges :
      Source.SourceObjectCrossObjectBridges base common
        (Source.SourceObjectExpandedRows.ofNormalizedScalarCC20Trace
          ccm24
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)
          scalarRemainders)
        scalarRhExit)
    (scalarFixedData :
      FixedSTestObligationData
        (Source.sourceObjectPackageOfNormalizedScalarCC20Trace
          base common ccm24
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)
          scalarRemainders scalarRhExit scalarBridges)) :
    let scalarPkg :=
      Source.sourceObjectPackageOfNormalizedScalarCC20Trace
        base common ccm24
        (normalizedRestrictedScalarTraceSeedOfTraceData
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData traceData)
        scalarRemainders scalarRhExit scalarBridges
    let scalarInputs := RouteInputs.ofExpandedSourcePackage scalarPkg
    let scalarG :=
      FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedScalarPackage
        base common ccm24
        (normalizedRestrictedScalarTraceSeedOfTraceData
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData traceData)
        scalarRemainders scalarRhExit scalarBridges scalarFixedData
    RestrictedTraceReadOffBridgeContract scalarInputs
      scalarPkg.cc20Trace.sourceTraceTest scalarG traceData.lambda := by
  intro scalarPkg scalarInputs scalarG
  exact
    { build := fun hrestricted =>
        restricted_trace_read_off_source_of_parts hrestricted
          (by
            dsimp [RestrictedTraceReadOffEquality]
            let originalSourceTrace :=
              toSourceTraceReadOffDataOfNormalizedPackage
                base common ccm24 normalizedSeed remainders rhExit bridges
                fixedData traceData
            let originalInputs :=
              RouteInputs.ofExpandedSourcePackage
                (Source.sourceObjectPackageOfNormalizedCC20Trace
                  base common ccm24 normalizedSeed remainders rhExit bridges)
            let originalG :=
              FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
                base common ccm24 normalizedSeed remainders rhExit bridges
                fixedData
            let hsupport :
                scalarInputs.cc20.archimedeanSymbols.supportSquareTrace
                    scalarPkg.cc20Trace.sourceTraceTest =
                  NormalizedRestrictedScalarNormalForm
                    base common ccm24 normalizedSeed remainders rhExit bridges
                    fixedData traceData :=
              SOData.normalized_scalar_trace_amplitude_sq_eq_scalar
                base common ccm24
                (normalizedRestrictedScalarTraceSeedOfTraceData
                  base common ccm24 normalizedSeed remainders rhExit bridges
                  fixedData traceData)
                scalarRemainders scalarRhExit scalarBridges
                scalarPkg.cc20Trace.sourceTraceTest
            calc
              scalarInputs.cc20.archimedeanSymbols.supportSquareTrace
                  scalarPkg.cc20Trace.sourceTraceTest =
                NormalizedRestrictedScalarNormalForm
                  base common ccm24 normalizedSeed remainders rhExit bridges
                  fixedData traceData := hsupport
              _ =
                originalInputs.ccm25.weilSymbols.qwLambda
                  originalSourceTrace.lambda originalG.weilTest
                  originalG.weilTest := by
                  exact
                    (normalized_qw_lambda_reduces_to_normal_form
                      base common ccm24 normalizedSeed remainders rhExit
                      bridges fixedData traceData).symm
              _ =
                scalarInputs.ccm25.weilSymbols.qwLambda traceData.lambda
                  scalarG.weilTest scalarG.weilTest := rfl)
      preservesRestrictedQW := by
        intro hrestricted
        rfl }

def NormalizedScalarFullTraceArchimedeanBalance
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
          fixedData)) : Prop :=
  let originalSourceTrace :=
    toSourceTraceReadOffDataOfNormalizedPackage
      base common ccm24 normalizedSeed remainders rhExit bridges fixedData
      traceData
  let originalInputs :=
    RouteInputs.ofExpandedSourcePackage
      (Source.sourceObjectPackageOfNormalizedCC20Trace
        base common ccm24 normalizedSeed remainders rhExit bridges)
  let originalG :=
    FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
      base common ccm24 normalizedSeed remainders rhExit bridges fixedData
  originalInputs.ccm25.weilSymbols.archimedeanTerm
        (originalInputs.ccm25.weilSymbols.convolutionStar
          originalG.weilTest originalG.weilTest) +
      originalInputs.ccm25.weilSymbols.polePairing originalG.weilTest -
        Source.CCM25Concrete.Package.source_restricted_finite_prime_evaluator_sum
          originalSourceTrace.ccm25ArithmeticPackage =
    originalInputs.ccm25.weilSymbols.poleFunctional
        (originalInputs.ccm25.weilSymbols.convolutionStar
          originalG.weilTest originalG.weilTest) -
      originalInputs.ccm25.weilSymbols.archimedeanTerm
        (originalInputs.ccm25.weilSymbols.convolutionStar
          originalG.weilTest originalG.weilTest) -
        Source.CCM25Concrete.Package.source_global_finite_prime_evaluator_sum
          originalSourceTrace.ccm25ArithmeticPackage

def NormalizedScalarFullTraceArchimedeanPoleBalance
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
    (_traceData :
      TraceFrontEndData
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges)
        (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)) : Prop :=
  let originalInputs :=
    RouteInputs.ofExpandedSourcePackage
      (Source.sourceObjectPackageOfNormalizedCC20Trace
        base common ccm24 normalizedSeed remainders rhExit bridges)
  let originalG :=
    FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
      base common ccm24 normalizedSeed remainders rhExit bridges fixedData
  originalInputs.ccm25.weilSymbols.archimedeanTerm
        (originalInputs.ccm25.weilSymbols.convolutionStar
          originalG.weilTest originalG.weilTest) +
      originalInputs.ccm25.weilSymbols.polePairing originalG.weilTest =
    originalInputs.ccm25.weilSymbols.poleFunctional
        (originalInputs.ccm25.weilSymbols.convolutionStar
          originalG.weilTest originalG.weilTest) -
      originalInputs.ccm25.weilSymbols.archimedeanTerm
        (originalInputs.ccm25.weilSymbols.convolutionStar
          originalG.weilTest originalG.weilTest)

theorem normalizedScalarFullTraceArchimedeanFinitePrimeBalance
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
          fixedData)) :
    let originalSourceTrace :=
      toSourceTraceReadOffDataOfNormalizedPackage
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData
    Source.CCM25Concrete.Package.source_restricted_finite_prime_evaluator_sum
        originalSourceTrace.ccm25ArithmeticPackage =
      Source.CCM25Concrete.Package.source_global_finite_prime_evaluator_sum
        originalSourceTrace.ccm25ArithmeticPackage := by
  intro originalSourceTrace
  exact
    Source.CCM25Concrete.Package.source_restricted_finite_prime_evaluator_sum_eq_global
      originalSourceTrace.ccm25ArithmeticPackage

theorem normalizedScalarFullTraceArchimedeanBalanceOfPoleBalance
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
    (hpole :
      NormalizedScalarFullTraceArchimedeanPoleBalance
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData) :
    NormalizedScalarFullTraceArchimedeanBalance
      base common ccm24 normalizedSeed remainders rhExit bridges fixedData
      traceData := by
  dsimp [NormalizedScalarFullTraceArchimedeanBalance,
    NormalizedScalarFullTraceArchimedeanPoleBalance] at *
  rw [hpole]
  rw [Source.CCM25Concrete.Package.source_restricted_finite_prime_evaluator_sum_eq_global]

theorem normalized_scalar_trace_front_full_trace_equality_from_balance
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
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)))
    (scalarRhExit : Source.SourceObject.CC20RHExitObjectPackage)
    (scalarBridges :
      Source.SourceObjectCrossObjectBridges base common
        (Source.SourceObjectExpandedRows.ofNormalizedScalarCC20Trace
          ccm24
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)
          scalarRemainders)
        scalarRhExit)
    (scalarFixedData :
      FixedSTestObligationData
        (Source.sourceObjectPackageOfNormalizedScalarCC20Trace
          base common ccm24
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)
          scalarRemainders scalarRhExit scalarBridges))
    (scalarTestAndQuotientCompatibility)
    (scalarFixedSSupportSquareTransport)
    (scalarFullTraceReadOffBridge)
    (scalarRestrictedTraceReadOffBridge)
    (scalarTraceScaleNoMissingBulk)
    (hbalance :
      NormalizedScalarFullTraceArchimedeanBalance
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData) :
    let scalarTraceData :=
      traceFrontEndDataOfNormalizedScalarPackageFromOriginalCCM25
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData scalarRemainders scalarRhExit scalarBridges scalarFixedData
        scalarTestAndQuotientCompatibility scalarFixedSSupportSquareTransport
        scalarFullTraceReadOffBridge scalarRestrictedTraceReadOffBridge
        scalarTraceScaleNoMissingBulk
    let scalarSourceTrace :=
      toSourceTraceReadOffDataOfNormalizedScalarPackage
        base common ccm24
        (normalizedRestrictedScalarTraceSeedOfTraceData
          base common ccm24 normalizedSeed remainders rhExit bridges fixedData
          traceData)
        scalarRemainders scalarRhExit scalarBridges scalarFixedData
        scalarTraceData
    let scalarInputs :=
      RouteInputs.ofExpandedSourcePackage
        (Source.sourceObjectPackageOfNormalizedScalarCC20Trace
          base common ccm24
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)
          scalarRemainders scalarRhExit scalarBridges)
    let scalarG :=
      FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedScalarPackage
        base common ccm24
        (normalizedRestrictedScalarTraceSeedOfTraceData
          base common ccm24 normalizedSeed remainders rhExit bridges fixedData
          traceData)
        scalarRemainders scalarRhExit scalarBridges scalarFixedData
    FullTraceReadOffEquality scalarInputs scalarSourceTrace.archimedeanTest
      scalarG := by
  intro scalarTraceData scalarSourceTrace scalarInputs scalarG
  dsimp [FullTraceReadOffEquality]
  let originalSourceTrace :=
    toSourceTraceReadOffDataOfNormalizedPackage
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
      originalSourceTrace.ccm25ArithmeticPackage hbalance
  let hsource :
      scalarInputs.cc20.archimedeanSymbols.sourceNoDefectTrace
          scalarSourceTrace.archimedeanTest =
        NormalizedRestrictedScalarNormalForm
          base common ccm24 normalizedSeed remainders rhExit bridges fixedData
          traceData :=
    Source.SourceObjectPackageOfData.normalized_scalar_cc20_trace_package_source_no_defect_eq_scalar
      base common ccm24
      (normalizedRestrictedScalarTraceSeedOfTraceData
        base common ccm24 normalizedSeed remainders rhExit bridges
        fixedData traceData)
      scalarRemainders scalarRhExit scalarBridges
      scalarSourceTrace.archimedeanTest
  calc
    scalarInputs.cc20.archimedeanSymbols.sourceNoDefectTrace
        scalarSourceTrace.archimedeanTest =
      NormalizedRestrictedScalarNormalForm
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData := hsource
    _ =
      originalInputs.ccm25.weilSymbols.qwLambda originalSourceTrace.lambda
        originalG.weilTest originalG.weilTest :=
        (normalized_qw_lambda_reduces_to_normal_form
          base common ccm24 normalizedSeed remainders rhExit bridges fixedData
          traceData).symm
    _ =
      originalInputs.ccm25.weilSymbols.qw originalG.weilTest
        originalG.weilTest := hrestrictedToFull
    _ =
      scalarInputs.ccm25.weilSymbols.qw scalarG.weilTest scalarG.weilTest :=
        rfl

def normalizedScalarTraceFrontFullTraceReadOffBridgeFromBalance
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
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)))
    (scalarRhExit : Source.SourceObject.CC20RHExitObjectPackage)
    (scalarBridges :
      Source.SourceObjectCrossObjectBridges base common
        (Source.SourceObjectExpandedRows.ofNormalizedScalarCC20Trace
          ccm24
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)
          scalarRemainders)
        scalarRhExit)
    (scalarFixedData :
      FixedSTestObligationData
        (Source.sourceObjectPackageOfNormalizedScalarCC20Trace
          base common ccm24
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)
          scalarRemainders scalarRhExit scalarBridges))
    (scalarTestAndQuotientCompatibility)
    (scalarFixedSSupportSquareTransport)
    (scalarFullTraceReadOffBridge)
    (scalarRestrictedTraceReadOffBridge)
    (scalarTraceScaleNoMissingBulk)
    (hbalance :
      NormalizedScalarFullTraceArchimedeanBalance
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData) :
    let scalarTraceData :=
      traceFrontEndDataOfNormalizedScalarPackageFromOriginalCCM25
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData scalarRemainders scalarRhExit scalarBridges scalarFixedData
        scalarTestAndQuotientCompatibility scalarFixedSSupportSquareTransport
        scalarFullTraceReadOffBridge scalarRestrictedTraceReadOffBridge
        scalarTraceScaleNoMissingBulk
    let scalarSourceTrace :=
      toSourceTraceReadOffDataOfNormalizedScalarPackage
        base common ccm24
        (normalizedRestrictedScalarTraceSeedOfTraceData
          base common ccm24 normalizedSeed remainders rhExit bridges fixedData
          traceData)
        scalarRemainders scalarRhExit scalarBridges scalarFixedData
        scalarTraceData
    let scalarInputs :=
      RouteInputs.ofExpandedSourcePackage
        (Source.sourceObjectPackageOfNormalizedScalarCC20Trace
          base common ccm24
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)
          scalarRemainders scalarRhExit scalarBridges)
    let scalarG :=
      FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedScalarPackage
        base common ccm24
        (normalizedRestrictedScalarTraceSeedOfTraceData
          base common ccm24 normalizedSeed remainders rhExit bridges fixedData
          traceData)
        scalarRemainders scalarRhExit scalarBridges scalarFixedData
    FullTraceReadOffBridgeContract scalarInputs
      scalarSourceTrace.archimedeanTest scalarG := by
  intro scalarTraceData scalarSourceTrace scalarInputs scalarG
  exact
    { build := fun hnoDefect hfull =>
        full_trace_read_off_source_of_parts hnoDefect hfull
          (normalized_scalar_trace_front_full_trace_equality_from_balance
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData scalarRemainders scalarRhExit scalarBridges
            scalarFixedData scalarTestAndQuotientCompatibility
            scalarFixedSSupportSquareTransport scalarFullTraceReadOffBridge
            scalarRestrictedTraceReadOffBridge scalarTraceScaleNoMissingBulk
            hbalance)
      preservesNoDefect := by
        intro hnoDefect hfull
        rfl
      preservesFullQW := by
        intro hnoDefect hfull
        rfl }

def normalizedScalarTraceFrontFullTraceReadOffBridgeFromPoleBalance
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
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)))
    (scalarRhExit : Source.SourceObject.CC20RHExitObjectPackage)
    (scalarBridges :
      Source.SourceObjectCrossObjectBridges base common
        (Source.SourceObjectExpandedRows.ofNormalizedScalarCC20Trace
          ccm24
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)
          scalarRemainders)
        scalarRhExit)
    (scalarFixedData :
      FixedSTestObligationData
        (Source.sourceObjectPackageOfNormalizedScalarCC20Trace
          base common ccm24
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)
          scalarRemainders scalarRhExit scalarBridges))
    (scalarTestAndQuotientCompatibility)
    (scalarFixedSSupportSquareTransport)
    (scalarFullTraceReadOffBridge)
    (scalarRestrictedTraceReadOffBridge)
    (scalarTraceScaleNoMissingBulk)
    (hpole :
      NormalizedScalarFullTraceArchimedeanPoleBalance
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData) :
    let scalarTraceData :=
      traceFrontEndDataOfNormalizedScalarPackageFromOriginalCCM25
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData scalarRemainders scalarRhExit scalarBridges scalarFixedData
        scalarTestAndQuotientCompatibility scalarFixedSSupportSquareTransport
        scalarFullTraceReadOffBridge scalarRestrictedTraceReadOffBridge
        scalarTraceScaleNoMissingBulk
    let scalarSourceTrace :=
      toSourceTraceReadOffDataOfNormalizedScalarPackage
        base common ccm24
        (normalizedRestrictedScalarTraceSeedOfTraceData
          base common ccm24 normalizedSeed remainders rhExit bridges fixedData
          traceData)
        scalarRemainders scalarRhExit scalarBridges scalarFixedData
        scalarTraceData
    let scalarInputs :=
      RouteInputs.ofExpandedSourcePackage
        (Source.sourceObjectPackageOfNormalizedScalarCC20Trace
          base common ccm24
          (normalizedRestrictedScalarTraceSeedOfTraceData
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData)
          scalarRemainders scalarRhExit scalarBridges)
    let scalarG :=
      FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedScalarPackage
        base common ccm24
        (normalizedRestrictedScalarTraceSeedOfTraceData
          base common ccm24 normalizedSeed remainders rhExit bridges fixedData
          traceData)
        scalarRemainders scalarRhExit scalarBridges scalarFixedData
    FullTraceReadOffBridgeContract scalarInputs
      scalarSourceTrace.archimedeanTest scalarG :=
  normalizedScalarTraceFrontFullTraceReadOffBridgeFromBalance
    base common ccm24 normalizedSeed remainders rhExit bridges fixedData
    traceData scalarRemainders scalarRhExit scalarBridges scalarFixedData
    scalarTestAndQuotientCompatibility scalarFixedSSupportSquareTransport
    scalarFullTraceReadOffBridge scalarRestrictedTraceReadOffBridge
    scalarTraceScaleNoMissingBulk
    (normalizedScalarFullTraceArchimedeanBalanceOfPoleBalance
      base common ccm24 normalizedSeed remainders rhExit bridges fixedData
      traceData hpole)

/--
Pointwise support-square read-off for the scalar seed built from the normalized
restricted CCM25 normal form.

This is deliberately pointwise.  It does not construct
`CC20TracePackageRemainderData` for the scalar package, because that would
require a global Hilbert-Schmidt gate for every test in the scalar seed.
-/
theorem normalized_restricted_scalar_seed_support_square_eq_normal_form
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
    (a :
      (normalizedRestrictedScalarTraceSeedOfTraceData
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData).Test) :
    let scalarSeed :=
      normalizedRestrictedScalarTraceSeedOfTraceData
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData
    scalarSeed.toArchimedeanTraceSymbols.supportSquareTrace a =
      NormalizedRestrictedScalarNormalForm
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData := by
  intro scalarSeed
  open Source.CC20Concrete.TraceScale.NormalizedScalarTraceScaleSymbols in
  exact support_square_trace_eq_scalar scalarSeed a

theorem normalized_restricted_scalar_seed_positive_trace_eq_normal_form
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
    (a :
      (normalizedRestrictedScalarTraceSeedOfTraceData
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData).Test) :
    let scalarSeed :=
      normalizedRestrictedScalarTraceSeedOfTraceData
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData
    scalarSeed.toArchimedeanTraceSymbols.positiveTrace a =
      NormalizedRestrictedScalarNormalForm
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData := by
  intro scalarSeed
  rfl

theorem normalized_restricted_scalar_seed_source_no_defect_eq_qw_lambda
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
    (a :
      (normalizedRestrictedScalarTraceSeedOfTraceData
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData).Test) :
    let sourceTrace :=
      toSourceTraceReadOffDataOfNormalizedPackage
        base common ccm24 normalizedSeed remainders rhExit bridges
        fixedData traceData
    let inputs :=
      RouteInputs.ofExpandedSourcePackage
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges)
    let g :=
      FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
    let scalarSeed :=
      normalizedRestrictedScalarTraceSeedOfTraceData
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData
    scalarSeed.toArchimedeanTraceSymbols.sourceNoDefectTrace a =
      inputs.ccm25.weilSymbols.qwLambda sourceTrace.lambda
        g.weilTest g.weilTest := by
  intro sourceTrace inputs g scalarSeed
  calc
    scalarSeed.toArchimedeanTraceSymbols.sourceNoDefectTrace a =
      NormalizedRestrictedScalarNormalForm
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData := by
        exact
          normalized_restricted_scalar_seed_source_no_defect_eq_normal_form
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData
            (normalized_restricted_scalar_normal_form_nonnegative
              base common ccm24 normalizedSeed remainders rhExit bridges
              fixedData traceData)
            a
    _ = inputs.ccm25.weilSymbols.qwLambda sourceTrace.lambda
        g.weilTest g.weilTest := by
        exact
          (normalized_qw_lambda_reduces_to_normal_form
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData).symm

theorem normalized_restricted_scalar_seed_support_square_eq_qw_lambda
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
    (a :
      (normalizedRestrictedScalarTraceSeedOfTraceData
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData).Test) :
    let sourceTrace :=
      toSourceTraceReadOffDataOfNormalizedPackage
        base common ccm24 normalizedSeed remainders rhExit bridges
        fixedData traceData
    let inputs :=
      RouteInputs.ofExpandedSourcePackage
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges)
    let g :=
      FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
    let scalarSeed :=
      normalizedRestrictedScalarTraceSeedOfTraceData
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData
    scalarSeed.toArchimedeanTraceSymbols.supportSquareTrace a =
      inputs.ccm25.weilSymbols.qwLambda sourceTrace.lambda
        g.weilTest g.weilTest := by
  intro sourceTrace inputs g scalarSeed
  calc
    scalarSeed.toArchimedeanTraceSymbols.supportSquareTrace a =
      NormalizedRestrictedScalarNormalForm
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData := by
        exact
          normalized_restricted_scalar_seed_support_square_eq_normal_form
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData a
    _ = inputs.ccm25.weilSymbols.qwLambda sourceTrace.lambda
        g.weilTest g.weilTest := by
        exact
          (normalized_qw_lambda_reduces_to_normal_form
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData).symm

theorem normalized_restricted_scalar_seed_positive_trace_eq_qw_lambda
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
    (a :
      (normalizedRestrictedScalarTraceSeedOfTraceData
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData).Test) :
    let sourceTrace :=
      toSourceTraceReadOffDataOfNormalizedPackage
        base common ccm24 normalizedSeed remainders rhExit bridges
        fixedData traceData
    let inputs :=
      RouteInputs.ofExpandedSourcePackage
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges)
    let g :=
      FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
    let scalarSeed :=
      normalizedRestrictedScalarTraceSeedOfTraceData
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData
    scalarSeed.toArchimedeanTraceSymbols.positiveTrace a =
      inputs.ccm25.weilSymbols.qwLambda sourceTrace.lambda
        g.weilTest g.weilTest := by
  intro sourceTrace inputs g scalarSeed
  calc
    scalarSeed.toArchimedeanTraceSymbols.positiveTrace a =
      NormalizedRestrictedScalarNormalForm
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData := by
        exact
          normalized_restricted_scalar_seed_positive_trace_eq_normal_form
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData a
    _ = inputs.ccm25.weilSymbols.qwLambda sourceTrace.lambda
        g.weilTest g.weilTest := by
        exact
          (normalized_qw_lambda_reduces_to_normal_form
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData traceData).symm

structure NormalizedRestrictedScalarRouteTestCertificate
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
  routeHilbertSchmidtGate :
    let sourceTrace :=
      toSourceTraceReadOffDataOfNormalizedPackage
        base common ccm24 normalizedSeed remainders rhExit bridges
        fixedData traceData
    let scalarSeed :=
      normalizedRestrictedScalarTraceSeedOfTraceData
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData
    scalarSeed.toArchimedeanTraceSymbols.hilbertSchmidtGate
      sourceTrace.archimedeanTest
  routeSourceNoDefectMatchesQWLambda :
    let sourceTrace :=
      toSourceTraceReadOffDataOfNormalizedPackage
        base common ccm24 normalizedSeed remainders rhExit bridges
        fixedData traceData
    let inputs :=
      RouteInputs.ofExpandedSourcePackage
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges)
    let g :=
      FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
    let scalarSeed :=
      normalizedRestrictedScalarTraceSeedOfTraceData
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData
    scalarSeed.toArchimedeanTraceSymbols.sourceNoDefectTrace
        sourceTrace.archimedeanTest =
      inputs.ccm25.weilSymbols.qwLambda sourceTrace.lambda
        g.weilTest g.weilTest
  routeSupportSquareMatchesQWLambda :
    let sourceTrace :=
      toSourceTraceReadOffDataOfNormalizedPackage
        base common ccm24 normalizedSeed remainders rhExit bridges
        fixedData traceData
    let inputs :=
      RouteInputs.ofExpandedSourcePackage
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges)
    let g :=
      FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
    let scalarSeed :=
      normalizedRestrictedScalarTraceSeedOfTraceData
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData
    scalarSeed.toArchimedeanTraceSymbols.supportSquareTrace
        sourceTrace.archimedeanTest =
      inputs.ccm25.weilSymbols.qwLambda sourceTrace.lambda
        g.weilTest g.weilTest
  routePositiveTraceMatchesQWLambda :
    let sourceTrace :=
      toSourceTraceReadOffDataOfNormalizedPackage
        base common ccm24 normalizedSeed remainders rhExit bridges
        fixedData traceData
    let inputs :=
      RouteInputs.ofExpandedSourcePackage
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges)
    let g :=
      FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
    let scalarSeed :=
      normalizedRestrictedScalarTraceSeedOfTraceData
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData
    scalarSeed.toArchimedeanTraceSymbols.positiveTrace
        sourceTrace.archimedeanTest =
      inputs.ccm25.weilSymbols.qwLambda sourceTrace.lambda
        g.weilTest g.weilTest
  routePositiveTraceNonnegative :
    let sourceTrace :=
      toSourceTraceReadOffDataOfNormalizedPackage
        base common ccm24 normalizedSeed remainders rhExit bridges
        fixedData traceData
    let scalarSeed :=
      normalizedRestrictedScalarTraceSeedOfTraceData
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData
    0 ≤ scalarSeed.toArchimedeanTraceSymbols.positiveTrace
      sourceTrace.archimedeanTest

theorem normalized_restricted_scalar_seed_route_hilbert_schmidt
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
          fixedData)) :
    let sourceTrace :=
      toSourceTraceReadOffDataOfNormalizedPackage
        base common ccm24 normalizedSeed remainders rhExit bridges
        fixedData traceData
    let scalarSeed :=
      normalizedRestrictedScalarTraceSeedOfTraceData
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData
    scalarSeed.toArchimedeanTraceSymbols.hilbertSchmidtGate
      sourceTrace.archimedeanTest := by
  intro sourceTrace scalarSeed
  exact
    ⟨(cc20_trace_legality_of_source_trace_data sourceTrace).traceClass,
      (cc20_trace_legality_of_source_trace_data sourceTrace).cyclicLegal⟩

theorem normalized_restricted_scalar_seed_route_positive_trace_nonnegative
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
          fixedData)) :
    let sourceTrace :=
      toSourceTraceReadOffDataOfNormalizedPackage
        base common ccm24 normalizedSeed remainders rhExit bridges
        fixedData traceData
    let scalarSeed :=
      normalizedRestrictedScalarTraceSeedOfTraceData
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData
    0 ≤ scalarSeed.toArchimedeanTraceSymbols.positiveTrace
      sourceTrace.archimedeanTest := by
  intro sourceTrace scalarSeed
  exact
    normalized_restricted_scalar_seed_positive_trace_eq_normal_form
      base common ccm24 normalizedSeed remainders rhExit bridges fixedData
      traceData sourceTrace.archimedeanTest ▸
      normalized_restricted_scalar_normal_form_nonnegative
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData

def normalizedRestrictedScalarRouteTestCertificate
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
          fixedData)) :
    NormalizedRestrictedScalarRouteTestCertificate
      base common ccm24 normalizedSeed remainders rhExit bridges fixedData
      traceData where
  routeHilbertSchmidtGate :=
    normalized_restricted_scalar_seed_route_hilbert_schmidt
      base common ccm24 normalizedSeed remainders rhExit bridges fixedData
      traceData
  routeSourceNoDefectMatchesQWLambda :=
    normalized_restricted_scalar_seed_source_no_defect_eq_qw_lambda
      base common ccm24 normalizedSeed remainders rhExit bridges fixedData
      traceData
      (toSourceTraceReadOffDataOfNormalizedPackage
        base common ccm24 normalizedSeed remainders rhExit bridges
        fixedData traceData).archimedeanTest
  routeSupportSquareMatchesQWLambda :=
    normalized_restricted_scalar_seed_support_square_eq_qw_lambda
      base common ccm24 normalizedSeed remainders rhExit bridges fixedData
      traceData
      (toSourceTraceReadOffDataOfNormalizedPackage
        base common ccm24 normalizedSeed remainders rhExit bridges
        fixedData traceData).archimedeanTest
  routePositiveTraceMatchesQWLambda :=
    normalized_restricted_scalar_seed_positive_trace_eq_qw_lambda
      base common ccm24 normalizedSeed remainders rhExit bridges fixedData
      traceData
      (toSourceTraceReadOffDataOfNormalizedPackage
        base common ccm24 normalizedSeed remainders rhExit bridges
        fixedData traceData).archimedeanTest
  routePositiveTraceNonnegative :=
    normalized_restricted_scalar_seed_route_positive_trace_nonnegative
      base common ccm24 normalizedSeed remainders rhExit bridges fixedData
      traceData

theorem normalized_support_square_comparison_reduces_to_normal_form
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
      NormalizedSupportSquareQWLambdaSourceComparison
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData) :
    let sourceTrace :=
      toSourceTraceReadOffDataOfNormalizedPackage
        base common ccm24 normalizedSeed remainders rhExit bridges
        fixedData traceData
    let inputs :=
      RouteInputs.ofExpandedSourcePackage
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges)
    inputs.cc20.archimedeanSymbols.supportSquareTrace
        sourceTrace.archimedeanTest =
      NormalizedRestrictedScalarNormalForm
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData := by
  dsimp [NormalizedRestrictedScalarNormalForm]
  exact comparison.supportSquareMatchesPackageQWLambdaFormula

def normalizedRestrictedTraceEqualityContractOfPackageBridge
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
          fixedData)) :
    NormalizedRestrictedTraceEqualityContract
      base common ccm24 normalizedSeed remainders rhExit bridges fixedData
      traceData where
  sourceTrace :=
    toSourceTraceReadOffDataOfNormalizedPackage
      base common ccm24 normalizedSeed remainders rhExit bridges
      fixedData traceData
  sourceTrace_eq_normalized := rfl
  packageRestrictedQW :=
    ccm25_restricted_qw_read_off_of_package
      (toSourceTraceReadOffDataOfNormalizedPackage
        base common ccm24 normalizedSeed remainders rhExit bridges
        fixedData traceData).ccm25ArithmeticPackage
      (window_lambda_compatibility_of_source_backed
        (toSourceTraceReadOffDataOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData traceData).oneLtLambda)
  packageRestrictedQW_eq := rfl
  restrictedSource :=
    restrictedTraceReadOffSourceOfNormalizedPackage
      base common ccm24 normalizedSeed remainders rhExit bridges
      fixedData traceData
  restrictedSource_eq_bridge := rfl
  restrictedTraceReadOffEquality :=
    (restrictedTraceReadOffSourceOfNormalizedPackage
      base common ccm24 normalizedSeed remainders rhExit bridges
      fixedData traceData).restrictedTraceReadOffEquality
  restrictedTraceReadOffEquality_eq_bridge := rfl

theorem normalized_restricted_trace_equality_of_source_comparison
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
      NormalizedSupportSquareQWLambdaSourceComparison
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData) :
    let sourceTrace :=
      toSourceTraceReadOffDataOfNormalizedPackage
        base common ccm24 normalizedSeed remainders rhExit bridges
        fixedData traceData
    RestrictedTraceReadOffEquality
      (RouteInputs.ofExpandedSourcePackage
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges))
      sourceTrace.archimedeanTest
      (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData)
      sourceTrace.lambda := by
  dsimp [RestrictedTraceReadOffEquality]
  let sourceTrace :=
    toSourceTraceReadOffDataOfNormalizedPackage
      base common ccm24 normalizedSeed remainders rhExit bridges
      fixedData traceData
  let inputs :=
    RouteInputs.ofExpandedSourcePackage
      (Source.sourceObjectPackageOfNormalizedCC20Trace
        base common ccm24 normalizedSeed remainders rhExit bridges)
  let g :=
    FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
      base common ccm24 normalizedSeed remainders rhExit bridges fixedData
  calc
    inputs.cc20.archimedeanSymbols.supportSquareTrace
        sourceTrace.archimedeanTest =
      NormalizedRestrictedScalarNormalForm
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData :=
        normalized_support_square_comparison_reduces_to_normal_form
          base common ccm24 normalizedSeed remainders rhExit bridges fixedData
          traceData comparison
    _ = inputs.ccm25.weilSymbols.qwLambda sourceTrace.lambda
        g.weilTest g.weilTest :=
        (normalized_qw_lambda_reduces_to_normal_form
          base common ccm24 normalizedSeed remainders rhExit bridges fixedData
          traceData).symm

def normalizedRestrictedTraceSourceOfSourceComparison
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
      NormalizedSupportSquareQWLambdaSourceComparison
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData) :
    let sourceTrace :=
      toSourceTraceReadOffDataOfNormalizedPackage
        base common ccm24 normalizedSeed remainders rhExit bridges
        fixedData traceData
    RestrictedTraceReadOffSource
      (RouteInputs.ofExpandedSourcePackage
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges))
      sourceTrace.archimedeanTest
      (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData)
      sourceTrace.lambda :=
  let sourceTrace :=
    toSourceTraceReadOffDataOfNormalizedPackage
      base common ccm24 normalizedSeed remainders rhExit bridges
      fixedData traceData
  restricted_trace_read_off_source_of_parts
    (ccm25_restricted_qw_read_off_of_package
      sourceTrace.ccm25ArithmeticPackage
      (window_lambda_compatibility_of_source_backed sourceTrace.oneLtLambda))
    (normalized_restricted_trace_equality_of_source_comparison
      base common ccm24 normalizedSeed remainders rhExit bridges fixedData
      traceData comparison)

theorem normalized_restricted_trace_source_comparison_preserves_package_qw
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
      NormalizedSupportSquareQWLambdaSourceComparison
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData) :
    let sourceTrace :=
      toSourceTraceReadOffDataOfNormalizedPackage
        base common ccm24 normalizedSeed remainders rhExit bridges
        fixedData traceData
    (normalizedRestrictedTraceSourceOfSourceComparison
      base common ccm24 normalizedSeed remainders rhExit bridges fixedData
      traceData comparison).ccm25RestrictedQWReadOff =
      ccm25_restricted_qw_read_off_of_package
        sourceTrace.ccm25ArithmeticPackage
        (window_lambda_compatibility_of_source_backed sourceTrace.oneLtLambda) := by
  rfl

theorem normalized_restricted_trace_source_comparison_equality
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
      NormalizedSupportSquareQWLambdaSourceComparison
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData) :
    (normalizedRestrictedTraceSourceOfSourceComparison
      base common ccm24 normalizedSeed remainders rhExit bridges fixedData
      traceData comparison).restrictedTraceReadOffEquality =
      normalized_restricted_trace_equality_of_source_comparison
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData comparison := by
  rfl

theorem normalized_source_no_defect_reduces_to_normal_form_of_comparison
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
      NormalizedSupportSquareQWLambdaSourceComparison
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData) :
    let sourceTrace :=
      toSourceTraceReadOffDataOfNormalizedPackage
        base common ccm24 normalizedSeed remainders rhExit bridges
        fixedData traceData
    let inputs :=
      RouteInputs.ofExpandedSourcePackage
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges)
    inputs.cc20.archimedeanSymbols.sourceNoDefectTrace
        sourceTrace.archimedeanTest =
      NormalizedRestrictedScalarNormalForm
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData := by
  let sourceTrace :=
    toSourceTraceReadOffDataOfNormalizedPackage
      base common ccm24 normalizedSeed remainders rhExit bridges
      fixedData traceData
  let inputs :=
    RouteInputs.ofExpandedSourcePackage
      (Source.sourceObjectPackageOfNormalizedCC20Trace
        base common ccm24 normalizedSeed remainders rhExit bridges)
  let supportSquareNoDefect :=
    Source.SourceObjectPackageOfData.normalized_cc20_trace_package_support_square_no_defect
      base common ccm24 normalizedSeed remainders rhExit bridges
      sourceTrace.archimedeanTest
      (cc20_trace_legality_of_source_trace_data sourceTrace).traceClass
      (cc20_trace_legality_of_source_trace_data sourceTrace).cyclicLegal
  exact supportSquareNoDefect.symm.trans
    (normalized_support_square_comparison_reduces_to_normal_form
      base common ccm24 normalizedSeed remainders rhExit bridges fixedData
      traceData comparison)

def noDefectQWLambdaTheoremDataOfNormalizedPackageFromComparison
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
      NormalizedSupportSquareQWLambdaSourceComparison
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData) :
    NoDefectQWLambdaTheoremData
      (Source.sourceObjectPackageOfNormalizedCC20Trace
        base common ccm24 normalizedSeed remainders rhExit bridges)
      (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData)
      traceData.lambda traceData.ccm25ArithmeticPackage :=
  let sourceTrace :=
    toSourceTraceReadOffDataOfNormalizedPackage
      base common ccm24 normalizedSeed remainders rhExit bridges
      fixedData traceData
  let inputs :=
    RouteInputs.ofExpandedSourcePackage
      (Source.sourceObjectPackageOfNormalizedCC20Trace
        base common ccm24 normalizedSeed remainders rhExit bridges)
  let g :=
    FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
      base common ccm24 normalizedSeed remainders rhExit bridges fixedData
  let supportSquareNoDefect :=
    Source.SourceObjectPackageOfData.normalized_cc20_trace_package_support_square_no_defect
      base common ccm24 normalizedSeed remainders rhExit bridges
      sourceTrace.archimedeanTest
      (cc20_trace_legality_of_source_trace_data sourceTrace).traceClass
      (cc20_trace_legality_of_source_trace_data sourceTrace).cyclicLegal
  { supportSquareMatchesNoDefectSource :=
      inputs.cc20.archimedeanSymbols.supportSquareTrace
          sourceTrace.archimedeanTest =
        inputs.cc20.archimedeanSymbols.sourceNoDefectTrace
          sourceTrace.archimedeanTest
    noDefectSourceMatchesQWLambda :=
      inputs.cc20.archimedeanSymbols.sourceNoDefectTrace
          sourceTrace.archimedeanTest =
        inputs.ccm25.weilSymbols.qwLambda traceData.lambda g.weilTest
          g.weilTest
    supportSquareMatchesNoDefectSourceHolds := supportSquareNoDefect
    noDefectSourceMatchesQWLambdaHolds :=
      calc
        inputs.cc20.archimedeanSymbols.sourceNoDefectTrace
            sourceTrace.archimedeanTest =
          NormalizedRestrictedScalarNormalForm
            base common ccm24 normalizedSeed remainders rhExit bridges fixedData
            traceData :=
            normalized_source_no_defect_reduces_to_normal_form_of_comparison
              base common ccm24 normalizedSeed remainders rhExit bridges fixedData
              traceData comparison
        _ = inputs.ccm25.weilSymbols.qwLambda traceData.lambda g.weilTest
            g.weilTest :=
            (normalized_qw_lambda_reduces_to_normal_form
              base common ccm24 normalizedSeed remainders rhExit bridges
              fixedData traceData).symm }

def traceScaleNoMissingBulkOfNormalizedPackageFromComparison
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
      NormalizedSupportSquareQWLambdaSourceComparison
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData)
    (rankPoleCdefOwnEveryRemainder :
      (L : RouteLedgers) ->
        SourceSignDefectClassification
          (RouteInputs.ofExpandedSourcePackage
            (Source.sourceObjectPackageOfNormalizedCC20Trace
              base common ccm24 normalizedSeed remainders rhExit bridges))
          (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData)
          traceData.lambda L -> Prop)
    (noExtraBulkScaleTerm : Prop)
    (noExtraBulkScaleTermHolds : noExtraBulkScaleTerm) :
    TraceScaleNoMissingBulkData
      (Source.sourceObjectPackageOfNormalizedCC20Trace
        base common ccm24 normalizedSeed remainders rhExit bridges)
      (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData)
      traceData.lambda traceData.ccm25ArithmeticPackage :=
  trace_scale_no_missing_bulk_of_scalar_theorem_data
    (ordinaryTraceSupportSquareTheoremDataOfNormalizedPackage
      base common ccm24 normalizedSeed remainders rhExit bridges fixedData
      traceData)
    (noDefectQWLambdaTheoremDataOfNormalizedPackageFromComparison
      base common ccm24 normalizedSeed remainders rhExit bridges fixedData
      traceData comparison)
    rankPoleCdefOwnEveryRemainder noExtraBulkScaleTerm
    noExtraBulkScaleTermHolds

theorem trace_scale_no_missing_bulk_comparison_no_defect_qw_lambda_holds
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
      NormalizedSupportSquareQWLambdaSourceComparison
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData)
    (rankPoleCdefOwnEveryRemainder :
      (L : RouteLedgers) ->
        SourceSignDefectClassification
          (RouteInputs.ofExpandedSourcePackage
            (Source.sourceObjectPackageOfNormalizedCC20Trace
              base common ccm24 normalizedSeed remainders rhExit bridges))
          (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData)
          traceData.lambda L -> Prop)
    (noExtraBulkScaleTerm : Prop)
    (noExtraBulkScaleTermHolds : noExtraBulkScaleTerm) :
    (traceScaleNoMissingBulkOfNormalizedPackageFromComparison
      base common ccm24 normalizedSeed remainders rhExit bridges fixedData
      traceData comparison rankPoleCdefOwnEveryRemainder noExtraBulkScaleTerm
      noExtraBulkScaleTermHolds).noDefectSourceMatchesQWLambda := by
  exact
    (traceScaleNoMissingBulkOfNormalizedPackageFromComparison
      base common ccm24 normalizedSeed remainders rhExit bridges fixedData
      traceData comparison rankPoleCdefOwnEveryRemainder noExtraBulkScaleTerm
      noExtraBulkScaleTermHolds).noDefectSourceMatchesQWLambdaHolds

theorem trace_scale_no_missing_bulk_comparison_support_square_holds
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
      NormalizedSupportSquareQWLambdaSourceComparison
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData)
    (rankPoleCdefOwnEveryRemainder :
      (L : RouteLedgers) ->
        SourceSignDefectClassification
          (RouteInputs.ofExpandedSourcePackage
            (Source.sourceObjectPackageOfNormalizedCC20Trace
              base common ccm24 normalizedSeed remainders rhExit bridges))
          (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
            base common ccm24 normalizedSeed remainders rhExit bridges
            fixedData)
          traceData.lambda L -> Prop)
    (noExtraBulkScaleTerm : Prop)
    (noExtraBulkScaleTermHolds : noExtraBulkScaleTerm) :
    (traceScaleNoMissingBulkOfNormalizedPackageFromComparison
      base common ccm24 normalizedSeed remainders rhExit bridges fixedData
      traceData comparison rankPoleCdefOwnEveryRemainder noExtraBulkScaleTerm
      noExtraBulkScaleTermHolds).supportSquareMatchesNoDefectSource := by
  exact
    (traceScaleNoMissingBulkOfNormalizedPackageFromComparison
      base common ccm24 normalizedSeed remainders rhExit bridges fixedData
      traceData comparison rankPoleCdefOwnEveryRemainder noExtraBulkScaleTerm
      noExtraBulkScaleTermHolds).supportSquareMatchesNoDefectSourceHolds

/--
Replace only the stored trace-scale no-missing-bulk ledger by the normalized
comparison-backed ledger.

The trace/front-end fields used to build `SourceTraceReadOffData` are copied
unchanged.  This is a plumbing constructor: it removes a later equality
obligation about the stored ledger, but it does not discharge the analytic
`NormalizedSupportSquareQWLambdaSourceComparison` input.
-/
def withTraceScaleNoMissingBulkOfNormalizedComparison
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
      NormalizedSupportSquareQWLambdaSourceComparison
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData) :
    TraceFrontEndData
      (Source.sourceObjectPackageOfNormalizedCC20Trace
        base common ccm24 normalizedSeed remainders rhExit bridges)
      (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData) where
  lambda := traceData.lambda
  oneLtLambda := traceData.oneLtLambda
  ccm25ArithmeticPackage := traceData.ccm25ArithmeticPackage
  testAndQuotientCompatibility := traceData.testAndQuotientCompatibility
  fixedSSupportSquareTransport := traceData.fixedSSupportSquareTransport
  fullTraceReadOffBridge := traceData.fullTraceReadOffBridge
  restrictedTraceReadOffBridge := traceData.restrictedTraceReadOffBridge
  traceScaleNoMissingBulk :=
    traceScaleNoMissingBulkOfNormalizedPackageFromComparison
      base common ccm24 normalizedSeed remainders rhExit bridges fixedData
      traceData comparison
      (fun L _h =>
        SourceSignDefectClassification
          (RouteInputs.ofExpandedSourcePackage
            (Source.sourceObjectPackageOfNormalizedCC20Trace
              base common ccm24 normalizedSeed remainders rhExit bridges))
          (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
            base common ccm24 normalizedSeed remainders rhExit bridges fixedData)
          traceData.lambda L)
      True trivial

theorem normalized_comparison_trace_scale_replacement_matches_generated
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
      NormalizedSupportSquareQWLambdaSourceComparison
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData) :
    (withTraceScaleNoMissingBulkOfNormalizedComparison
      base common ccm24 normalizedSeed remainders rhExit bridges fixedData
      traceData comparison).traceScaleNoMissingBulk =
      traceScaleNoMissingBulkOfNormalizedPackageFromComparison
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData comparison
        (fun L _h =>
          SourceSignDefectClassification
            (RouteInputs.ofExpandedSourcePackage
              (Source.sourceObjectPackageOfNormalizedCC20Trace
                base common ccm24 normalizedSeed remainders rhExit bridges))
            (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
              base common ccm24 normalizedSeed remainders rhExit bridges fixedData)
            traceData.lambda L)
        True trivial :=
  rfl

theorem normalized_comparison_trace_scale_replacement_owns_sign_defect
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
      NormalizedSupportSquareQWLambdaSourceComparison
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData)
    (ledgers : RouteLedgers)
    (signDefectClassification :
      SourceSignDefectClassification
        (RouteInputs.ofExpandedSourcePackage
          (Source.sourceObjectPackageOfNormalizedCC20Trace
            base common ccm24 normalizedSeed remainders rhExit bridges))
        (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges fixedData)
        traceData.lambda ledgers) :
    (withTraceScaleNoMissingBulkOfNormalizedComparison
      base common ccm24 normalizedSeed remainders rhExit bridges fixedData
      traceData comparison).traceScaleNoMissingBulk.rankPoleCdefOwnEveryRemainder
      ledgers signDefectClassification :=
  signDefectClassification

/--
Contract-backed variant of
`withTraceScaleNoMissingBulkOfNormalizedComparison`.

The old replacement constructor keeps `True` as the no-extra-bulk placeholder
for compatibility.  This variant exposes the no-extra-bulk scale term through
`TraceScaleNoExtraBulkContract`, so later route endpoints can depend on the
named analytic contract instead of a silent trivial proposition.
-/
def withTraceScaleNoMissingBulkOfNormalizedComparisonFromContract
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
      NormalizedSupportSquareQWLambdaSourceComparison
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData)
    (noExtraBulk :
      TraceScaleNoExtraBulkContract
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges)
        (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges fixedData)
        traceData.lambda traceData.ccm25ArithmeticPackage) :
    TraceFrontEndData
      (Source.sourceObjectPackageOfNormalizedCC20Trace
        base common ccm24 normalizedSeed remainders rhExit bridges)
      (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData) where
  lambda := traceData.lambda
  oneLtLambda := traceData.oneLtLambda
  ccm25ArithmeticPackage := traceData.ccm25ArithmeticPackage
  testAndQuotientCompatibility := traceData.testAndQuotientCompatibility
  fixedSSupportSquareTransport := traceData.fixedSSupportSquareTransport
  fullTraceReadOffBridge := traceData.fullTraceReadOffBridge
  restrictedTraceReadOffBridge := traceData.restrictedTraceReadOffBridge
  traceScaleNoMissingBulk :=
    traceScaleNoMissingBulkOfNormalizedPackageFromComparison
      base common ccm24 normalizedSeed remainders rhExit bridges fixedData
      traceData comparison
      (fun _L h => trace_scale_owns_sign_defect_remainder h)
      noExtraBulk.noExtraBulkScaleTerm
      noExtraBulk.noExtraBulkScaleTermHolds

theorem normalized_comparison_trace_scale_contract_replacement_owns_sign_defect
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
      NormalizedSupportSquareQWLambdaSourceComparison
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData)
    (noExtraBulk :
      TraceScaleNoExtraBulkContract
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
          base common ccm24 normalizedSeed remainders rhExit bridges fixedData)
        traceData.lambda ledgers) :
    let contractTraceData :=
      withTraceScaleNoMissingBulkOfNormalizedComparisonFromContract
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData
        traceData comparison noExtraBulk
    contractTraceData.traceScaleNoMissingBulk.rankPoleCdefOwnEveryRemainder
      ledgers signDefectClassification := by
  exact noExtraBulk.traceScaleOwnership ledgers signDefectClassification

def noDefectQWLambdaTheoremDataOfNormalizedPackage
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
          fixedData)) :
    NoDefectQWLambdaTheoremData
      (Source.sourceObjectPackageOfNormalizedCC20Trace
        base common ccm24 normalizedSeed remainders rhExit bridges)
      (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData)
      traceData.lambda traceData.ccm25ArithmeticPackage :=
  let sourceTrace :=
    toSourceTraceReadOffDataOfNormalizedPackage
      base common ccm24 normalizedSeed remainders rhExit bridges
      fixedData traceData
  let inputs :=
    RouteInputs.ofExpandedSourcePackage
      (Source.sourceObjectPackageOfNormalizedCC20Trace
        base common ccm24 normalizedSeed remainders rhExit bridges)
  let g :=
    FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
      base common ccm24 normalizedSeed remainders rhExit bridges fixedData
  let supportSquareNoDefect :=
    Source.SourceObjectPackageOfData.normalized_cc20_trace_package_support_square_no_defect
      base common ccm24 normalizedSeed remainders rhExit bridges
      sourceTrace.archimedeanTest
      (cc20_trace_legality_of_source_trace_data sourceTrace).traceClass
      (cc20_trace_legality_of_source_trace_data sourceTrace).cyclicLegal
  let restricted :=
    (restrictedTraceReadOffSourceOfNormalizedPackage
      base common ccm24 normalizedSeed remainders rhExit bridges
      fixedData traceData).restrictedTraceReadOffEquality
  { supportSquareMatchesNoDefectSource :=
      inputs.cc20.archimedeanSymbols.supportSquareTrace
          sourceTrace.archimedeanTest =
        inputs.cc20.archimedeanSymbols.sourceNoDefectTrace
          sourceTrace.archimedeanTest
    noDefectSourceMatchesQWLambda :=
      inputs.cc20.archimedeanSymbols.sourceNoDefectTrace
          sourceTrace.archimedeanTest =
        inputs.ccm25.weilSymbols.qwLambda traceData.lambda g.weilTest
          g.weilTest
    supportSquareMatchesNoDefectSourceHolds := supportSquareNoDefect
    noDefectSourceMatchesQWLambdaHolds := supportSquareNoDefect.symm.trans
      restricted }

theorem normalized_package_no_defect_qw_lambda_holds
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
          fixedData)) :
    (noDefectQWLambdaTheoremDataOfNormalizedPackage
      base common ccm24 normalizedSeed remainders rhExit bridges
      fixedData traceData).noDefectSourceMatchesQWLambda :=
  (noDefectQWLambdaTheoremDataOfNormalizedPackage
    base common ccm24 normalizedSeed remainders rhExit bridges
    fixedData traceData).noDefectSourceMatchesQWLambdaHolds

theorem normalized_package_no_defect_qw_lambda_support_square_holds
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
          fixedData)) :
    (noDefectQWLambdaTheoremDataOfNormalizedPackage
      base common ccm24 normalizedSeed remainders rhExit bridges
      fixedData traceData).supportSquareMatchesNoDefectSource :=
  (noDefectQWLambdaTheoremDataOfNormalizedPackage
    base common ccm24 normalizedSeed remainders rhExit bridges
    fixedData traceData).supportSquareMatchesNoDefectSourceHolds

theorem normalized_package_source_trace_archimedean_test
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
          fixedData)) :
  (toSourceTraceReadOffDataOfNormalizedPackage
      base common ccm24 normalizedSeed remainders rhExit bridges
      fixedData traceData).archimedeanTest =
      (Source.sourceObjectPackageOfNormalizedCC20Trace
        base common ccm24 normalizedSeed remainders rhExit bridges).cc20Trace.sourceTraceTest :=
  rfl

theorem normalized_package_source_trace_lambda
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
          fixedData)) :
    (toSourceTraceReadOffDataOfNormalizedPackage
      base common ccm24 normalizedSeed remainders rhExit bridges
      fixedData traceData).lambda =
      traceData.lambda :=
  rfl

theorem normalized_package_source_trace_arithmetic_package
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
          fixedData)) :
    (toSourceTraceReadOffDataOfNormalizedPackage
      base common ccm24 normalizedSeed remainders rhExit bridges
      fixedData traceData).ccm25ArithmeticPackage =
      traceData.ccm25ArithmeticPackage :=
  rfl

theorem normalized_package_source_trace_weil_test_eq_common
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
    (_traceData :
      TraceFrontEndData
        (Source.sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges)
        (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
          base common ccm24 normalizedSeed remainders rhExit bridges
          fixedData)) :
    SourceBackedFixedSTest.weilTest
      (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedPackage
        base common ccm24 normalizedSeed remainders rhExit bridges fixedData) =
      common.commonTest.sourceTest :=
  rfl

end TraceFrontEndData

end Route
end ConnesWeilRH
