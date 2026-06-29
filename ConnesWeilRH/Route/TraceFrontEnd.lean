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
