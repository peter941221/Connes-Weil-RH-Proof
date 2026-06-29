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

end TraceFrontEndData

end Route
end ConnesWeilRH
