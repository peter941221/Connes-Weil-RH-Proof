/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.Objects
import ConnesWeilRH.Source.ObjectTheoremBasePackage
import ConnesWeilRH.Source.CC20Concrete.TraceScale

/-!
# Source-object expanded row staging

Goal 2C groups the expanded row data needed by `SourceObjectPackage` without
constructing a full source-object package.  The CCM25 row is derived from the
same concrete arithmetic rows used by Goal 0E, while CCM24 and CC20 remain
explicit expanded-row inputs.
-/

namespace ConnesWeilRH
namespace Source

/--
Common source-test data for Goal 2C.

The record forces the CCM25 arithmetic rows to use the same source evaluator as
the common source test.  This is the equality that later fills the
`SourceObjectPackage.ccm25Test_eq_commonTest` field.
-/
structure SourceObjectCommonData
    (base : SourceObjectTheoremBasePackage) where
  commonTest :
    SourceObject.CommonTestObject base.ccm25Model.toWeilFormSymbols
  concreteArithmeticRows :
    CCM25Concrete.Interface.ConcreteCCM25ArithmeticRows
      base.ccm25Model.toWeilFormSymbols
  ccm25Test_eq_commonTest :
    commonTest.ccm25SourceTest =
      CCM25Concrete.Rows.source_test_of_arithmetic_rows
        concreteArithmeticRows commonTest.sourceTest commonTest.sourceTest

namespace SourceObjectCommonData

def toCCM25WeilObjectPackage
    {base : SourceObjectTheoremBasePackage}
    (common : SourceObjectCommonData base) :
    SourceObject.CCM25WeilObjectPackage where
  weilSymbols := base.ccm25Model.toWeilFormSymbols
  concreteArithmeticRows := common.concreteArithmeticRows

theorem ccm25_source_test_eq_arithmetic_rows
    {base : SourceObjectTheoremBasePackage}
    (common : SourceObjectCommonData base) :
    common.commonTest.ccm25SourceTest =
      CCM25Concrete.Rows.source_test_of_arithmetic_rows
        common.concreteArithmeticRows
        common.commonTest.sourceTest common.commonTest.sourceTest :=
  common.ccm25Test_eq_commonTest

theorem finite_prime_normalization
    {base : SourceObjectTheoremBasePackage}
    (common : SourceObjectCommonData base) :
    WeilFormSymbols.FinitePrimeNormalizationStatement
      base.ccm25Model.toWeilFormSymbols :=
  ccm25_finite_prime_normalization_of_concrete_arithmetic_rows
    common.concreteArithmeticRows

def toFinitePrimeTheoremBase
    {base : SourceObjectTheoremBasePackage}
    (common : SourceObjectCommonData base) :
    CCM25TheoremBaseFinitePrime where
  weilSymbols := base.ccm25Model.toWeilFormSymbols
  concreteArithmeticRows := common.concreteArithmeticRows
  finitePrimeNormalization := common.finite_prime_normalization

def toPartialQWFinitePrime
    {base : SourceObjectTheoremBasePackage}
    (common : SourceObjectCommonData base) :
    CCM25TheoremBasePartialQWFinitePrime where
  sourceModel := base.ccm25Model
  concreteArithmeticRows := common.concreteArithmeticRows
  qwDefinition := ccm25_source_qw_definition base.ccm25Model
  finitePrimeNormalization := common.finite_prime_normalization

def toCCM25TheoremBaseWithConcreteFinitePrime
    {base : SourceObjectTheoremBasePackage}
    (common : SourceObjectCommonData base) :
    CCM25TheoremBase where
  weilSymbols := base.ccm25Model.toWeilFormSymbols
  qwDefinition := ccm25_source_qw_definition base.ccm25Model
  psiSign := ccm25_source_psi_sign base.ccm25Model
  qwLambdaFormula := ccm25_source_qw_lambda_formula base.ccm25Model
  finitePrimeNormalization := common.finite_prime_normalization
  poleNormalization := ccm25_source_pole_normalization base.ccm25Model
  noSpectralShortcutImport := ccm25_no_spectral_shortcut_import

theorem toCCM25WeilObjectPackage_rows_eq
    {base : SourceObjectTheoremBasePackage}
    (common : SourceObjectCommonData base) :
    (common.toCCM25WeilObjectPackage).concreteArithmeticRows =
      common.concreteArithmeticRows :=
  rfl

theorem toCCM25WeilObjectPackage_symbols_eq
    {base : SourceObjectTheoremBasePackage}
    (common : SourceObjectCommonData base) :
    (common.toCCM25WeilObjectPackage).weilSymbols =
      base.ccm25Model.toWeilFormSymbols :=
  rfl

end SourceObjectCommonData

/--
Expanded row data after Goal 2C.

The CCM25 row is intentionally not a free field: it is computed from
`SourceObjectCommonData`, which already ties the arithmetic rows to the common
source test and the Goal 0E finite-prime theorem path.
-/
structure SourceObjectExpandedRows
    (base : SourceObjectTheoremBasePackage)
    (common : SourceObjectCommonData base) where
  ccm24 : SourceObject.CCM24SemilocalObjectPackage
  cc20Trace : SourceObject.CC20TraceObjectPackage
  cc20SupportSquareComparison :
    CC20Concrete.TraceScale.CC20TracePackageSupportSquareComparison cc20Trace

namespace SourceObjectExpandedRows

open CC20Concrete.TraceScale

abbrev CC20SupportSquareComparison :=
  CC20Concrete.TraceScale.CC20TracePackageSupportSquareComparison

def normalizedCC20SupportSquareComparison
    (normalizedSeed :
      CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (remainders :
      CC20Concrete.TraceScale.CC20TracePackageRemainderData normalizedSeed) :
    CC20SupportSquareComparison
      (CC20Concrete.TraceScale.normalizedSeedTraceObjectPackage
        normalizedSeed remainders) :=
  CC20TracePackageSupportSquareComparison.forNormalizedSeedTraceObjectPackage
    normalizedSeed remainders

def ofNormalizedCC20Trace
    {base : SourceObjectTheoremBasePackage}
    {common : SourceObjectCommonData base}
    (ccm24 : SourceObject.CCM24SemilocalObjectPackage)
    (normalizedSeed :
      CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (remainders :
      CC20Concrete.TraceScale.CC20TracePackageRemainderData normalizedSeed) :
    SourceObjectExpandedRows base common where
  ccm24 := ccm24
  cc20Trace :=
    CC20Concrete.TraceScale.normalizedSeedTraceObjectPackage
      normalizedSeed remainders
  cc20SupportSquareComparison :=
    normalizedCC20SupportSquareComparison normalizedSeed remainders

theorem of_normalized_cc20_trace_cc20_trace_eq
    {base : SourceObjectTheoremBasePackage}
    {common : SourceObjectCommonData base}
    (ccm24 : SourceObject.CCM24SemilocalObjectPackage)
    (normalizedSeed :
      CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (remainders :
      CC20Concrete.TraceScale.CC20TracePackageRemainderData normalizedSeed) :
    (ofNormalizedCC20Trace (base := base) (common := common)
      ccm24 normalizedSeed remainders).cc20Trace =
      CC20Concrete.TraceScale.normalizedSeedTraceObjectPackage
        normalizedSeed remainders :=
  rfl

theorem of_normalized_cc20_trace_support_square_comparison
    {base : SourceObjectTheoremBasePackage}
    {common : SourceObjectCommonData base}
    (ccm24 : SourceObject.CCM24SemilocalObjectPackage)
    (normalizedSeed :
      CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (remainders :
      CC20Concrete.TraceScale.CC20TracePackageRemainderData normalizedSeed) :
    (ofNormalizedCC20Trace (base := base) (common := common)
      ccm24 normalizedSeed remainders).cc20SupportSquareComparison =
      normalizedCC20SupportSquareComparison normalizedSeed remainders :=
  rfl

def ccm25
    {base : SourceObjectTheoremBasePackage}
    {common : SourceObjectCommonData base}
    (_rows : SourceObjectExpandedRows base common) :
    SourceObject.CCM25WeilObjectPackage :=
  common.toCCM25WeilObjectPackage

theorem ccm25_rows_eq_common_rows
    {base : SourceObjectTheoremBasePackage}
    {common : SourceObjectCommonData base}
    (rows : SourceObjectExpandedRows base common) :
    rows.ccm25.concreteArithmeticRows = common.concreteArithmeticRows :=
  rfl

theorem ccm25_symbols_eq_base
    {base : SourceObjectTheoremBasePackage}
    {common : SourceObjectCommonData base}
    (rows : SourceObjectExpandedRows base common) :
    rows.ccm25.weilSymbols = base.ccm25Model.toWeilFormSymbols :=
  rfl

theorem ccm25_source_test_eq_arithmetic_rows
    {base : SourceObjectTheoremBasePackage}
    {common : SourceObjectCommonData base}
    (_rows : SourceObjectExpandedRows base common) :
    common.commonTest.ccm25SourceTest =
      CCM25Concrete.Rows.source_test_of_arithmetic_rows
        (ccm25 _rows).concreteArithmeticRows
        common.commonTest.sourceTest common.commonTest.sourceTest :=
  common.ccm25Test_eq_commonTest

theorem finite_prime_normalization
    {base : SourceObjectTheoremBasePackage}
    {common : SourceObjectCommonData base}
    (_rows : SourceObjectExpandedRows base common) :
    WeilFormSymbols.FinitePrimeNormalizationStatement
      (ccm25 _rows).weilSymbols :=
  common.finite_prime_normalization

def cc20_support_square_comparison
    {base : SourceObjectTheoremBasePackage}
    {common : SourceObjectCommonData base}
    (rows : SourceObjectExpandedRows base common) :
    CC20Concrete.TraceScale.CC20TracePackageSupportSquareComparison
      rows.cc20Trace :=
  rows.cc20SupportSquareComparison

theorem cc20_support_square_existing_identification
    {base : SourceObjectTheoremBasePackage}
    {common : SourceObjectCommonData base}
    (rows : SourceObjectExpandedRows base common) :
    HEq
      (ArchimedeanTraceSymbols.supportSquareTrace
        (CC20Concrete.TraceScale.normalizedSeedTraceObjectArchimedeanSymbols
          rows.cc20SupportSquareComparison.normalizedSeed
          rows.cc20SupportSquareComparison.remainders))
      rows.cc20Trace.archimedeanSymbols.supportSquareTrace :=
  rows.cc20SupportSquareComparison.supportSquareTrace_eq

def toPartialQWFinitePrime
    {base : SourceObjectTheoremBasePackage}
    {common : SourceObjectCommonData base}
    (_rows : SourceObjectExpandedRows base common) :
    CCM25TheoremBasePartialQWFinitePrime :=
  common.toPartialQWFinitePrime

end SourceObjectExpandedRows

/--
Cross-object bridge data needed to assemble a `SourceObjectPackage`.

The bridge keeps the remaining mixed-row obligations explicit: common-test
involution, CCM24/CC20 common-test ownership, window controls, finite-prime
support matching, final sign compatibility, and the RH-exit bridge used by the
expanded CC20 exit object.
-/
structure SourceObjectCrossObjectBridges
    (base : SourceObjectTheoremBasePackage)
    (common : SourceObjectCommonData base)
    (rows : SourceObjectExpandedRows base common)
    (rhExit : SourceObject.CC20RHExitObjectPackage) where
  rhDefinitionBridge_eq_base :
    rhExit.rhDefinitionBridge = base.rhDefinitionBridge
  commonTestInvolution :
    SourceObject.CommonTestInvolutionBridge
      (SourceObjectExpandedRows.ccm25 rows).weilSymbols common.commonTest
  ccm24Test_eq_commonTest :
    SourceObject.CCM24CommonTestBridge
      (SourceObjectExpandedRows.ccm25 rows).weilSymbols
      common.commonTest rows.ccm24
  cc20TraceTest_eq_commonTest :
    SourceObject.CC20CommonTestBridge
      (SourceObjectExpandedRows.ccm25 rows).weilSymbols
      common.commonTest rows.cc20Trace
  convolutionSquare_eq_Fg : Prop
  ccm24Window_controls_qwLambda : Prop
  ccm24Window_controls_cdef : Prop
  finitePrimeSupport_matches_window : Prop
  qW_sign_bridge : Prop

namespace SourceObjectCrossObjectBridges

theorem ccm25_source_test_eq_arithmetic_rows
    {base : SourceObjectTheoremBasePackage}
    {common : SourceObjectCommonData base}
    {rows : SourceObjectExpandedRows base common}
    {rhExit : SourceObject.CC20RHExitObjectPackage}
    (_bridges : SourceObjectCrossObjectBridges base common rows rhExit) :
    common.commonTest.ccm25SourceTest =
      CCM25Concrete.Rows.source_test_of_arithmetic_rows
        (SourceObjectExpandedRows.ccm25 rows).concreteArithmeticRows
        common.commonTest.sourceTest common.commonTest.sourceTest :=
  SourceObjectExpandedRows.ccm25_source_test_eq_arithmetic_rows rows

theorem rh_definition_bridge_eq_base
    {base : SourceObjectTheoremBasePackage}
    {common : SourceObjectCommonData base}
    {rows : SourceObjectExpandedRows base common}
    {rhExit : SourceObject.CC20RHExitObjectPackage}
    (bridges : SourceObjectCrossObjectBridges base common rows rhExit) :
    rhExit.rhDefinitionBridge = base.rhDefinitionBridge :=
  bridges.rhDefinitionBridge_eq_base

end SourceObjectCrossObjectBridges

/--
Goal 2D constructor for the expanded source-object package.

Every field is supplied by the staged base package, common-test data, expanded
rows, explicit RH-exit object, or named cross-object bridge data.  This is not
a no-argument source package and does not prove the remaining analytic rows.
-/
def sourceObjectPackageOfData
    (base : SourceObjectTheoremBasePackage)
    (common : SourceObjectCommonData base)
    (rows : SourceObjectExpandedRows base common)
    (rhExit : SourceObject.CC20RHExitObjectPackage)
    (bridges : SourceObjectCrossObjectBridges base common rows rhExit) :
    SourceObject.SourceObjectPackage where
  ccm24 := rows.ccm24
  ccm25 := SourceObjectExpandedRows.ccm25 rows
  commonTest := common.commonTest
  cc20Trace := rows.cc20Trace
  cc20RHExit := rhExit
  commonTestInvolution := bridges.commonTestInvolution
  ccm24Test_eq_commonTest := bridges.ccm24Test_eq_commonTest
  ccm25Test_eq_commonTest :=
    SourceObjectExpandedRows.ccm25_source_test_eq_arithmetic_rows rows
  cc20TraceTest_eq_commonTest := bridges.cc20TraceTest_eq_commonTest
  convolutionSquare_eq_Fg := bridges.convolutionSquare_eq_Fg
  ccm24Window_controls_qwLambda := bridges.ccm24Window_controls_qwLambda
  ccm24Window_controls_cdef := bridges.ccm24Window_controls_cdef
  finitePrimeSupport_matches_window := bridges.finitePrimeSupport_matches_window
  qW_sign_bridge := bridges.qW_sign_bridge

def sourceObjectPackageOfNormalizedCC20Trace
    (base : SourceObjectTheoremBasePackage)
    (common : SourceObjectCommonData base)
    (ccm24 : SourceObject.CCM24SemilocalObjectPackage)
    (normalizedSeed :
      CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (remainders :
      CC20Concrete.TraceScale.CC20TracePackageRemainderData normalizedSeed)
    (rhExit : SourceObject.CC20RHExitObjectPackage)
    (bridges :
      SourceObjectCrossObjectBridges base common
        (SourceObjectExpandedRows.ofNormalizedCC20Trace
          ccm24 normalizedSeed remainders)
        rhExit) :
    SourceObject.SourceObjectPackage :=
  sourceObjectPackageOfData base common
    (SourceObjectExpandedRows.ofNormalizedCC20Trace
      ccm24 normalizedSeed remainders)
    rhExit bridges

namespace SourceObjectPackageOfData

theorem normalized_cc20_trace_package_eq_data_constructor
    (base : SourceObjectTheoremBasePackage)
    (common : SourceObjectCommonData base)
    (ccm24 : SourceObject.CCM24SemilocalObjectPackage)
    (normalizedSeed :
      CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (remainders :
      CC20Concrete.TraceScale.CC20TracePackageRemainderData normalizedSeed)
    (rhExit : SourceObject.CC20RHExitObjectPackage)
    (bridges :
      SourceObjectCrossObjectBridges base common
        (SourceObjectExpandedRows.ofNormalizedCC20Trace
          ccm24 normalizedSeed remainders)
        rhExit) :
    sourceObjectPackageOfNormalizedCC20Trace
      base common ccm24 normalizedSeed remainders rhExit bridges =
      sourceObjectPackageOfData base common
        (SourceObjectExpandedRows.ofNormalizedCC20Trace
          ccm24 normalizedSeed remainders)
        rhExit bridges :=
  rfl

theorem normalized_cc20_trace_package_cc20_trace_eq
    (base : SourceObjectTheoremBasePackage)
    (common : SourceObjectCommonData base)
    (ccm24 : SourceObject.CCM24SemilocalObjectPackage)
    (normalizedSeed :
      CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (remainders :
      CC20Concrete.TraceScale.CC20TracePackageRemainderData normalizedSeed)
    (rhExit : SourceObject.CC20RHExitObjectPackage)
    (bridges :
      SourceObjectCrossObjectBridges base common
        (SourceObjectExpandedRows.ofNormalizedCC20Trace
          ccm24 normalizedSeed remainders)
        rhExit) :
    (sourceObjectPackageOfNormalizedCC20Trace
      base common ccm24 normalizedSeed remainders rhExit bridges).cc20Trace =
      CC20Concrete.TraceScale.normalizedSeedTraceObjectPackage
        normalizedSeed remainders :=
  rfl

def normalized_seed_ordinary_trace_support_square_statement
    (normalizedSeed :
      CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols) :
    ArchimedeanTraceSymbols.OrdinaryTraceSupportSquareStatement
      (CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
        normalizedSeed).archimedeanSymbols :=
  normalizedSeed.ordinary_trace_support_square_statement

theorem normalized_cc20_trace_package_ordinary_trace_support_square
    (base : SourceObjectTheoremBasePackage)
    (common : SourceObjectCommonData base)
    (ccm24 : SourceObject.CCM24SemilocalObjectPackage)
    (normalizedSeed :
      CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (remainders :
      CC20Concrete.TraceScale.CC20TracePackageRemainderData normalizedSeed)
    (rhExit : SourceObject.CC20RHExitObjectPackage)
    (bridges :
      SourceObjectCrossObjectBridges base common
        (SourceObjectExpandedRows.ofNormalizedCC20Trace
          ccm24 normalizedSeed remainders)
        rhExit) :
    ArchimedeanTraceSymbols.OrdinaryTraceSupportSquareStatement
      (SourceObject.SourceObjectPackage.toArchimedeanTraceSymbols
        (sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges)) :=
  normalized_seed_ordinary_trace_support_square_statement normalizedSeed

def normalized_cc20_trace_package_support_square_comparison
    (base : SourceObjectTheoremBasePackage)
    (common : SourceObjectCommonData base)
    (ccm24 : SourceObject.CCM24SemilocalObjectPackage)
    (normalizedSeed :
      CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (remainders :
      CC20Concrete.TraceScale.CC20TracePackageRemainderData normalizedSeed)
    (rhExit : SourceObject.CC20RHExitObjectPackage)
    (bridges :
      SourceObjectCrossObjectBridges base common
        (SourceObjectExpandedRows.ofNormalizedCC20Trace
          ccm24 normalizedSeed remainders)
        rhExit) :
    CC20Concrete.TraceScale.CC20TracePackageSupportSquareComparison
      (sourceObjectPackageOfNormalizedCC20Trace
        base common ccm24 normalizedSeed remainders rhExit bridges).cc20Trace :=
  SourceObjectExpandedRows.cc20SupportSquareComparison
    (SourceObjectExpandedRows.ofNormalizedCC20Trace
      (base := base) (common := common) ccm24 normalizedSeed remainders)

theorem ccm25_eq_rows
    {base : SourceObjectTheoremBasePackage}
    {common : SourceObjectCommonData base}
    {rows : SourceObjectExpandedRows base common}
    {rhExit : SourceObject.CC20RHExitObjectPackage}
    (bridges : SourceObjectCrossObjectBridges base common rows rhExit) :
    (sourceObjectPackageOfData base common rows rhExit bridges).ccm25 =
      SourceObjectExpandedRows.ccm25 rows :=
  rfl

theorem commonTest_eq_common
    {base : SourceObjectTheoremBasePackage}
    {common : SourceObjectCommonData base}
    {rows : SourceObjectExpandedRows base common}
    {rhExit : SourceObject.CC20RHExitObjectPackage}
    (bridges : SourceObjectCrossObjectBridges base common rows rhExit) :
    (sourceObjectPackageOfData base common rows rhExit bridges).commonTest =
      common.commonTest :=
  rfl

theorem ccm25_source_test_eq_arithmetic_rows
    {base : SourceObjectTheoremBasePackage}
    {common : SourceObjectCommonData base}
    {rows : SourceObjectExpandedRows base common}
    {rhExit : SourceObject.CC20RHExitObjectPackage}
    (bridges : SourceObjectCrossObjectBridges base common rows rhExit) :
    (sourceObjectPackageOfData base common rows rhExit bridges).ccm25Test_eq_commonTest =
      SourceObjectExpandedRows.ccm25_source_test_eq_arithmetic_rows rows :=
  rfl

theorem finite_prime_normalization
    {base : SourceObjectTheoremBasePackage}
    {common : SourceObjectCommonData base}
    {rows : SourceObjectExpandedRows base common}
    {rhExit : SourceObject.CC20RHExitObjectPackage}
    (bridges : SourceObjectCrossObjectBridges base common rows rhExit) :
    WeilFormSymbols.FinitePrimeNormalizationStatement
      (sourceObjectPackageOfData base common rows rhExit bridges).ccm25.weilSymbols :=
  SourceObjectExpandedRows.finite_prime_normalization rows

def cc20_support_square_comparison
    {base : SourceObjectTheoremBasePackage}
    {common : SourceObjectCommonData base}
    {rows : SourceObjectExpandedRows base common}
    {rhExit : SourceObject.CC20RHExitObjectPackage}
    (bridges : SourceObjectCrossObjectBridges base common rows rhExit) :
    CC20Concrete.TraceScale.CC20TracePackageSupportSquareComparison
      (sourceObjectPackageOfData base common rows rhExit bridges).cc20Trace :=
  rows.cc20SupportSquareComparison

theorem cc20_support_square_existing_identification
    {base : SourceObjectTheoremBasePackage}
    {common : SourceObjectCommonData base}
    {rows : SourceObjectExpandedRows base common}
    {rhExit : SourceObject.CC20RHExitObjectPackage}
    (bridges : SourceObjectCrossObjectBridges base common rows rhExit) :
    HEq
      (ArchimedeanTraceSymbols.supportSquareTrace
        (CC20Concrete.TraceScale.normalizedSeedTraceObjectArchimedeanSymbols
          rows.cc20SupportSquareComparison.normalizedSeed
          rows.cc20SupportSquareComparison.remainders))
      (ArchimedeanTraceSymbols.supportSquareTrace
        (SourceObject.CC20TraceObjectPackage.archimedeanSymbols
          (SourceObject.SourceObjectPackage.cc20Trace
            (sourceObjectPackageOfData base common rows rhExit bridges)))) :=
  SourceObjectExpandedRows.cc20_support_square_existing_identification rows

theorem rh_definition_bridge_eq_base
    {base : SourceObjectTheoremBasePackage}
    {common : SourceObjectCommonData base}
    {rows : SourceObjectExpandedRows base common}
    {rhExit : SourceObject.CC20RHExitObjectPackage}
    (bridges : SourceObjectCrossObjectBridges base common rows rhExit) :
    (sourceObjectPackageOfData base common rows rhExit bridges).cc20RHExit.rhDefinitionBridge =
      base.rhDefinitionBridge :=
  bridges.rhDefinitionBridge_eq_base

end SourceObjectPackageOfData

end Source
end ConnesWeilRH
