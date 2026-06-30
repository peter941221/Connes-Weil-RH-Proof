/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.CCM25Concrete.CommonSourceTest
import ConnesWeilRH.Source.CCM25Concrete.Rows
import ConnesWeilRH.Source.CC20RHExit

/-!
# Expanded source-object boundary

This module names the source objects that later accepted imports or analytic
Lean proofs must provide. It does not prove the CCM24, CCM25, or CC20 analytic
theorems. Its purpose is to keep the common test, finite-prime atoms, trace
legality, final sign bridge, and RH definition bridge visible before the route
uses the compact records in `ConnesWeilRH.Basic`.
-/

namespace ConnesWeilRH
namespace Source
namespace SourceObject

structure CommonTestObject (W : WeilFormSymbols) where
  concreteCommonTest : CCM25Concrete.CommonSourceTest.ConcreteCommonSourceTest W
  sourceTest : TestFunction
  sourceTestReadOff : sourceTest = concreteCommonTest.sourceTest
  sourceConvolutionSquare : TestFunction
  sourceConvolutionSquareConcreteReadOff :
    sourceConvolutionSquare = concreteCommonTest.sourceConvolutionSquare
  ccm25SourceTest :
    CCM25Concrete.PrimePowerTest.SourceTestEvaluationInterface
      W sourceTest sourceTest
  ccm25SourceTestConcreteReadOff :
    ccm25SourceTest =
      (sourceTestReadOff ▸ sourceTestReadOff ▸
        concreteCommonTest.toSourceTestEvaluationInterface)
  sourceConvolutionSquareReadOff :
    sourceConvolutionSquare = W.convolutionStar sourceTest sourceTest
  ccm25SourceTestSquareReadOff :
    ccm25SourceTest.sourceConvolutionSquare = sourceConvolutionSquare

namespace CommonTestObject

def ofConcrete
    {W : WeilFormSymbols}
    (common : CCM25Concrete.CommonSourceTest.ConcreteCommonSourceTest W) :
    CommonTestObject W where
  concreteCommonTest := common
  sourceTest := common.sourceTest
  sourceTestReadOff := rfl
  sourceConvolutionSquare := common.sourceConvolutionSquare
  sourceConvolutionSquareConcreteReadOff := rfl
  ccm25SourceTest := common.toSourceTestEvaluationInterface
  ccm25SourceTestConcreteReadOff := rfl
  sourceConvolutionSquareReadOff := common.source_convolution_square_read_off
  ccm25SourceTestSquareReadOff := common.evaluator_square_eq_concrete_square

def concreteSourceAtomVisible
    {W : WeilFormSymbols} (common : CommonTestObject W) (n : ℕ) : Prop :=
  common.concreteCommonTest.sourceAtomVisible n

theorem source_test_eq_concrete
    {W : WeilFormSymbols} (common : CommonTestObject W) :
    common.sourceTest = common.concreteCommonTest.sourceTest :=
  common.sourceTestReadOff

theorem source_square_eq_concrete
    {W : WeilFormSymbols} (common : CommonTestObject W) :
    common.sourceConvolutionSquare =
      common.concreteCommonTest.sourceConvolutionSquare :=
  common.sourceConvolutionSquareConcreteReadOff

theorem ccm25_source_test_eq_concrete
    {W : WeilFormSymbols} (common : CommonTestObject W) :
    common.ccm25SourceTest =
      (common.sourceTestReadOff ▸ common.sourceTestReadOff ▸
        common.concreteCommonTest.toSourceTestEvaluationInterface) :=
  common.ccm25SourceTestConcreteReadOff

theorem route_visibility_iff_concrete_visibility
    {W : WeilFormSymbols} (common : CommonTestObject W) (n : ℕ) :
    W.finitePrimeAtomVisible n
        (W.convolutionStar common.sourceTest common.sourceTest) ↔
      common.concreteSourceAtomVisible n := by
  rw [common.sourceTestReadOff]
  exact common.concreteCommonTest.route_visibility_iff_source_visibility n

end CommonTestObject

structure CommonTestInvolutionBridge (W : WeilFormSymbols)
    (commonTest : CommonTestObject W) where
  sourceInvolutionCompatible : Prop
  convolutionSquareUsesInvolution : Prop

structure CCM24SemilocalObjectPackage where
  semilocalSymbols : SemilocalModelSymbols
  sourcePlaceSet : semilocalSymbols.PlaceSet
  sourceSupportWindow : semilocalSymbols.Window
  sourceTestLeg : semilocalSymbols.Test
  sourceCCM24TestCompatibility : Prop
  sourceCanonicalModelData :
    semilocalSymbols.canonicalHilbertModel sourcePlaceSet
  sourceSupportInWindowData :
    semilocalSymbols.supportInWindow sourceTestLeg sourceSupportWindow
  sourceFourierSupportInWindowData :
    semilocalSymbols.fourierSupportInWindow sourceTestLeg sourceSupportWindow
  sourceSoninSpaceComparisonData :
    semilocalSymbols.soninSpaceComparison sourceSupportWindow
  sourceWindowContainedInLambdaData :
    ∀ lambda : ℝ,
      1 < lambda →
        semilocalSymbols.windowContainedInLambda sourceSupportWindow lambda
  sourceLambdaCompatibilityBridge :
    ∀ lambda : ℝ,
      semilocalSymbols.supportInWindow sourceTestLeg sourceSupportWindow →
        semilocalSymbols.fourierSupportInWindow
            sourceTestLeg sourceSupportWindow →
          semilocalSymbols.supportTransported sourceTestLeg
              sourceSupportWindow →
            semilocalSymbols.convolutionSupportTransported
                sourceTestLeg sourceSupportWindow →
              semilocalSymbols.fixedWindowExhaustionCompatible
                  sourceSupportWindow →
                semilocalSymbols.windowContainedInLambda
                    sourceSupportWindow lambda →
                  semilocalSymbols.lambdaCompatible
                    sourceSupportWindow lambda
  sourceCanonicalSemilocalModel :
    SemilocalModelSymbols.CanonicalSemilocalModelStatement semilocalSymbols
  sourceSupportAndFourierSupportTransport :
    SemilocalModelSymbols.SupportTransportStatement semilocalSymbols
  sourceConvolutionSupportTransport : Prop
  sourceWindowLambdaCompatibility : Prop
  sourceBoundedComparisonTraceClassTransport :
    SemilocalModelSymbols.BoundedComparisonStatement semilocalSymbols
  sourceFixedWindowSoninExhaustion :
    SemilocalModelSymbols.SoninComparisonStatement semilocalSymbols

structure CCM24CommonTestBridge
    (W : WeilFormSymbols) (commonTest : CommonTestObject W)
    (ccm24 : CCM24SemilocalObjectPackage)
    where
  sourceTestCompatibility : Prop
  semilocalLegIsCommonTest : Prop
  supportWindowOwnsCommonTest :
    ccm24.semilocalSymbols.supportInWindow
      ccm24.sourceTestLeg ccm24.sourceSupportWindow
  fourierWindowOwnsCommonTest :
    ccm24.semilocalSymbols.fourierSupportInWindow
      ccm24.sourceTestLeg ccm24.sourceSupportWindow
  convolutionSupportTransported :
    ccm24.semilocalSymbols.convolutionSupportTransported
      ccm24.sourceTestLeg ccm24.sourceSupportWindow

structure CCM25WeilObjectPackage where
  weilSymbols : WeilFormSymbols
  concreteArithmeticRows :
    CCM25Concrete.Rows.ConcreteCCM25ArithmeticRows weilSymbols

structure CC20TraceObjectPackage where
  archimedeanSymbols : ArchimedeanTraceSymbols
  sourceTraceTest : archimedeanSymbols.Test
  sourceCC20TraceTestCompatibility : Prop
  sourceOperatorIdentity : Prop
  sourceHilbertSchmidtGate :
    ∀ g : archimedeanSymbols.Test,
      archimedeanSymbols.hilbertSchmidtGate g
  sourceTraceClassCyclicityTemplate :
    ArchimedeanTraceSymbols.TraceClassTemplateStatement archimedeanSymbols
  sourcePerMoveCyclicityLedger : Prop
  sourceOrdinaryTraceSupportSquare :
    ArchimedeanTraceSymbols.OrdinaryTraceSupportSquareStatement
      archimedeanSymbols
  sourceSupportSquareTraceReadOff :
    ∀ g : archimedeanSymbols.Test,
      archimedeanSymbols.traceClass g →
        archimedeanSymbols.cyclicLegal g →
          archimedeanSymbols.supportSquareTrace g =
            archimedeanSymbols.sourceNoDefectTrace g
  sourceNoDefectTraceReadOff : Prop
  sourcePositiveTraceNonnegative :
    ∀ g : archimedeanSymbols.Test,
      archimedeanSymbols.traceClass g →
        archimedeanSymbols.cyclicLegal g →
          0 ≤ archimedeanSymbols.positiveTrace g
  sourceRemainderOrientationWInftyEqLMinusD : Prop
  sourceRemainderOrientationWInftyEqSMinusE : Prop
  sourceRemainderObject : Prop
  sourceRemainderAfterQ : Prop
  cc20PostQRemainderFixedSSoninTransport : Prop
  sourceProjectionDefectNormalForm : Prop
  sourceRankPoleLedgerIdentification : Prop
  sourceEndpointStripRemainderCdefDomination : Prop
  noBulkScaleTermOutsideLedger : Prop
  noHiddenFinitePartSubtraction : Prop
  noBulkScaleTermOutsideLedgerHolds : noBulkScaleTermOutsideLedger
  noHiddenFinitePartSubtractionHolds : noHiddenFinitePartSubtraction
  noBulkScaleTermOutsideLedgerAt :
    ℝ → archimedeanSymbols.Test → TestFunction → Prop
  noHiddenFinitePartSubtractionAt :
    ℝ → archimedeanSymbols.Test → TestFunction → Prop
  noBulkScaleTermOutsideLedgerAtHolds :
    ∀ lambda : ℝ, 1 < lambda →
      ∀ archimedeanTest : archimedeanSymbols.Test,
      ∀ weilTest : TestFunction,
        noBulkScaleTermOutsideLedgerAt lambda archimedeanTest weilTest
  noHiddenFinitePartSubtractionAtHolds :
    ∀ lambda : ℝ, 1 < lambda →
      ∀ archimedeanTest : archimedeanSymbols.Test,
      ∀ weilTest : TestFunction,
        noHiddenFinitePartSubtractionAt lambda archimedeanTest weilTest
  noHiddenPositiveDefectOutsideCdef : Prop
  sourceBoundedComparisonTraceIdealTransport : Prop
  sourceMellinHalfDensityCompatibility :
    ArchimedeanTraceSymbols.MellinHalfDensityConventionStatement
      archimedeanSymbols
  sourceCC20SignNormalizations :
    ArchimedeanTraceSymbols.SignsAndNormalizationsStatement
      archimedeanSymbols

structure CC20CommonTestBridge
    (W : WeilFormSymbols) (commonTest : CommonTestObject W)
    (cc20Trace : CC20TraceObjectPackage)
    where
  sourceTraceTestCompatibility : Prop
  traceLegIsCommonTest : Prop
  mellinLegIsCommonTest : Prop
  halfDensityMatchesCommonTest :
    ArchimedeanTraceSymbols.MellinHalfDensityConventionStatement
      cc20Trace.archimedeanSymbols

structure CC20RHExitObjectPackage where
  rhDefinitionBridge : RHDefinitionBridge
  sourceFiniteVanishingCriterionPackage :
    SourceFiniteVanishingCriterionPackage rhDefinitionBridge
  sourceMellinVanishing : WeilPositivityInput → Prop
  sourceQWNonnegative : WeilPositivityInput → Prop
  sourceCC20WeilNonpositivity : WeilPositivityInput → Prop
  tripleVanishingToMellinBridge :
    ∀ input : WeilPositivityInput,
      input.tripleVanishing → sourceMellinVanishing input
  routeFullPositivityToQWNonnegative :
    ∀ input : WeilPositivityInput,
      input.fullWeilPositivity → sourceQWNonnegative input
  qW_sign_bridge :
    ∀ input : WeilPositivityInput,
      sourceQWNonnegative input → sourceCC20WeilNonpositivity input
  sourceCC20PropositionC1 :
    ∀ input : WeilPositivityInput,
      sourceMellinVanishing input →
        sourceCC20WeilNonpositivity input →
          rhDefinitionBridge.SourceRH
  rhDefinitionContractConsumption : Prop

structure SourceObjectPackage where
  ccm24 : CCM24SemilocalObjectPackage
  ccm25 : CCM25WeilObjectPackage
  commonTest : CommonTestObject ccm25.weilSymbols
  cc20Trace : CC20TraceObjectPackage
  cc20RHExit : CC20RHExitObjectPackage
  commonTestInvolution :
    CommonTestInvolutionBridge ccm25.weilSymbols commonTest
  ccm24Test_eq_commonTest :
    CCM24CommonTestBridge ccm25.weilSymbols commonTest ccm24
  ccm25Test_eq_commonTest :
    commonTest.ccm25SourceTest =
      CCM25Concrete.Rows.source_test_of_arithmetic_rows
        ccm25.concreteArithmeticRows commonTest.sourceTest commonTest.sourceTest
  cc20TraceTest_eq_commonTest :
    CC20CommonTestBridge ccm25.weilSymbols commonTest cc20Trace
  convolutionSquare_eq_Fg : Prop
  ccm24Window_controls_qwLambda : Prop
  ccm24Window_controls_cdef : Prop
  finitePrimeSupport_matches_window : Prop
  qW_sign_bridge : Prop

end SourceObject
end Source
end ConnesWeilRH
