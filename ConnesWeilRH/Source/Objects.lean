/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

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

structure CommonTestObject where
  sourceTest : TestFunction
  sourceConvolutionSquare : TestFunction
  sourceConvolutionSquareReadOff : Prop
  sourceInvolutionBridge : Prop

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
  sourceOrdinaryPositiveTrace : Prop
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
  noHiddenPositiveDefectOutsideCdef : Prop
  sourceBoundedComparisonTraceIdealTransport : Prop
  sourceMellinHalfDensityCompatibility :
    ArchimedeanTraceSymbols.MellinHalfDensityConventionStatement
      archimedeanSymbols
  sourceCC20SignNormalizations :
    ArchimedeanTraceSymbols.SignsAndNormalizationsStatement
      archimedeanSymbols

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
  commonTest : CommonTestObject
  ccm24 : CCM24SemilocalObjectPackage
  ccm25 : CCM25WeilObjectPackage
  cc20Trace : CC20TraceObjectPackage
  cc20RHExit : CC20RHExitObjectPackage
  ccm24Test_eq_commonTest : Prop
  ccm25Test_eq_commonTest : Prop
  cc20TraceTest_eq_commonTest : Prop
  cc20MellinTest_eq_commonTest : Prop
  convolutionSquare_eq_Fg : Prop
  ccm24Window_controls_qwLambda : Prop
  ccm24Window_controls_cdef : Prop
  finitePrimeSupport_matches_window : Prop
  qW_sign_bridge : Prop

end SourceObject
end Source
end ConnesWeilRH
