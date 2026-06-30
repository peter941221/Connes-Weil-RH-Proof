/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Route.RouteTheorem

/-!
# Development skeleton for the unconditional RH checklist

This module is not imported by `ConnesWeilRH.lean`.  It records the intended
route-facing theorem names for checklist items 6 through 15. Every declaration
here is a temporary skeleton and must be replaced by concrete proofs or clean
theorem imports before any final project-root `unconditional_rh` theorem is
claimed.
-/

namespace ConnesWeilRH
namespace Dev
namespace UnconditionalSkeleton

open Route

/-- Checklist item 6 skeleton. -/
def sourceObjectPackageFromTheorems :
    Source.SourceObject.SourceObjectPackage := by
  sorry

/-- Checklist item 7 skeleton. -/
def fixedFrontEndFromTheorems :
    ExpandedSourceFixedSTestFrontEnd sourceObjectPackageFromTheorems := by
  sorry

/-- Checklist item 8 skeleton. -/
def traceFrontEndFromTheorems :
    ExpandedSourceTraceReadOffFrontEnd
      sourceObjectPackageFromTheorems fixedFrontEndFromTheorems := by
  sorry

structure RouteLedgerClearingInputData where
  ledgers : RouteLedgers
  cleared : LedgersCleared ledgers

/-- Route ledger evidence used by the development skeletons. -/
def routeLedgerClearingInputDataFromTheorems :
    RouteLedgerClearingInputData := by
  sorry

/-- Route ledgers used by the development skeletons. -/
def routeLedgersFromTheorems : RouteLedgers :=
  routeLedgerClearingInputDataFromTheorems.ledgers

theorem rankLedgerKilledFromTheorems :
    routeLedgersFromTheorems.rankKilled :=
  routeLedgerClearingInputDataFromTheorems.cleared.rankKilled

theorem poleLedgerKilledFromTheorems :
    routeLedgersFromTheorems.poleKilled :=
  routeLedgerClearingInputDataFromTheorems.cleared.poleKilled

theorem cdefExhaustsFromTheorems :
    routeLedgersFromTheorems.cdefExhausts :=
  routeLedgerClearingInputDataFromTheorems.cleared.cdefExhausts

def ledgersClearedFromTheorems :
    LedgersCleared routeLedgersFromTheorems :=
  routeLedgerClearingInputDataFromTheorems.cleared

/-- Checklist item 11/12 skeleton input for route-front construction. -/
theorem signDefectClassificationFromTheorems :
    SourceSignDefectClassification
      (RouteInputs.ofExpandedSourcePackage sourceObjectPackageFromTheorems)
      (SourceBackedFixedSTest.ofExpandedSourcePackage
        sourceObjectPackageFromTheorems fixedFrontEndFromTheorems)
      traceFrontEndFromTheorems.lambda routeLedgersFromTheorems :=
  source_sign_defect_classification_of_ledgers_cleared
    traceFrontEndFromTheorems.oneLtLambda
    ledgersClearedFromTheorems

/-- Checklist item 10 common-test skeleton used by restricted-to-full and sign. -/
def commonTupleFromTheorems :
    SourceCommonTestTupleContract
      (RouteInputs.ofExpandedSourcePackage sourceObjectPackageFromTheorems)
      (SourceBackedFixedSTest.ofExpandedSourcePackage
        sourceObjectPackageFromTheorems fixedFrontEndFromTheorems)
      traceFrontEndFromTheorems.lambda
      sourceObjectPackageFromTheorems.commonTest.sourceConvolutionSquare
      traceFrontEndFromTheorems.ccm25ArithmeticPackage := by
  exact
    source_common_test_tuple_contract_of_package
      (window_lambda_compatibility_of_source_backed
        traceFrontEndFromTheorems.oneLtLambda)
      (expanded_source_package_convolution_square_read_off
        sourceObjectPackageFromTheorems fixedFrontEndFromTheorems)

/-- Checklist item 9 skeleton. -/
structure RestrictedToFullThresholdInputData where
  threshold :
    RestrictedToFullQWLargeLambdaThreshold
      (RouteInputs.ofExpandedSourcePackage sourceObjectPackageFromTheorems)
      (SourceBackedFixedSTest.ofExpandedSourcePackage
        sourceObjectPackageFromTheorems fixedFrontEndFromTheorems)
      sourceObjectPackageFromTheorems.commonTest.sourceConvolutionSquare
  currentAboveThreshold :
    threshold.lambda0 ≤ traceFrontEndFromTheorems.lambda

def restrictedToFullThresholdInputDataFromTheorems :
    RestrictedToFullThresholdInputData := by
  sorry

def restrictedToFullLargeLambdaThresholdFromTheorems :
    RestrictedToFullQWLargeLambdaThreshold
      (RouteInputs.ofExpandedSourcePackage sourceObjectPackageFromTheorems)
      (SourceBackedFixedSTest.ofExpandedSourcePackage
        sourceObjectPackageFromTheorems fixedFrontEndFromTheorems)
      sourceObjectPackageFromTheorems.commonTest.sourceConvolutionSquare :=
  restrictedToFullThresholdInputDataFromTheorems.threshold

theorem restrictedToFullCurrentAboveThresholdFromTheorems :
    restrictedToFullLargeLambdaThresholdFromTheorems.lambda0 ≤
      traceFrontEndFromTheorems.lambda :=
  restrictedToFullThresholdInputDataFromTheorems.currentAboveThreshold

noncomputable def restrictedToFullCurrentCutoffBindingFromTheorems :
    RestrictedToFullCurrentCutoffBinding
      (RouteInputs.ofExpandedSourcePackage sourceObjectPackageFromTheorems)
      (SourceBackedFixedSTest.ofExpandedSourcePackage
        sourceObjectPackageFromTheorems fixedFrontEndFromTheorems)
      traceFrontEndFromTheorems.lambda
      sourceObjectPackageFromTheorems.commonTest.sourceConvolutionSquare
      routeLedgersFromTheorems
      traceFrontEndFromTheorems.ccm25ArithmeticPackage :=
  restricted_to_full_current_cutoff_binding_of_sign_defect
    restrictedToFullLargeLambdaThresholdFromTheorems
    restrictedToFullCurrentAboveThresholdFromTheorems
    commonTupleFromTheorems
    signDefectClassificationFromTheorems

noncomputable def restrictedToFullQWBridgeOfCurrentCutoffBindingFromTheorems :
    RestrictedToFullQWBridgeContract
      (RouteInputs.ofExpandedSourcePackage sourceObjectPackageFromTheorems)
      (SourceBackedFixedSTest.ofExpandedSourcePackage
        sourceObjectPackageFromTheorems fixedFrontEndFromTheorems)
      traceFrontEndFromTheorems.lambda
      sourceObjectPackageFromTheorems.commonTest.sourceConvolutionSquare
      routeLedgersFromTheorems
      traceFrontEndFromTheorems.ccm25ArithmeticPackage :=
  restricted_to_full_bridge_contract_of_current_cutoff_binding
    restrictedToFullCurrentCutoffBindingFromTheorems

noncomputable def restrictedToFullQWFromTheorems :
    RestrictedToFullQWBridgeContract
      (RouteInputs.ofExpandedSourcePackage sourceObjectPackageFromTheorems)
      (SourceBackedFixedSTest.ofExpandedSourcePackage
        sourceObjectPackageFromTheorems fixedFrontEndFromTheorems)
      traceFrontEndFromTheorems.lambda
      sourceObjectPackageFromTheorems.commonTest.sourceConvolutionSquare
      routeLedgersFromTheorems
      traceFrontEndFromTheorems.ccm25ArithmeticPackage :=
  restrictedToFullQWBridgeOfCurrentCutoffBindingFromTheorems

/-- Checklist item 10 archimedean sign leg skeleton. -/
theorem sourceArchimedeanSignBridgeFromTheorems :
    SourceArchimedeanSignBridge
      (RouteInputs.ofExpandedSourcePackage sourceObjectPackageFromTheorems)
      sourceObjectPackageFromTheorems.cc20Trace.sourceTraceTest
      (SourceBackedFixedSTest.ofExpandedSourcePackage
        sourceObjectPackageFromTheorems fixedFrontEndFromTheorems) :=
  source_archimedean_sign_bridge_of_source_trace_read_off
    (SourceTraceReadOffData.ofExpandedSourcePackage
      sourceObjectPackageFromTheorems fixedFrontEndFromTheorems
      traceFrontEndFromTheorems)

/-- Checklist item 10 final sign contract skeleton. -/
def finalSignBridgeFromTheorems :
    FinalSignBridgeContract
      (RouteInputs.ofExpandedSourcePackage sourceObjectPackageFromTheorems)
      (SourceTraceReadOffData.ofExpandedSourcePackage
        sourceObjectPackageFromTheorems fixedFrontEndFromTheorems
        traceFrontEndFromTheorems).archimedeanTest
      (SourceBackedFixedSTest.ofExpandedSourcePackage
        sourceObjectPackageFromTheorems fixedFrontEndFromTheorems)
      traceFrontEndFromTheorems.lambda
      ((RouteInputs.ofExpandedSourcePackage
          sourceObjectPackageFromTheorems).ccm25.weilSymbols.convolutionStar
        (SourceBackedFixedSTest.ofExpandedSourcePackage
          sourceObjectPackageFromTheorems fixedFrontEndFromTheorems).weilTest
        (SourceBackedFixedSTest.ofExpandedSourcePackage
          sourceObjectPackageFromTheorems fixedFrontEndFromTheorems).weilTest)
      traceFrontEndFromTheorems.ccm25ArithmeticPackage :=
  final_sign_bridge_contract_of_common_test
    (source_qw_uses_common_test_of_common_tuple
      (by
        rw [← expanded_source_package_convolution_square_read_off
          sourceObjectPackageFromTheorems fixedFrontEndFromTheorems]
        exact commonTupleFromTheorems))
    sourceArchimedeanSignBridgeFromTheorems

/-- Checklist item 10 sign-direction skeleton. -/
noncomputable def finalSignNonpositiveFromTheorems :
    SourceQWNonnegativeToCC20Nonpositive
      (RouteInputs.ofExpandedSourcePackage sourceObjectPackageFromTheorems)
      (SourceTraceReadOffData.ofExpandedSourcePackage
        sourceObjectPackageFromTheorems fixedFrontEndFromTheorems
        traceFrontEndFromTheorems).archimedeanTest
      (SourceBackedFixedSTest.ofExpandedSourcePackage
        sourceObjectPackageFromTheorems fixedFrontEndFromTheorems)
      traceFrontEndFromTheorems.lambda
      ((RouteInputs.ofExpandedSourcePackage
          sourceObjectPackageFromTheorems).ccm25.weilSymbols.convolutionStar
        (SourceBackedFixedSTest.ofExpandedSourcePackage
          sourceObjectPackageFromTheorems fixedFrontEndFromTheorems).weilTest
        (SourceBackedFixedSTest.ofExpandedSourcePackage
          sourceObjectPackageFromTheorems fixedFrontEndFromTheorems).weilTest)
      traceFrontEndFromTheorems.ccm25ArithmeticPackage :=
  final_sign_nonnegative_to_nonpositive_of_contract finalSignBridgeFromTheorems

/-- Checklist item 11 source-backed ledger skeleton. -/
def sourceBackedLedgersFromTheorems :
    SourceBackedLedgers
      (RouteInputs.ofExpandedSourcePackage sourceObjectPackageFromTheorems)
      (SourceBackedFixedSTest.ofExpandedSourcePackage
        sourceObjectPackageFromTheorems fixedFrontEndFromTheorems)
      routeLedgersFromTheorems :=
  source_backed_ledgers_of_ledgers_cleared
    traceFrontEndFromTheorems.oneLtLambda
    ledgersClearedFromTheorems

/-- Checklist item 12 skeleton. -/
def fullWeilPositivityFromTheorems :
    SourceBackedFullPositivity
      (RouteInputs.ofExpandedSourcePackage sourceObjectPackageFromTheorems)
      (SourceBackedFixedSTest.ofExpandedSourcePackage
        sourceObjectPackageFromTheorems fixedFrontEndFromTheorems)
      routeLedgersFromTheorems where
  sourceTraceReadOff :=
    SourceTraceReadOffData.ofExpandedSourcePackage
      sourceObjectPackageFromTheorems fixedFrontEndFromTheorems
      traceFrontEndFromTheorems
  sourceBackedLedgers := sourceBackedLedgersFromTheorems

/-- Checklist item 14 skeleton in the expanded-source-front-end shape. -/
noncomputable def expandedSourceRouteCertificateFrontEndFromTheorems :
    ExpandedSourceRouteCertificateFrontEnd
      sourceObjectPackageFromTheorems fixedFrontEndFromTheorems
      traceFrontEndFromTheorems where
  ledgers := routeLedgersFromTheorems
  commonTuple := commonTupleFromTheorems
  signDefectClassification := signDefectClassificationFromTheorems
  restrictedToFullQWBridge := restrictedToFullQWFromTheorems
  sourceArchimedeanSignBridge := sourceArchimedeanSignBridgeFromTheorems

/-- Checklist item 14 skeleton. -/
noncomputable def routeCertificateFromTheorems :
    RouteCertificate
      (RouteInputs.ofExpandedSourcePackage sourceObjectPackageFromTheorems) :=
  route_certificate_of_expanded_source_package
    sourceObjectPackageFromTheorems
    fixedFrontEndFromTheorems
    traceFrontEndFromTheorems
    expandedSourceRouteCertificateFrontEndFromTheorems

/-- Checklist item 13 skeleton. -/
theorem cc20FiniteVanishingExitFromTheorems :
    (RouteInputs.ofExpandedSourcePackage
      sourceObjectPackageFromTheorems).cc20.rhDefinitionBridge.SourceRH :=
  cc20_source_rh_of_route_certificate routeCertificateFromTheorems

/-- Checklist item 13 RH-definition bridge skeleton to Mathlib's statement. -/
theorem rhDefinitionBridgeToMathlibFromTheorems :
    _root_.RiemannHypothesis :=
  Source.RHDefinitionBridge.source_rh_to_mathlib_rh
    (RouteInputs.ofExpandedSourcePackage
      sourceObjectPackageFromTheorems).cc20.rhDefinitionBridge
    cc20FiniteVanishingExitFromTheorems

/--
Checklist item 15 skeleton.

This declaration intentionally lives only in the development namespace. It is a
top-down wiring target, not a completed RH proof while upstream declarations in
this module or active route modules still contain `sorry`.
-/
theorem unconditional_rh_skeleton : _root_.RiemannHypothesis := by
  exact final_connes_weil_rh routeCertificateFromTheorems

/-
Normalized contract-backed lane.

This is the stricter top-down target for the current Lean work.  Unlike the
generic skeleton above, it follows the normalized route endpoint whose
trace-scale ledger is backed by a named no-extra-bulk contract rather than the
older compatibility path that used `True`.
-/

def normalizedBaseFromTheorems :
    Source.SourceObjectTheoremBasePackage := by
  sorry

def normalizedGlobalQWPsiRowsFromTheorems :
    Source.CCM25Concrete.Rows.ConcreteGlobalQWPsiRows
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols := by
  sorry

theorem normalizedQWDefinitionFromTheorems :
    WeilFormSymbols.QWDefinitionStatement
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols :=
  normalizedGlobalQWPsiRowsFromTheorems.qwDefinition

theorem normalizedPsiSignFromTheorems :
    WeilFormSymbols.PsiSignStatement
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols :=
  normalizedGlobalQWPsiRowsFromTheorems.psiSign

def normalizedConcreteGlobalQWPsiRowsFromTheorems :
    Source.CCM25Concrete.Rows.ConcreteGlobalQWPsiRows
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols :=
  normalizedGlobalQWPsiRowsFromTheorems

structure RestrictedQWLambdaPoleRows (W : WeilFormSymbols) where
  restrictedRows : Source.CCM25Concrete.Rows.ConcreteRestrictedQWLambdaRows W
  poleRows : Source.CCM25Concrete.Rows.ConcretePoleNormalizationRows W

def normalizedRestrictedQWLambdaPoleRowsFromTheorems :
    RestrictedQWLambdaPoleRows
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols := by
  sorry

theorem normalizedQWLambdaFormulaFromTheorems :
    WeilFormSymbols.QWLambdaFormulaStatement
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols :=
  normalizedRestrictedQWLambdaPoleRowsFromTheorems.restrictedRows.qwLambdaFormula

def normalizedConcreteRestrictedQWLambdaRowsFromTheorems :
    Source.CCM25Concrete.Rows.ConcreteRestrictedQWLambdaRows
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols :=
  normalizedRestrictedQWLambdaPoleRowsFromTheorems.restrictedRows

structure FinitePrimeSourceTestSelectorData
    (W : WeilFormSymbols)
    (common :
      Source.CCM25Concrete.CommonSourceTest.ConcreteCommonSourceTest W) where
  sourceTest :
    ∀ f g : TestFunction,
      Source.CCM25Concrete.PrimePowerTest.SourceTestEvaluationInterface W f g
  commonPairSourceTest :
    sourceTest common.sourceTest common.sourceTest =
      common.toSourceTestEvaluationInterface

structure FixedLambdaArithmeticCertificateSourceTestData
    (W : WeilFormSymbols) (f g : TestFunction) (lambda : ℝ)
    (sourceTest :
      Source.CCM25Concrete.PrimePowerTest.SourceTestEvaluationInterface
        W f g) where
  visibleIff :
    ∀ n : ℕ,
      W.finitePrimeAtomVisible n (W.convolutionStar f g) ↔
        Source.CCM25Concrete.PrimePowerSupport.SourceVisibleAtomData
          Source.CCM25Concrete.PrimePowerArithmetic.SourcePrimePowerIndex
          sourceTest.sourceAtomVisible n
  globalExact :
    ∀ n : ℕ,
      n ∈ W.globalPrimeIndexSet ↔
        Source.CCM25Concrete.PrimePowerSupport.SourceGlobalIndexData
          Source.CCM25Concrete.PrimePowerArithmetic.SourcePrimePowerIndex
          sourceTest.sourceAtomVisible n
  restrictedExact :
    ∀ n : ℕ,
      n ∈ W.restrictedPrimeIndexSet lambda ↔
        Source.CCM25Concrete.PrimePowerSupport.SourceRestrictedIndexData
          Source.CCM25Concrete.PrimePowerArithmetic.SourcePrimePowerIndex
          sourceTest.sourceAtomVisible lambda n
  visibleAtomsInLambdaCut :
    ∀ n : ℕ,
      W.finitePrimeAtomVisible n (W.convolutionStar f g) →
        Source.CCM25Concrete.PrimePowerSupport.SourceLambdaCut lambda n
  atoms :
    Source.CCM25Concrete.PrimePowerArithmetic.SourceFinitePrimeArithmeticNormalization
      W f g
  atomsUseSourceTest :
    Source.CCM25Concrete.PrimePowerArithmetic.UsesSourceTest atoms sourceTest

namespace FixedLambdaArithmeticCertificateSourceTestData

def toSupport
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    {sourceTest :
      Source.CCM25Concrete.PrimePowerTest.SourceTestEvaluationInterface
        W f g}
    (data :
      FixedLambdaArithmeticCertificateSourceTestData
        W f g lambda sourceTest)
    (hlambda : 1 < lambda) :
    Source.CCM25Concrete.PrimePowerSupport.SourcePrimePowerArithmeticSupportSkeletonAtLambda
      W f g lambda where
  oneLtLambda := hlambda
  sourceTest := sourceTest
  visibleIff := data.visibleIff
  globalExact := data.globalExact
  restrictedExact := data.restrictedExact
  visibleAtomsInLambdaCut := data.visibleAtomsInLambdaCut

def toCertificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    {sourceTest :
      Source.CCM25Concrete.PrimePowerTest.SourceTestEvaluationInterface
        W f g}
    (data :
      FixedLambdaArithmeticCertificateSourceTestData
        W f g lambda sourceTest)
    (hlambda : 1 < lambda) :
    Source.CCM25Concrete.FinitePrimeCertificate.FixedLambdaFinitePrimeArithmeticCertificate
      W f g lambda where
  support := data.toSupport hlambda
  atoms := data.atoms
  atomsUseSupportSourceTest := data.atomsUseSourceTest

theorem toCertificate_support_sourceTest
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    {sourceTest :
      Source.CCM25Concrete.PrimePowerTest.SourceTestEvaluationInterface
        W f g}
    (data :
      FixedLambdaArithmeticCertificateSourceTestData
        W f g lambda sourceTest)
    (hlambda : 1 < lambda) :
    (data.toCertificate hlambda).support.sourceTest = sourceTest :=
  rfl

end FixedLambdaArithmeticCertificateSourceTestData

structure FinitePrimeArithmeticSourceData
    (W : WeilFormSymbols)
    (common :
      Source.CCM25Concrete.CommonSourceTest.ConcreteCommonSourceTest W) where
  selector : FinitePrimeSourceTestSelectorData W common
  certificateData :
    ∀ f g : TestFunction, ∀ lambda : ℝ,
      FixedLambdaArithmeticCertificateSourceTestData
        W f g lambda (selector.sourceTest f g)

structure CommonFinitePrimeArithmeticSourceData
    (W : WeilFormSymbols) where
  commonTestFunction : TestFunction
  finitePrimeData :
    FinitePrimeArithmeticSourceData W
      (Source.CCM25Concrete.CommonSourceTest.concreteCommonSourceTest
        W commonTestFunction)

def normalizedCommonFinitePrimeArithmeticSourceDataFromTheorems :
    CommonFinitePrimeArithmeticSourceData
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols := by
  sorry

def normalizedCommonTestFunctionFromTheorems : TestFunction :=
  normalizedCommonFinitePrimeArithmeticSourceDataFromTheorems.commonTestFunction

def normalizedConcreteCommonTestFromTheorems :
    Source.CCM25Concrete.CommonSourceTest.ConcreteCommonSourceTest
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols :=
  Source.CCM25Concrete.CommonSourceTest.concreteCommonSourceTest
    normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols
    normalizedCommonTestFunctionFromTheorems

def normalizedFinitePrimeArithmeticSourceDataFromTheorems :
    FinitePrimeArithmeticSourceData
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols
      normalizedConcreteCommonTestFromTheorems :=
  normalizedCommonFinitePrimeArithmeticSourceDataFromTheorems.finitePrimeData

def normalizedFinitePrimeSourceTestSelectorDataFromTheorems :
    FinitePrimeSourceTestSelectorData
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols
      normalizedConcreteCommonTestFromTheorems :=
  normalizedFinitePrimeArithmeticSourceDataFromTheorems.selector

def normalizedFinitePrimeSourceTestFromTheorems
    (f g : TestFunction) :
    Source.CCM25Concrete.PrimePowerTest.SourceTestEvaluationInterface
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols f g :=
  normalizedFinitePrimeSourceTestSelectorDataFromTheorems.sourceTest f g

theorem normalizedFinitePrimeSourceTestCommonPairFromTheorems :
    normalizedFinitePrimeSourceTestFromTheorems
        normalizedConcreteCommonTestFromTheorems.sourceTest
        normalizedConcreteCommonTestFromTheorems.sourceTest =
      normalizedConcreteCommonTestFromTheorems.toSourceTestEvaluationInterface :=
  normalizedFinitePrimeSourceTestSelectorDataFromTheorems.commonPairSourceTest

def normalizedFixedLambdaArithmeticCertificateDataFromTheorems
    (f g : TestFunction) (lambda : ℝ) :
    FixedLambdaArithmeticCertificateSourceTestData
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols f g lambda
      (normalizedFinitePrimeSourceTestFromTheorems f g) :=
  normalizedFinitePrimeArithmeticSourceDataFromTheorems.certificateData
    f g lambda

def normalizedFixedLambdaArithmeticCertificatesFromTheorems :
    Source.CCM25Concrete.FinitePrimeInterface.FixedLambdaArithmeticCertificatesForAllTests
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols := by
  intro f g lambda hlambda
  exact
    FixedLambdaArithmeticCertificateSourceTestData.toCertificate
      (normalizedFixedLambdaArithmeticCertificateDataFromTheorems f g lambda)
      hlambda

theorem normalizedFixedLambdaArithmeticCertificateSourceTestFromTheorems
    (f g : TestFunction) (lambda : ℝ) (hlambda : 1 < lambda) :
    ((normalizedFixedLambdaArithmeticCertificatesFromTheorems
          f g lambda hlambda).support.sourceTest =
      normalizedFinitePrimeSourceTestFromTheorems f g) :=
  rfl

def normalizedFinitePrimeArithmeticCertificatesFromTheorems :
    Source.CCM25Concrete.FinitePrimeInterface.FixedLambdaArithmeticSourceTestCertificatesForAllTests
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols := by
  intro f g
  exact
    { sourceTest := normalizedFinitePrimeSourceTestFromTheorems f g
      certificate := normalizedFixedLambdaArithmeticCertificatesFromTheorems f g
      certificateSourceTest :=
        normalizedFixedLambdaArithmeticCertificateSourceTestFromTheorems f g }

theorem normalizedPoleNormalizationFromTheorems :
    WeilFormSymbols.PoleNormalizationStatement
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols :=
  normalizedRestrictedQWLambdaPoleRowsFromTheorems.poleRows.poleNormalization

def normalizedConcretePoleNormalizationRowsFromTheorems :
    Source.CCM25Concrete.Rows.ConcretePoleNormalizationRows
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols :=
  normalizedRestrictedQWLambdaPoleRowsFromTheorems.poleRows

def normalizedConcreteArithmeticRowsFromTheorems :
    Source.CCM25Concrete.Interface.ConcreteCCM25ArithmeticRows
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols where
  globalRows := normalizedConcreteGlobalQWPsiRowsFromTheorems
  restrictedRows := normalizedConcreteRestrictedQWLambdaRowsFromTheorems
  finitePrimeArithmeticCertificates :=
    normalizedFinitePrimeArithmeticCertificatesFromTheorems
  poleRows := normalizedConcretePoleNormalizationRowsFromTheorems

theorem normalizedCommonPairSourceTestFromTheorems :
    (normalizedConcreteArithmeticRowsFromTheorems.finitePrimeArithmeticCertificates
        normalizedConcreteCommonTestFromTheorems.sourceTest
        normalizedConcreteCommonTestFromTheorems.sourceTest).sourceTest =
      normalizedConcreteCommonTestFromTheorems.toSourceTestEvaluationInterface :=
  normalizedFinitePrimeSourceTestCommonPairFromTheorems

def normalizedConcreteCommonFromTheorems :
    Source.SourceObjectConcreteCommonData normalizedBaseFromTheorems :=
  Source.SourceObjectConcreteCommonData.ofCommonPairSourceTest
    normalizedConcreteCommonTestFromTheorems
    normalizedConcreteArithmeticRowsFromTheorems
    normalizedCommonPairSourceTestFromTheorems

def normalizedCommonFromTheorems :
    Source.SourceObjectCommonData normalizedBaseFromTheorems :=
  normalizedConcreteCommonFromTheorems.toSourceObjectCommonData

def normalizedCCM24FromTheorems :
    Source.SourceObject.CCM24SemilocalObjectPackage := by
  sorry

def normalizedSeedFromTheorems :
    Source.CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols := by
  sorry

def normalizedRemaindersFromTheorems :
    Source.CC20Concrete.TraceScale.CC20TracePackageRemainderData
      normalizedSeedFromTheorems := by
  sorry

def normalizedRhExitFromTheorems :
    Source.SourceObject.CC20RHExitObjectPackage := by
  sorry

def normalizedRowsFromTheorems :
    Source.SourceObjectExpandedRows normalizedBaseFromTheorems
      normalizedCommonFromTheorems :=
  Source.SourceObjectExpandedRows.ofNormalizedCC20Trace
    normalizedCCM24FromTheorems normalizedSeedFromTheorems
    normalizedRemaindersFromTheorems

def normalizedBridgesFromTheorems :
    Source.SourceObjectCrossObjectBridges normalizedBaseFromTheorems
      normalizedCommonFromTheorems normalizedRowsFromTheorems
      normalizedRhExitFromTheorems := by
  sorry

abbrev normalizedSourceObjectPackageFromTheorems :
    Source.SourceObject.SourceObjectPackage :=
  Source.sourceObjectPackageOfNormalizedCC20Trace
    normalizedBaseFromTheorems normalizedCommonFromTheorems
    normalizedCCM24FromTheorems normalizedSeedFromTheorems
    normalizedRemaindersFromTheorems normalizedRhExitFromTheorems
    normalizedBridgesFromTheorems

def normalizedFixedDataFromTheorems :
    FixedSTestObligationData normalizedSourceObjectPackageFromTheorems := by
  sorry

abbrev normalizedFixedFrontEndFromTheorems :
    ExpandedSourceFixedSTestFrontEnd
      normalizedSourceObjectPackageFromTheorems :=
  FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
    normalizedBaseFromTheorems normalizedCommonFromTheorems
    normalizedCCM24FromTheorems normalizedSeedFromTheorems
    normalizedRemaindersFromTheorems normalizedRhExitFromTheorems
    normalizedBridgesFromTheorems normalizedFixedDataFromTheorems

def normalizedTraceDataFromTheorems :
    TraceFrontEndData
      normalizedSourceObjectPackageFromTheorems
      normalizedFixedFrontEndFromTheorems := by
  sorry

abbrev normalizedTraceFrontEndFromTheorems :
    ExpandedSourceTraceReadOffFrontEnd
      normalizedSourceObjectPackageFromTheorems
      normalizedFixedFrontEndFromTheorems :=
  normalizedTraceDataFromTheorems.toExpandedSourceTraceReadOffFrontEnd
    normalizedSourceObjectPackageFromTheorems
    normalizedFixedFrontEndFromTheorems

noncomputable abbrev normalizedScalarSeedFromTheorems :
    Source.CC20Concrete.TraceScale.NormalizedScalarTraceScaleSymbols :=
  TraceFrontEndData.normalizedRestrictedScalarTraceSeedOfTraceData
    normalizedBaseFromTheorems normalizedCommonFromTheorems
    normalizedCCM24FromTheorems normalizedSeedFromTheorems
    normalizedRemaindersFromTheorems normalizedRhExitFromTheorems
    normalizedBridgesFromTheorems normalizedFixedDataFromTheorems
    normalizedTraceDataFromTheorems

def normalizedScalarRemaindersFromTheorems :
    Source.CC20Concrete.TraceScale.CC20TracePackageRemainderData
      (Source.CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
        normalizedScalarSeedFromTheorems) := by
  sorry

def normalizedScalarRhExitFromTheorems :
    Source.SourceObject.CC20RHExitObjectPackage := by
  sorry

def normalizedScalarBridgesFromTheorems :
    Source.SourceObjectCrossObjectBridges normalizedBaseFromTheorems
      normalizedCommonFromTheorems
      (Source.SourceObjectExpandedRows.ofNormalizedScalarCC20Trace
        normalizedCCM24FromTheorems normalizedScalarSeedFromTheorems
        normalizedScalarRemaindersFromTheorems)
      normalizedScalarRhExitFromTheorems := by
  sorry

noncomputable abbrev normalizedScalarSourceObjectPackageFromTheorems :
    Source.SourceObject.SourceObjectPackage :=
  Source.sourceObjectPackageOfNormalizedScalarCC20Trace
    normalizedBaseFromTheorems normalizedCommonFromTheorems
    normalizedCCM24FromTheorems normalizedScalarSeedFromTheorems
    normalizedScalarRemaindersFromTheorems
    normalizedScalarRhExitFromTheorems
    normalizedScalarBridgesFromTheorems

def normalizedScalarFixedDataFromTheorems :
    FixedSTestObligationData
      normalizedScalarSourceObjectPackageFromTheorems := by
  sorry

def normalizedScalarTestAndQuotientCompatibilityFromTheorems :
    TestAndQuotientCompatibility
      (RouteInputs.ofExpandedSourcePackage
        normalizedScalarSourceObjectPackageFromTheorems)
      (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedScalarPackage
        normalizedBaseFromTheorems normalizedCommonFromTheorems
        normalizedCCM24FromTheorems normalizedScalarSeedFromTheorems
        normalizedScalarRemaindersFromTheorems
        normalizedScalarRhExitFromTheorems
        normalizedScalarBridgesFromTheorems
        normalizedScalarFixedDataFromTheorems) :=
  TraceFrontEndData.normalizedScalarTestAndQuotientCompatibilityFromOriginalCCM25
    normalizedBaseFromTheorems normalizedCommonFromTheorems
    normalizedCCM24FromTheorems normalizedSeedFromTheorems
    normalizedRemaindersFromTheorems normalizedRhExitFromTheorems
    normalizedBridgesFromTheorems normalizedFixedDataFromTheorems
    normalizedTraceDataFromTheorems normalizedScalarRemaindersFromTheorems
    normalizedScalarRhExitFromTheorems normalizedScalarBridgesFromTheorems
    normalizedScalarFixedDataFromTheorems

def normalizedScalarFixedSSupportSquareTransportFromTheorems :
    FixedSQuantizedSupportSquareTransport
      (RouteInputs.ofExpandedSourcePackage
        normalizedScalarSourceObjectPackageFromTheorems)
      normalizedScalarSourceObjectPackageFromTheorems.cc20Trace.sourceTraceTest
      (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedScalarPackage
        normalizedBaseFromTheorems normalizedCommonFromTheorems
        normalizedCCM24FromTheorems normalizedScalarSeedFromTheorems
        normalizedScalarRemaindersFromTheorems
        normalizedScalarRhExitFromTheorems
        normalizedScalarBridgesFromTheorems
        normalizedScalarFixedDataFromTheorems)
      normalizedTraceDataFromTheorems.lambda :=
  TraceFrontEndData.normalizedScalarFixedSSupportSquareTransportFromOriginalCCM25
    normalizedBaseFromTheorems normalizedCommonFromTheorems
    normalizedCCM24FromTheorems normalizedSeedFromTheorems
    normalizedRemaindersFromTheorems normalizedRhExitFromTheorems
    normalizedBridgesFromTheorems normalizedFixedDataFromTheorems
    normalizedTraceDataFromTheorems normalizedScalarRemaindersFromTheorems
    normalizedScalarRhExitFromTheorems normalizedScalarBridgesFromTheorems
    normalizedScalarFixedDataFromTheorems

def normalizedNoExtraBulkSourceTermsFromTheorems :
    TraceFrontEndData.TraceScaleNoExtraBulkSourceTermData
      normalizedSourceObjectPackageFromTheorems
      normalizedFixedFrontEndFromTheorems
      normalizedTraceFrontEndFromTheorems.lambda
      normalizedTraceFrontEndFromTheorems.ccm25ArithmeticPackage :=
  TraceFrontEndData.no_extra_bulk_source_term_data_of_trace_scale_no_missing_bulk
    normalizedTraceDataFromTheorems.traceScaleNoMissingBulk

def normalizedNoExtraBulkContractFromTheorems :
    TraceFrontEndData.TraceScaleNoExtraBulkContract
      normalizedSourceObjectPackageFromTheorems
      normalizedFixedFrontEndFromTheorems
      normalizedTraceFrontEndFromTheorems.lambda
      normalizedTraceFrontEndFromTheorems.ccm25ArithmeticPackage :=
  TraceFrontEndData.no_extra_bulk_contract_of_source_term_data
    normalizedNoExtraBulkSourceTermsFromTheorems

structure NormalizedRouteLedgerClearingInputData where
  ledgers : RouteLedgers
  cleared : LedgersCleared ledgers

def normalizedRouteLedgerClearingInputDataFromTheorems :
    NormalizedRouteLedgerClearingInputData := by
  sorry

def normalizedRouteLedgersFromTheorems : RouteLedgers :=
  normalizedRouteLedgerClearingInputDataFromTheorems.ledgers

theorem normalizedRankLedgerKilledFromTheorems :
    normalizedRouteLedgersFromTheorems.rankKilled :=
  normalizedRouteLedgerClearingInputDataFromTheorems.cleared.rankKilled

theorem normalizedPoleLedgerKilledFromTheorems :
    normalizedRouteLedgersFromTheorems.poleKilled :=
  normalizedRouteLedgerClearingInputDataFromTheorems.cleared.poleKilled

theorem normalizedCdefExhaustsFromTheorems :
    normalizedRouteLedgersFromTheorems.cdefExhausts :=
  normalizedRouteLedgerClearingInputDataFromTheorems.cleared.cdefExhausts

def normalizedLedgersClearedFromTheorems :
    LedgersCleared normalizedRouteLedgersFromTheorems :=
  normalizedRouteLedgerClearingInputDataFromTheorems.cleared

def normalizedSourceBackedLedgersFromTheorems :
    SourceBackedLedgers
      (RouteInputs.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems)
      (SourceBackedFixedSTest.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems
        normalizedFixedFrontEndFromTheorems)
      normalizedRouteLedgersFromTheorems :=
  source_backed_ledgers_of_ledgers_cleared
    normalizedTraceFrontEndFromTheorems.oneLtLambda
    normalizedLedgersClearedFromTheorems

theorem normalizedSignDefectClassificationFromTheorems :
    SourceSignDefectClassification
      (RouteInputs.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems)
      (SourceBackedFixedSTest.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems
        normalizedFixedFrontEndFromTheorems)
      normalizedTraceFrontEndFromTheorems.lambda
      normalizedRouteLedgersFromTheorems :=
  source_sign_defect_classification_of_ledgers_cleared
    normalizedTraceFrontEndFromTheorems.oneLtLambda
    normalizedLedgersClearedFromTheorems

def normalizedCommonTupleFromTheorems :
    SourceCommonTestTupleContract
      (RouteInputs.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems)
      (SourceBackedFixedSTest.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems
        normalizedFixedFrontEndFromTheorems)
      normalizedTraceFrontEndFromTheorems.lambda
      normalizedSourceObjectPackageFromTheorems.commonTest.sourceConvolutionSquare
      normalizedTraceFrontEndFromTheorems.ccm25ArithmeticPackage := by
  exact
    source_common_test_tuple_contract_of_package
      (window_lambda_compatibility_of_source_backed
        normalizedTraceFrontEndFromTheorems.oneLtLambda)
      (expanded_source_package_convolution_square_read_off
        normalizedSourceObjectPackageFromTheorems
        normalizedFixedFrontEndFromTheorems)

structure NormalizedRestrictedToFullThresholdInputData where
  threshold :
    RestrictedToFullQWLargeLambdaThreshold
      (RouteInputs.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems)
      (SourceBackedFixedSTest.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems
        normalizedFixedFrontEndFromTheorems)
      normalizedSourceObjectPackageFromTheorems.commonTest.sourceConvolutionSquare
  currentAboveThreshold :
    threshold.lambda0 ≤ normalizedTraceFrontEndFromTheorems.lambda

def normalizedRestrictedToFullThresholdInputDataFromTheorems :
    NormalizedRestrictedToFullThresholdInputData := by
  sorry

def normalizedRestrictedToFullLargeLambdaThresholdFromTheorems :
    RestrictedToFullQWLargeLambdaThreshold
      (RouteInputs.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems)
      (SourceBackedFixedSTest.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems
        normalizedFixedFrontEndFromTheorems)
      normalizedSourceObjectPackageFromTheorems.commonTest.sourceConvolutionSquare :=
  normalizedRestrictedToFullThresholdInputDataFromTheorems.threshold

theorem normalizedRestrictedToFullCurrentAboveThresholdFromTheorems :
    normalizedRestrictedToFullLargeLambdaThresholdFromTheorems.lambda0 ≤
      normalizedTraceFrontEndFromTheorems.lambda :=
  normalizedRestrictedToFullThresholdInputDataFromTheorems.currentAboveThreshold

noncomputable def normalizedRestrictedToFullCurrentCutoffBindingFromTheorems :
    RestrictedToFullCurrentCutoffBinding
      (RouteInputs.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems)
      (SourceBackedFixedSTest.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems
        normalizedFixedFrontEndFromTheorems)
      normalizedTraceFrontEndFromTheorems.lambda
      normalizedSourceObjectPackageFromTheorems.commonTest.sourceConvolutionSquare
      normalizedRouteLedgersFromTheorems
      normalizedTraceFrontEndFromTheorems.ccm25ArithmeticPackage :=
  restricted_to_full_current_cutoff_binding_of_sign_defect
    normalizedRestrictedToFullLargeLambdaThresholdFromTheorems
    normalizedRestrictedToFullCurrentAboveThresholdFromTheorems
    normalizedCommonTupleFromTheorems
    normalizedSignDefectClassificationFromTheorems

noncomputable def normalizedRestrictedToFullQWFromTheorems :
    RestrictedToFullQWBridgeContract
      (RouteInputs.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems)
      (SourceBackedFixedSTest.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems
        normalizedFixedFrontEndFromTheorems)
      normalizedTraceFrontEndFromTheorems.lambda
      normalizedSourceObjectPackageFromTheorems.commonTest.sourceConvolutionSquare
      normalizedRouteLedgersFromTheorems
      normalizedTraceFrontEndFromTheorems.ccm25ArithmeticPackage :=
  restricted_to_full_bridge_contract_of_current_cutoff_binding
    normalizedRestrictedToFullCurrentCutoffBindingFromTheorems

structure NormalizedScalarTraceScaleInputData where
  noExtraBulk :
    TraceFrontEndData.TraceScaleNoExtraBulkContract
      normalizedScalarSourceObjectPackageFromTheorems
      (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedScalarPackage
        normalizedBaseFromTheorems normalizedCommonFromTheorems
        normalizedCCM24FromTheorems normalizedScalarSeedFromTheorems
        normalizedScalarRemaindersFromTheorems
        normalizedScalarRhExitFromTheorems
        normalizedScalarBridgesFromTheorems
        normalizedScalarFixedDataFromTheorems)
      normalizedTraceDataFromTheorems.lambda
      normalizedTraceDataFromTheorems.ccm25ArithmeticPackage
  amplitudeSquareScalar :
    TraceFrontEndData.NormalizedTraceAmplitudeSquareScalarContract
      normalizedBaseFromTheorems normalizedCommonFromTheorems
      normalizedCCM24FromTheorems normalizedSeedFromTheorems
      normalizedRemaindersFromTheorems normalizedRhExitFromTheorems
      normalizedBridgesFromTheorems normalizedFixedDataFromTheorems
      normalizedTraceDataFromTheorems

def normalizedSupportSquareScalarNormalFormInputFromTheorems :
    TraceFrontEndData.NormalizedSupportSquareScalarNormalFormContract
      normalizedBaseFromTheorems normalizedCommonFromTheorems
      normalizedCCM24FromTheorems normalizedSeedFromTheorems
      normalizedRemaindersFromTheorems normalizedRhExitFromTheorems
      normalizedBridgesFromTheorems normalizedFixedDataFromTheorems
      normalizedTraceDataFromTheorems := by
  sorry

def normalizedTraceAmplitudeSquareScalarInputFromTheorems :
    TraceFrontEndData.NormalizedTraceAmplitudeSquareScalarContract
      normalizedBaseFromTheorems normalizedCommonFromTheorems
      normalizedCCM24FromTheorems normalizedSeedFromTheorems
      normalizedRemaindersFromTheorems normalizedRhExitFromTheorems
      normalizedBridgesFromTheorems normalizedFixedDataFromTheorems
      normalizedTraceDataFromTheorems :=
  TraceFrontEndData.normalizedTraceAmplitudeSquareScalarContractOfSupportSquareScalarNormalForm
    normalizedBaseFromTheorems normalizedCommonFromTheorems
    normalizedCCM24FromTheorems normalizedSeedFromTheorems
    normalizedRemaindersFromTheorems normalizedRhExitFromTheorems
    normalizedBridgesFromTheorems normalizedFixedDataFromTheorems
    normalizedTraceDataFromTheorems
    normalizedSupportSquareScalarNormalFormInputFromTheorems

noncomputable def normalizedScalarTraceScaleInputDataFromTheorems :
    NormalizedScalarTraceScaleInputData where
  noExtraBulk :=
    TraceFrontEndData.no_extra_bulk_contract_of_parts
      normalizedNoExtraBulkContractFromTheorems.noExtraBulkScaleTerm
      normalizedNoExtraBulkContractFromTheorems.noExtraBulkScaleTermHolds
  amplitudeSquareScalar :=
    normalizedTraceAmplitudeSquareScalarInputFromTheorems

def normalizedScalarFullTraceReadOffBridgeFromTheorems :
    FullTraceReadOffBridgeContract
      (RouteInputs.ofExpandedSourcePackage
        normalizedScalarSourceObjectPackageFromTheorems)
      normalizedScalarSourceObjectPackageFromTheorems.cc20Trace.sourceTraceTest
      (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedScalarPackage
        normalizedBaseFromTheorems normalizedCommonFromTheorems
        normalizedCCM24FromTheorems normalizedScalarSeedFromTheorems
        normalizedScalarRemaindersFromTheorems
        normalizedScalarRhExitFromTheorems
        normalizedScalarBridgesFromTheorems
        normalizedScalarFixedDataFromTheorems) :=
  normalizedScalarTraceFrontFullTraceReadOffBridgeFromRestrictedToFullContract
    normalizedBaseFromTheorems normalizedCommonFromTheorems
    normalizedCCM24FromTheorems normalizedSeedFromTheorems
    normalizedRemaindersFromTheorems normalizedRhExitFromTheorems
    normalizedBridgesFromTheorems normalizedFixedDataFromTheorems
    normalizedTraceDataFromTheorems normalizedScalarRemaindersFromTheorems
    normalizedScalarRhExitFromTheorems normalizedScalarBridgesFromTheorems
    normalizedScalarFixedDataFromTheorems normalizedRouteLedgersFromTheorems
    normalizedRestrictedToFullQWFromTheorems

def normalizedScalarRestrictedTraceReadOffBridgeFromTheorems :
    RestrictedTraceReadOffBridgeContract
      (RouteInputs.ofExpandedSourcePackage
        normalizedScalarSourceObjectPackageFromTheorems)
      normalizedScalarSourceObjectPackageFromTheorems.cc20Trace.sourceTraceTest
      (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedScalarPackage
        normalizedBaseFromTheorems normalizedCommonFromTheorems
        normalizedCCM24FromTheorems normalizedScalarSeedFromTheorems
        normalizedScalarRemaindersFromTheorems
        normalizedScalarRhExitFromTheorems
        normalizedScalarBridgesFromTheorems
        normalizedScalarFixedDataFromTheorems)
      normalizedTraceDataFromTheorems.lambda :=
  TraceFrontEndData.normalizedScalarRestrictedTraceReadOffBridgeFromOriginalCCM25
    normalizedBaseFromTheorems normalizedCommonFromTheorems
    normalizedCCM24FromTheorems normalizedSeedFromTheorems
    normalizedRemaindersFromTheorems normalizedRhExitFromTheorems
    normalizedBridgesFromTheorems normalizedFixedDataFromTheorems
    normalizedTraceDataFromTheorems normalizedScalarRemaindersFromTheorems
    normalizedScalarRhExitFromTheorems normalizedScalarBridgesFromTheorems
    normalizedScalarFixedDataFromTheorems

noncomputable def normalizedScalarTraceScaleNoMissingBulkFromTheorems :
    TraceScaleNoMissingBulkData
      normalizedScalarSourceObjectPackageFromTheorems
      (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedScalarPackage
        normalizedBaseFromTheorems normalizedCommonFromTheorems
        normalizedCCM24FromTheorems normalizedScalarSeedFromTheorems
        normalizedScalarRemaindersFromTheorems
        normalizedScalarRhExitFromTheorems
        normalizedScalarBridgesFromTheorems
        normalizedScalarFixedDataFromTheorems)
      normalizedTraceDataFromTheorems.lambda
      normalizedTraceDataFromTheorems.ccm25ArithmeticPackage :=
  TraceFrontEndData.traceScaleNoMissingBulkOfNormalizedScalarPackageFromOriginalCCM25
    normalizedBaseFromTheorems normalizedCommonFromTheorems
    normalizedCCM24FromTheorems normalizedSeedFromTheorems
    normalizedRemaindersFromTheorems normalizedRhExitFromTheorems
    normalizedBridgesFromTheorems normalizedFixedDataFromTheorems
    normalizedTraceDataFromTheorems normalizedScalarRemaindersFromTheorems
    normalizedScalarRhExitFromTheorems normalizedScalarBridgesFromTheorems
    normalizedScalarFixedDataFromTheorems
    normalizedScalarTraceScaleInputDataFromTheorems.noExtraBulk

noncomputable def normalizedScalarTraceDataFromTheorems :
    TraceFrontEndData
      normalizedScalarSourceObjectPackageFromTheorems
      (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedScalarPackage
        normalizedBaseFromTheorems normalizedCommonFromTheorems
        normalizedCCM24FromTheorems normalizedScalarSeedFromTheorems
        normalizedScalarRemaindersFromTheorems
        normalizedScalarRhExitFromTheorems
        normalizedScalarBridgesFromTheorems
        normalizedScalarFixedDataFromTheorems) :=
  TraceFrontEndData.traceFrontEndDataOfNormalizedScalarPackageFromOriginalCCM25
    normalizedBaseFromTheorems normalizedCommonFromTheorems
    normalizedCCM24FromTheorems normalizedSeedFromTheorems
    normalizedRemaindersFromTheorems normalizedRhExitFromTheorems
    normalizedBridgesFromTheorems normalizedFixedDataFromTheorems
    normalizedTraceDataFromTheorems normalizedScalarRemaindersFromTheorems
    normalizedScalarRhExitFromTheorems normalizedScalarBridgesFromTheorems
    normalizedScalarFixedDataFromTheorems
    normalizedScalarTestAndQuotientCompatibilityFromTheorems
    normalizedScalarFixedSSupportSquareTransportFromTheorems
    normalizedScalarFullTraceReadOffBridgeFromTheorems
    normalizedScalarRestrictedTraceReadOffBridgeFromTheorems
    normalizedScalarTraceScaleNoMissingBulkFromTheorems

theorem normalizedScalarTraceAmplitudeSquareFromTheorems :
    let scalarSourceTrace :=
      TraceFrontEndData.toSourceTraceReadOffDataOfNormalizedScalarPackage
        normalizedBaseFromTheorems normalizedCommonFromTheorems
        normalizedCCM24FromTheorems normalizedScalarSeedFromTheorems
        normalizedScalarRemaindersFromTheorems
        normalizedScalarRhExitFromTheorems
        normalizedScalarBridgesFromTheorems
        normalizedScalarFixedDataFromTheorems
        normalizedScalarTraceDataFromTheorems
    (Source.CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
        normalizedScalarSeedFromTheorems).traceAmplitude
        scalarSourceTrace.archimedeanTest ^ 2 =
      TraceFrontEndData.NormalizedRestrictedScalarNormalForm
        normalizedBaseFromTheorems normalizedCommonFromTheorems
        normalizedCCM24FromTheorems normalizedSeedFromTheorems
        normalizedRemaindersFromTheorems normalizedRhExitFromTheorems
        normalizedBridgesFromTheorems normalizedFixedDataFromTheorems
        normalizedTraceDataFromTheorems :=
  TraceFrontEndData.normalized_scalar_trace_front_trace_amplitude_square_eq_original_normal_form
    normalizedBaseFromTheorems normalizedCommonFromTheorems
    normalizedCCM24FromTheorems normalizedSeedFromTheorems
    normalizedRemaindersFromTheorems normalizedRhExitFromTheorems
    normalizedBridgesFromTheorems normalizedFixedDataFromTheorems
    normalizedTraceDataFromTheorems normalizedScalarRemaindersFromTheorems
    normalizedScalarRhExitFromTheorems normalizedScalarBridgesFromTheorems
    normalizedScalarFixedDataFromTheorems
    normalizedScalarTestAndQuotientCompatibilityFromTheorems
    normalizedScalarFixedSSupportSquareTransportFromTheorems
    normalizedScalarFullTraceReadOffBridgeFromTheorems
    normalizedScalarRestrictedTraceReadOffBridgeFromTheorems
    normalizedScalarTraceScaleNoMissingBulkFromTheorems

def normalizedTraceAmplitudeSquareScalarFromTheorems :
    TraceFrontEndData.NormalizedTraceAmplitudeSquareScalarContract
      normalizedBaseFromTheorems normalizedCommonFromTheorems
      normalizedCCM24FromTheorems normalizedSeedFromTheorems
      normalizedRemaindersFromTheorems normalizedRhExitFromTheorems
      normalizedBridgesFromTheorems normalizedFixedDataFromTheorems
      normalizedTraceDataFromTheorems :=
  normalizedScalarTraceScaleInputDataFromTheorems.amplitudeSquareScalar

def normalizedSupportSquareScalarNormalFormFromTheorems :
    TraceFrontEndData.NormalizedSupportSquareScalarNormalFormContract
      normalizedBaseFromTheorems normalizedCommonFromTheorems
      normalizedCCM24FromTheorems normalizedSeedFromTheorems
      normalizedRemaindersFromTheorems normalizedRhExitFromTheorems
      normalizedBridgesFromTheorems normalizedFixedDataFromTheorems
      normalizedTraceDataFromTheorems :=
  TraceFrontEndData.normalizedSupportSquareScalarNormalFormContractOfTraceAmplitudeSquare
    normalizedBaseFromTheorems normalizedCommonFromTheorems
    normalizedCCM24FromTheorems normalizedSeedFromTheorems
    normalizedRemaindersFromTheorems normalizedRhExitFromTheorems
    normalizedBridgesFromTheorems normalizedFixedDataFromTheorems
    normalizedTraceDataFromTheorems
    normalizedTraceAmplitudeSquareScalarFromTheorems

def normalizedComparisonFromTheorems :
    TraceFrontEndData.NormalizedSupportSquareQWLambdaSourceComparison
      normalizedBaseFromTheorems normalizedCommonFromTheorems
      normalizedCCM24FromTheorems normalizedSeedFromTheorems
      normalizedRemaindersFromTheorems normalizedRhExitFromTheorems
      normalizedBridgesFromTheorems normalizedFixedDataFromTheorems
      normalizedTraceDataFromTheorems :=
  TraceFrontEndData.normalizedSupportSquareQWLambdaSourceComparisonOfScalarNormalForms
    normalizedBaseFromTheorems normalizedCommonFromTheorems
    normalizedCCM24FromTheorems normalizedSeedFromTheorems
    normalizedRemaindersFromTheorems normalizedRhExitFromTheorems
    normalizedBridgesFromTheorems normalizedFixedDataFromTheorems
    normalizedTraceDataFromTheorems
    normalizedSupportSquareScalarNormalFormFromTheorems

theorem normalizedSourceArchimedeanSignBridgeFromTheorems :
    SourceArchimedeanSignBridge
      (RouteInputs.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems)
      normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceTraceTest
      (SourceBackedFixedSTest.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems
        normalizedFixedFrontEndFromTheorems) :=
  source_archimedean_sign_bridge_of_source_trace_read_off
    (SourceTraceReadOffData.ofExpandedSourcePackage
      normalizedSourceObjectPackageFromTheorems
      normalizedFixedFrontEndFromTheorems
      normalizedTraceFrontEndFromTheorems)

noncomputable def normalizedRouteCertificateFromTheorems :
    RouteCertificate
      (RouteInputs.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems) :=
  route_certificate_of_normalized_comparison_current_cutoff_binding
    normalizedBaseFromTheorems normalizedCommonFromTheorems
    normalizedCCM24FromTheorems normalizedSeedFromTheorems
    normalizedRemaindersFromTheorems normalizedRhExitFromTheorems
    normalizedBridgesFromTheorems normalizedFixedDataFromTheorems
    normalizedTraceDataFromTheorems normalizedComparisonFromTheorems
    normalizedNoExtraBulkContractFromTheorems
    normalizedRouteLedgersFromTheorems
    normalizedSignDefectClassificationFromTheorems
    normalizedRestrictedToFullCurrentCutoffBindingFromTheorems
    normalizedSourceArchimedeanSignBridgeFromTheorems

theorem unconditional_rh_contract_skeleton : _root_.RiemannHypothesis := by
  exact
    final_rh_of_normalized_comparison_current_cutoff_binding
      normalizedBaseFromTheorems normalizedCommonFromTheorems
      normalizedCCM24FromTheorems normalizedSeedFromTheorems
      normalizedRemaindersFromTheorems normalizedRhExitFromTheorems
      normalizedBridgesFromTheorems normalizedFixedDataFromTheorems
      normalizedTraceDataFromTheorems normalizedComparisonFromTheorems
      normalizedNoExtraBulkContractFromTheorems
      normalizedRouteLedgersFromTheorems
      normalizedSignDefectClassificationFromTheorems
      normalizedRestrictedToFullCurrentCutoffBindingFromTheorems
      normalizedSourceArchimedeanSignBridgeFromTheorems

end UnconditionalSkeleton
end Dev
end ConnesWeilRH
