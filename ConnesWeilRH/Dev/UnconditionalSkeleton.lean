/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Route.RouteTheorem
import ConnesWeilRH.Source.S2B1TraceScale

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

structure RouteLedgerClearingInputData where
  ledgers : RouteLedgers
  cleared : LedgersCleared ledgers

structure RestrictedToFullThresholdInputData
    (pkg : Source.SourceObject.SourceObjectPackage)
    (fixed : SourceBackedFixedSTest (RouteInputs.ofExpandedSourcePackage pkg))
    (lambda : ℝ)
    (convolutionSquare : TestFunction) where
  threshold :
    RestrictedToFullQWLargeLambdaThreshold
      (RouteInputs.ofExpandedSourcePackage pkg)
      fixed
      convolutionSquare
  currentAboveThreshold :
    threshold.lambda0 ≤ lambda

/-
Normalized contract-backed lane.

This is the stricter top-down target for the current Lean work.  Unlike the
generic skeleton above, it follows the normalized route endpoint whose
trace-scale ledger is backed by a named no-extra-bulk contract rather than the
older compatibility path that used `True`.
-/

noncomputable section NormalizedContractBackedLane

def normalizedCoreCCM24SemilocalSymbolsFromTheorems :
    SemilocalModelSymbols := by
  sorry

theorem normalizedCoreCCM24CanonicalSemilocalModelFromTheorems :
    SemilocalModelSymbols.CanonicalSemilocalModelStatement
      normalizedCoreCCM24SemilocalSymbolsFromTheorems := by
  sorry

theorem normalizedCoreCCM24SupportTransportFromTheorems :
    SemilocalModelSymbols.SupportTransportStatement
      normalizedCoreCCM24SemilocalSymbolsFromTheorems := by
  sorry

theorem normalizedCoreCCM24BoundedComparisonFromTheorems :
    SemilocalModelSymbols.BoundedComparisonStatement
      normalizedCoreCCM24SemilocalSymbolsFromTheorems := by
  sorry

theorem normalizedCoreCCM24SoninComparisonFromTheorems :
    SemilocalModelSymbols.SoninComparisonStatement
      normalizedCoreCCM24SemilocalSymbolsFromTheorems := by
  sorry

def normalizedCoreCCM24SourceModelFromTheorems :
    Source.CCM24SourceModel where
  semilocalSymbols := normalizedCoreCCM24SemilocalSymbolsFromTheorems
  canonicalSemilocalModel :=
    normalizedCoreCCM24CanonicalSemilocalModelFromTheorems
  supportTransport := normalizedCoreCCM24SupportTransportFromTheorems
  boundedComparison := normalizedCoreCCM24BoundedComparisonFromTheorems
  soninComparison := normalizedCoreCCM24SoninComparisonFromTheorems

def normalizedCoreCCM25WeilFormSymbolsFromTheorems :
    WeilFormSymbols := by
  sorry

theorem normalizedCoreCCM25QWDefinitionFromTheorems :
    WeilFormSymbols.QWDefinitionStatement
      normalizedCoreCCM25WeilFormSymbolsFromTheorems := by
  sorry

theorem normalizedCoreCCM25PsiSignFromTheorems :
    WeilFormSymbols.PsiSignStatement
      normalizedCoreCCM25WeilFormSymbolsFromTheorems := by
  sorry

theorem normalizedCoreCCM25QWLambdaFormulaFromTheorems :
    WeilFormSymbols.QWLambdaFormulaStatement
      normalizedCoreCCM25WeilFormSymbolsFromTheorems := by
  sorry

theorem normalizedCoreCCM25FinitePrimeNormalizationFromTheorems :
    WeilFormSymbols.FinitePrimeNormalizationStatement
      normalizedCoreCCM25WeilFormSymbolsFromTheorems := by
  sorry

theorem normalizedCoreCCM25PoleNormalizationFromTheorems :
    WeilFormSymbols.PoleNormalizationStatement
      normalizedCoreCCM25WeilFormSymbolsFromTheorems := by
  sorry

def normalizedCoreCCM25SourceModelFromTheorems :
    Source.CCM25SourceModel where
  qw := normalizedCoreCCM25WeilFormSymbolsFromTheorems.qw
  convolutionStar := normalizedCoreCCM25WeilFormSymbolsFromTheorems.convolutionStar
  psi := normalizedCoreCCM25WeilFormSymbolsFromTheorems.psi
  qwLambda := normalizedCoreCCM25WeilFormSymbolsFromTheorems.qwLambda
  globalPrimeIndexSet :=
    normalizedCoreCCM25WeilFormSymbolsFromTheorems.globalPrimeIndexSet
  restrictedPrimeIndexSet :=
    normalizedCoreCCM25WeilFormSymbolsFromTheorems.restrictedPrimeIndexSet
  finitePrimeAtomVisible :=
    normalizedCoreCCM25WeilFormSymbolsFromTheorems.finitePrimeAtomVisible
  finitePrimeTerm :=
    normalizedCoreCCM25WeilFormSymbolsFromTheorems.finitePrimeTerm
  archimedeanTerm :=
    normalizedCoreCCM25WeilFormSymbolsFromTheorems.archimedeanTerm
  poleFunctional :=
    normalizedCoreCCM25WeilFormSymbolsFromTheorems.poleFunctional
  polePairing := normalizedCoreCCM25WeilFormSymbolsFromTheorems.polePairing
  primePowerPairing :=
    normalizedCoreCCM25WeilFormSymbolsFromTheorems.primePowerPairing
  vonMangoldtWeight :=
    normalizedCoreCCM25WeilFormSymbolsFromTheorems.vonMangoldtWeight
  qw_eq_psi_convolution :=
    normalizedCoreCCM25QWDefinitionFromTheorems
  psi_sign_formula := normalizedCoreCCM25PsiSignFromTheorems
  qw_lambda_formula := normalizedCoreCCM25QWLambdaFormulaFromTheorems
  global_prime_index_coverage := by
    intro f g
    exact
      (normalizedCoreCCM25FinitePrimeNormalizationFromTheorems
        f g).globalPrimeIndexCoverage
  restricted_prime_index_coverage := by
    intro f g lambda hlambda
    exact
      (normalizedCoreCCM25FinitePrimeNormalizationFromTheorems
        f g).restrictedPrimeIndexCoverage lambda hlambda
  finite_prime_term_normalization := by
    intro f g
    exact
      (normalizedCoreCCM25FinitePrimeNormalizationFromTheorems
        f g).finitePrimeTermNormalization
  pole_normalization := normalizedCoreCCM25PoleNormalizationFromTheorems

def normalizedCoreS2B1NormalizedSeedFromTheorems :
    Source.CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols := by
  sorry

def normalizedCoreCC20TraceModelFromTheorems :
    Source.CC20TraceModel :=
  Source.CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
    normalizedCoreS2B1NormalizedSeedFromTheorems

theorem normalizedCoreS2B1NormalizedSeedArchimedeanSymbolsEqFromTheorems :
    (Source.CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
      normalizedCoreS2B1NormalizedSeedFromTheorems).archimedeanSymbols =
      normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols := by
  rfl

theorem normalizedCoreCC20ArchimedeanTraceSquareFromTheorems :
    ArchimedeanTraceSymbols.TraceSquareStatement
      normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols :=
  Source.CC20Concrete.TraceScale.normalized_legal_square_trace_scale_to_cc20_trace_model_trace_square
    normalizedCoreS2B1NormalizedSeedFromTheorems

theorem normalizedCoreCC20TraceClassTemplateFromTheorems :
    ArchimedeanTraceSymbols.TraceClassTemplateStatement
      normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols :=
  Source.CC20Concrete.TraceScale.normalized_legal_square_trace_scale_to_cc20_trace_model_trace_class_template
    normalizedCoreS2B1NormalizedSeedFromTheorems

theorem normalizedCoreCC20OrdinaryTraceSupportSquareFromTheorems :
    ArchimedeanTraceSymbols.OrdinaryTraceSupportSquareStatement
      normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols :=
  Source.CC20Concrete.TraceScale.normalized_legal_square_trace_scale_to_cc20_trace_model_ordinary_trace_support_square
    normalizedCoreS2B1NormalizedSeedFromTheorems

theorem normalizedCoreCC20MellinHalfDensityConventionFromTheorems :
    ArchimedeanTraceSymbols.MellinHalfDensityConventionStatement
      normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols :=
  Source.CC20Concrete.TraceScale.normalized_legal_square_trace_scale_to_cc20_trace_model_mellin
    normalizedCoreS2B1NormalizedSeedFromTheorems

theorem normalizedCoreCC20SignsAndNormalizationsFromTheorems :
    ArchimedeanTraceSymbols.SignsAndNormalizationsStatement
      normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols :=
  Source.CC20Concrete.TraceScale.normalized_legal_square_trace_scale_to_cc20_trace_model_signs
    normalizedCoreS2B1NormalizedSeedFromTheorems

def normalizedCoreS2B1RemainderRowsOutsideNoBulkFromTheorems :
    Source.S2B1NormalizedCC20RemainderRowsOutsideNoBulk
      normalizedCoreS2B1NormalizedSeedFromTheorems := by
  sorry

def normalizedCoreS2B1TracePackageRemaindersFromTheorems :
    Source.CC20Concrete.TraceScale.CC20TracePackageRemainderData
      normalizedCoreS2B1NormalizedSeedFromTheorems := by
  sorry

def normalizedCoreS2B1ActualScalarIdentificationFromTheorems
    (lambda : ℝ) (_hlambda : 1 < lambda)
    (archimedeanTest :
      normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols.Test)
    (weilTest : TestFunction) :
    Source.NormalizedSeedQWLambdaScalarIdentification
      normalizedCoreS2B1NormalizedSeedFromTheorems
      normalizedCoreCCM25SourceModelFromTheorems.toWeilFormSymbols
      normalizedCoreS2B1TracePackageRemaindersFromTheorems
      lambda
      (cast
        (congrArg ArchimedeanTraceSymbols.Test
          normalizedCoreS2B1NormalizedSeedArchimedeanSymbolsEqFromTheorems.symm)
        archimedeanTest)
      weilTest := by
  sorry

theorem normalizedCoreS2B1CC20SupportSquareTraceReadOffFromTheorems
    (lambda : ℝ) (hlambda : 1 < lambda)
    (archimedeanTest :
      normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols.Test)
    (weilTest : TestFunction) :
    normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols.supportSquareTrace
        archimedeanTest =
      normalizedCoreCCM25SourceModelFromTheorems.toWeilFormSymbols.qwLambda
        lambda weilTest weilTest := by
  let readOff :=
    Source.normalizedSeedSupportSquareQWLambdaReadOffOfQWLambdaScalarIdentification
      normalizedCoreS2B1NormalizedSeedFromTheorems
      normalizedCoreCCM25SourceModelFromTheorems.toWeilFormSymbols
      normalizedCoreS2B1TracePackageRemaindersFromTheorems
      lambda
      (cast
        (congrArg ArchimedeanTraceSymbols.Test
          normalizedCoreS2B1NormalizedSeedArchimedeanSymbolsEqFromTheorems.symm)
        archimedeanTest)
      weilTest
      (normalizedCoreS2B1ActualScalarIdentificationFromTheorems
        lambda hlambda archimedeanTest weilTest)
  exact
    (Source.S2B1FixedTupleSupportSquareQWLambdaReadOffSourceData.transportArchimedean
      normalizedCoreS2B1NormalizedSeedArchimedeanSymbolsEqFromTheorems
      archimedeanTest readOff).toRow.supportSquareMainTermEqualsQWLambda

def normalizedCoreS2B1SupportSquareSourceRestrictedTraceScalarFromTheorems
    (lambda : ℝ) (hlambda : 1 < lambda)
    (archimedeanTest :
      normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols.Test)
    (weilTest : TestFunction) : ℝ :=
  normalizedCoreCCM25SourceModelFromTheorems.toWeilFormSymbols.qwLambda
    lambda weilTest weilTest

theorem normalizedCoreS2B1CCM25QWLambdaSourceReadOffFromTheorems
    (lambda : ℝ) (hlambda : 1 < lambda)
    (archimedeanTest :
      normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols.Test)
    (weilTest : TestFunction) :
    normalizedCoreS2B1SupportSquareSourceRestrictedTraceScalarFromTheorems
        lambda hlambda archimedeanTest weilTest =
      normalizedCoreCCM25SourceModelFromTheorems.toWeilFormSymbols.qwLambda
        lambda weilTest weilTest := by
  rfl

def normalizedCoreS2B1SupportSquareQWLambdaReadOffSourceDataFromTheorems
    (lambda : ℝ) (hlambda : 1 < lambda)
    (archimedeanTest :
      normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols.Test)
    (weilTest : TestFunction) :
    Source.S2B1FixedTupleSupportSquareQWLambdaReadOffSourceData
      normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols
      normalizedCoreCCM25SourceModelFromTheorems.toWeilFormSymbols
      lambda archimedeanTest weilTest where
  sourceRestrictedTraceScalar :=
    normalizedCoreS2B1SupportSquareSourceRestrictedTraceScalarFromTheorems
      lambda hlambda archimedeanTest weilTest
  cc20SupportSquareTraceReadOff :=
    normalizedCoreS2B1CC20SupportSquareTraceReadOffFromTheorems
      lambda hlambda archimedeanTest weilTest
  ccm25QWLambdaSourceReadOff :=
    normalizedCoreS2B1CCM25QWLambdaSourceReadOffFromTheorems
      lambda hlambda archimedeanTest weilTest

def normalizedCoreS2B1SupportSquareQWLambdaReadOffConstructorInputFromTheorems
    (lambda : ℝ) (hlambda : 1 < lambda)
    (archimedeanTest :
      normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols.Test)
    (weilTest : TestFunction) :
    Source.S2B1FixedTupleSupportSquareQWLambdaReadOffConstructorInput
      normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols
      normalizedCoreCCM25SourceModelFromTheorems.toWeilFormSymbols
      lambda archimedeanTest weilTest :=
  (normalizedCoreS2B1SupportSquareQWLambdaReadOffSourceDataFromTheorems
    lambda hlambda archimedeanTest weilTest).toConstructorInput

theorem normalizedCoreS2B1SupportSquareMainTermEqualsQWLambdaAtHoldsFromTheorems :
    ∀ lambda : ℝ, ∀ _hlambda : 1 < lambda,
      ∀ archimedeanTest :
        normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols.Test,
      ∀ weilTest : TestFunction,
        normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols.supportSquareTrace
            archimedeanTest =
          normalizedCoreCCM25SourceModelFromTheorems.toWeilFormSymbols.qwLambda
            lambda weilTest weilTest := by
  intro lambda hlambda archimedeanTest weilTest
  exact
    ((normalizedCoreS2B1SupportSquareQWLambdaReadOffConstructorInputFromTheorems
      lambda hlambda archimedeanTest weilTest).toConstructorInput).supportSquareMainTermEqualsQWLambdaAtHolds

def normalizedCoreS2B1SupportSquareQWLambdaRowInputFromTheorems
    (lambda : ℝ) (hlambda : 1 < lambda)
    (archimedeanTest :
      normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols.Test)
    (weilTest : TestFunction) :
    Source.S2B1FixedTupleSupportSquareQWLambdaConstructorInput
      normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols
      normalizedCoreCCM25SourceModelFromTheorems.toWeilFormSymbols
      lambda archimedeanTest weilTest where
  supportSquareMainTermEqualsQWLambdaAtHolds :=
    ((normalizedCoreS2B1SupportSquareQWLambdaReadOffConstructorInputFromTheorems
      lambda hlambda archimedeanTest weilTest).toConstructorInput).supportSquareMainTermEqualsQWLambdaAtHolds

def normalizedCoreS2B1SupportSquareQWLambdaRowFromTheorems :
    ∀ lambda : ℝ, ∀ _hlambda : 1 < lambda,
      ∀ archimedeanTest :
        normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols.Test,
      ∀ weilTest : TestFunction,
        Source.S2B1FixedTupleSupportSquareQWLambdaRow
          normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols
          normalizedCoreCCM25SourceModelFromTheorems.toWeilFormSymbols
          lambda archimedeanTest weilTest :=
  fun lambda hlambda archimedeanTest weilTest =>
    (normalizedCoreS2B1SupportSquareQWLambdaRowInputFromTheorems
      lambda hlambda archimedeanTest weilTest).toRow

structure NormalizedCoreS2B1RemainingConstructorInputs where
  rankZeroModeConstructorInput :
    ∀ lambda : ℝ, ∀ _hlambda : 1 < lambda,
      ∀ archimedeanTest :
        normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols.Test,
      ∀ weilTest : TestFunction,
        Source.S2B1FixedTupleRankZeroModeConstructorInput
          normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols
          normalizedCoreCCM25SourceModelFromTheorems.toWeilFormSymbols
          lambda archimedeanTest weilTest
  noStripRankPoleConstructorInput :
    ∀ lambda : ℝ, ∀ _hlambda : 1 < lambda,
      ∀ archimedeanTest :
        normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols.Test,
      ∀ weilTest : TestFunction,
        Source.S2B1FixedTupleNoStripRankPoleConstructorInput
          normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols
          normalizedCoreCCM25SourceModelFromTheorems.toWeilFormSymbols
          lambda archimedeanTest weilTest
  endpointStripCdefConstructorInput :
    ∀ lambda : ℝ, ∀ _hlambda : 1 < lambda,
      ∀ archimedeanTest :
        normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols.Test,
      ∀ weilTest : TestFunction,
        Source.S2B1FixedTupleEndpointStripCdefConstructorInput
          normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols
          normalizedCoreCCM25SourceModelFromTheorems.toWeilFormSymbols
          lambda archimedeanTest weilTest
  noExtraBulkConstructorInput :
    ∀ lambda : ℝ, ∀ _hlambda : 1 < lambda,
      ∀ archimedeanTest :
        normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols.Test,
      ∀ weilTest : TestFunction,
        Source.S2B1FixedTupleNoExtraBulkConstructorInput
          normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols
          normalizedCoreCCM25SourceModelFromTheorems.toWeilFormSymbols
          lambda archimedeanTest weilTest
  finitePartSourceNormalFormData :
    ∀ lambda : ℝ, ∀ _hlambda : 1 < lambda,
      ∀ archimedeanTest :
        normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols.Test,
      ∀ weilTest : TestFunction,
        Source.S2B1FinitePartSourceNormalFormData
          normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols
          normalizedCoreCCM25SourceModelFromTheorems.toWeilFormSymbols
          lambda archimedeanTest weilTest

def normalizedCoreS2B1RemainingConstructorInputsFromTheorems :
    NormalizedCoreS2B1RemainingConstructorInputs := by
  sorry

def normalizedCoreS2B1RankZeroModeConstructorInputFromTheorems
    (lambda : ℝ) (_hlambda : 1 < lambda)
    (archimedeanTest :
      normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols.Test)
    (weilTest : TestFunction) :
    Source.S2B1FixedTupleRankZeroModeConstructorInput
      normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols
      normalizedCoreCCM25SourceModelFromTheorems.toWeilFormSymbols
      lambda archimedeanTest weilTest :=
  normalizedCoreS2B1RemainingConstructorInputsFromTheorems.rankZeroModeConstructorInput
    lambda _hlambda archimedeanTest weilTest

def normalizedCoreS2B1NoStripRankPoleConstructorInputFromTheorems
    (lambda : ℝ) (_hlambda : 1 < lambda)
    (archimedeanTest :
      normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols.Test)
    (weilTest : TestFunction) :
    Source.S2B1FixedTupleNoStripRankPoleConstructorInput
      normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols
      normalizedCoreCCM25SourceModelFromTheorems.toWeilFormSymbols
      lambda archimedeanTest weilTest :=
  normalizedCoreS2B1RemainingConstructorInputsFromTheorems.noStripRankPoleConstructorInput
    lambda _hlambda archimedeanTest weilTest

def normalizedCoreS2B1EndpointStripCdefConstructorInputFromTheorems
    (lambda : ℝ) (_hlambda : 1 < lambda)
    (archimedeanTest :
      normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols.Test)
    (weilTest : TestFunction) :
    Source.S2B1FixedTupleEndpointStripCdefConstructorInput
      normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols
      normalizedCoreCCM25SourceModelFromTheorems.toWeilFormSymbols
      lambda archimedeanTest weilTest :=
  normalizedCoreS2B1RemainingConstructorInputsFromTheorems.endpointStripCdefConstructorInput
    lambda _hlambda archimedeanTest weilTest

def normalizedCoreS2B1NoExtraBulkConstructorInputFromTheorems
    (lambda : ℝ) (_hlambda : 1 < lambda)
    (archimedeanTest :
      normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols.Test)
    (weilTest : TestFunction) :
    Source.S2B1FixedTupleNoExtraBulkConstructorInput
      normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols
      normalizedCoreCCM25SourceModelFromTheorems.toWeilFormSymbols
      lambda archimedeanTest weilTest :=
  normalizedCoreS2B1RemainingConstructorInputsFromTheorems.noExtraBulkConstructorInput
    lambda _hlambda archimedeanTest weilTest

def normalizedCoreS2B1FinitePartSourceNormalFormDataFromTheorems
    (lambda : ℝ) (_hlambda : 1 < lambda)
    (archimedeanTest :
      normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols.Test)
    (weilTest : TestFunction) :
    Source.S2B1FinitePartSourceNormalFormData
      normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols
      normalizedCoreCCM25SourceModelFromTheorems.toWeilFormSymbols
      lambda archimedeanTest weilTest :=
  normalizedCoreS2B1RemainingConstructorInputsFromTheorems.finitePartSourceNormalFormData
    lambda _hlambda archimedeanTest weilTest

def normalizedCoreS2B1FinitePartSourceScalarDataFromTheorems
    (lambda : ℝ) (hlambda : 1 < lambda)
    (archimedeanTest :
      normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols.Test)
    (weilTest : TestFunction) :
    Source.S2B1FinitePartSourceScalarData
      normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols
      normalizedCoreCCM25SourceModelFromTheorems.toWeilFormSymbols
      lambda archimedeanTest weilTest :=
  (normalizedCoreS2B1FinitePartSourceNormalFormDataFromTheorems
    lambda hlambda archimedeanTest weilTest).sourceScalars

def normalizedCoreS2B1FinitePartScalarInterfaceFromTheorems
    (lambda : ℝ) (hlambda : 1 < lambda)
    (archimedeanTest :
      normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols.Test)
    (weilTest : TestFunction) :
    Source.S2B1FinitePartScalarInterface
      normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols
      normalizedCoreCCM25SourceModelFromTheorems.toWeilFormSymbols
      lambda archimedeanTest weilTest :=
  (normalizedCoreS2B1FinitePartSourceScalarDataFromTheorems
    lambda hlambda archimedeanTest weilTest).toScalarInterface

theorem normalizedCoreS2B1FinitePartNormalizationFixedHoldsFromTheorems
    (lambda : ℝ) (hlambda : 1 < lambda)
    (archimedeanTest :
      normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols.Test)
    (weilTest : TestFunction) :
    Source.S2B1FinitePartScalarInterface.finitePartNormalizationFixedStatement
      (normalizedCoreS2B1FinitePartScalarInterfaceFromTheorems
        lambda hlambda archimedeanTest weilTest) := by
  exact
    (normalizedCoreS2B1FinitePartSourceNormalFormDataFromTheorems
      lambda hlambda archimedeanTest weilTest).finitePartNormalizationFixedHolds

theorem normalizedCoreS2B1NoSubtractedFinitePartTermHoldsFromTheorems
    (lambda : ℝ) (hlambda : 1 < lambda)
    (archimedeanTest :
      normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols.Test)
    (weilTest : TestFunction) :
    Source.S2B1FinitePartScalarInterface.noSubtractedFinitePartTermStatement
      (normalizedCoreS2B1FinitePartScalarInterfaceFromTheorems
        lambda hlambda archimedeanTest weilTest) := by
  exact
    (normalizedCoreS2B1FinitePartSourceNormalFormDataFromTheorems
      lambda hlambda archimedeanTest weilTest).noSubtractedFinitePartTermHolds

def normalizedCoreS2B1FinitePartNormalFormRowsFromTheorems
    (lambda : ℝ) (hlambda : 1 < lambda)
    (archimedeanTest :
      normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols.Test)
    (weilTest : TestFunction) :
    Source.S2B1FinitePartNormalFormRows
      normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols
      normalizedCoreCCM25SourceModelFromTheorems.toWeilFormSymbols
      lambda archimedeanTest weilTest :=
  (normalizedCoreS2B1FinitePartSourceNormalFormDataFromTheorems
    lambda hlambda archimedeanTest weilTest).toRows

def normalizedCoreS2B1NoHiddenFinitePartSubtractionRowsFromTheorems
    (lambda : ℝ) (hlambda : 1 < lambda)
    (archimedeanTest :
      normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols.Test)
    (weilTest : TestFunction) :
    Source.S2B1NoHiddenFinitePartSubtractionConstructorRows
      normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols
      normalizedCoreCCM25SourceModelFromTheorems.toWeilFormSymbols
      lambda archimedeanTest weilTest :=
  (normalizedCoreS2B1FinitePartNormalFormRowsFromTheorems
    lambda hlambda archimedeanTest weilTest).toNoHiddenFinitePartRows

def normalizedCoreS2B1NoHiddenFinitePartSubtractionConstructorInputFromTheorems
    (lambda : ℝ) (hlambda : 1 < lambda)
    (archimedeanTest :
      normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols.Test)
    (weilTest : TestFunction) :
    Source.S2B1FixedTupleNoHiddenFinitePartSubtractionConstructorInput
      normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols
      normalizedCoreCCM25SourceModelFromTheorems.toWeilFormSymbols
      lambda archimedeanTest weilTest :=
  (normalizedCoreS2B1NoHiddenFinitePartSubtractionRowsFromTheorems
    lambda hlambda archimedeanTest weilTest).toConstructorInput

def normalizedCoreS2B1RemainingConstructorInputPackageFromTheorems :
    ∀ lambda : ℝ, ∀ _hlambda : 1 < lambda,
      ∀ archimedeanTest :
        normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols.Test,
      ∀ weilTest : TestFunction,
        Source.S2B1FixedTupleRemainingConstructorInputPackage
          normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols
          normalizedCoreCCM25SourceModelFromTheorems.toWeilFormSymbols
          lambda archimedeanTest weilTest :=
  fun lambda hlambda archimedeanTest weilTest =>
    Source.S2B1FixedTupleRemainingConstructorInputPackage.ofFinitePartNormalForm
      (normalizedCoreS2B1RankZeroModeConstructorInputFromTheorems
        lambda hlambda archimedeanTest weilTest)
      (normalizedCoreS2B1NoStripRankPoleConstructorInputFromTheorems
        lambda hlambda archimedeanTest weilTest)
      (normalizedCoreS2B1EndpointStripCdefConstructorInputFromTheorems
        lambda hlambda archimedeanTest weilTest)
      (normalizedCoreS2B1NoExtraBulkConstructorInputFromTheorems
        lambda hlambda archimedeanTest weilTest)
      (normalizedCoreS2B1FinitePartSourceNormalFormDataFromTheorems
        lambda hlambda archimedeanTest weilTest)

def normalizedCoreS2B1TraceScaleTheoremDataInputFromTheorems :
    Source.S2B1TraceScaleTheoremData
      normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols
      normalizedCoreCCM25SourceModelFromTheorems.toWeilFormSymbols :=
  Source.S2B1TraceScaleTheoremData.ofSupportSquareAndRemainingConstructorInputs
    normalizedCoreS2B1SupportSquareQWLambdaReadOffSourceDataFromTheorems
    normalizedCoreS2B1RemainingConstructorInputPackageFromTheorems

def normalizedCoreS2B1RankZeroModeRowFromTheorems :
    ∀ lambda : ℝ, ∀ _hlambda : 1 < lambda,
      ∀ archimedeanTest :
        normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols.Test,
      ∀ weilTest : TestFunction,
        Source.S2B1FixedTupleRankZeroModeRow
          normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols
          normalizedCoreCCM25SourceModelFromTheorems.toWeilFormSymbols
          lambda archimedeanTest weilTest :=
  fun lambda _hlambda archimedeanTest weilTest =>
    (normalizedCoreS2B1RankZeroModeConstructorInputFromTheorems
      lambda _hlambda archimedeanTest weilTest).toRow

def normalizedCoreS2B1NoStripRankPoleRowFromTheorems :
    ∀ lambda : ℝ, ∀ _hlambda : 1 < lambda,
      ∀ archimedeanTest :
        normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols.Test,
      ∀ weilTest : TestFunction,
        Source.S2B1FixedTupleNoStripRankPoleRow
          normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols
          normalizedCoreCCM25SourceModelFromTheorems.toWeilFormSymbols
          lambda archimedeanTest weilTest :=
  fun lambda _hlambda archimedeanTest weilTest =>
    (normalizedCoreS2B1NoStripRankPoleConstructorInputFromTheorems
      lambda _hlambda archimedeanTest weilTest).toRow

def normalizedCoreS2B1EndpointStripCdefRowFromTheorems :
    ∀ lambda : ℝ, ∀ _hlambda : 1 < lambda,
      ∀ archimedeanTest :
        normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols.Test,
      ∀ weilTest : TestFunction,
        Source.S2B1FixedTupleEndpointStripCdefRow
          normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols
          normalizedCoreCCM25SourceModelFromTheorems.toWeilFormSymbols
          lambda archimedeanTest weilTest :=
  fun lambda _hlambda archimedeanTest weilTest =>
    (normalizedCoreS2B1EndpointStripCdefConstructorInputFromTheorems
      lambda _hlambda archimedeanTest weilTest).toRow

def normalizedCoreS2B1NoExtraBulkRowFromTheorems :
    ∀ lambda : ℝ, ∀ _hlambda : 1 < lambda,
      ∀ archimedeanTest :
        normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols.Test,
      ∀ weilTest : TestFunction,
        Source.S2B1FixedTupleNoExtraBulkRow
          normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols
          normalizedCoreCCM25SourceModelFromTheorems.toWeilFormSymbols
          lambda archimedeanTest weilTest :=
  fun lambda _hlambda archimedeanTest weilTest =>
    (normalizedCoreS2B1NoExtraBulkConstructorInputFromTheorems
      lambda _hlambda archimedeanTest weilTest).toRow

def normalizedCoreS2B1NoHiddenFinitePartSubtractionRowFromTheorems :
    ∀ lambda : ℝ, ∀ _hlambda : 1 < lambda,
      ∀ archimedeanTest :
        normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols.Test,
      ∀ weilTest : TestFunction,
        Source.S2B1FixedTupleNoHiddenFinitePartSubtractionRow
          normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols
          normalizedCoreCCM25SourceModelFromTheorems.toWeilFormSymbols
          lambda archimedeanTest weilTest :=
  fun lambda _hlambda archimedeanTest weilTest =>
    (normalizedCoreS2B1NoHiddenFinitePartSubtractionConstructorInputFromTheorems
      lambda _hlambda archimedeanTest weilTest).toRow

def normalizedCoreS2B1TraceScaleTheoremDataFromTheorems :
    Source.S2B1TraceScaleTheoremData
      normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols
      normalizedCoreCCM25SourceModelFromTheorems.toWeilFormSymbols :=
  normalizedCoreS2B1TraceScaleTheoremDataInputFromTheorems

def normalizedCoreS2B1TraceScaleAnalyticExclusionConstructorInputFromTheorems :
    Source.S2B1TraceScaleAnalyticExclusionConstructorInput
      normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols
      normalizedCoreCCM25SourceModelFromTheorems.toWeilFormSymbols :=
  (Source.S2B1TraceScaleTheoremData.toConstructorInput
    normalizedCoreS2B1TraceScaleTheoremDataFromTheorems)

def normalizedCoreS2B1TraceScaleAnalyticExclusionsFromTheorems :
    Source.S2B1TraceScaleAnalyticExclusionPackage
      normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols
      normalizedCoreCCM25SourceModelFromTheorems.toWeilFormSymbols :=
  normalizedCoreS2B1TraceScaleAnalyticExclusionConstructorInputFromTheorems.toPackage

noncomputable def normalizedCoreRHDefinitionBridgeFromTheorems :
    Source.RHDefinitionBridge :=
  Source.RHDefinitionBridge.standard

noncomputable def normalizedCoreCC20RHExitObjectPackageFromTheorems :
    Source.CC20RHExitObjectPackage
      normalizedCoreRHDefinitionBridgeFromTheorems := by
  sorry

def normalizedSourceObjectCoreBasePackageConstructorInputFromTheorems :
    Source.SourceObjectTheoremBaseConstructorInput where
  ccm24Model := normalizedCoreCCM24SourceModelFromTheorems
  ccm25Model := normalizedCoreCCM25SourceModelFromTheorems
  cc20TraceModel := normalizedCoreCC20TraceModelFromTheorems
  s2b1NormalizedSeed := normalizedCoreS2B1NormalizedSeedFromTheorems
  s2b1NormalizedSeedArchimedeanSymbolsEq :=
    normalizedCoreS2B1NormalizedSeedArchimedeanSymbolsEqFromTheorems
  s2b1RemainderRowsOutsideNoBulk :=
    normalizedCoreS2B1RemainderRowsOutsideNoBulkFromTheorems
  s2b1TraceScaleAnalyticExclusionConstructorInput :=
    normalizedCoreS2B1TraceScaleAnalyticExclusionConstructorInputFromTheorems
  rhDefinitionBridge := normalizedCoreRHDefinitionBridgeFromTheorems
  cc20RHExitObjectPackage :=
    normalizedCoreCC20RHExitObjectPackageFromTheorems

def normalizedSourceObjectCoreBasePackageFromTheorems :
    Source.SourceObjectTheoremBasePackage :=
  normalizedSourceObjectCoreBasePackageConstructorInputFromTheorems.toPackage

def normalizedSourceObjectCoreFinitePrimeExactFromTheorems :
    Source.CCM25Concrete.FinitePrimeSourceData.CommonFinitePrimeArithmeticSourceData
      normalizedSourceObjectCoreBasePackageFromTheorems.ccm25Model.toWeilFormSymbols := by
  sorry

def normalizedSourceObjectCoreTheoremBaseConstructorInputFromTheorems :
    Source.NormalizedSourceObjectCoreTheoremBaseConstructorInput where
  base := normalizedSourceObjectCoreBasePackageFromTheorems
  finitePrimeExact := normalizedSourceObjectCoreFinitePrimeExactFromTheorems

def normalizedSourceObjectCoreTheoremBaseDataFromTheorems :
    Source.NormalizedSourceObjectCoreTheoremBaseData :=
  normalizedSourceObjectCoreTheoremBaseConstructorInputFromTheorems.toCoreData

def normalizedSourceObjectCCM24ObjectFromTheorems :
    Source.SourceObject.CCM24SemilocalObjectPackage := by
  sorry

def normalizedSourceObjectRHExitObjectFromTheorems :
    Source.SourceObject.CC20RHExitObjectPackage := by
  sorry

theorem normalizedSourceObjectRHExitBridgeEqFromTheorems :
    normalizedSourceObjectRHExitObjectFromTheorems.rhDefinitionBridge =
      normalizedSourceObjectCoreTheoremBaseDataFromTheorems.base.rhDefinitionBridge := by
  sorry

def normalizedSourceObjectObjectConstructorInputFromTheorems :
    Source.NormalizedSourceObjectObjectConstructorInput
      normalizedSourceObjectCoreTheoremBaseDataFromTheorems where
  ccm24Object := normalizedSourceObjectCCM24ObjectFromTheorems
  sourceObjectRHExit := normalizedSourceObjectRHExitObjectFromTheorems
  sourceObjectRHExitBridgeEq := normalizedSourceObjectRHExitBridgeEqFromTheorems

def normalizedSourceObjectObjectDataFromTheorems :
    Source.NormalizedSourceObjectObjectData
      normalizedSourceObjectCoreTheoremBaseDataFromTheorems :=
  normalizedSourceObjectObjectConstructorInputFromTheorems.toObjectData

structure NormalizedSourceObjectBridgeReadOffRowsInput where
  rows :
    Source.NormalizedSourceObjectBridgeReadOffConstructorInput
      normalizedSourceObjectCoreTheoremBaseDataFromTheorems
      normalizedSourceObjectObjectDataFromTheorems

def normalizedSourceObjectBridgeReadOffRowsInputFromTheorems :
    NormalizedSourceObjectBridgeReadOffRowsInput := by
  sorry

def normalizedSourceObjectCommonTestBridgeRowsProviderFromTheorems :
    ∀ commonTest :
      Source.SourceObject.CommonTestObject
        normalizedSourceObjectCoreTheoremBaseDataFromTheorems.base.ccm25Model.toWeilFormSymbols,
      ∀ cc20Trace : Source.SourceObject.CC20TraceObjectPackage,
      Source.NormalizedSourceObjectCommonTestBridgeRows
        normalizedSourceObjectCoreTheoremBaseDataFromTheorems.base commonTest
        normalizedSourceObjectObjectDataFromTheorems.ccm24Object
        cc20Trace :=
  normalizedSourceObjectBridgeReadOffRowsInputFromTheorems.rows.commonTestBridgeRows

def normalizedSourceTraceReadOffEqualityRowsProviderFromTheorems :
    ∀ (commonTest :
        Source.SourceObject.CommonTestObject
          normalizedSourceObjectCoreTheoremBaseDataFromTheorems.base.ccm25Model.toWeilFormSymbols)
      (cc20Trace : Source.SourceObject.CC20TraceObjectPackage)
      (lambda : ℝ),
      Source.NormalizedSourceTraceReadOffEqualityRows
        normalizedSourceObjectCoreTheoremBaseDataFromTheorems.base commonTest
        cc20Trace lambda :=
  normalizedSourceObjectBridgeReadOffRowsInputFromTheorems.rows.traceReadOffEqualityRows

def normalizedSourceObjectBridgeReadOffConstructorInputFromTheorems :
    Source.NormalizedSourceObjectBridgeReadOffConstructorInput
      normalizedSourceObjectCoreTheoremBaseDataFromTheorems
      normalizedSourceObjectObjectDataFromTheorems :=
  normalizedSourceObjectBridgeReadOffRowsInputFromTheorems.rows

def normalizedSourceObjectBridgeReadOffDataFromTheorems :
    Source.NormalizedSourceObjectBridgeReadOffData
      normalizedSourceObjectCoreTheoremBaseDataFromTheorems
      normalizedSourceObjectObjectDataFromTheorems :=
  normalizedSourceObjectBridgeReadOffConstructorInputFromTheorems.toBridgeReadOffData

def normalizedSourceObjectScalarRemainderRowsProviderFromTheorems :
    ∀ scalarSeed :
      Source.CC20Concrete.TraceScale.NormalizedScalarTraceScaleSymbols,
      Source.NormalizedScalarCC20RemainderRows scalarSeed := by
  sorry

def normalizedSourceObjectScalarFinitePartSourceNormalFormDataFromTheorems :
    ∀ scalarSeed :
      Source.CC20Concrete.TraceScale.NormalizedScalarTraceScaleSymbols,
      ∀ lambda : ℝ, ∀ _hlambda : 1 < lambda,
        ∀ archimedeanTest :
          (Source.CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
            (Source.CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
              scalarSeed)).archimedeanSymbols.Test,
        ∀ weilTest : TestFunction,
          Source.S2B1FinitePartSourceNormalFormData
            (Source.CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
              (Source.CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
                scalarSeed)).archimedeanSymbols
            normalizedSourceObjectCoreTheoremBaseDataFromTheorems.base.ccm25Model.toWeilFormSymbols
            lambda archimedeanTest weilTest := by
  sorry

def normalizedSourceObjectScalarCommonTestBridgeRowsProviderFromTheorems :
    ∀ (commonTest :
        Source.SourceObject.CommonTestObject
          normalizedSourceObjectCoreTheoremBaseDataFromTheorems.base.ccm25Model.toWeilFormSymbols)
      (scalarSeed :
        Source.CC20Concrete.TraceScale.NormalizedScalarTraceScaleSymbols),
      Source.NormalizedScalarCC20CommonTestBridgeRows
        normalizedSourceObjectCoreTheoremBaseDataFromTheorems.base commonTest
        scalarSeed
        (normalizedSourceObjectScalarRemainderRowsProviderFromTheorems
          scalarSeed) := by
  sorry

def normalizedSourceObjectScalarRowsConstructorInputFromTheorems :
    Source.NormalizedSourceObjectScalarRowsConstructorInput
      normalizedSourceObjectCoreTheoremBaseDataFromTheorems where
  scalarRemainderRows :=
    normalizedSourceObjectScalarRemainderRowsProviderFromTheorems
  scalarFinitePartSourceNormalFormData :=
    normalizedSourceObjectScalarFinitePartSourceNormalFormDataFromTheorems
  scalarCommonTestBridgeRows :=
    normalizedSourceObjectScalarCommonTestBridgeRowsProviderFromTheorems

def normalizedSourceObjectScalarRowsDataFromTheorems :
    Source.NormalizedSourceObjectScalarRowsData
      normalizedSourceObjectCoreTheoremBaseDataFromTheorems :=
  normalizedSourceObjectScalarRowsConstructorInputFromTheorems.toScalarRowsData

def normalizedSourceObjectRankLedgerKilledFromTheorems : Prop :=
  Source.S2B1NormalizedCC20RemainderRowsOutsideNoBulk.sourceRankPoleLedgerIdentification
    (Source.SourceObjectTheoremBasePackage.s2b1RemainderRowsOutsideNoBulk
      normalizedSourceObjectCoreTheoremBaseDataFromTheorems.base)

def normalizedSourceObjectPoleLedgerKilledFromTheorems : Prop :=
  Source.S2B1NormalizedCC20RemainderRowsOutsideNoBulk.sourceRankPoleLedgerIdentification
    (Source.SourceObjectTheoremBasePackage.s2b1RemainderRowsOutsideNoBulk
      normalizedSourceObjectCoreTheoremBaseDataFromTheorems.base)

def normalizedSourceObjectCdefExhaustsFromTheorems : Prop :=
  Source.S2B1NormalizedCC20RemainderRowsOutsideNoBulk.sourceEndpointStripRemainderCdefDomination
    (Source.SourceObjectTheoremBasePackage.s2b1RemainderRowsOutsideNoBulk
      normalizedSourceObjectCoreTheoremBaseDataFromTheorems.base)

theorem normalizedSourceObjectRankLedgerKilledHoldsFromTheorems :
    normalizedSourceObjectRankLedgerKilledFromTheorems :=
  Source.S2B1NormalizedCC20RemainderRowsOutsideNoBulk.sourceRankPoleLedgerIdentificationHolds
    (Source.SourceObjectTheoremBasePackage.s2b1RemainderRowsOutsideNoBulk
      normalizedSourceObjectCoreTheoremBaseDataFromTheorems.base)

theorem normalizedSourceObjectPoleLedgerKilledHoldsFromTheorems :
    normalizedSourceObjectPoleLedgerKilledFromTheorems :=
  Source.S2B1NormalizedCC20RemainderRowsOutsideNoBulk.sourceRankPoleLedgerIdentificationHolds
    (Source.SourceObjectTheoremBasePackage.s2b1RemainderRowsOutsideNoBulk
      normalizedSourceObjectCoreTheoremBaseDataFromTheorems.base)

theorem normalizedSourceObjectCdefExhaustsHoldsFromTheorems :
    normalizedSourceObjectCdefExhaustsFromTheorems :=
  Source.S2B1NormalizedCC20RemainderRowsOutsideNoBulk.sourceEndpointStripRemainderCdefDominationHolds
    (Source.SourceObjectTheoremBasePackage.s2b1RemainderRowsOutsideNoBulk
      normalizedSourceObjectCoreTheoremBaseDataFromTheorems.base)

def normalizedSourceObjectLedgerRowsConstructorInputFromTheorems :
    Source.NormalizedSourceObjectLedgerRowsConstructorInput where
  rankKilled := normalizedSourceObjectRankLedgerKilledFromTheorems
  poleKilled := normalizedSourceObjectPoleLedgerKilledFromTheorems
  cdefExhausts := normalizedSourceObjectCdefExhaustsFromTheorems
  rankKilledHolds := normalizedSourceObjectRankLedgerKilledHoldsFromTheorems
  poleKilledHolds := normalizedSourceObjectPoleLedgerKilledHoldsFromTheorems
  cdefExhaustsHolds := normalizedSourceObjectCdefExhaustsHoldsFromTheorems

def normalizedSourceObjectLedgerRowsDataFromTheorems :
    Source.NormalizedSourceObjectLedgerRowsData :=
  normalizedSourceObjectLedgerRowsConstructorInputFromTheorems.toLedgerRowsData

def normalizedSourceObjectTheoremBaseConstructorInputFromTheorems :
    Source.NormalizedSourceObjectTheoremBaseConstructorInput where
  core := normalizedSourceObjectCoreTheoremBaseDataFromTheorems
  objects := normalizedSourceObjectObjectDataFromTheorems
  bridgeReadOff := normalizedSourceObjectBridgeReadOffDataFromTheorems
  scalarRows := normalizedSourceObjectScalarRowsDataFromTheorems
  ledgerRows := normalizedSourceObjectLedgerRowsDataFromTheorems

def normalizedSourceObjectTheoremBaseInputFromTheorems :
    Source.NormalizedSourceObjectTheoremBaseInput :=
  normalizedSourceObjectTheoremBaseConstructorInputFromTheorems.toInput

def normalizedBaseFromTheorems :
    Source.SourceObjectTheoremBasePackage :=
  normalizedSourceObjectTheoremBaseInputFromTheorems.base

def normalizedGlobalQWPsiRowsFromTheorems :
    Source.CCM25Concrete.Rows.ConcreteGlobalQWPsiRows
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols where
  qwDefinition :=
    Source.ccm25_source_qw_definition normalizedBaseFromTheorems.ccm25Model
  psiSign :=
    Source.ccm25_source_psi_sign normalizedBaseFromTheorems.ccm25Model

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
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols where
  restrictedRows :=
    { qwLambdaFormula :=
        Source.ccm25_source_qw_lambda_formula normalizedBaseFromTheorems.ccm25Model }
  poleRows :=
    { poleNormalization :=
        Source.ccm25_source_pole_normalization normalizedBaseFromTheorems.ccm25Model }

theorem normalizedQWLambdaFormulaFromTheorems :
    WeilFormSymbols.QWLambdaFormulaStatement
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols :=
  normalizedRestrictedQWLambdaPoleRowsFromTheorems.restrictedRows.qwLambdaFormula

def normalizedConcreteRestrictedQWLambdaRowsFromTheorems :
    Source.CCM25Concrete.Rows.ConcreteRestrictedQWLambdaRows
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols :=
  normalizedRestrictedQWLambdaPoleRowsFromTheorems.restrictedRows

theorem normalizedPoleNormalizationFromTheorems :
    WeilFormSymbols.PoleNormalizationStatement
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols :=
  normalizedRestrictedQWLambdaPoleRowsFromTheorems.poleRows.poleNormalization

def normalizedConcretePoleNormalizationRowsFromTheorems :
    Source.CCM25Concrete.Rows.ConcretePoleNormalizationRows
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols :=
  normalizedRestrictedQWLambdaPoleRowsFromTheorems.poleRows

structure NormalizedConcreteCommonInputData where
  commonTestFunction : TestFunction
  finitePrimeArithmeticCertificates :
    Source.CCM25Concrete.FinitePrimeInterface.FixedLambdaArithmeticSourceTestCertificatesForAllTests
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols
  commonPairSourceTest :
    (finitePrimeArithmeticCertificates commonTestFunction commonTestFunction).sourceTest =
      (Source.CCM25Concrete.CommonSourceTest.concreteCommonSourceTest
        normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols
        commonTestFunction).toSourceTestEvaluationInterface

def normalizedCommonFinitePrimeArithmeticSourceDataInputFromTheorems :
    Source.CCM25Concrete.FinitePrimeSourceData.CommonFinitePrimeArithmeticSourceData
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols :=
  normalizedSourceObjectTheoremBaseInputFromTheorems.finitePrimeExact

def normalizedCommonTestFunctionInputFromTheorems : TestFunction :=
  normalizedCommonFinitePrimeArithmeticSourceDataInputFromTheorems.commonTestFunction

def normalizedFinitePrimeArithmeticSourceDataInputFromTheorems :
    Source.CCM25Concrete.FinitePrimeSourceData.FinitePrimeArithmeticSourceData
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols
      (Source.CCM25Concrete.CommonSourceTest.concreteCommonSourceTest
        normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols
        normalizedCommonTestFunctionInputFromTheorems) :=
  normalizedCommonFinitePrimeArithmeticSourceDataInputFromTheorems.finitePrimeData

def normalizedFinitePrimeSourceTestSelectorDataInputFromTheorems :
    Source.CCM25Concrete.FinitePrimeSourceData.FinitePrimeSourceTestSelectorData
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols
      (Source.CCM25Concrete.CommonSourceTest.concreteCommonSourceTest
        normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols
        normalizedCommonTestFunctionInputFromTheorems) :=
  normalizedFinitePrimeArithmeticSourceDataInputFromTheorems.selector

def normalizedFinitePrimeSourceTestSelectorInputFromTheorems
    (f g : TestFunction) :
    Source.CCM25Concrete.PrimePowerTest.SourceTestEvaluationInterface
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols f g :=
  normalizedFinitePrimeSourceTestSelectorDataInputFromTheorems.sourceTest f g

def normalizedFixedLambdaArithmeticCertificateDataInputFromTheorems
    (f g : TestFunction) (lambda : ℝ) (hlambda : 1 < lambda) :
    Source.CCM25Concrete.FinitePrimeSourceData.FixedLambdaArithmeticCertificateSourceTestData
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols f g lambda
      (normalizedFinitePrimeSourceTestSelectorInputFromTheorems f g) :=
  normalizedFinitePrimeArithmeticSourceDataInputFromTheorems.certificateData
    f g lambda hlambda

theorem normalizedFinitePrimeVisibleIffSourceAtomInputFromTheorems
    (f g : TestFunction) (lambda : ℝ) (hlambda : 1 < lambda) :
    ∀ n : ℕ,
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols.finitePrimeAtomVisible
          n (normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols.convolutionStar f g) ↔
        Source.CCM25Concrete.PrimePowerSupport.SourceVisibleAtomData
          Source.CCM25Concrete.PrimePowerArithmetic.SourcePrimePowerIndex
          (normalizedFinitePrimeSourceTestSelectorInputFromTheorems
            f g).sourceAtomVisible n :=
  (normalizedFixedLambdaArithmeticCertificateDataInputFromTheorems
    f g lambda hlambda).visibleIff

theorem normalizedGlobalPrimeIndexExactInputFromTheorems
    (f g : TestFunction) (lambda : ℝ) (hlambda : 1 < lambda) :
    ∀ n : ℕ,
      n ∈ normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols.globalPrimeIndexSet ↔
        Source.CCM25Concrete.PrimePowerSupport.SourceGlobalIndexData
          Source.CCM25Concrete.PrimePowerArithmetic.SourcePrimePowerIndex
          (normalizedFinitePrimeSourceTestSelectorInputFromTheorems
            f g).sourceAtomVisible n :=
  (normalizedFixedLambdaArithmeticCertificateDataInputFromTheorems
    f g lambda hlambda).globalExact

theorem normalizedRestrictedPrimeIndexExactInputFromTheorems
    (f g : TestFunction) (lambda : ℝ) (hlambda : 1 < lambda) :
    ∀ n : ℕ,
      n ∈ normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols.restrictedPrimeIndexSet
          lambda ↔
        Source.CCM25Concrete.PrimePowerSupport.SourceRestrictedIndexData
          Source.CCM25Concrete.PrimePowerArithmetic.SourcePrimePowerIndex
          (normalizedFinitePrimeSourceTestSelectorInputFromTheorems
            f g).sourceAtomVisible lambda n :=
  (normalizedFixedLambdaArithmeticCertificateDataInputFromTheorems
    f g lambda hlambda).restrictedExact

theorem normalizedVisibleAtomsInLambdaCutInputFromTheorems
    (f g : TestFunction) (lambda : ℝ) (hlambda : 1 < lambda) :
    ∀ n : ℕ,
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols.finitePrimeAtomVisible
          n (normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols.convolutionStar f g) →
        Source.CCM25Concrete.PrimePowerSupport.SourceLambdaCut lambda n :=
  (normalizedFixedLambdaArithmeticCertificateDataInputFromTheorems
    f g lambda hlambda).visibleAtomsInLambdaCut

def normalizedPrimePowerArithmeticSupportSkeletonInputFromTheorems
    (f g : TestFunction) (lambda : ℝ) (hlambda : 1 < lambda) :
    Source.CCM25Concrete.PrimePowerSupport.SourcePrimePowerArithmeticSupportSkeletonAtLambda
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols f g lambda :=
  (normalizedFixedLambdaArithmeticCertificateDataInputFromTheorems
    f g lambda hlambda).toSupport hlambda

def normalizedPrimePowerSupportSkeletonInputFromTheorems
    (f g : TestFunction) (lambda : ℝ) (hlambda : 1 < lambda) :
    Source.CCM25Concrete.PrimePowerSupport.SourcePrimePowerSupportSkeletonAtLambda
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols f g lambda :=
  Source.CCM25Concrete.PrimePowerSupport.support_skeleton_of_arithmetic_support_skeleton
    (normalizedPrimePowerArithmeticSupportSkeletonInputFromTheorems
      f g lambda hlambda)

def normalizedFixedLambdaFinitePrimeArithmeticNormalizationInputFromTheorems
    (f g : TestFunction) (lambda : ℝ) (hlambda : 1 < lambda) :
    Source.CCM25Concrete.PrimePowerArithmetic.SourceFinitePrimeArithmeticNormalization
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols f g :=
  (normalizedFixedLambdaArithmeticCertificateDataInputFromTheorems
    f g lambda hlambda).atoms

theorem normalizedFinitePrimeArithmeticNormalizationUsesSupportSourceTestInputFromTheorems
    (f g : TestFunction) (lambda : ℝ) (hlambda : 1 < lambda) :
    Source.CCM25Concrete.PrimePowerArithmetic.UsesSourceTest
      (normalizedFixedLambdaFinitePrimeArithmeticNormalizationInputFromTheorems
        f g lambda hlambda)
      (normalizedPrimePowerArithmeticSupportSkeletonInputFromTheorems
        f g lambda hlambda).sourceTest :=
  (normalizedFixedLambdaArithmeticCertificateDataInputFromTheorems
    f g lambda hlambda).atomsUseSourceTest

theorem normalizedPrimePowerArithmeticSupportUsesSelectedSourceTestInputFromTheorems
    (f g : TestFunction) (lambda : ℝ) (hlambda : 1 < lambda) :
    (normalizedPrimePowerArithmeticSupportSkeletonInputFromTheorems
        f g lambda hlambda).sourceTest =
      normalizedFinitePrimeSourceTestSelectorInputFromTheorems f g :=
  rfl

def normalizedFixedLambdaArithmeticCertificateInputFromTheorems
    (f g : TestFunction) (lambda : ℝ) (hlambda : 1 < lambda) :
    Source.CCM25Concrete.FinitePrimeCertificate.FixedLambdaFinitePrimeArithmeticCertificate
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols f g lambda :=
  (normalizedFixedLambdaArithmeticCertificateDataInputFromTheorems
    f g lambda hlambda).toCertificate hlambda

theorem normalizedFixedLambdaArithmeticCertificateSourceTestInputFromTheorems
    (f g : TestFunction) (lambda : ℝ) (hlambda : 1 < lambda) :
    ((normalizedFixedLambdaArithmeticCertificateInputFromTheorems
          f g lambda hlambda).support.sourceTest =
      normalizedFinitePrimeSourceTestSelectorInputFromTheorems f g) := by
  rfl

def normalizedFinitePrimeArithmeticSourceTestCertificatesInputFromTheorems :
    Source.CCM25Concrete.FinitePrimeInterface.FixedLambdaArithmeticSourceTestCertificatesForAllTests
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols :=
  Source.CCM25Concrete.FinitePrimeSourceData.fixedLambdaArithmeticSourceTestCertificatesForAllTests
    normalizedCommonFinitePrimeArithmeticSourceDataInputFromTheorems

theorem normalizedCommonPairSourceTestInputFromTheorems :
    (normalizedFinitePrimeArithmeticSourceTestCertificatesInputFromTheorems
        normalizedCommonTestFunctionInputFromTheorems
        normalizedCommonTestFunctionInputFromTheorems).sourceTest =
      (Source.CCM25Concrete.CommonSourceTest.concreteCommonSourceTest
        normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols
        normalizedCommonTestFunctionInputFromTheorems).toSourceTestEvaluationInterface :=
  Source.CCM25Concrete.FinitePrimeSourceData.commonPairSourceTest
    normalizedCommonFinitePrimeArithmeticSourceDataInputFromTheorems

def normalizedConcreteCommonInputDataFromTheorems :
    NormalizedConcreteCommonInputData where
  commonTestFunction :=
    normalizedCommonTestFunctionInputFromTheorems
  finitePrimeArithmeticCertificates :=
    normalizedFinitePrimeArithmeticSourceTestCertificatesInputFromTheorems
  commonPairSourceTest :=
    normalizedCommonPairSourceTestInputFromTheorems

def normalizedCommonTestFunctionFromTheorems : TestFunction :=
  normalizedConcreteCommonInputDataFromTheorems.commonTestFunction

def normalizedConcreteCommonTestFromTheorems :
    Source.CCM25Concrete.CommonSourceTest.ConcreteCommonSourceTest
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols :=
  Source.CCM25Concrete.CommonSourceTest.concreteCommonSourceTest
    normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols
    normalizedCommonTestFunctionFromTheorems

def normalizedConcreteArithmeticRowsFromTheorems :
    Source.CCM25Concrete.Interface.ConcreteCCM25ArithmeticRows
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols where
  globalRows := normalizedConcreteGlobalQWPsiRowsFromTheorems
  restrictedRows := normalizedConcreteRestrictedQWLambdaRowsFromTheorems
  finitePrimeArithmeticCertificates :=
    normalizedConcreteCommonInputDataFromTheorems.finitePrimeArithmeticCertificates
  poleRows := normalizedConcretePoleNormalizationRowsFromTheorems

theorem normalizedCommonPairSourceTestFromTheorems :
    (normalizedConcreteArithmeticRowsFromTheorems.finitePrimeArithmeticCertificates
        normalizedConcreteCommonTestFromTheorems.sourceTest
        normalizedConcreteCommonTestFromTheorems.sourceTest).sourceTest =
      normalizedConcreteCommonTestFromTheorems.toSourceTestEvaluationInterface :=
  normalizedConcreteCommonInputDataFromTheorems.commonPairSourceTest

def normalizedConcreteCommonFromTheorems :
    Source.SourceObjectConcreteCommonData normalizedBaseFromTheorems :=
  Source.SourceObjectConcreteCommonData.ofCommonPairSourceTest
    normalizedConcreteCommonTestFromTheorems
    normalizedConcreteArithmeticRowsFromTheorems
    normalizedCommonPairSourceTestFromTheorems
    normalizedCommonFinitePrimeArithmeticSourceDataInputFromTheorems.scopedArchimedeanContributionBalance

def normalizedCommonFinitePrimeArithmeticSourceDataFromTheorems :
    Source.CCM25Concrete.FinitePrimeSourceData.CommonFinitePrimeArithmeticSourceData
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols :=
  normalizedConcreteCommonFromTheorems.commonFinitePrimeArithmeticSourceData

def normalizedFinitePrimeArithmeticSourceDataFromTheorems :
    Source.CCM25Concrete.FinitePrimeSourceData.FinitePrimeArithmeticSourceData
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols
      normalizedConcreteCommonTestFromTheorems :=
  normalizedCommonFinitePrimeArithmeticSourceDataFromTheorems.finitePrimeData

def normalizedFinitePrimeSourceTestSelectorDataFromTheorems :
    Source.CCM25Concrete.FinitePrimeSourceData.FinitePrimeSourceTestSelectorData
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
    (f g : TestFunction) (lambda : ℝ) (hlambda : 1 < lambda) :
    Source.CCM25Concrete.FinitePrimeSourceData.FixedLambdaArithmeticCertificateSourceTestData
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols f g lambda
      (normalizedFinitePrimeSourceTestFromTheorems f g) :=
  normalizedFinitePrimeArithmeticSourceDataFromTheorems.certificateData
    f g lambda hlambda

def normalizedFixedLambdaArithmeticCertificatesFromTheorems :
    Source.CCM25Concrete.FinitePrimeInterface.FixedLambdaArithmeticCertificatesForAllTests
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols := by
  intro f g lambda hlambda
  exact
    Source.CCM25Concrete.FinitePrimeSourceData.FixedLambdaArithmeticCertificateSourceTestData.toCertificate
      (normalizedFixedLambdaArithmeticCertificateDataFromTheorems
        f g lambda hlambda)
      hlambda

theorem normalizedFixedLambdaArithmeticCertificateSourceTestFromTheorems
    (f g : TestFunction) (lambda : ℝ) (hlambda : 1 < lambda) :
    ((normalizedFixedLambdaArithmeticCertificatesFromTheorems
          f g lambda hlambda).support.sourceTest =
      normalizedFinitePrimeSourceTestFromTheorems f g) :=
  rfl

def normalizedCommonFromTheorems :
    Source.SourceObjectCommonData normalizedBaseFromTheorems :=
  normalizedConcreteCommonFromTheorems.toSourceObjectCommonData

structure NormalizedSeedInputData where
  seed : Source.CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols
  archimedeanSymbols_eq_base :
    (Source.CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
      seed).archimedeanSymbols =
      normalizedBaseFromTheorems.cc20TraceModel.archimedeanSymbols

def normalizedSeedInputDataFromTheorems :
    NormalizedSeedInputData where
  seed := normalizedBaseFromTheorems.s2b1NormalizedSeed
  archimedeanSymbols_eq_base :=
    normalizedBaseFromTheorems.s2b1NormalizedSeedArchimedeanSymbolsEq

def normalizedSeedFromTheorems :
    Source.CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols :=
  normalizedSeedInputDataFromTheorems.seed

theorem normalizedSeedArchimedeanSymbolsEqBase :
    (Source.CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
      normalizedSeedFromTheorems).archimedeanSymbols =
      normalizedBaseFromTheorems.cc20TraceModel.archimedeanSymbols :=
  normalizedSeedInputDataFromTheorems.archimedeanSymbols_eq_base

structure NormalizedCC20RemainderRowsOutsideS2B1 where
  sourceTraceTest :
    (Source.CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
      normalizedSeedFromTheorems).archimedeanSymbols.Test
  sourceCC20TraceTestCompatibility : Prop
  sourceOperatorIdentity : Prop
  sourceHilbertSchmidtGate :
    ∀ g :
      (Source.CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
        normalizedSeedFromTheorems).archimedeanSymbols.Test,
        ArchimedeanTraceSymbols.hilbertSchmidtGate
          (Source.CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
            normalizedSeedFromTheorems).archimedeanSymbols
          g
  sourcePerMoveCyclicityLedger : Prop
  sourceNoDefectTraceReadOff : Prop
  sourceRemainderOrientationWInftyEqLMinusD : Prop
  sourceRemainderOrientationWInftyEqSMinusE : Prop
  sourceRemainderObject : Prop
  sourceRemainderObjectHolds : sourceRemainderObject
  sourceRemainderAfterQ : Prop
  sourceRemainderAfterQHolds : sourceRemainderAfterQ
  cc20PostQRemainderFixedSSoninTransport : Prop
  cc20PostQRemainderFixedSSoninTransportHolds :
    cc20PostQRemainderFixedSSoninTransport
  sourceProjectionDefectNormalForm : Prop
  sourceProjectionDefectNormalFormHolds :
    sourceProjectionDefectNormalForm
  sourceRankPoleLedgerIdentification : Prop
  sourceRankPoleLedgerIdentificationHolds :
    sourceRankPoleLedgerIdentification
  sourceEndpointStripRemainderCdefDomination : Prop
  sourceEndpointStripRemainderCdefDominationHolds :
    sourceEndpointStripRemainderCdefDomination
  noHiddenPositiveDefectOutsideCdef : Prop
  noHiddenPositiveDefectOutsideCdefHolds :
    noHiddenPositiveDefectOutsideCdef
  sourceBoundedComparisonTraceIdealTransport : Prop
  sourceBoundedComparisonTraceIdealTransportHolds :
    sourceBoundedComparisonTraceIdealTransport

def normalizedCC20RemainderRowsOutsideS2B1FromTheorems :
    NormalizedCC20RemainderRowsOutsideS2B1 where
  sourceTraceTest :=
    normalizedBaseFromTheorems.s2b1RemainderRowsOutsideNoBulk.sourceTraceTest
  sourceCC20TraceTestCompatibility :=
    normalizedBaseFromTheorems.s2b1RemainderRowsOutsideNoBulk.sourceCC20TraceTestCompatibility
  sourceOperatorIdentity :=
    normalizedBaseFromTheorems.s2b1RemainderRowsOutsideNoBulk.sourceOperatorIdentity
  sourceHilbertSchmidtGate :=
    normalizedBaseFromTheorems.s2b1RemainderRowsOutsideNoBulk.sourceHilbertSchmidtGate
  sourcePerMoveCyclicityLedger :=
    normalizedBaseFromTheorems.s2b1RemainderRowsOutsideNoBulk.sourcePerMoveCyclicityLedger
  sourceNoDefectTraceReadOff :=
    normalizedBaseFromTheorems.s2b1RemainderRowsOutsideNoBulk.sourceNoDefectTraceReadOff
  sourceRemainderOrientationWInftyEqLMinusD :=
    normalizedBaseFromTheorems.s2b1RemainderRowsOutsideNoBulk.sourceRemainderOrientationWInftyEqLMinusD
  sourceRemainderOrientationWInftyEqSMinusE :=
    normalizedBaseFromTheorems.s2b1RemainderRowsOutsideNoBulk.sourceRemainderOrientationWInftyEqSMinusE
  sourceRemainderObject :=
    normalizedBaseFromTheorems.s2b1RemainderRowsOutsideNoBulk.sourceRemainderObject
  sourceRemainderObjectHolds :=
    normalizedBaseFromTheorems.s2b1RemainderRowsOutsideNoBulk.sourceRemainderObjectHolds
  sourceRemainderAfterQ :=
    normalizedBaseFromTheorems.s2b1RemainderRowsOutsideNoBulk.sourceRemainderAfterQ
  sourceRemainderAfterQHolds :=
    normalizedBaseFromTheorems.s2b1RemainderRowsOutsideNoBulk.sourceRemainderAfterQHolds
  cc20PostQRemainderFixedSSoninTransport :=
    normalizedBaseFromTheorems.s2b1RemainderRowsOutsideNoBulk.cc20PostQRemainderFixedSSoninTransport
  cc20PostQRemainderFixedSSoninTransportHolds :=
    normalizedBaseFromTheorems.s2b1RemainderRowsOutsideNoBulk.cc20PostQRemainderFixedSSoninTransportHolds
  sourceProjectionDefectNormalForm :=
    normalizedBaseFromTheorems.s2b1RemainderRowsOutsideNoBulk.sourceProjectionDefectNormalForm
  sourceProjectionDefectNormalFormHolds :=
    normalizedBaseFromTheorems.s2b1RemainderRowsOutsideNoBulk.sourceProjectionDefectNormalFormHolds
  sourceRankPoleLedgerIdentification :=
    normalizedBaseFromTheorems.s2b1RemainderRowsOutsideNoBulk.sourceRankPoleLedgerIdentification
  sourceRankPoleLedgerIdentificationHolds :=
    normalizedBaseFromTheorems.s2b1RemainderRowsOutsideNoBulk.sourceRankPoleLedgerIdentificationHolds
  sourceEndpointStripRemainderCdefDomination :=
    normalizedBaseFromTheorems.s2b1RemainderRowsOutsideNoBulk.sourceEndpointStripRemainderCdefDomination
  sourceEndpointStripRemainderCdefDominationHolds :=
    normalizedBaseFromTheorems.s2b1RemainderRowsOutsideNoBulk.sourceEndpointStripRemainderCdefDominationHolds
  noHiddenPositiveDefectOutsideCdef :=
    normalizedBaseFromTheorems.s2b1RemainderRowsOutsideNoBulk.noHiddenPositiveDefectOutsideCdef
  noHiddenPositiveDefectOutsideCdefHolds :=
    normalizedBaseFromTheorems.s2b1RemainderRowsOutsideNoBulk.noHiddenPositiveDefectOutsideCdefHolds
  sourceBoundedComparisonTraceIdealTransport :=
    normalizedBaseFromTheorems.s2b1RemainderRowsOutsideNoBulk.sourceBoundedComparisonTraceIdealTransport
  sourceBoundedComparisonTraceIdealTransportHolds :=
    normalizedBaseFromTheorems.s2b1RemainderRowsOutsideNoBulk.sourceBoundedComparisonTraceIdealTransportHolds

structure NormalizedS2B1NoBulkRows where
  witness :
    ∀ lambda : ℝ, 1 < lambda →
      ∀ archimedeanTest :
        (Source.CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
          normalizedSeedFromTheorems).archimedeanSymbols.Test,
        ∀ weilTest : TestFunction,
          Source.CC20CCMTraceScaleNoBulkWitness
            (Source.CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
              normalizedSeedFromTheorems).archimedeanSymbols
            normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols
            lambda archimedeanTest weilTest

structure NormalizedS2B1NoBulkRowsFromBaseTransport where
  archimedeanSymbols_eq_base :
    (Source.CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
      normalizedSeedFromTheorems).archimedeanSymbols =
      normalizedBaseFromTheorems.cc20TraceModel.archimedeanSymbols
  baseWitness :
    ∀ lambda : ℝ, 1 < lambda →
      ∀ archimedeanTest : normalizedBaseFromTheorems.cc20TraceModel.archimedeanSymbols.Test,
        ∀ weilTest : TestFunction,
          Source.CC20CCMTraceScaleNoBulkWitness
            normalizedBaseFromTheorems.cc20TraceModel.archimedeanSymbols
            normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols
            lambda archimedeanTest weilTest := by
    intro lambda hlambda archimedeanTest weilTest
    exact normalizedBaseFromTheorems.s2b1FixedTupleNoBulkWitness
      lambda hlambda archimedeanTest weilTest

def normalizedS2B1NoBulkRowsFromBaseTransportFromTheorems :
    NormalizedS2B1NoBulkRowsFromBaseTransport where
  archimedeanSymbols_eq_base := normalizedSeedArchimedeanSymbolsEqBase

def normalizedS2B1NoBulkRowsFromTheorems :
    NormalizedS2B1NoBulkRows where
  witness := by
    rw [normalizedS2B1NoBulkRowsFromBaseTransportFromTheorems.archimedeanSymbols_eq_base]
    exact normalizedS2B1NoBulkRowsFromBaseTransportFromTheorems.baseWitness

def normalizedS2B1FixedTupleSupportSquareQWLambdaRowFromTheorems
    (lambda : ℝ) (hlambda : 1 < lambda)
    (archimedeanTest :
      (Source.CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
        normalizedSeedFromTheorems).archimedeanSymbols.Test)
    (weilTest : TestFunction) :
    Source.S2B1FixedTupleSupportSquareQWLambdaRow
      (Source.CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
        normalizedSeedFromTheorems).archimedeanSymbols
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols
      lambda archimedeanTest weilTest :=
  normalizedBaseFromTheorems.s2b1NormalizedSeedSupportSquareQWLambdaRow
    lambda hlambda archimedeanTest weilTest

def normalizedS2B1FixedTupleAnalyticExclusionFromTheorems
    (lambda : ℝ) (hlambda : 1 < lambda)
    (archimedeanTest :
      (Source.CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
        normalizedSeedFromTheorems).archimedeanSymbols.Test)
    (weilTest : TestFunction) :
    Source.S2B1TraceScaleFixedTupleAnalyticExclusionPackage
      (Source.CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
        normalizedSeedFromTheorems).archimedeanSymbols
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols
      lambda archimedeanTest weilTest :=
  normalizedBaseFromTheorems.s2b1NormalizedSeedFixedTupleAnalyticExclusion
    lambda hlambda archimedeanTest weilTest

def normalizedRemaindersFromTheorems :
    Source.CC20Concrete.TraceScale.CC20TracePackageRemainderData
      normalizedSeedFromTheorems :=
  normalizedBaseFromTheorems.s2b1RemainderRowsOutsideNoBulk.toRemainderData
    normalizedBaseFromTheorems.s2b1NormalizedSeedTraceScaleNoBulkRows
    2 (by norm_num)
    normalizedBaseFromTheorems.s2b1RemainderRowsOutsideNoBulk.sourceTraceTest
    normalizedCommonFromTheorems.commonTest.sourceTest

def normalizedActualScalarIdentificationFromTheoremBasePackage
    (lambda : ℝ) (hlambda : 1 < lambda)
    (archimedeanTest :
      (Source.CC20Concrete.TraceScale.normalizedSeedTraceObjectPackage
        normalizedSeedFromTheorems normalizedRemaindersFromTheorems).archimedeanSymbols.Test)
    (weilTest : TestFunction) :
    Source.NormalizedSeedQWLambdaScalarIdentification
      normalizedSeedFromTheorems
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols
      normalizedRemaindersFromTheorems
      lambda archimedeanTest weilTest :=
  Source.normalizedSeedQWLambdaScalarIdentificationOfTheoremBasePackage
    normalizedBaseFromTheorems lambda hlambda normalizedRemaindersFromTheorems
    archimedeanTest weilTest

structure NormalizedSourceObjectCCM24Input where
  ccm24 : Source.SourceObject.CCM24SemilocalObjectPackage

def normalizedSourceObjectCCM24InputFromTheorems :
    NormalizedSourceObjectCCM24Input where
  ccm24 :=
    normalizedSourceObjectTheoremBaseInputFromTheorems.sourceObjectCCM24

structure NormalizedSourceObjectRHExitInput where
  rhExit : Source.SourceObject.CC20RHExitObjectPackage

def normalizedSourceObjectRHExitInputFromTheorems :
    NormalizedSourceObjectRHExitInput where
  rhExit :=
    normalizedSourceObjectTheoremBaseInputFromTheorems.sourceObjectCC20RHExit

def normalizedSourceObjectBridgeRowsFromTheorems :
    Source.SourceObjectExpandedRows normalizedBaseFromTheorems
      normalizedCommonFromTheorems :=
  Source.SourceObjectExpandedRows.ofNormalizedCC20Trace
    normalizedSourceObjectCCM24InputFromTheorems.ccm24
    normalizedSeedFromTheorems normalizedRemaindersFromTheorems

structure NormalizedSourceObjectRHDefinitionBridgeEqInput where
  rhDefinitionBridge_eq_base :
    normalizedSourceObjectRHExitInputFromTheorems.rhExit.rhDefinitionBridge =
      normalizedBaseFromTheorems.rhDefinitionBridge

def normalizedSourceObjectRHDefinitionBridgeEqInputFromTheorems :
    NormalizedSourceObjectRHDefinitionBridgeEqInput where
  rhDefinitionBridge_eq_base :=
    normalizedSourceObjectTheoremBaseInputFromTheorems.sourceObjectCC20RHExitBridgeEq

structure NormalizedSourceObjectCommonTestInvolutionBridgeInput where
  commonTestInvolution :
    Source.SourceObject.CommonTestInvolutionBridge
      (Source.SourceObjectExpandedRows.ccm25
        normalizedSourceObjectBridgeRowsFromTheorems).weilSymbols
      normalizedCommonFromTheorems.commonTest

def normalizedSourceObjectCommonTestBridgeRowsFromTheorems :
    Source.NormalizedSourceObjectCommonTestBridgeRows
      normalizedBaseFromTheorems normalizedCommonFromTheorems.commonTest
      normalizedSourceObjectCCM24InputFromTheorems.ccm24
      normalizedSourceObjectBridgeRowsFromTheorems.cc20Trace :=
  normalizedSourceObjectTheoremBaseInputFromTheorems.sourceObjectCommonTestBridgeRows
    normalizedCommonFromTheorems.commonTest
    normalizedSourceObjectBridgeRowsFromTheorems.cc20Trace

def normalizedSourceObjectCommonTestInvolutionBridgeInputFromTheorems :
    NormalizedSourceObjectCommonTestInvolutionBridgeInput where
  commonTestInvolution :=
    normalizedSourceObjectCommonTestBridgeRowsFromTheorems.commonTestInvolution

structure NormalizedSourceObjectCCM24CommonTestBridgeInput where
  ccm24Test_eq_commonTest :
    Source.SourceObject.CCM24CommonTestBridge
      (Source.SourceObjectExpandedRows.ccm25
        normalizedSourceObjectBridgeRowsFromTheorems).weilSymbols
      normalizedCommonFromTheorems.commonTest
      normalizedSourceObjectCCM24InputFromTheorems.ccm24

def normalizedSourceObjectCCM24CommonTestBridgeInputFromTheorems :
    NormalizedSourceObjectCCM24CommonTestBridgeInput where
  ccm24Test_eq_commonTest :=
    normalizedSourceObjectCommonTestBridgeRowsFromTheorems.ccm24Test_eq_commonTest

structure NormalizedSourceObjectCC20CommonTestBridgeInput where
  cc20TraceTest_eq_commonTest :
    Source.SourceObject.CC20CommonTestBridge
      (Source.SourceObjectExpandedRows.ccm25
        normalizedSourceObjectBridgeRowsFromTheorems).weilSymbols
      normalizedCommonFromTheorems.commonTest
      normalizedSourceObjectBridgeRowsFromTheorems.cc20Trace

def normalizedSourceObjectCC20CommonTestBridgeInputFromTheorems :
    NormalizedSourceObjectCC20CommonTestBridgeInput where
  cc20TraceTest_eq_commonTest :=
    normalizedSourceObjectCommonTestBridgeRowsFromTheorems.cc20TraceTest_eq_commonTest

structure NormalizedSourceObjectConvolutionSquareEqFgInput where
  convolutionSquare_eq_Fg : Prop

def normalizedSourceObjectConvolutionSquareEqFgInputFromTheorems :
    NormalizedSourceObjectConvolutionSquareEqFgInput where
  convolutionSquare_eq_Fg :=
    normalizedCommonFromTheorems.commonTest.sourceConvolutionSquare =
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols.convolutionStar
        normalizedCommonFromTheorems.commonTest.sourceTest
        normalizedCommonFromTheorems.commonTest.sourceTest

structure NormalizedSourceObjectQWLambdaWindowControlInput where
  ccm24Window_controls_qwLambda : Prop

def normalizedSourceObjectQWLambdaWindowControlInputFromTheorems :
    NormalizedSourceObjectQWLambdaWindowControlInput where
  ccm24Window_controls_qwLambda :=
    ∀ lambda : ℝ, 1 < lambda →
      SemilocalModelSymbols.lambdaCompatible
        normalizedSourceObjectCCM24InputFromTheorems.ccm24.semilocalSymbols
        normalizedSourceObjectCCM24InputFromTheorems.ccm24.sourceSupportWindow
        lambda

structure NormalizedSourceObjectCdefWindowControlInput where
  ccm24Window_controls_cdef : Prop

def normalizedSourceObjectCdefWindowControlInputFromTheorems :
    NormalizedSourceObjectCdefWindowControlInput where
  ccm24Window_controls_cdef :=
    SemilocalModelSymbols.fixedWindowExhaustionCompatible
      normalizedSourceObjectCCM24InputFromTheorems.ccm24.semilocalSymbols
      normalizedSourceObjectCCM24InputFromTheorems.ccm24.sourceSupportWindow

structure NormalizedSourceObjectFinitePrimeWindowMatchInput where
  finitePrimeSupport_matches_window : Prop

def normalizedSourceObjectFinitePrimeWindowMatchInputFromTheorems :
    NormalizedSourceObjectFinitePrimeWindowMatchInput where
  finitePrimeSupport_matches_window :=
    WeilFormSymbols.FinitePrimeNormalizationStatement
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols

structure NormalizedSourceObjectQWSignBridgeInput where
  qW_sign_bridge : Prop

def normalizedSourceObjectQWSignBridgeInputFromTheorems :
    NormalizedSourceObjectQWSignBridgeInput where
  qW_sign_bridge :=
    ∀ input : WeilPositivityInput,
      normalizedSourceObjectRHExitInputFromTheorems.rhExit.sourceQWNonnegative input →
        normalizedSourceObjectRHExitInputFromTheorems.rhExit.sourceCC20WeilNonpositivity input

structure NormalizedSourceObjectCrossObjectBridgeInput where
  bridges :
    Source.SourceObjectCrossObjectBridges normalizedBaseFromTheorems
      normalizedCommonFromTheorems
      normalizedSourceObjectBridgeRowsFromTheorems
      normalizedSourceObjectRHExitInputFromTheorems.rhExit

def normalizedSourceObjectCrossObjectBridgeInputFromTheorems :
    NormalizedSourceObjectCrossObjectBridgeInput where
  bridges :=
    { rhDefinitionBridge_eq_base :=
        (normalizedSourceObjectRHDefinitionBridgeEqInputFromTheorems).rhDefinitionBridge_eq_base
      commonTestInvolution :=
        (normalizedSourceObjectCommonTestInvolutionBridgeInputFromTheorems).commonTestInvolution
      ccm24Test_eq_commonTest :=
        (normalizedSourceObjectCCM24CommonTestBridgeInputFromTheorems).ccm24Test_eq_commonTest
      cc20TraceTest_eq_commonTest :=
        (normalizedSourceObjectCC20CommonTestBridgeInputFromTheorems).cc20TraceTest_eq_commonTest
      convolutionSquare_eq_Fg :=
        (normalizedSourceObjectConvolutionSquareEqFgInputFromTheorems).convolutionSquare_eq_Fg
      ccm24Window_controls_qwLambda :=
        (normalizedSourceObjectQWLambdaWindowControlInputFromTheorems).ccm24Window_controls_qwLambda
      ccm24Window_controls_cdef :=
        (normalizedSourceObjectCdefWindowControlInputFromTheorems).ccm24Window_controls_cdef
      finitePrimeSupport_matches_window :=
        (normalizedSourceObjectFinitePrimeWindowMatchInputFromTheorems).finitePrimeSupport_matches_window
      qW_sign_bridge :=
        normalizedSourceObjectQWSignBridgeInputFromTheorems.qW_sign_bridge }

structure NormalizedSourceObjectLayerBridgeInput where
  ccm24 : Source.SourceObject.CCM24SemilocalObjectPackage
  rhExit : Source.SourceObject.CC20RHExitObjectPackage
  bridges :
    Source.SourceObjectCrossObjectBridges normalizedBaseFromTheorems
      normalizedCommonFromTheorems
      (Source.SourceObjectExpandedRows.ofNormalizedCC20Trace
        ccm24 normalizedSeedFromTheorems normalizedRemaindersFromTheorems)
      rhExit

def normalizedSourceObjectLayerBridgeInputFromTheorems :
    NormalizedSourceObjectLayerBridgeInput where
  ccm24 := normalizedSourceObjectCCM24InputFromTheorems.ccm24
  rhExit := normalizedSourceObjectRHExitInputFromTheorems.rhExit
  bridges := normalizedSourceObjectCrossObjectBridgeInputFromTheorems.bridges

def normalizedSourceObjectLayerInputFromTheorems :
    Source.NormalizedCC20SourceObjectLayerInput
      normalizedBaseFromTheorems normalizedCommonFromTheorems
      normalizedSeedFromTheorems normalizedRemaindersFromTheorems :=
  { ccm24 := normalizedSourceObjectLayerBridgeInputFromTheorems.ccm24
    rhExit := normalizedSourceObjectLayerBridgeInputFromTheorems.rhExit
    bridges := normalizedSourceObjectLayerBridgeInputFromTheorems.bridges }

def normalizedCCM24FromTheorems :
    Source.SourceObject.CCM24SemilocalObjectPackage :=
  normalizedSourceObjectLayerInputFromTheorems.ccm24

def normalizedRhExitFromTheorems :
    Source.SourceObject.CC20RHExitObjectPackage :=
  normalizedSourceObjectLayerInputFromTheorems.rhExit

def normalizedRowsFromTheorems :
    Source.SourceObjectExpandedRows normalizedBaseFromTheorems
      normalizedCommonFromTheorems :=
  Source.SourceObjectExpandedRows.ofNormalizedCC20Trace
    normalizedCCM24FromTheorems normalizedSeedFromTheorems
    normalizedRemaindersFromTheorems

def normalizedBridgesFromTheorems :
    Source.SourceObjectCrossObjectBridges normalizedBaseFromTheorems
      normalizedCommonFromTheorems normalizedRowsFromTheorems
      normalizedRhExitFromTheorems :=
  normalizedSourceObjectLayerInputFromTheorems.bridges

abbrev normalizedSourceObjectPackageFromTheorems :
    Source.SourceObject.SourceObjectPackage :=
  Source.sourceObjectPackageOfNormalizedCC20Trace
    normalizedBaseFromTheorems normalizedCommonFromTheorems
    normalizedCCM24FromTheorems normalizedSeedFromTheorems
    normalizedRemaindersFromTheorems normalizedRhExitFromTheorems
    normalizedBridgesFromTheorems

structure NormalizedFixedSTestAdmissibleWindowInput where
  admissibleWindow : Prop
  admissibleWindowHolds : admissibleWindow

def normalizedFixedSTestAdmissibleWindowInputFromTheorems :
    NormalizedFixedSTestAdmissibleWindowInput where
  admissibleWindow :=
    normalizedSourceObjectPackageFromTheorems.ccm24.semilocalSymbols.supportInWindow
      normalizedSourceObjectPackageFromTheorems.ccm24.sourceTestLeg
      normalizedSourceObjectPackageFromTheorems.ccm24.sourceSupportWindow
  admissibleWindowHolds :=
    normalizedSourceObjectPackageFromTheorems.ccm24.sourceSupportInWindowData

structure NormalizedFixedSTestTripleVanishingInput where
  tripleVanishingSymbols : TripleVanishingSymbols
  tripleVanishingSourceHolds :
    TripleVanishingSymbols.TripleVanishingStatement tripleVanishingSymbols

def normalizedFixedSTestTripleVanishingInputFromTheorems :
    NormalizedFixedSTestTripleVanishingInput := by
  sorry

structure NormalizedFixedSTestSourceInput where
  admissibleWindow : Prop
  admissibleWindowHolds : admissibleWindow
  tripleVanishingSymbols : TripleVanishingSymbols
  tripleVanishingSourceHolds :
    TripleVanishingSymbols.TripleVanishingStatement tripleVanishingSymbols

def normalizedFixedSTestSourceInputFromTheorems :
    NormalizedFixedSTestSourceInput where
  admissibleWindow :=
    normalizedFixedSTestAdmissibleWindowInputFromTheorems.admissibleWindow
  admissibleWindowHolds :=
    normalizedFixedSTestAdmissibleWindowInputFromTheorems.admissibleWindowHolds
  tripleVanishingSymbols :=
    normalizedFixedSTestTripleVanishingInputFromTheorems.tripleVanishingSymbols
  tripleVanishingSourceHolds :=
    normalizedFixedSTestTripleVanishingInputFromTheorems.tripleVanishingSourceHolds

def normalizedFixedTestFromTheorems : FixedSTest where
  admissibleWindow :=
    normalizedFixedSTestSourceInputFromTheorems.admissibleWindow
  tripleVanishing :=
    TripleVanishingSymbols.TripleVanishingStatement
      normalizedFixedSTestSourceInputFromTheorems.tripleVanishingSymbols
  finitePrimesVisible :=
    WeilFormSymbols.FinitePrimeVisibilityStatement
      (RouteInputs.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems).ccm25.weilSymbols
      normalizedSourceObjectPackageFromTheorems.commonTest.sourceTest
      normalizedSourceObjectPackageFromTheorems.commonTest.sourceTest

def normalizedFixedDataFromTheorems :
    FixedSTestObligationData normalizedSourceObjectPackageFromTheorems where
  test := normalizedFixedTestFromTheorems
  tripleVanishingSymbols :=
    normalizedFixedSTestSourceInputFromTheorems.tripleVanishingSymbols
  admissibleWindow :=
    normalizedFixedSTestSourceInputFromTheorems.admissibleWindowHolds
  tripleVanishingBridge := by
    intro h
    exact h
  tripleVanishingSourceHolds :=
    normalizedFixedSTestSourceInputFromTheorems.tripleVanishingSourceHolds
  routeTest := normalizedSourceObjectPackageFromTheorems.commonTest.sourceTest
  routeTest_eq_commonTest := rfl
  finitePrimeVisibilityBridge := by
    intro h
    exact h

abbrev normalizedFixedFrontEndFromTheorems :
    ExpandedSourceFixedSTestFrontEnd
      normalizedSourceObjectPackageFromTheorems :=
  FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
    normalizedBaseFromTheorems normalizedCommonFromTheorems
    normalizedCCM24FromTheorems normalizedSeedFromTheorems
    normalizedRemaindersFromTheorems normalizedRhExitFromTheorems
    normalizedBridgesFromTheorems normalizedFixedDataFromTheorems

structure NormalizedTraceLambdaInput where
  lambda : ℝ
  oneLtLambda : 1 < lambda

def normalizedTraceLambdaInputFromTheorems :
    NormalizedTraceLambdaInput where
  lambda := 2
  oneLtLambda := by norm_num

def normalizedTraceCCM25ArithmeticPackageFromTheorems :
    Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
      (RouteInputs.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems).ccm25.weilSymbols
      normalizedSourceObjectPackageFromTheorems.commonTest.sourceTest
      normalizedTraceLambdaInputFromTheorems.lambda where
  rows := normalizedConcreteArithmeticRowsFromTheorems
  oneLtLambda := normalizedTraceLambdaInputFromTheorems.oneLtLambda

structure NormalizedTraceQuotientCompatibilityInput where
  testAndQuotientCompatibility :
    TestAndQuotientCompatibility
      (RouteInputs.ofExpandedSourcePackage normalizedSourceObjectPackageFromTheorems)
      (SourceBackedFixedSTest.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems normalizedFixedFrontEndFromTheorems)

def normalizedTraceQuotientCompatibilityInputFromTheorems :
    NormalizedTraceQuotientCompatibilityInput where
  testAndQuotientCompatibility :=
    test_and_quotient_compatibility_of_package
      normalizedTraceCCM25ArithmeticPackageFromTheorems

structure NormalizedTraceSupportSquareTransportInput where
  fixedSSupportSquareTransport :
    FixedSQuantizedSupportSquareTransport
      (RouteInputs.ofExpandedSourcePackage normalizedSourceObjectPackageFromTheorems)
      normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceTraceTest
      (SourceBackedFixedSTest.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems normalizedFixedFrontEndFromTheorems)
      normalizedTraceLambdaInputFromTheorems.lambda

def normalizedTraceSupportSquareTransportInputFromTheorems :
    NormalizedTraceSupportSquareTransportInput where
  fixedSSupportSquareTransport :=
    fixed_s_quantized_support_square_transport_of_parts
      normalizedTraceLambdaInputFromTheorems.oneLtLambda
      (cc20_archimedean_trace_square_output
        (cc20_trace_legality_template_output
          (normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceHilbertSchmidtGate
            normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceTraceTest)).traceLegality).noDefectSourceReadOff
      (cc20_trace_legality_template_output
        (normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceHilbertSchmidtGate
          normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceTraceTest)).traceLegality

structure NormalizedTraceFullReadOffBuildInput where
  build :
    CC20NoDefectSourceReadOff
        (RouteInputs.ofExpandedSourcePackage normalizedSourceObjectPackageFromTheorems)
        normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceTraceTest →
      CCM25FullQWReadOff
        (RouteInputs.ofExpandedSourcePackage normalizedSourceObjectPackageFromTheorems)
        (SourceBackedFixedSTest.ofExpandedSourcePackage
          normalizedSourceObjectPackageFromTheorems normalizedFixedFrontEndFromTheorems) →
      FullTraceReadOffSource
        (RouteInputs.ofExpandedSourcePackage normalizedSourceObjectPackageFromTheorems)
        normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceTraceTest
        (SourceBackedFixedSTest.ofExpandedSourcePackage
          normalizedSourceObjectPackageFromTheorems normalizedFixedFrontEndFromTheorems)

structure NormalizedTraceFullReadOffEqualityInput where
  fullTraceReadOffEquality :
    FullTraceReadOffEquality
      (RouteInputs.ofExpandedSourcePackage normalizedSourceObjectPackageFromTheorems)
      normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceTraceTest
      (SourceBackedFixedSTest.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems normalizedFixedFrontEndFromTheorems)

def normalizedTraceReadOffEqualityRowsFromTheorems :
    Source.NormalizedSourceTraceReadOffEqualityRows
      normalizedBaseFromTheorems normalizedCommonFromTheorems.commonTest
      normalizedSourceObjectPackageFromTheorems.cc20Trace
      normalizedTraceLambdaInputFromTheorems.lambda :=
  normalizedSourceObjectTheoremBaseInputFromTheorems.sourceTraceReadOffEqualityRows
    normalizedCommonFromTheorems.commonTest
    normalizedSourceObjectPackageFromTheorems.cc20Trace
    normalizedTraceLambdaInputFromTheorems.lambda

def normalizedTraceFullReadOffEqualityInputFromTheorems :
    NormalizedTraceFullReadOffEqualityInput where
  fullTraceReadOffEquality := by
    simpa [FullTraceReadOffEquality] using
      normalizedTraceReadOffEqualityRowsFromTheorems.fullTraceReadOffEquality

def normalizedTraceFullReadOffBuildInputFromTheorems :
    NormalizedTraceFullReadOffBuildInput where
  build := by
    intro hnoDefect hfull
    exact
      full_trace_read_off_source_of_parts hnoDefect hfull
        normalizedTraceFullReadOffEqualityInputFromTheorems.fullTraceReadOffEquality

structure NormalizedTraceFullReadOffPreservationInput where
  preservesNoDefect :
    ∀ hnoDefect hfull,
      (normalizedTraceFullReadOffBuildInputFromTheorems.build
        hnoDefect hfull).noDefectSourceReadOff = hnoDefect
  preservesFullQW :
    ∀ hnoDefect hfull,
      (normalizedTraceFullReadOffBuildInputFromTheorems.build
        hnoDefect hfull).ccm25FullQWReadOff = hfull

def normalizedTraceFullReadOffPreservationInputFromTheorems :
    NormalizedTraceFullReadOffPreservationInput where
  preservesNoDefect := by
    intro hnoDefect hfull
    rfl
  preservesFullQW := by
    intro hnoDefect hfull
    rfl

structure NormalizedTraceFullReadOffBridgeInput where
  fullTraceReadOffBridge :
    FullTraceReadOffBridgeContract
      (RouteInputs.ofExpandedSourcePackage normalizedSourceObjectPackageFromTheorems)
      normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceTraceTest
      (SourceBackedFixedSTest.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems normalizedFixedFrontEndFromTheorems)

def normalizedTraceFullReadOffBridgeInputFromTheorems :
    NormalizedTraceFullReadOffBridgeInput where
  fullTraceReadOffBridge :=
    { build :=
        normalizedTraceFullReadOffBuildInputFromTheorems.build
      preservesNoDefect :=
        normalizedTraceFullReadOffPreservationInputFromTheorems.preservesNoDefect
      preservesFullQW :=
        normalizedTraceFullReadOffPreservationInputFromTheorems.preservesFullQW }

structure NormalizedTraceRestrictedReadOffBuildInput where
  build :
    CCM25RestrictedQWReadOff
        (RouteInputs.ofExpandedSourcePackage normalizedSourceObjectPackageFromTheorems)
        (SourceBackedFixedSTest.ofExpandedSourcePackage
          normalizedSourceObjectPackageFromTheorems normalizedFixedFrontEndFromTheorems)
        normalizedTraceLambdaInputFromTheorems.lambda →
      RestrictedTraceReadOffSource
        (RouteInputs.ofExpandedSourcePackage normalizedSourceObjectPackageFromTheorems)
        normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceTraceTest
        (SourceBackedFixedSTest.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems normalizedFixedFrontEndFromTheorems)
        normalizedTraceLambdaInputFromTheorems.lambda

structure NormalizedTraceRestrictedReadOffEqualityInput where
  restrictedTraceReadOffEquality :
    RestrictedTraceReadOffEquality
      (RouteInputs.ofExpandedSourcePackage normalizedSourceObjectPackageFromTheorems)
      normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceTraceTest
      (SourceBackedFixedSTest.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems normalizedFixedFrontEndFromTheorems)
      normalizedTraceLambdaInputFromTheorems.lambda

def normalizedTraceRestrictedReadOffEqualityInputFromTheorems :
    NormalizedTraceRestrictedReadOffEqualityInput where
  restrictedTraceReadOffEquality := by
    simpa [RestrictedTraceReadOffEquality] using
      normalizedTraceReadOffEqualityRowsFromTheorems.restrictedTraceReadOffEquality

def normalizedTraceRestrictedReadOffBuildInputFromTheorems :
    NormalizedTraceRestrictedReadOffBuildInput where
  build := by
    intro hrestricted
    exact
      restricted_trace_read_off_source_of_parts hrestricted
        normalizedTraceRestrictedReadOffEqualityInputFromTheorems.restrictedTraceReadOffEquality

structure NormalizedTraceRestrictedReadOffPreservationInput where
  preservesRestrictedQW :
    ∀ hrestricted,
      (normalizedTraceRestrictedReadOffBuildInputFromTheorems.build
        hrestricted).ccm25RestrictedQWReadOff = hrestricted

def normalizedTraceRestrictedReadOffPreservationInputFromTheorems :
    NormalizedTraceRestrictedReadOffPreservationInput where
  preservesRestrictedQW := by
    intro hrestricted
    rfl

structure NormalizedTraceRestrictedReadOffBridgeInput where
  restrictedTraceReadOffBridge :
    RestrictedTraceReadOffBridgeContract
      (RouteInputs.ofExpandedSourcePackage normalizedSourceObjectPackageFromTheorems)
      normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceTraceTest
      (SourceBackedFixedSTest.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems normalizedFixedFrontEndFromTheorems)
      normalizedTraceLambdaInputFromTheorems.lambda

def normalizedTraceRestrictedReadOffBridgeInputFromTheorems :
    NormalizedTraceRestrictedReadOffBridgeInput where
  restrictedTraceReadOffBridge :=
    { build :=
        normalizedTraceRestrictedReadOffBuildInputFromTheorems.build
      preservesRestrictedQW :=
        normalizedTraceRestrictedReadOffPreservationInputFromTheorems.preservesRestrictedQW }

structure NormalizedTraceReadOffBridgeInput where
  full : NormalizedTraceFullReadOffBridgeInput
  restricted : NormalizedTraceRestrictedReadOffBridgeInput

def normalizedTraceReadOffBridgeInputFromTheorems :
    NormalizedTraceReadOffBridgeInput where
  full := normalizedTraceFullReadOffBridgeInputFromTheorems
  restricted := normalizedTraceRestrictedReadOffBridgeInputFromTheorems

def normalizedTraceSourceReadOffDataFromParts :
    SourceTraceReadOffData
      (RouteInputs.ofExpandedSourcePackage normalizedSourceObjectPackageFromTheorems)
      (SourceBackedFixedSTest.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems normalizedFixedFrontEndFromTheorems) :=
  TraceFrontEndData.sourceTraceReadOffDataOfTraceFrontParts
    normalizedSourceObjectPackageFromTheorems
    normalizedFixedFrontEndFromTheorems
    normalizedTraceLambdaInputFromTheorems.lambda
    normalizedTraceLambdaInputFromTheorems.oneLtLambda
    normalizedTraceCCM25ArithmeticPackageFromTheorems
    normalizedTraceQuotientCompatibilityInputFromTheorems.testAndQuotientCompatibility
    normalizedTraceSupportSquareTransportInputFromTheorems.fixedSSupportSquareTransport
    normalizedTraceFullReadOffBridgeInputFromTheorems.fullTraceReadOffBridge
    normalizedTraceRestrictedReadOffBridgeInputFromTheorems.restrictedTraceReadOffBridge

theorem normalizedTraceFullReadOffEqualityOfSourceTraceDataFromParts :
    FullTraceReadOffEquality
      (RouteInputs.ofExpandedSourcePackage normalizedSourceObjectPackageFromTheorems)
      normalizedTraceSourceReadOffDataFromParts.archimedeanTest
      (SourceBackedFixedSTest.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems normalizedFixedFrontEndFromTheorems) :=
  (full_trace_read_off_of_source_trace_data
    normalizedTraceSourceReadOffDataFromParts).fullTraceReadOffEquality

theorem normalizedTraceRestrictedReadOffEqualityOfSourceTraceDataFromParts :
    RestrictedTraceReadOffEquality
      (RouteInputs.ofExpandedSourcePackage normalizedSourceObjectPackageFromTheorems)
      normalizedTraceSourceReadOffDataFromParts.archimedeanTest
      (SourceBackedFixedSTest.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems normalizedFixedFrontEndFromTheorems)
      normalizedTraceSourceReadOffDataFromParts.lambda :=
  (restricted_trace_read_off_of_source_trace_data
    normalizedTraceSourceReadOffDataFromParts).restrictedTraceReadOffEquality

structure NormalizedTraceOrdinarySupportSquareInput where
  ordinary :
    OrdinaryTraceSupportSquareTheoremData
      normalizedSourceObjectPackageFromTheorems normalizedFixedFrontEndFromTheorems
      normalizedTraceLambdaInputFromTheorems.lambda
      normalizedTraceCCM25ArithmeticPackageFromTheorems

def normalizedTraceOrdinarySupportSquareInputFromTheorems :
    NormalizedTraceOrdinarySupportSquareInput where
  ordinary :=
    TraceFrontEndData.ordinary_trace_support_square_theorem_data_of_trace_front_parts
      (pkg := normalizedSourceObjectPackageFromTheorems)
      (fixedFront := normalizedFixedFrontEndFromTheorems)
      normalizedTraceSourceReadOffDataFromParts

structure NormalizedTraceNoDefectQWLambdaInput where
  noDefect :
    NoDefectQWLambdaTheoremData
      normalizedSourceObjectPackageFromTheorems normalizedFixedFrontEndFromTheorems
      normalizedTraceLambdaInputFromTheorems.lambda
      normalizedTraceCCM25ArithmeticPackageFromTheorems

def normalizedTraceNoDefectQWLambdaInputFromTheorems :
    NormalizedTraceNoDefectQWLambdaInput where
  noDefect :=
    TraceFrontEndData.no_defect_qw_lambda_theorem_data_of_trace_front_parts
      (pkg := normalizedSourceObjectPackageFromTheorems)
      (fixedFront := normalizedFixedFrontEndFromTheorems)
      normalizedTraceSourceReadOffDataFromParts rfl HEq.rfl

structure NormalizedTraceRankPoleCdefOwnershipInput where
  rankPoleCdefOwnEveryRemainder :
    (L : RouteLedgers) ->
      SourceSignDefectClassification
        (RouteInputs.ofExpandedSourcePackage normalizedSourceObjectPackageFromTheorems)
        (SourceBackedFixedSTest.ofExpandedSourcePackage
          normalizedSourceObjectPackageFromTheorems normalizedFixedFrontEndFromTheorems)
        normalizedTraceLambdaInputFromTheorems.lambda L -> Prop

def normalizedTraceRankPoleCdefOwnershipInputFromTheorems :
    NormalizedTraceRankPoleCdefOwnershipInput where
  rankPoleCdefOwnEveryRemainder := by
    intro _L h
    exact TraceFrontEndData.trace_scale_owns_sign_defect_remainder h

def normalizedTraceSupportSquareQWLambdaReadOffFromParts :
    TraceFrontEndData.SourceTraceSupportSquareQWLambdaReadOff
      (pkg := normalizedSourceObjectPackageFromTheorems)
      (fixedFront := normalizedFixedFrontEndFromTheorems)
      (lambda := normalizedTraceLambdaInputFromTheorems.lambda)
      (ccm25ArithmeticPackage := normalizedTraceCCM25ArithmeticPackageFromTheorems)
      normalizedTraceSourceReadOffDataFromParts :=
  TraceFrontEndData.source_trace_support_square_qw_lambda_read_off_of_parts
    (pkg := normalizedSourceObjectPackageFromTheorems)
    (fixedFront := normalizedFixedFrontEndFromTheorems)
    normalizedTraceSourceReadOffDataFromParts rfl

def normalizedTraceFixedTupleSupportSquareQWLambdaRowFromTheorems :
    Source.S2B1FixedTupleSupportSquareQWLambdaRow
      normalizedSourceObjectPackageFromTheorems.cc20Trace.archimedeanSymbols
      normalizedSourceObjectPackageFromTheorems.ccm25.weilSymbols
      normalizedTraceLambdaInputFromTheorems.lambda
      normalizedTraceSourceReadOffDataFromParts.archimedeanTest
      (SourceBackedFixedSTest.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems
        normalizedFixedFrontEndFromTheorems).weilTest :=
  (Source.normalizedSeedSupportSquareQWLambdaReadOffOfQWLambdaScalarIdentification
    normalizedSeedFromTheorems
    normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols
    normalizedRemaindersFromTheorems
    normalizedTraceLambdaInputFromTheorems.lambda
    normalizedTraceSourceReadOffDataFromParts.archimedeanTest
    (SourceBackedFixedSTest.ofExpandedSourcePackage
      normalizedSourceObjectPackageFromTheorems
      normalizedFixedFrontEndFromTheorems).weilTest
    (normalizedActualScalarIdentificationFromTheoremBasePackage
      normalizedTraceLambdaInputFromTheorems.lambda
      normalizedTraceLambdaInputFromTheorems.oneLtLambda
      normalizedTraceSourceReadOffDataFromParts.archimedeanTest
      (SourceBackedFixedSTest.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems
        normalizedFixedFrontEndFromTheorems).weilTest)).toRow

def normalizedTraceFixedTupleRankZeroModeConstructorInputFromTheorems :
    Source.S2B1FixedTupleRankZeroModeConstructorInput
      normalizedSourceObjectPackageFromTheorems.cc20Trace.archimedeanSymbols
      normalizedSourceObjectPackageFromTheorems.ccm25.weilSymbols
      normalizedTraceLambdaInputFromTheorems.lambda
      normalizedTraceSourceReadOffDataFromParts.archimedeanTest
      (SourceBackedFixedSTest.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems
        normalizedFixedFrontEndFromTheorems).weilTest :=
  normalizedBaseFromTheorems.s2b1NormalizedSeedRankZeroModeConstructorInput
    normalizedTraceLambdaInputFromTheorems.lambda
    normalizedTraceLambdaInputFromTheorems.oneLtLambda
    normalizedTraceSourceReadOffDataFromParts.archimedeanTest
    (SourceBackedFixedSTest.ofExpandedSourcePackage
      normalizedSourceObjectPackageFromTheorems
      normalizedFixedFrontEndFromTheorems).weilTest

def normalizedTraceFixedTupleRankZeroModeRowFromTheorems :
    Source.S2B1FixedTupleRankZeroModeRow
      normalizedSourceObjectPackageFromTheorems.cc20Trace.archimedeanSymbols
      normalizedSourceObjectPackageFromTheorems.ccm25.weilSymbols
      normalizedTraceLambdaInputFromTheorems.lambda
      normalizedTraceSourceReadOffDataFromParts.archimedeanTest
      (SourceBackedFixedSTest.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems
        normalizedFixedFrontEndFromTheorems).weilTest :=
  normalizedTraceFixedTupleRankZeroModeConstructorInputFromTheorems.toRow

def normalizedTraceFixedTupleNoStripRankPoleConstructorInputFromTheorems :
    Source.S2B1FixedTupleNoStripRankPoleConstructorInput
      normalizedSourceObjectPackageFromTheorems.cc20Trace.archimedeanSymbols
      normalizedSourceObjectPackageFromTheorems.ccm25.weilSymbols
      normalizedTraceLambdaInputFromTheorems.lambda
      normalizedTraceSourceReadOffDataFromParts.archimedeanTest
      (SourceBackedFixedSTest.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems
        normalizedFixedFrontEndFromTheorems).weilTest :=
  normalizedBaseFromTheorems.s2b1NormalizedSeedNoStripRankPoleConstructorInput
    normalizedTraceLambdaInputFromTheorems.lambda
    normalizedTraceLambdaInputFromTheorems.oneLtLambda
    normalizedTraceSourceReadOffDataFromParts.archimedeanTest
    (SourceBackedFixedSTest.ofExpandedSourcePackage
      normalizedSourceObjectPackageFromTheorems
      normalizedFixedFrontEndFromTheorems).weilTest

def normalizedTraceFixedTupleNoStripRankPoleRowFromTheorems :
    Source.S2B1FixedTupleNoStripRankPoleRow
      normalizedSourceObjectPackageFromTheorems.cc20Trace.archimedeanSymbols
      normalizedSourceObjectPackageFromTheorems.ccm25.weilSymbols
      normalizedTraceLambdaInputFromTheorems.lambda
      normalizedTraceSourceReadOffDataFromParts.archimedeanTest
      (SourceBackedFixedSTest.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems
        normalizedFixedFrontEndFromTheorems).weilTest :=
  normalizedTraceFixedTupleNoStripRankPoleConstructorInputFromTheorems.toRow

def normalizedTraceFixedTupleEndpointStripCdefConstructorInputFromTheorems :
    Source.S2B1FixedTupleEndpointStripCdefConstructorInput
      normalizedSourceObjectPackageFromTheorems.cc20Trace.archimedeanSymbols
      normalizedSourceObjectPackageFromTheorems.ccm25.weilSymbols
      normalizedTraceLambdaInputFromTheorems.lambda
      normalizedTraceSourceReadOffDataFromParts.archimedeanTest
      (SourceBackedFixedSTest.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems
        normalizedFixedFrontEndFromTheorems).weilTest :=
  normalizedBaseFromTheorems.s2b1NormalizedSeedEndpointStripCdefConstructorInput
    normalizedTraceLambdaInputFromTheorems.lambda
    normalizedTraceLambdaInputFromTheorems.oneLtLambda
    normalizedTraceSourceReadOffDataFromParts.archimedeanTest
    (SourceBackedFixedSTest.ofExpandedSourcePackage
      normalizedSourceObjectPackageFromTheorems
      normalizedFixedFrontEndFromTheorems).weilTest

def normalizedTraceFixedTupleEndpointStripCdefRowFromTheorems :
    Source.S2B1FixedTupleEndpointStripCdefRow
      normalizedSourceObjectPackageFromTheorems.cc20Trace.archimedeanSymbols
      normalizedSourceObjectPackageFromTheorems.ccm25.weilSymbols
      normalizedTraceLambdaInputFromTheorems.lambda
      normalizedTraceSourceReadOffDataFromParts.archimedeanTest
      (SourceBackedFixedSTest.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems
        normalizedFixedFrontEndFromTheorems).weilTest :=
  normalizedTraceFixedTupleEndpointStripCdefConstructorInputFromTheorems.toRow

def normalizedTraceFixedTupleNoExtraBulkConstructorInputFromTheorems :
    Source.S2B1FixedTupleNoExtraBulkConstructorInput
      normalizedSourceObjectPackageFromTheorems.cc20Trace.archimedeanSymbols
      normalizedSourceObjectPackageFromTheorems.ccm25.weilSymbols
      normalizedTraceLambdaInputFromTheorems.lambda
      normalizedTraceSourceReadOffDataFromParts.archimedeanTest
      (SourceBackedFixedSTest.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems
        normalizedFixedFrontEndFromTheorems).weilTest :=
  normalizedBaseFromTheorems.s2b1NormalizedSeedNoExtraBulkConstructorInput
    normalizedTraceLambdaInputFromTheorems.lambda
    normalizedTraceLambdaInputFromTheorems.oneLtLambda
    normalizedTraceSourceReadOffDataFromParts.archimedeanTest
    (SourceBackedFixedSTest.ofExpandedSourcePackage
      normalizedSourceObjectPackageFromTheorems
      normalizedFixedFrontEndFromTheorems).weilTest

def normalizedTraceFixedTupleNoExtraBulkRowFromTheorems :
    Source.S2B1FixedTupleNoExtraBulkRow
      normalizedSourceObjectPackageFromTheorems.cc20Trace.archimedeanSymbols
      normalizedSourceObjectPackageFromTheorems.ccm25.weilSymbols
      normalizedTraceLambdaInputFromTheorems.lambda
      normalizedTraceSourceReadOffDataFromParts.archimedeanTest
      (SourceBackedFixedSTest.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems
        normalizedFixedFrontEndFromTheorems).weilTest :=
  normalizedTraceFixedTupleNoExtraBulkConstructorInputFromTheorems.toRow

def normalizedTraceFixedTupleNoHiddenFinitePartSubtractionConstructorInputFromTheorems :
    Source.S2B1FixedTupleNoHiddenFinitePartSubtractionConstructorInput
      normalizedSourceObjectPackageFromTheorems.cc20Trace.archimedeanSymbols
      normalizedSourceObjectPackageFromTheorems.ccm25.weilSymbols
      normalizedTraceLambdaInputFromTheorems.lambda
      normalizedTraceSourceReadOffDataFromParts.archimedeanTest
      (SourceBackedFixedSTest.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems
        normalizedFixedFrontEndFromTheorems).weilTest :=
  normalizedBaseFromTheorems.s2b1NormalizedSeedNoHiddenFinitePartSubtractionConstructorInput
    normalizedTraceLambdaInputFromTheorems.lambda
    normalizedTraceLambdaInputFromTheorems.oneLtLambda
    normalizedTraceSourceReadOffDataFromParts.archimedeanTest
    (SourceBackedFixedSTest.ofExpandedSourcePackage
      normalizedSourceObjectPackageFromTheorems
      normalizedFixedFrontEndFromTheorems).weilTest

def normalizedTraceFixedTupleNoHiddenFinitePartSubtractionRowFromTheorems :
    Source.S2B1FixedTupleNoHiddenFinitePartSubtractionRow
      normalizedSourceObjectPackageFromTheorems.cc20Trace.archimedeanSymbols
      normalizedSourceObjectPackageFromTheorems.ccm25.weilSymbols
      normalizedTraceLambdaInputFromTheorems.lambda
      normalizedTraceSourceReadOffDataFromParts.archimedeanTest
      (SourceBackedFixedSTest.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems
        normalizedFixedFrontEndFromTheorems).weilTest :=
  normalizedTraceFixedTupleNoHiddenFinitePartSubtractionConstructorInputFromTheorems.toRow

def normalizedTraceFixedTupleRemainingRowsPackageFromTheorems :
    Source.S2B1FixedTupleRemainingRowsPackage
      normalizedSourceObjectPackageFromTheorems.cc20Trace.archimedeanSymbols
      normalizedSourceObjectPackageFromTheorems.ccm25.weilSymbols
      normalizedTraceLambdaInputFromTheorems.lambda
      normalizedTraceSourceReadOffDataFromParts.archimedeanTest
      (SourceBackedFixedSTest.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems
        normalizedFixedFrontEndFromTheorems).weilTest where
  rankZeroModeRow :=
    normalizedTraceFixedTupleRankZeroModeRowFromTheorems
  noStripRankPoleRow :=
    normalizedTraceFixedTupleNoStripRankPoleRowFromTheorems
  endpointStripCdefRow :=
    normalizedTraceFixedTupleEndpointStripCdefRowFromTheorems
  noExtraBulkRow :=
    normalizedTraceFixedTupleNoExtraBulkRowFromTheorems
  noHiddenFinitePartSubtractionRow :=
    normalizedTraceFixedTupleNoHiddenFinitePartSubtractionRowFromTheorems

def normalizedTraceFixedTupleAnalyticExclusionFromTheorems :
    Source.S2B1TraceScaleFixedTupleAnalyticExclusionPackage
      normalizedSourceObjectPackageFromTheorems.cc20Trace.archimedeanSymbols
      normalizedSourceObjectPackageFromTheorems.ccm25.weilSymbols
      normalizedTraceLambdaInputFromTheorems.lambda
      normalizedTraceSourceReadOffDataFromParts.archimedeanTest
      (SourceBackedFixedSTest.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems
        normalizedFixedFrontEndFromTheorems).weilTest :=
  Source.S2B1FixedTupleRemainingRowsPackage.toAnalyticExclusionPackage
    normalizedTraceFixedTupleRemainingRowsPackageFromTheorems
    normalizedTraceLambdaInputFromTheorems.oneLtLambda
    normalizedTraceFixedTupleSupportSquareQWLambdaRowFromTheorems

def normalizedTraceNoBulkSourceWitnessFromParts :
    Source.CC20CCMTraceScaleNoBulkWitness
      normalizedSourceObjectPackageFromTheorems.cc20Trace.archimedeanSymbols
      normalizedSourceObjectPackageFromTheorems.ccm25.weilSymbols
      normalizedTraceLambdaInputFromTheorems.lambda
      normalizedTraceSourceReadOffDataFromParts.archimedeanTest
      (SourceBackedFixedSTest.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems
        normalizedFixedFrontEndFromTheorems).weilTest :=
  normalizedS2B1NoBulkRowsFromTheorems.witness
    normalizedTraceLambdaInputFromTheorems.lambda
    normalizedTraceLambdaInputFromTheorems.oneLtLambda
    normalizedTraceSourceReadOffDataFromParts.archimedeanTest
    (SourceBackedFixedSTest.ofExpandedSourcePackage
      normalizedSourceObjectPackageFromTheorems
      normalizedFixedFrontEndFromTheorems).weilTest

structure NormalizedTracePositiveTraceDecompositionInput where
  positiveTraceDecomposesIntoQWLambdaRankPoleCdef : Prop
  positiveTraceDecomposesIntoQWLambdaRankPoleCdefHolds :
    positiveTraceDecomposesIntoQWLambdaRankPoleCdef

def normalizedTracePositiveTraceDecompositionInputFromTheorems :
    NormalizedTracePositiveTraceDecompositionInput where
  positiveTraceDecomposesIntoQWLambdaRankPoleCdef :=
    normalizedTraceOrdinarySupportSquareInputFromTheorems.ordinary.ordinaryTraceMatchesSupportSquare ∧
      normalizedSourceObjectPackageFromTheorems.cc20Trace.archimedeanSymbols.supportSquareTrace
          normalizedTraceSourceReadOffDataFromParts.archimedeanTest =
        normalizedSourceObjectPackageFromTheorems.ccm25.weilSymbols.qwLambda
          normalizedTraceLambdaInputFromTheorems.lambda
          (SourceBackedFixedSTest.ofExpandedSourcePackage
            normalizedSourceObjectPackageFromTheorems
            normalizedFixedFrontEndFromTheorems).weilTest
          (SourceBackedFixedSTest.ofExpandedSourcePackage
            normalizedSourceObjectPackageFromTheorems
            normalizedFixedFrontEndFromTheorems).weilTest ∧
      normalizedTraceFixedTupleRemainingRowsPackageFromTheorems.rankZeroModeRow.rankZeroModeChannelClassified ∧
      normalizedTraceFixedTupleRemainingRowsPackageFromTheorems.noStripRankPoleRow.noStripPostQRemainderRankPoleClassified ∧
      normalizedTraceFixedTupleRemainingRowsPackageFromTheorems.endpointStripCdefRow.endpointStripBulkClassifiedIntoCdef ∧
      normalizedTraceFixedTupleRemainingRowsPackageFromTheorems.endpointStripCdefRow.endpointStripBoundaryTermsClassified ∧
      normalizedTraceFixedTupleRemainingRowsPackageFromTheorems.endpointStripCdefRow.sourceSeriesTailClassifiedIntoCdef ∧
      normalizedTraceFixedTupleRemainingRowsPackageFromTheorems.endpointStripCdefRow.cdefExhaustionOwnsEndpointStrip
  positiveTraceDecomposesIntoQWLambdaRankPoleCdefHolds :=
    ⟨normalizedTraceOrdinarySupportSquareInputFromTheorems.ordinary.ordinaryTraceMatchesSupportSquareHolds,
      normalizedTraceFixedTupleSupportSquareQWLambdaRowFromTheorems.supportSquareMainTermEqualsQWLambda,
      normalizedTraceFixedTupleRemainingRowsPackageFromTheorems.rankZeroModeRow.rankZeroModeChannelClassifiedHolds,
      normalizedTraceFixedTupleRemainingRowsPackageFromTheorems.noStripRankPoleRow.noStripPostQRemainderRankPoleClassifiedHolds,
      normalizedTraceFixedTupleRemainingRowsPackageFromTheorems.endpointStripCdefRow.endpointStripBulkClassifiedIntoCdefHolds,
      normalizedTraceFixedTupleRemainingRowsPackageFromTheorems.endpointStripCdefRow.endpointStripBoundaryTermsClassifiedHolds,
      normalizedTraceFixedTupleRemainingRowsPackageFromTheorems.endpointStripCdefRow.sourceSeriesTailClassifiedIntoCdefHolds,
      normalizedTraceFixedTupleRemainingRowsPackageFromTheorems.endpointStripCdefRow.cdefExhaustionOwnsEndpointStripHolds⟩

structure NormalizedTraceNoExtraBulkTermInput where
  noBulkScaleTermOutsideLedger : Prop
  noBulkScaleTermOutsideLedgerHolds : noBulkScaleTermOutsideLedger

def normalizedTraceNoExtraBulkTermInputFromTheorems :
    NormalizedTraceNoExtraBulkTermInput where
  noBulkScaleTermOutsideLedger :=
    normalizedTraceFixedTupleRemainingRowsPackageFromTheorems.noExtraBulkRow.noExtraBulkScaleTermExcluded
  noBulkScaleTermOutsideLedgerHolds :=
    normalizedTraceFixedTupleRemainingRowsPackageFromTheorems.noExtraBulkRow.noExtraBulkScaleTermExcludedHolds

structure NormalizedTraceNoHiddenFinitePartInput where
  noHiddenFinitePartSubtraction : Prop
  noHiddenFinitePartSubtractionHolds : noHiddenFinitePartSubtraction

def normalizedTraceNoHiddenFinitePartInputFromTheorems :
    NormalizedTraceNoHiddenFinitePartInput where
  noHiddenFinitePartSubtraction :=
    normalizedTraceFixedTupleRemainingRowsPackageFromTheorems.noHiddenFinitePartSubtractionRow.noHiddenFinitePartSubtractionExcluded
  noHiddenFinitePartSubtractionHolds :=
    normalizedTraceFixedTupleRemainingRowsPackageFromTheorems.noHiddenFinitePartSubtractionRow.noHiddenFinitePartSubtractionExcludedHolds

structure NormalizedTraceNoExtraBulkScaleTermInput where
  noExtraBulkScaleTerm : Prop
  noExtraBulkScaleTermHolds : noExtraBulkScaleTerm

def normalizedTraceNoExtraBulkScaleTermInputFromTheorems :
    NormalizedTraceNoExtraBulkScaleTermInput where
  noExtraBulkScaleTerm :=
    normalizedTracePositiveTraceDecompositionInputFromTheorems.positiveTraceDecomposesIntoQWLambdaRankPoleCdef ∧
      normalizedTraceNoExtraBulkTermInputFromTheorems.noBulkScaleTermOutsideLedger ∧
        normalizedTraceNoHiddenFinitePartInputFromTheorems.noHiddenFinitePartSubtraction
  noExtraBulkScaleTermHolds :=
    ⟨normalizedTracePositiveTraceDecompositionInputFromTheorems.positiveTraceDecomposesIntoQWLambdaRankPoleCdefHolds,
      normalizedTraceNoExtraBulkTermInputFromTheorems.noBulkScaleTermOutsideLedgerHolds,
      normalizedTraceNoHiddenFinitePartInputFromTheorems.noHiddenFinitePartSubtractionHolds⟩

structure NormalizedTraceScaleNoMissingBulkInput where
  ordinarySupportSquare : NormalizedTraceOrdinarySupportSquareInput
  noDefectQWLambda : NormalizedTraceNoDefectQWLambdaInput
  rankPoleCdefOwnership : NormalizedTraceRankPoleCdefOwnershipInput
  noExtraBulk : NormalizedTraceNoExtraBulkScaleTermInput

def normalizedTraceScaleNoMissingBulkInputFromTheorems :
    NormalizedTraceScaleNoMissingBulkInput where
  ordinarySupportSquare :=
    normalizedTraceOrdinarySupportSquareInputFromTheorems
  noDefectQWLambda :=
    normalizedTraceNoDefectQWLambdaInputFromTheorems
  rankPoleCdefOwnership :=
    normalizedTraceRankPoleCdefOwnershipInputFromTheorems
  noExtraBulk :=
    normalizedTraceNoExtraBulkScaleTermInputFromTheorems

def normalizedTraceScaleNoMissingBulkDataFromTheorems :
    TraceScaleNoMissingBulkData
      normalizedSourceObjectPackageFromTheorems normalizedFixedFrontEndFromTheorems
      normalizedTraceLambdaInputFromTheorems.lambda
      normalizedTraceCCM25ArithmeticPackageFromTheorems :=
  trace_scale_no_missing_bulk_of_scalar_theorem_data
    normalizedTraceScaleNoMissingBulkInputFromTheorems.ordinarySupportSquare.ordinary
    normalizedTraceScaleNoMissingBulkInputFromTheorems.noDefectQWLambda.noDefect
    normalizedTraceScaleNoMissingBulkInputFromTheorems.rankPoleCdefOwnership.rankPoleCdefOwnEveryRemainder
    normalizedTraceScaleNoMissingBulkInputFromTheorems.noExtraBulk.noExtraBulkScaleTerm
    normalizedTraceScaleNoMissingBulkInputFromTheorems.noExtraBulk.noExtraBulkScaleTermHolds

structure NormalizedTraceFrontEndSourceInput where
  quotientCompatibility : NormalizedTraceQuotientCompatibilityInput
  supportSquareTransport : NormalizedTraceSupportSquareTransportInput
  readOffBridges : NormalizedTraceReadOffBridgeInput
  noMissingBulk : NormalizedTraceScaleNoMissingBulkInput

def normalizedTraceFrontEndSourceInputFromTheorems :
    NormalizedTraceFrontEndSourceInput where
  quotientCompatibility := normalizedTraceQuotientCompatibilityInputFromTheorems
  supportSquareTransport := normalizedTraceSupportSquareTransportInputFromTheorems
  readOffBridges := normalizedTraceReadOffBridgeInputFromTheorems
  noMissingBulk := normalizedTraceScaleNoMissingBulkInputFromTheorems

def normalizedTraceDataFromTheorems :
    TraceFrontEndData
      normalizedSourceObjectPackageFromTheorems
      normalizedFixedFrontEndFromTheorems :=
  { lambda := normalizedTraceLambdaInputFromTheorems.lambda
    oneLtLambda := normalizedTraceLambdaInputFromTheorems.oneLtLambda
    ccm25ArithmeticPackage :=
      normalizedTraceCCM25ArithmeticPackageFromTheorems
    testAndQuotientCompatibility :=
      normalizedTraceFrontEndSourceInputFromTheorems.quotientCompatibility.testAndQuotientCompatibility
    fixedSSupportSquareTransport :=
      normalizedTraceFrontEndSourceInputFromTheorems.supportSquareTransport.fixedSSupportSquareTransport
    fullTraceReadOffBridge :=
      normalizedTraceFrontEndSourceInputFromTheorems.readOffBridges.full.fullTraceReadOffBridge
    restrictedTraceReadOffBridge :=
      normalizedTraceFrontEndSourceInputFromTheorems.readOffBridges.restricted.restrictedTraceReadOffBridge
    traceScaleNoMissingBulk :=
      normalizedTraceScaleNoMissingBulkDataFromTheorems }

def normalizedFrontEndPackageFromTheorems :
    TraceFrontEndData.SourceFixedTraceFrontEndPackage
      normalizedSourceObjectPackageFromTheorems :=
  TraceFrontEndData.source_fixed_trace_front_end_package_of_trace_data
    normalizedSourceObjectPackageFromTheorems
    normalizedFixedFrontEndFromTheorems
    normalizedTraceDataFromTheorems

theorem normalizedFrontEndPackageSourceTraceReadOffData_eq :
    normalizedFrontEndPackageFromTheorems.sourceTraceReadOffData =
      normalizedTraceSourceReadOffDataFromParts :=
  rfl

abbrev normalizedTraceFrontEndFromTheorems :
    ExpandedSourceTraceReadOffFrontEnd
      normalizedSourceObjectPackageFromTheorems
      normalizedFixedFrontEndFromTheorems :=
  normalizedFrontEndPackageFromTheorems.traceFront

noncomputable abbrev normalizedScalarSeedFromTheorems :
    Source.CC20Concrete.TraceScale.NormalizedScalarTraceScaleSymbols :=
  TraceFrontEndData.normalizedRestrictedScalarTraceSeedOfTraceData
    normalizedBaseFromTheorems normalizedCommonFromTheorems
    normalizedCCM24FromTheorems normalizedSeedFromTheorems
    normalizedRemaindersFromTheorems normalizedRhExitFromTheorems
    normalizedBridgesFromTheorems normalizedFixedDataFromTheorems
    normalizedTraceDataFromTheorems

structure NormalizedScalarCC20RemainderRowsInput where
  rows :
    Source.NormalizedScalarCC20RemainderRows
      normalizedScalarSeedFromTheorems

noncomputable def normalizedScalarCC20RemainderRowsInputFromTheorems :
    NormalizedScalarCC20RemainderRowsInput where
  rows :=
    normalizedSourceObjectTheoremBaseInputFromTheorems.scalarCC20RemainderRows
      normalizedScalarSeedFromTheorems

noncomputable def normalizedScalarFinitePartSourceNormalFormDataFromTheorems
    (lambda : ℝ) (hlambda : 1 < lambda)
    (archimedeanTest :
      (Source.CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
        (Source.CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
          normalizedScalarSeedFromTheorems)).archimedeanSymbols.Test)
    (weilTest : TestFunction) :
    Source.S2B1FinitePartSourceNormalFormData
      (Source.CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
        (Source.CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
          normalizedScalarSeedFromTheorems)).archimedeanSymbols
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols
      lambda archimedeanTest weilTest :=
  Source.NormalizedSourceObjectTheoremBaseInput.scalarFinitePartSourceNormalFormDataAt
    normalizedSourceObjectTheoremBaseInputFromTheorems
    normalizedScalarSeedFromTheorems lambda hlambda archimedeanTest weilTest

structure NormalizedScalarTraceLegalityRemainderInput where
  sourceTraceTest :
    (Source.CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
      (Source.CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
        normalizedScalarSeedFromTheorems)).archimedeanSymbols.Test
  sourceCC20TraceTestCompatibility : Prop
  sourceOperatorIdentity : Prop
  sourceHilbertSchmidtGate :
    ∀ g :
      (Source.CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
        (Source.CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
          normalizedScalarSeedFromTheorems)).archimedeanSymbols.Test,
        ArchimedeanTraceSymbols.hilbertSchmidtGate
          (Source.CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
            (Source.CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
              normalizedScalarSeedFromTheorems)).archimedeanSymbols
          g
  sourcePerMoveCyclicityLedger : Prop
  sourceNoDefectTraceReadOff : Prop

structure NormalizedScalarTraceLegalitySourceRowsInput where
  sourceTraceTest :
    (Source.CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
      (Source.CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
        normalizedScalarSeedFromTheorems)).archimedeanSymbols.Test
  sourceCC20TraceTestCompatibility : Prop
  sourceOperatorIdentity : Prop
  sourceHilbertSchmidtGate :
    ∀ g :
      (Source.CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
        (Source.CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
          normalizedScalarSeedFromTheorems)).archimedeanSymbols.Test,
        ArchimedeanTraceSymbols.hilbertSchmidtGate
          (Source.CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
            (Source.CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
              normalizedScalarSeedFromTheorems)).archimedeanSymbols
          g
  sourcePerMoveCyclicityLedger : Prop
  sourceNoDefectTraceReadOff : Prop

structure NormalizedScalarTraceTestSelectionInput where
  sourceTraceTest :
    (Source.CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
      (Source.CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
        normalizedScalarSeedFromTheorems)).archimedeanSymbols.Test
  sourceCC20TraceTestCompatibility : Prop

noncomputable def normalizedScalarTraceTestSelectionInputFromTheorems :
    NormalizedScalarTraceTestSelectionInput where
  sourceTraceTest :=
    normalizedScalarCC20RemainderRowsInputFromTheorems.rows.sourceTraceTest
  sourceCC20TraceTestCompatibility :=
    normalizedScalarCC20RemainderRowsInputFromTheorems.rows.sourceCC20TraceTestCompatibility

structure NormalizedScalarTraceOperatorIdentityInput where
  sourceOperatorIdentity : Prop

noncomputable def normalizedScalarTraceOperatorIdentityInputFromTheorems :
    NormalizedScalarTraceOperatorIdentityInput where
  sourceOperatorIdentity :=
    normalizedScalarCC20RemainderRowsInputFromTheorems.rows.sourceOperatorIdentity

structure NormalizedScalarTraceLegalityGateInput where
  sourceHilbertSchmidtGate :
    ∀ g :
      (Source.CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
        (Source.CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
          normalizedScalarSeedFromTheorems)).archimedeanSymbols.Test,
        ArchimedeanTraceSymbols.hilbertSchmidtGate
          (Source.CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
            (Source.CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
              normalizedScalarSeedFromTheorems)).archimedeanSymbols
          g
  sourcePerMoveCyclicityLedger : Prop

noncomputable def normalizedScalarTraceLegalityGateInputFromTheorems :
    NormalizedScalarTraceLegalityGateInput where
  sourceHilbertSchmidtGate :=
    normalizedScalarCC20RemainderRowsInputFromTheorems.rows.sourceHilbertSchmidtGate
  sourcePerMoveCyclicityLedger :=
    normalizedScalarCC20RemainderRowsInputFromTheorems.rows.sourcePerMoveCyclicityLedger

structure NormalizedScalarTraceNoDefectReadOffInput where
  sourceNoDefectTraceReadOff : Prop

noncomputable def normalizedScalarTraceNoDefectReadOffInputFromTheorems :
    NormalizedScalarTraceNoDefectReadOffInput where
  sourceNoDefectTraceReadOff :=
    normalizedScalarCC20RemainderRowsInputFromTheorems.rows.sourceNoDefectTraceReadOff

noncomputable def normalizedScalarTraceLegalitySourceRowsInputFromTheorems :
    NormalizedScalarTraceLegalitySourceRowsInput where
  sourceTraceTest :=
    normalizedScalarTraceTestSelectionInputFromTheorems.sourceTraceTest
  sourceCC20TraceTestCompatibility :=
    normalizedScalarTraceTestSelectionInputFromTheorems.sourceCC20TraceTestCompatibility
  sourceOperatorIdentity :=
    normalizedScalarTraceOperatorIdentityInputFromTheorems.sourceOperatorIdentity
  sourceHilbertSchmidtGate :=
    normalizedScalarTraceLegalityGateInputFromTheorems.sourceHilbertSchmidtGate
  sourcePerMoveCyclicityLedger :=
    normalizedScalarTraceLegalityGateInputFromTheorems.sourcePerMoveCyclicityLedger
  sourceNoDefectTraceReadOff :=
    normalizedScalarTraceNoDefectReadOffInputFromTheorems.sourceNoDefectTraceReadOff

noncomputable def normalizedScalarTraceLegalityRemainderInputFromTheorems :
    NormalizedScalarTraceLegalityRemainderInput where
  sourceTraceTest :=
    normalizedScalarTraceLegalitySourceRowsInputFromTheorems.sourceTraceTest
  sourceCC20TraceTestCompatibility :=
    normalizedScalarTraceLegalitySourceRowsInputFromTheorems.sourceCC20TraceTestCompatibility
  sourceOperatorIdentity :=
    normalizedScalarTraceLegalitySourceRowsInputFromTheorems.sourceOperatorIdentity
  sourceHilbertSchmidtGate :=
    normalizedScalarTraceLegalitySourceRowsInputFromTheorems.sourceHilbertSchmidtGate
  sourcePerMoveCyclicityLedger :=
    normalizedScalarTraceLegalitySourceRowsInputFromTheorems.sourcePerMoveCyclicityLedger
  sourceNoDefectTraceReadOff :=
    normalizedScalarTraceLegalitySourceRowsInputFromTheorems.sourceNoDefectTraceReadOff

structure NormalizedScalarRemainderTransportInput where
  sourceRemainderOrientationWInftyEqLMinusD : Prop
  sourceRemainderOrientationWInftyEqSMinusE : Prop
  sourceRemainderObject : Prop
  sourceRemainderAfterQ : Prop
  cc20PostQRemainderFixedSSoninTransport : Prop
  sourceProjectionDefectNormalForm : Prop
  sourceRankPoleLedgerIdentification : Prop
  sourceEndpointStripRemainderCdefDomination : Prop

structure NormalizedScalarRemainderOrientationInput where
  sourceRemainderOrientationWInftyEqLMinusD : Prop
  sourceRemainderOrientationWInftyEqSMinusE : Prop

noncomputable def normalizedScalarRemainderOrientationInputFromTheorems :
    NormalizedScalarRemainderOrientationInput where
  sourceRemainderOrientationWInftyEqLMinusD :=
    normalizedScalarCC20RemainderRowsInputFromTheorems.rows.sourceRemainderOrientationWInftyEqLMinusD
  sourceRemainderOrientationWInftyEqSMinusE :=
    normalizedScalarCC20RemainderRowsInputFromTheorems.rows.sourceRemainderOrientationWInftyEqSMinusE

structure NormalizedScalarRemainderObjectAfterQInput where
  sourceRemainderObject : Prop
  sourceRemainderAfterQ : Prop

noncomputable def normalizedScalarRemainderObjectAfterQInputFromTheorems :
    NormalizedScalarRemainderObjectAfterQInput where
  sourceRemainderObject :=
    normalizedScalarCC20RemainderRowsInputFromTheorems.rows.sourceRemainderObject
  sourceRemainderAfterQ :=
    normalizedScalarCC20RemainderRowsInputFromTheorems.rows.sourceRemainderAfterQ

structure NormalizedScalarPostQTransportInput where
  cc20PostQRemainderFixedSSoninTransport : Prop

noncomputable def normalizedScalarPostQTransportInputFromTheorems :
    NormalizedScalarPostQTransportInput where
  cc20PostQRemainderFixedSSoninTransport :=
    normalizedScalarCC20RemainderRowsInputFromTheorems.rows.cc20PostQRemainderFixedSSoninTransport

structure NormalizedScalarProjectionRankCdefInput where
  sourceProjectionDefectNormalForm : Prop
  sourceRankPoleLedgerIdentification : Prop
  sourceEndpointStripRemainderCdefDomination : Prop

noncomputable def normalizedScalarProjectionRankCdefInputFromTheorems :
    NormalizedScalarProjectionRankCdefInput where
  sourceProjectionDefectNormalForm :=
    normalizedScalarCC20RemainderRowsInputFromTheorems.rows.sourceProjectionDefectNormalForm
  sourceRankPoleLedgerIdentification :=
    normalizedScalarCC20RemainderRowsInputFromTheorems.rows.sourceRankPoleLedgerIdentification
  sourceEndpointStripRemainderCdefDomination :=
    normalizedScalarCC20RemainderRowsInputFromTheorems.rows.sourceEndpointStripRemainderCdefDomination

noncomputable def normalizedScalarRemainderTransportInputFromTheorems :
    NormalizedScalarRemainderTransportInput where
  sourceRemainderOrientationWInftyEqLMinusD :=
    normalizedScalarRemainderOrientationInputFromTheorems.sourceRemainderOrientationWInftyEqLMinusD
  sourceRemainderOrientationWInftyEqSMinusE :=
    normalizedScalarRemainderOrientationInputFromTheorems.sourceRemainderOrientationWInftyEqSMinusE
  sourceRemainderObject :=
    normalizedScalarRemainderObjectAfterQInputFromTheorems.sourceRemainderObject
  sourceRemainderAfterQ :=
    normalizedScalarRemainderObjectAfterQInputFromTheorems.sourceRemainderAfterQ
  cc20PostQRemainderFixedSSoninTransport :=
    normalizedScalarPostQTransportInputFromTheorems.cc20PostQRemainderFixedSSoninTransport
  sourceProjectionDefectNormalForm :=
    normalizedScalarProjectionRankCdefInputFromTheorems.sourceProjectionDefectNormalForm
  sourceRankPoleLedgerIdentification :=
    normalizedScalarProjectionRankCdefInputFromTheorems.sourceRankPoleLedgerIdentification
  sourceEndpointStripRemainderCdefDomination :=
    normalizedScalarProjectionRankCdefInputFromTheorems.sourceEndpointStripRemainderCdefDomination

structure NormalizedScalarNoBulkRemainderInput where
  noBulkScaleTermOutsideLedger : Prop
  noHiddenFinitePartSubtraction : Prop
  noBulkScaleTermOutsideLedgerHolds : noBulkScaleTermOutsideLedger
  noHiddenFinitePartSubtractionHolds : noHiddenFinitePartSubtraction
  noBulkScaleTermOutsideLedgerAt :
    ℝ →
      (Source.CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
        (Source.CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
          normalizedScalarSeedFromTheorems)).archimedeanSymbols.Test →
        TestFunction → Prop
  noHiddenFinitePartSubtractionAt :
    ℝ →
      (Source.CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
        (Source.CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
          normalizedScalarSeedFromTheorems)).archimedeanSymbols.Test →
        TestFunction → Prop
  noBulkScaleTermOutsideLedgerAtHolds :
    ∀ lambda : ℝ, 1 < lambda →
      ∀ archimedeanTest :
        (Source.CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
          (Source.CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
            normalizedScalarSeedFromTheorems)).archimedeanSymbols.Test,
        ∀ weilTest : TestFunction,
          noBulkScaleTermOutsideLedgerAt lambda archimedeanTest weilTest
  noHiddenFinitePartSubtractionAtHolds :
    ∀ lambda : ℝ, 1 < lambda →
      ∀ archimedeanTest :
        (Source.CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
          (Source.CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
            normalizedScalarSeedFromTheorems)).archimedeanSymbols.Test,
        ∀ weilTest : TestFunction,
          noHiddenFinitePartSubtractionAt lambda archimedeanTest weilTest

structure NormalizedScalarNoBulkStaticRowsInput where
  noBulkScaleTermOutsideLedger : Prop
  noHiddenFinitePartSubtraction : Prop
  noBulkScaleTermOutsideLedgerHolds : noBulkScaleTermOutsideLedger
  noHiddenFinitePartSubtractionHolds : noHiddenFinitePartSubtraction

noncomputable def normalizedScalarNoBulkStaticRowsInputFromTheorems :
    NormalizedScalarNoBulkStaticRowsInput where
  noBulkScaleTermOutsideLedger :=
    normalizedScalarCC20RemainderRowsInputFromTheorems.rows.noBulkScaleTermOutsideLedger
  noHiddenFinitePartSubtraction :=
    ∃ hlambda : 1 < (2 : ℝ),
      Source.S2B1FinitePartScalarInterface.finitePartNormalizationFixedStatement
        ((normalizedScalarFinitePartSourceNormalFormDataFromTheorems
          2 hlambda
          normalizedScalarCC20RemainderRowsInputFromTheorems.rows.sourceTraceTest
          normalizedCommonFromTheorems.commonTest.sourceTest).sourceScalars.toScalarInterface) ∧
      Source.S2B1FinitePartScalarInterface.noSubtractedFinitePartTermStatement
        ((normalizedScalarFinitePartSourceNormalFormDataFromTheorems
          2 hlambda
          normalizedScalarCC20RemainderRowsInputFromTheorems.rows.sourceTraceTest
          normalizedCommonFromTheorems.commonTest.sourceTest).sourceScalars.toScalarInterface)
  noBulkScaleTermOutsideLedgerHolds :=
    normalizedScalarCC20RemainderRowsInputFromTheorems.rows.noBulkScaleTermOutsideLedgerHolds
  noHiddenFinitePartSubtractionHolds :=
    ⟨by norm_num,
      (normalizedScalarFinitePartSourceNormalFormDataFromTheorems
        2 (by norm_num)
        normalizedScalarCC20RemainderRowsInputFromTheorems.rows.sourceTraceTest
        normalizedCommonFromTheorems.commonTest.sourceTest).finitePartNormalizationFixedHolds,
      (normalizedScalarFinitePartSourceNormalFormDataFromTheorems
        2 (by norm_num)
        normalizedScalarCC20RemainderRowsInputFromTheorems.rows.sourceTraceTest
        normalizedCommonFromTheorems.commonTest.sourceTest).noSubtractedFinitePartTermHolds⟩

structure NormalizedScalarNoBulkSameCutoffRowsInput where
  noBulkScaleTermOutsideLedgerAt :
    ℝ →
      (Source.CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
        (Source.CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
          normalizedScalarSeedFromTheorems)).archimedeanSymbols.Test →
        TestFunction → Prop
  noHiddenFinitePartSubtractionAt :
    ℝ →
      (Source.CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
        (Source.CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
          normalizedScalarSeedFromTheorems)).archimedeanSymbols.Test →
        TestFunction → Prop
  noBulkScaleTermOutsideLedgerAtHolds :
    ∀ lambda : ℝ, 1 < lambda →
      ∀ archimedeanTest :
        (Source.CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
          (Source.CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
            normalizedScalarSeedFromTheorems)).archimedeanSymbols.Test,
        ∀ weilTest : TestFunction,
          noBulkScaleTermOutsideLedgerAt lambda archimedeanTest weilTest
  noHiddenFinitePartSubtractionAtHolds :
    ∀ lambda : ℝ, 1 < lambda →
      ∀ archimedeanTest :
        (Source.CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
          (Source.CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
            normalizedScalarSeedFromTheorems)).archimedeanSymbols.Test,
        ∀ weilTest : TestFunction,
          noHiddenFinitePartSubtractionAt lambda archimedeanTest weilTest

noncomputable def normalizedScalarNoBulkSameCutoffRowsInputFromTheorems :
    NormalizedScalarNoBulkSameCutoffRowsInput where
  noBulkScaleTermOutsideLedgerAt :=
    normalizedScalarCC20RemainderRowsInputFromTheorems.rows.noBulkScaleTermOutsideLedgerAt
  noHiddenFinitePartSubtractionAt :=
    fun lambda archimedeanTest weilTest =>
      ∃ hlambda : 1 < lambda,
        Source.S2B1FinitePartScalarInterface.finitePartNormalizationFixedStatement
          ((normalizedScalarFinitePartSourceNormalFormDataFromTheorems
            lambda hlambda archimedeanTest weilTest).sourceScalars.toScalarInterface) ∧
        Source.S2B1FinitePartScalarInterface.noSubtractedFinitePartTermStatement
          ((normalizedScalarFinitePartSourceNormalFormDataFromTheorems
            lambda hlambda archimedeanTest weilTest).sourceScalars.toScalarInterface)
  noBulkScaleTermOutsideLedgerAtHolds :=
    normalizedScalarCC20RemainderRowsInputFromTheorems.rows.noBulkScaleTermOutsideLedgerAtHolds
  noHiddenFinitePartSubtractionAtHolds :=
    by
      intro lambda hlambda archimedeanTest weilTest
      exact
        ⟨hlambda,
          (normalizedScalarFinitePartSourceNormalFormDataFromTheorems
            lambda hlambda archimedeanTest weilTest).finitePartNormalizationFixedHolds,
          (normalizedScalarFinitePartSourceNormalFormDataFromTheorems
            lambda hlambda archimedeanTest weilTest).noSubtractedFinitePartTermHolds⟩

noncomputable def normalizedScalarNoBulkRemainderInputFromTheorems :
    NormalizedScalarNoBulkRemainderInput where
  noBulkScaleTermOutsideLedger :=
    normalizedScalarNoBulkStaticRowsInputFromTheorems.noBulkScaleTermOutsideLedger
  noHiddenFinitePartSubtraction :=
    normalizedScalarNoBulkStaticRowsInputFromTheorems.noHiddenFinitePartSubtraction
  noBulkScaleTermOutsideLedgerHolds :=
    normalizedScalarNoBulkStaticRowsInputFromTheorems.noBulkScaleTermOutsideLedgerHolds
  noHiddenFinitePartSubtractionHolds :=
    normalizedScalarNoBulkStaticRowsInputFromTheorems.noHiddenFinitePartSubtractionHolds
  noBulkScaleTermOutsideLedgerAt :=
    normalizedScalarNoBulkSameCutoffRowsInputFromTheorems.noBulkScaleTermOutsideLedgerAt
  noHiddenFinitePartSubtractionAt :=
    normalizedScalarNoBulkSameCutoffRowsInputFromTheorems.noHiddenFinitePartSubtractionAt
  noBulkScaleTermOutsideLedgerAtHolds :=
    normalizedScalarNoBulkSameCutoffRowsInputFromTheorems.noBulkScaleTermOutsideLedgerAtHolds
  noHiddenFinitePartSubtractionAtHolds :=
    normalizedScalarNoBulkSameCutoffRowsInputFromTheorems.noHiddenFinitePartSubtractionAtHolds

structure NormalizedScalarDefectBoundedComparisonInput where
  noHiddenPositiveDefectOutsideCdef : Prop
  sourceBoundedComparisonTraceIdealTransport : Prop

structure NormalizedScalarNoHiddenPositiveDefectInput where
  noHiddenPositiveDefectOutsideCdef : Prop

noncomputable def normalizedScalarNoHiddenPositiveDefectInputFromTheorems :
    NormalizedScalarNoHiddenPositiveDefectInput where
  noHiddenPositiveDefectOutsideCdef :=
    normalizedScalarCC20RemainderRowsInputFromTheorems.rows.noHiddenPositiveDefectOutsideCdef

structure NormalizedScalarBoundedComparisonTransportInput where
  sourceBoundedComparisonTraceIdealTransport : Prop

noncomputable def normalizedScalarBoundedComparisonTransportInputFromTheorems :
    NormalizedScalarBoundedComparisonTransportInput where
  sourceBoundedComparisonTraceIdealTransport :=
    normalizedScalarCC20RemainderRowsInputFromTheorems.rows.sourceBoundedComparisonTraceIdealTransport

noncomputable def normalizedScalarDefectBoundedComparisonInputFromTheorems :
    NormalizedScalarDefectBoundedComparisonInput where
  noHiddenPositiveDefectOutsideCdef :=
    normalizedScalarNoHiddenPositiveDefectInputFromTheorems.noHiddenPositiveDefectOutsideCdef
  sourceBoundedComparisonTraceIdealTransport :=
    normalizedScalarBoundedComparisonTransportInputFromTheorems.sourceBoundedComparisonTraceIdealTransport

structure NormalizedScalarRemainderInputData where
  traceLegality : NormalizedScalarTraceLegalityRemainderInput
  transport : NormalizedScalarRemainderTransportInput
  noBulk : NormalizedScalarNoBulkRemainderInput
  boundedComparison : NormalizedScalarDefectBoundedComparisonInput

noncomputable def normalizedScalarRemainderInputDataFromTheorems :
    NormalizedScalarRemainderInputData where
  traceLegality := normalizedScalarTraceLegalityRemainderInputFromTheorems
  transport := normalizedScalarRemainderTransportInputFromTheorems
  noBulk := normalizedScalarNoBulkRemainderInputFromTheorems
  boundedComparison := normalizedScalarDefectBoundedComparisonInputFromTheorems

noncomputable def normalizedScalarRemaindersFromTheorems :
    Source.CC20Concrete.TraceScale.CC20TracePackageRemainderData
      (Source.CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
        normalizedScalarSeedFromTheorems) where
  sourceTraceTest :=
    normalizedScalarRemainderInputDataFromTheorems.traceLegality.sourceTraceTest
  sourceCC20TraceTestCompatibility :=
    normalizedScalarRemainderInputDataFromTheorems.traceLegality.sourceCC20TraceTestCompatibility
  sourceOperatorIdentity :=
    normalizedScalarRemainderInputDataFromTheorems.traceLegality.sourceOperatorIdentity
  sourceHilbertSchmidtGate :=
    normalizedScalarRemainderInputDataFromTheorems.traceLegality.sourceHilbertSchmidtGate
  sourcePerMoveCyclicityLedger :=
    normalizedScalarRemainderInputDataFromTheorems.traceLegality.sourcePerMoveCyclicityLedger
  sourceNoDefectTraceReadOff :=
    normalizedScalarRemainderInputDataFromTheorems.traceLegality.sourceNoDefectTraceReadOff
  sourceRemainderOrientationWInftyEqLMinusD :=
    normalizedScalarRemainderInputDataFromTheorems.transport.sourceRemainderOrientationWInftyEqLMinusD
  sourceRemainderOrientationWInftyEqSMinusE :=
    normalizedScalarRemainderInputDataFromTheorems.transport.sourceRemainderOrientationWInftyEqSMinusE
  sourceRemainderObject :=
    normalizedScalarRemainderInputDataFromTheorems.transport.sourceRemainderObject
  sourceRemainderAfterQ :=
    normalizedScalarRemainderInputDataFromTheorems.transport.sourceRemainderAfterQ
  cc20PostQRemainderFixedSSoninTransport :=
    normalizedScalarRemainderInputDataFromTheorems.transport.cc20PostQRemainderFixedSSoninTransport
  sourceProjectionDefectNormalForm :=
    normalizedScalarRemainderInputDataFromTheorems.transport.sourceProjectionDefectNormalForm
  sourceRankPoleLedgerIdentification :=
    normalizedScalarRemainderInputDataFromTheorems.transport.sourceRankPoleLedgerIdentification
  sourceEndpointStripRemainderCdefDomination :=
    normalizedScalarRemainderInputDataFromTheorems.transport.sourceEndpointStripRemainderCdefDomination
  noBulkScaleTermOutsideLedger :=
    normalizedScalarRemainderInputDataFromTheorems.noBulk.noBulkScaleTermOutsideLedger
  noHiddenFinitePartSubtraction :=
    normalizedScalarRemainderInputDataFromTheorems.noBulk.noHiddenFinitePartSubtraction
  noBulkScaleTermOutsideLedgerHolds :=
    normalizedScalarRemainderInputDataFromTheorems.noBulk.noBulkScaleTermOutsideLedgerHolds
  noHiddenFinitePartSubtractionHolds :=
    normalizedScalarRemainderInputDataFromTheorems.noBulk.noHiddenFinitePartSubtractionHolds
  noBulkScaleTermOutsideLedgerAt :=
    normalizedScalarRemainderInputDataFromTheorems.noBulk.noBulkScaleTermOutsideLedgerAt
  noHiddenFinitePartSubtractionAt :=
    normalizedScalarRemainderInputDataFromTheorems.noBulk.noHiddenFinitePartSubtractionAt
  noBulkScaleTermOutsideLedgerAtHolds :=
    normalizedScalarRemainderInputDataFromTheorems.noBulk.noBulkScaleTermOutsideLedgerAtHolds
  noHiddenFinitePartSubtractionAtHolds :=
    normalizedScalarRemainderInputDataFromTheorems.noBulk.noHiddenFinitePartSubtractionAtHolds
  noHiddenPositiveDefectOutsideCdef :=
    normalizedScalarRemainderInputDataFromTheorems.boundedComparison.noHiddenPositiveDefectOutsideCdef
  sourceBoundedComparisonTraceIdealTransport :=
    normalizedScalarRemainderInputDataFromTheorems.boundedComparison.sourceBoundedComparisonTraceIdealTransport

structure NormalizedScalarSourceObjectRHExitInput where
  rhExit : Source.SourceObject.CC20RHExitObjectPackage

def normalizedScalarSourceObjectRHExitInputFromTheorems :
    NormalizedScalarSourceObjectRHExitInput where
  rhExit := normalizedSourceObjectRHExitInputFromTheorems.rhExit

noncomputable def normalizedScalarSourceObjectBridgeRowsFromTheorems :
    Source.SourceObjectExpandedRows normalizedBaseFromTheorems
      normalizedCommonFromTheorems :=
  Source.SourceObjectExpandedRows.ofNormalizedScalarCC20Trace
    normalizedCCM24FromTheorems normalizedScalarSeedFromTheorems
    normalizedScalarRemaindersFromTheorems

structure NormalizedScalarSourceObjectRHDefinitionBridgeEqInput where
  rhDefinitionBridge_eq_base :
    normalizedScalarSourceObjectRHExitInputFromTheorems.rhExit.rhDefinitionBridge =
      normalizedBaseFromTheorems.rhDefinitionBridge

def normalizedScalarSourceObjectRHDefinitionBridgeEqInputFromTheorems :
    NormalizedScalarSourceObjectRHDefinitionBridgeEqInput where
  rhDefinitionBridge_eq_base :=
    normalizedSourceObjectRHDefinitionBridgeEqInputFromTheorems.rhDefinitionBridge_eq_base

structure NormalizedScalarSourceObjectCommonTestInvolutionBridgeInput where
  commonTestInvolution :
    Source.SourceObject.CommonTestInvolutionBridge
      (Source.SourceObjectExpandedRows.ccm25
        normalizedScalarSourceObjectBridgeRowsFromTheorems).weilSymbols
      normalizedCommonFromTheorems.commonTest

def normalizedScalarSourceObjectCommonTestInvolutionBridgeInputFromTheorems :
    NormalizedScalarSourceObjectCommonTestInvolutionBridgeInput where
  commonTestInvolution :=
    normalizedSourceObjectCommonTestInvolutionBridgeInputFromTheorems.commonTestInvolution

structure NormalizedScalarSourceObjectCCM24CommonTestBridgeInput where
  ccm24Test_eq_commonTest :
    Source.SourceObject.CCM24CommonTestBridge
      (Source.SourceObjectExpandedRows.ccm25
        normalizedScalarSourceObjectBridgeRowsFromTheorems).weilSymbols
      normalizedCommonFromTheorems.commonTest
      normalizedCCM24FromTheorems

def normalizedScalarSourceObjectCCM24CommonTestBridgeInputFromTheorems :
    NormalizedScalarSourceObjectCCM24CommonTestBridgeInput where
  ccm24Test_eq_commonTest :=
    normalizedSourceObjectCCM24CommonTestBridgeInputFromTheorems.ccm24Test_eq_commonTest

structure NormalizedScalarSourceObjectCC20CommonTestBridgeInput where
  cc20TraceTest_eq_commonTest :
    Source.SourceObject.CC20CommonTestBridge
      (Source.SourceObjectExpandedRows.ccm25
        normalizedScalarSourceObjectBridgeRowsFromTheorems).weilSymbols
      normalizedCommonFromTheorems.commonTest
      normalizedScalarSourceObjectBridgeRowsFromTheorems.cc20Trace

structure NormalizedScalarSourceObjectCC20CommonTestBridgeRowsInput where
  rows :
    Source.NormalizedScalarCC20CommonTestBridgeRows
      normalizedBaseFromTheorems normalizedCommonFromTheorems.commonTest
      normalizedScalarSeedFromTheorems
      normalizedScalarCC20RemainderRowsInputFromTheorems.rows

noncomputable def normalizedScalarSourceObjectCC20CommonTestBridgeRowsInputFromTheorems :
    NormalizedScalarSourceObjectCC20CommonTestBridgeRowsInput where
  rows :=
    normalizedSourceObjectTheoremBaseInputFromTheorems.scalarCC20CommonTestBridgeRows
      normalizedCommonFromTheorems.commonTest
      normalizedScalarSeedFromTheorems

noncomputable def normalizedScalarSourceObjectCC20CommonTestBridgeInputFromTheorems :
    NormalizedScalarSourceObjectCC20CommonTestBridgeInput where
  cc20TraceTest_eq_commonTest :=
    { sourceTraceTestCompatibility :=
        normalizedScalarSourceObjectCC20CommonTestBridgeRowsInputFromTheorems.rows.sourceTraceTestCompatibility
      traceLegIsCommonTest :=
        normalizedScalarSourceObjectCC20CommonTestBridgeRowsInputFromTheorems.rows.traceLegIsCommonTest
      mellinLegIsCommonTest :=
        normalizedScalarSourceObjectCC20CommonTestBridgeRowsInputFromTheorems.rows.mellinLegIsCommonTest
      halfDensityMatchesCommonTest :=
        normalizedScalarSourceObjectBridgeRowsFromTheorems.cc20Trace.sourceMellinHalfDensityCompatibility }

structure NormalizedScalarSourceObjectConvolutionSquareEqFgInput where
  convolutionSquare_eq_Fg : Prop

def normalizedScalarSourceObjectConvolutionSquareEqFgInputFromTheorems :
    NormalizedScalarSourceObjectConvolutionSquareEqFgInput where
  convolutionSquare_eq_Fg :=
    normalizedCommonFromTheorems.commonTest.sourceConvolutionSquare =
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols.convolutionStar
        normalizedCommonFromTheorems.commonTest.sourceTest
        normalizedCommonFromTheorems.commonTest.sourceTest

structure NormalizedScalarSourceObjectQWLambdaWindowControlInput where
  ccm24Window_controls_qwLambda : Prop

def normalizedScalarSourceObjectQWLambdaWindowControlInputFromTheorems :
    NormalizedScalarSourceObjectQWLambdaWindowControlInput where
  ccm24Window_controls_qwLambda :=
    ∀ lambda : ℝ, 1 < lambda →
      SemilocalModelSymbols.lambdaCompatible
        normalizedCCM24FromTheorems.semilocalSymbols
        normalizedCCM24FromTheorems.sourceSupportWindow
        lambda

structure NormalizedScalarSourceObjectCdefWindowControlInput where
  ccm24Window_controls_cdef : Prop

def normalizedScalarSourceObjectCdefWindowControlInputFromTheorems :
    NormalizedScalarSourceObjectCdefWindowControlInput where
  ccm24Window_controls_cdef :=
    SemilocalModelSymbols.fixedWindowExhaustionCompatible
      normalizedCCM24FromTheorems.semilocalSymbols
      normalizedCCM24FromTheorems.sourceSupportWindow

structure NormalizedScalarSourceObjectFinitePrimeWindowMatchInput where
  finitePrimeSupport_matches_window : Prop

def normalizedScalarSourceObjectFinitePrimeWindowMatchInputFromTheorems :
    NormalizedScalarSourceObjectFinitePrimeWindowMatchInput where
  finitePrimeSupport_matches_window :=
    WeilFormSymbols.FinitePrimeNormalizationStatement
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols

structure NormalizedScalarSourceObjectQWSignBridgeInput where
  qW_sign_bridge : Prop

def normalizedScalarSourceObjectQWSignBridgeInputFromTheorems :
    NormalizedScalarSourceObjectQWSignBridgeInput where
  qW_sign_bridge :=
    ∀ input : WeilPositivityInput,
      normalizedScalarSourceObjectRHExitInputFromTheorems.rhExit.sourceQWNonnegative input →
        normalizedScalarSourceObjectRHExitInputFromTheorems.rhExit.sourceCC20WeilNonpositivity input

structure NormalizedScalarSourceObjectCrossObjectBridgeInput where
  bridges :
    Source.SourceObjectCrossObjectBridges normalizedBaseFromTheorems
      normalizedCommonFromTheorems
      normalizedScalarSourceObjectBridgeRowsFromTheorems
      normalizedScalarSourceObjectRHExitInputFromTheorems.rhExit

noncomputable def normalizedScalarSourceObjectCrossObjectBridgeInputFromTheorems :
    NormalizedScalarSourceObjectCrossObjectBridgeInput where
  bridges :=
    { rhDefinitionBridge_eq_base :=
        (normalizedScalarSourceObjectRHDefinitionBridgeEqInputFromTheorems).rhDefinitionBridge_eq_base
      commonTestInvolution :=
        (normalizedScalarSourceObjectCommonTestInvolutionBridgeInputFromTheorems).commonTestInvolution
      ccm24Test_eq_commonTest :=
        (normalizedScalarSourceObjectCCM24CommonTestBridgeInputFromTheorems).ccm24Test_eq_commonTest
      cc20TraceTest_eq_commonTest :=
        (normalizedScalarSourceObjectCC20CommonTestBridgeInputFromTheorems).cc20TraceTest_eq_commonTest
      convolutionSquare_eq_Fg :=
        (normalizedScalarSourceObjectConvolutionSquareEqFgInputFromTheorems).convolutionSquare_eq_Fg
      ccm24Window_controls_qwLambda :=
        (normalizedScalarSourceObjectQWLambdaWindowControlInputFromTheorems).ccm24Window_controls_qwLambda
      ccm24Window_controls_cdef :=
        (normalizedScalarSourceObjectCdefWindowControlInputFromTheorems).ccm24Window_controls_cdef
      finitePrimeSupport_matches_window :=
        (normalizedScalarSourceObjectFinitePrimeWindowMatchInputFromTheorems).finitePrimeSupport_matches_window
      qW_sign_bridge :=
        normalizedScalarSourceObjectQWSignBridgeInputFromTheorems.qW_sign_bridge }

structure NormalizedScalarSourceObjectLayerBridgeInput where
  rhExit : Source.SourceObject.CC20RHExitObjectPackage
  bridges :
    Source.SourceObjectCrossObjectBridges normalizedBaseFromTheorems
      normalizedCommonFromTheorems
      (Source.SourceObjectExpandedRows.ofNormalizedScalarCC20Trace
        normalizedCCM24FromTheorems normalizedScalarSeedFromTheorems
        normalizedScalarRemaindersFromTheorems)
      rhExit

noncomputable def normalizedScalarSourceObjectLayerBridgeInputFromTheorems :
    NormalizedScalarSourceObjectLayerBridgeInput where
  rhExit := normalizedScalarSourceObjectRHExitInputFromTheorems.rhExit
  bridges := normalizedScalarSourceObjectCrossObjectBridgeInputFromTheorems.bridges

noncomputable def normalizedScalarSourceObjectLayerInputFromTheorems :
    Source.NormalizedScalarSourceObjectLayerInput
      normalizedBaseFromTheorems normalizedCommonFromTheorems
      normalizedCCM24FromTheorems normalizedScalarSeedFromTheorems
      normalizedScalarRemaindersFromTheorems :=
  { rhExit := normalizedScalarSourceObjectLayerBridgeInputFromTheorems.rhExit
    bridges := normalizedScalarSourceObjectLayerBridgeInputFromTheorems.bridges }

noncomputable def normalizedScalarRhExitFromTheorems :
    Source.SourceObject.CC20RHExitObjectPackage :=
  normalizedScalarSourceObjectLayerInputFromTheorems.rhExit

noncomputable def normalizedScalarBridgesFromTheorems :
    Source.SourceObjectCrossObjectBridges normalizedBaseFromTheorems
      normalizedCommonFromTheorems
      (Source.SourceObjectExpandedRows.ofNormalizedScalarCC20Trace
        normalizedCCM24FromTheorems normalizedScalarSeedFromTheorems
        normalizedScalarRemaindersFromTheorems)
      normalizedScalarRhExitFromTheorems :=
  normalizedScalarSourceObjectLayerInputFromTheorems.bridges

noncomputable abbrev normalizedScalarSourceObjectPackageFromTheorems :
    Source.SourceObject.SourceObjectPackage :=
  Source.sourceObjectPackageOfNormalizedScalarCC20Trace
    normalizedBaseFromTheorems normalizedCommonFromTheorems
    normalizedCCM24FromTheorems normalizedScalarSeedFromTheorems
    normalizedScalarRemaindersFromTheorems
    normalizedScalarRhExitFromTheorems
    normalizedScalarBridgesFromTheorems

structure NormalizedScalarFixedSTestAdmissibleWindowInput where
  admissibleWindow : Prop
  admissibleWindowHolds : admissibleWindow

def normalizedScalarFixedSTestAdmissibleWindowInputFromTheorems :
    NormalizedScalarFixedSTestAdmissibleWindowInput where
  admissibleWindow :=
    normalizedScalarSourceObjectPackageFromTheorems.ccm24.semilocalSymbols.supportInWindow
      normalizedScalarSourceObjectPackageFromTheorems.ccm24.sourceTestLeg
      normalizedScalarSourceObjectPackageFromTheorems.ccm24.sourceSupportWindow
  admissibleWindowHolds :=
    normalizedScalarSourceObjectPackageFromTheorems.ccm24.sourceSupportInWindowData

structure NormalizedScalarFixedSTestTripleVanishingInput where
  tripleVanishingSymbols : TripleVanishingSymbols
  tripleVanishingSourceHolds :
    TripleVanishingSymbols.TripleVanishingStatement tripleVanishingSymbols

def normalizedScalarFixedSTestTripleVanishingInputFromTheorems :
    NormalizedScalarFixedSTestTripleVanishingInput where
  tripleVanishingSymbols :=
    normalizedFixedSTestTripleVanishingInputFromTheorems.tripleVanishingSymbols
  tripleVanishingSourceHolds :=
    normalizedFixedSTestTripleVanishingInputFromTheorems.tripleVanishingSourceHolds

structure NormalizedScalarFixedSTestSourceInput where
  admissibleWindow : Prop
  admissibleWindowHolds : admissibleWindow
  tripleVanishingSymbols : TripleVanishingSymbols
  tripleVanishingSourceHolds :
    TripleVanishingSymbols.TripleVanishingStatement tripleVanishingSymbols

def normalizedScalarFixedSTestSourceInputFromTheorems :
    NormalizedScalarFixedSTestSourceInput where
  admissibleWindow :=
    normalizedScalarFixedSTestAdmissibleWindowInputFromTheorems.admissibleWindow
  admissibleWindowHolds :=
    normalizedScalarFixedSTestAdmissibleWindowInputFromTheorems.admissibleWindowHolds
  tripleVanishingSymbols :=
    normalizedScalarFixedSTestTripleVanishingInputFromTheorems.tripleVanishingSymbols
  tripleVanishingSourceHolds :=
    normalizedScalarFixedSTestTripleVanishingInputFromTheorems.tripleVanishingSourceHolds

def normalizedScalarFixedTestFromTheorems : FixedSTest where
  admissibleWindow :=
    normalizedScalarFixedSTestSourceInputFromTheorems.admissibleWindow
  tripleVanishing :=
    TripleVanishingSymbols.TripleVanishingStatement
      normalizedScalarFixedSTestSourceInputFromTheorems.tripleVanishingSymbols
  finitePrimesVisible :=
    WeilFormSymbols.FinitePrimeVisibilityStatement
      (RouteInputs.ofExpandedSourcePackage
        normalizedScalarSourceObjectPackageFromTheorems).ccm25.weilSymbols
      normalizedScalarSourceObjectPackageFromTheorems.commonTest.sourceTest
      normalizedScalarSourceObjectPackageFromTheorems.commonTest.sourceTest

def normalizedScalarFixedDataFromTheorems :
    FixedSTestObligationData
      normalizedScalarSourceObjectPackageFromTheorems where
  test := normalizedScalarFixedTestFromTheorems
  tripleVanishingSymbols :=
    normalizedScalarFixedSTestSourceInputFromTheorems.tripleVanishingSymbols
  admissibleWindow :=
    normalizedScalarFixedSTestSourceInputFromTheorems.admissibleWindowHolds
  tripleVanishingBridge := by
    intro h
    exact h
  tripleVanishingSourceHolds :=
    normalizedScalarFixedSTestSourceInputFromTheorems.tripleVanishingSourceHolds
  routeTest := normalizedScalarSourceObjectPackageFromTheorems.commonTest.sourceTest
  routeTest_eq_commonTest := rfl
  finitePrimeVisibilityBridge := by
    intro h
    exact h

noncomputable abbrev normalizedScalarFixedFrontEndFromTheorems :
    ExpandedSourceFixedSTestFrontEnd
      normalizedScalarSourceObjectPackageFromTheorems :=
  FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedScalarPackage
    normalizedBaseFromTheorems normalizedCommonFromTheorems
    normalizedCCM24FromTheorems normalizedScalarSeedFromTheorems
    normalizedScalarRemaindersFromTheorems
    normalizedScalarRhExitFromTheorems normalizedScalarBridgesFromTheorems
    normalizedScalarFixedDataFromTheorems

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

structure NormalizedS2B1NoBulkSourceTheoremData where
  witness :
    ∀ lambda : ℝ, 1 < lambda →
      ∀ archimedeanTest :
        normalizedSourceObjectPackageFromTheorems.cc20Trace.archimedeanSymbols.Test,
        ∀ weilTest : TestFunction,
          Source.CC20CCMTraceScaleNoBulkWitness
            normalizedSourceObjectPackageFromTheorems.cc20Trace.archimedeanSymbols
            normalizedSourceObjectPackageFromTheorems.ccm25.weilSymbols
            lambda archimedeanTest weilTest

def normalizedS2B1NoBulkSourceTheoremDataFromTheorems :
    NormalizedS2B1NoBulkSourceTheoremData where
  witness := by
    intro lambda hlambda archimedeanTest weilTest
    exact
      { noBulkScaleTermOutsideLedger :=
          (normalizedS2B1NoBulkRowsFromTheorems.witness
            lambda hlambda archimedeanTest weilTest).noBulkScaleTermOutsideLedger
        noHiddenFinitePartSubtraction :=
          (normalizedS2B1NoBulkRowsFromTheorems.witness
            lambda hlambda archimedeanTest weilTest).noHiddenFinitePartSubtraction
        noBulkScaleTermOutsideLedgerHolds :=
          (normalizedS2B1NoBulkRowsFromTheorems.witness
            lambda hlambda archimedeanTest weilTest).noBulkScaleTermOutsideLedgerHolds
        noHiddenFinitePartSubtractionHolds :=
          (normalizedS2B1NoBulkRowsFromTheorems.witness
            lambda hlambda archimedeanTest weilTest).noHiddenFinitePartSubtractionHolds }

def normalizedS2B1NoBulkSourceTheoremFromTheorems :
    (Source.cc20CcmTraceScaleNoBulk
      normalizedSourceObjectPackageFromTheorems.cc20Trace.archimedeanSymbols
      normalizedSourceObjectPackageFromTheorems.ccm25.weilSymbols).Holds := by
  intro lambda hlambda archimedeanTest weilTest
  exact
    ⟨normalizedS2B1NoBulkSourceTheoremDataFromTheorems.witness
      lambda hlambda archimedeanTest weilTest⟩

def normalizedS2B1NoBulkSourceWitnessFromTheorems :
    Source.CC20CCMTraceScaleNoBulkWitness
      normalizedSourceObjectPackageFromTheorems.cc20Trace.archimedeanSymbols
      normalizedSourceObjectPackageFromTheorems.ccm25.weilSymbols
      normalizedTraceFrontEndFromTheorems.lambda
      normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceTraceTest
      normalizedSourceObjectPackageFromTheorems.commonTest.sourceTest :=
  normalizedS2B1NoBulkSourceTheoremDataFromTheorems.witness
    normalizedTraceFrontEndFromTheorems.lambda
    normalizedTraceFrontEndFromTheorems.oneLtLambda
    normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceTraceTest
    normalizedSourceObjectPackageFromTheorems.commonTest.sourceTest

theorem normalizedS2B1NoBulkSourceWitnessSatisfiesStatement :
    Nonempty
      (Source.CC20CCMTraceScaleNoBulkWitness
        normalizedSourceObjectPackageFromTheorems.cc20Trace.archimedeanSymbols
        normalizedSourceObjectPackageFromTheorems.ccm25.weilSymbols
        normalizedTraceFrontEndFromTheorems.lambda
        normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceTraceTest
        normalizedSourceObjectPackageFromTheorems.commonTest.sourceTest) :=
  ⟨normalizedS2B1NoBulkSourceWitnessFromTheorems⟩

structure NormalizedNoExtraBulkSourceTermInputData where
  noBulkSourceTheorem :
    Source.CC20CCMTraceScaleNoBulkWitness
      normalizedSourceObjectPackageFromTheorems.cc20Trace.archimedeanSymbols
      normalizedSourceObjectPackageFromTheorems.ccm25.weilSymbols
      normalizedTraceFrontEndFromTheorems.lambda
      normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceTraceTest
      normalizedSourceObjectPackageFromTheorems.commonTest.sourceTest

def normalizedNoExtraBulkSourceTermInputDataFromTheorems :
    NormalizedNoExtraBulkSourceTermInputData where
  noBulkSourceTheorem := normalizedS2B1NoBulkSourceWitnessFromTheorems

def normalizedSupportSquareQWLambdaScalarReadOffFromTheorems :
    TraceFrontEndData.NormalizedSupportSquareQWLambdaScalarReadOff
      normalizedBaseFromTheorems normalizedCommonFromTheorems
      normalizedCCM24FromTheorems normalizedSeedFromTheorems
      normalizedRemaindersFromTheorems normalizedRhExitFromTheorems
      normalizedBridgesFromTheorems normalizedFixedDataFromTheorems
      normalizedTraceDataFromTheorems :=
  TraceFrontEndData.normalizedSupportSquareQWLambdaScalarReadOffOfTheoremBaseRows
    normalizedBaseFromTheorems normalizedCommonFromTheorems
    normalizedCCM24FromTheorems normalizedSeedFromTheorems
    normalizedRemaindersFromTheorems normalizedRhExitFromTheorems
    normalizedBridgesFromTheorems normalizedFixedDataFromTheorems
    normalizedTraceDataFromTheorems rfl

def normalizedNoExtraBulkSourceTermsFromTheorems :
    TraceFrontEndData.TraceScaleNoExtraBulkSourceTermData
      normalizedSourceObjectPackageFromTheorems
      normalizedFixedFrontEndFromTheorems
      normalizedTraceFrontEndFromTheorems.lambda
      normalizedTraceFrontEndFromTheorems.ccm25ArithmeticPackage where
  positiveTraceDecomposesIntoQWLambdaRankPoleCdef :=
    normalizedTracePositiveTraceDecompositionInputFromTheorems.positiveTraceDecomposesIntoQWLambdaRankPoleCdef
  noBulkScaleTermOutsideLedger :=
    normalizedTraceNoExtraBulkTermInputFromTheorems.noBulkScaleTermOutsideLedger
  noHiddenFinitePartSubtraction :=
    normalizedTraceNoHiddenFinitePartInputFromTheorems.noHiddenFinitePartSubtraction
  positiveTraceDecomposesIntoQWLambdaRankPoleCdefHolds :=
    normalizedTracePositiveTraceDecompositionInputFromTheorems.positiveTraceDecomposesIntoQWLambdaRankPoleCdefHolds
  noBulkScaleTermOutsideLedgerHolds :=
    normalizedTraceNoExtraBulkTermInputFromTheorems.noBulkScaleTermOutsideLedgerHolds
  noHiddenFinitePartSubtractionHolds :=
    normalizedTraceNoHiddenFinitePartInputFromTheorems.noHiddenFinitePartSubtractionHolds

def normalizedNoExtraBulkContractFromTheorems :
    TraceFrontEndData.TraceScaleNoExtraBulkContract
      normalizedSourceObjectPackageFromTheorems
      normalizedFixedFrontEndFromTheorems
      normalizedTraceFrontEndFromTheorems.lambda
      normalizedTraceFrontEndFromTheorems.ccm25ArithmeticPackage :=
  TraceFrontEndData.no_extra_bulk_contract_of_source_term_data
    normalizedNoExtraBulkSourceTermsFromTheorems

def normalizedS2B1NoExtraBulkScaleTermExcludedFromTheorems : Prop :=
  TraceFrontEndData.S2B1NoExtraBulkScaleTermExcluded
    normalizedNoExtraBulkSourceTermsFromTheorems

theorem normalizedS2B1NoExtraBulkScaleTermExcludedHoldsFromTheorems :
    normalizedS2B1NoExtraBulkScaleTermExcludedFromTheorems :=
  TraceFrontEndData.noExtraBulkScaleTermExcludedHolds_of_source_terms
    normalizedNoExtraBulkSourceTermsFromTheorems

def normalizedS2B1NoHiddenFinitePartSubtractionExcludedFromTheorems : Prop :=
  TraceFrontEndData.S2B1NoHiddenFinitePartSubtractionExcluded
    normalizedNoExtraBulkSourceTermsFromTheorems

theorem normalizedS2B1NoHiddenFinitePartSubtractionExcludedHoldsFromTheorems :
    normalizedS2B1NoHiddenFinitePartSubtractionExcludedFromTheorems :=
  TraceFrontEndData.noHiddenFinitePartSubtractionExcludedHolds_of_source_terms
    normalizedNoExtraBulkSourceTermsFromTheorems

structure NormalizedScalarNoExtraBulkTransportData
    (sourceTerms :
      TraceFrontEndData.TraceScaleNoExtraBulkSourceTermData
        normalizedSourceObjectPackageFromTheorems
        normalizedFixedFrontEndFromTheorems
        normalizedTraceFrontEndFromTheorems.lambda
        normalizedTraceFrontEndFromTheorems.ccm25ArithmeticPackage) where
  scalarNoExtraBulkScaleTerm : Prop
  scalarStatementMatchesSource :
    scalarNoExtraBulkScaleTerm =
      TraceFrontEndData.TraceScaleNoExtraBulkSourceTermStatement sourceTerms

def normalizedScalarNoExtraBulkTransportDataFromTheorems :
    NormalizedScalarNoExtraBulkTransportData
      normalizedNoExtraBulkSourceTermsFromTheorems where
  scalarNoExtraBulkScaleTerm :=
    TraceFrontEndData.TraceScaleNoExtraBulkSourceTermStatement
      normalizedNoExtraBulkSourceTermsFromTheorems
  scalarStatementMatchesSource := rfl

noncomputable def normalizedScalarNoExtraBulkContractFromTransportData
    (sourceTerms :
      TraceFrontEndData.TraceScaleNoExtraBulkSourceTermData
        normalizedSourceObjectPackageFromTheorems
        normalizedFixedFrontEndFromTheorems
        normalizedTraceFrontEndFromTheorems.lambda
        normalizedTraceFrontEndFromTheorems.ccm25ArithmeticPackage)
    (transport :
      NormalizedScalarNoExtraBulkTransportData sourceTerms) :
    TraceFrontEndData.TraceScaleNoExtraBulkContract
      normalizedScalarSourceObjectPackageFromTheorems
      normalizedScalarFixedFrontEndFromTheorems
      normalizedTraceDataFromTheorems.lambda
      normalizedTraceDataFromTheorems.ccm25ArithmeticPackage :=
  { traceScaleOwnership := by
      intro L signDefectClassification
      exact
        TraceFrontEndData.trace_scale_owns_sign_defect_remainder_holds
          signDefectClassification
    sourceTerms :=
      { positiveTraceDecomposesIntoQWLambdaRankPoleCdef :=
          sourceTerms.positiveTraceDecomposesIntoQWLambdaRankPoleCdef
        noBulkScaleTermOutsideLedger :=
          sourceTerms.noBulkScaleTermOutsideLedger
        noHiddenFinitePartSubtraction :=
          sourceTerms.noHiddenFinitePartSubtraction
        positiveTraceDecomposesIntoQWLambdaRankPoleCdefHolds :=
          sourceTerms.positiveTraceDecomposesIntoQWLambdaRankPoleCdefHolds
        noBulkScaleTermOutsideLedgerHolds :=
          sourceTerms.noBulkScaleTermOutsideLedgerHolds
        noHiddenFinitePartSubtractionHolds :=
          sourceTerms.noHiddenFinitePartSubtractionHolds }
    sourceTermStatementHolds :=
      ⟨sourceTerms.positiveTraceDecomposesIntoQWLambdaRankPoleCdefHolds,
        sourceTerms.noBulkScaleTermOutsideLedgerHolds,
        sourceTerms.noHiddenFinitePartSubtractionHolds⟩
    noExtraBulkScaleTerm := transport.scalarNoExtraBulkScaleTerm
    noExtraBulkScaleTermHolds := by
      exact transport.scalarStatementMatchesSource.symm ▸
        TraceFrontEndData.trace_scale_no_extra_bulk_source_term_statement_holds
          sourceTerms }

structure NormalizedNoExtraBulkInputData where
  sourceInput : NormalizedNoExtraBulkSourceTermInputData
  scalarTransport :
    NormalizedScalarNoExtraBulkTransportData
      normalizedNoExtraBulkSourceTermsFromTheorems
  scalarContract :
    TraceFrontEndData.TraceScaleNoExtraBulkContract
      normalizedScalarSourceObjectPackageFromTheorems
      normalizedScalarFixedFrontEndFromTheorems
      normalizedTraceDataFromTheorems.lambda
      normalizedTraceDataFromTheorems.ccm25ArithmeticPackage
  scalarContractMatchesTransport :
    scalarContract =
      normalizedScalarNoExtraBulkContractFromTransportData
        normalizedNoExtraBulkSourceTermsFromTheorems scalarTransport

noncomputable def normalizedNoExtraBulkInputDataFromTheorems :
    NormalizedNoExtraBulkInputData where
  sourceInput := normalizedNoExtraBulkSourceTermInputDataFromTheorems
  scalarTransport := normalizedScalarNoExtraBulkTransportDataFromTheorems
  scalarContract :=
    normalizedScalarNoExtraBulkContractFromTransportData
      normalizedNoExtraBulkSourceTermsFromTheorems
      normalizedScalarNoExtraBulkTransportDataFromTheorems
  scalarContractMatchesTransport := rfl

structure NormalizedRouteLedgerRowsInput where
  rows : Source.NormalizedRouteLedgerRows

def normalizedRouteLedgerRowsInputFromTheorems :
    NormalizedRouteLedgerRowsInput where
  rows :=
    normalizedSourceObjectTheoremBaseInputFromTheorems.normalizedRouteLedgerRows

structure NormalizedRouteLedgerSourceInput where
  rankKilled : Prop
  poleKilled : Prop
  cdefExhausts : Prop
  rankKilledHolds : rankKilled
  poleKilledHolds : poleKilled
  cdefExhaustsHolds : cdefExhausts

def normalizedRouteLedgerSourceInputFromTheorems :
    NormalizedRouteLedgerSourceInput where
  rankKilled := normalizedRouteLedgerRowsInputFromTheorems.rows.rankKilled
  poleKilled := normalizedRouteLedgerRowsInputFromTheorems.rows.poleKilled
  cdefExhausts := normalizedRouteLedgerRowsInputFromTheorems.rows.cdefExhausts
  rankKilledHolds :=
    normalizedRouteLedgerRowsInputFromTheorems.rows.rankKilledHolds
  poleKilledHolds :=
    normalizedRouteLedgerRowsInputFromTheorems.rows.poleKilledHolds
  cdefExhaustsHolds :=
    normalizedRouteLedgerRowsInputFromTheorems.rows.cdefExhaustsHolds

def normalizedRouteLedgerInputFromTheorems : RouteLedgers where
  rankKilled := normalizedRouteLedgerSourceInputFromTheorems.rankKilled
  poleKilled := normalizedRouteLedgerSourceInputFromTheorems.poleKilled
  cdefExhausts := normalizedRouteLedgerSourceInputFromTheorems.cdefExhausts

def normalizedRouteLedgersClearedInputFromTheorems :
    LedgersCleared normalizedRouteLedgerInputFromTheorems where
  rankKilled := normalizedRouteLedgerSourceInputFromTheorems.rankKilledHolds
  poleKilled := normalizedRouteLedgerSourceInputFromTheorems.poleKilledHolds
  cdefExhausts := normalizedRouteLedgerSourceInputFromTheorems.cdefExhaustsHolds

def normalizedRouteLedgerClearingInputDataFromTheorems :
    LedgerSignDefectPackage
      (RouteInputs.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems)
      (SourceBackedFixedSTest.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems
        normalizedFixedFrontEndFromTheorems)
      normalizedTraceFrontEndFromTheorems.lambda :=
  ledger_sign_defect_package_of_ledgers_cleared
    normalizedRouteLedgerInputFromTheorems
    normalizedTraceFrontEndFromTheorems.oneLtLambda
    normalizedRouteLedgersClearedInputFromTheorems

def normalizedRouteLedgersFromTheorems : RouteLedgers :=
  normalizedRouteLedgerClearingInputDataFromTheorems.ledgers

theorem normalizedRankLedgerKilledFromTheorems :
    normalizedRouteLedgersFromTheorems.rankKilled :=
  normalizedRouteLedgerClearingInputDataFromTheorems.ledgersCleared.rankKilled

theorem normalizedPoleLedgerKilledFromTheorems :
    normalizedRouteLedgersFromTheorems.poleKilled :=
  normalizedRouteLedgerClearingInputDataFromTheorems.ledgersCleared.poleKilled

theorem normalizedCdefExhaustsFromTheorems :
    normalizedRouteLedgersFromTheorems.cdefExhausts :=
  normalizedRouteLedgerClearingInputDataFromTheorems.ledgersCleared.cdefExhausts

def normalizedLedgersClearedFromTheorems :
    LedgersCleared normalizedRouteLedgersFromTheorems :=
  normalizedRouteLedgerClearingInputDataFromTheorems.ledgersCleared

def normalizedSourceBackedLedgersFromTheorems :
    SourceBackedLedgers
      (RouteInputs.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems)
      (SourceBackedFixedSTest.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems
        normalizedFixedFrontEndFromTheorems)
      normalizedRouteLedgersFromTheorems :=
  normalizedRouteLedgerClearingInputDataFromTheorems.sourceBackedLedgers

theorem normalizedSignDefectClassificationFromTheorems :
    SourceSignDefectClassification
      (RouteInputs.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems)
      (SourceBackedFixedSTest.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems
        normalizedFixedFrontEndFromTheorems)
      normalizedTraceFrontEndFromTheorems.lambda
      normalizedRouteLedgersFromTheorems :=
  normalizedRouteLedgerClearingInputDataFromTheorems.signDefectClassification

def normalizedS2B1RankZeroModeChannelClassifiedFromTheorems : Prop :=
  TraceFrontEndData.S2B1RankZeroModeChannelClassified
    (RouteInputs.ofExpandedSourcePackage normalizedSourceObjectPackageFromTheorems)
    (SourceBackedFixedSTest.ofExpandedSourcePackage
      normalizedSourceObjectPackageFromTheorems normalizedFixedFrontEndFromTheorems)
    normalizedTraceFrontEndFromTheorems.lambda
    normalizedRouteLedgersFromTheorems

theorem normalizedS2B1RankZeroModeChannelClassifiedHoldsFromTheorems :
    normalizedS2B1RankZeroModeChannelClassifiedFromTheorems :=
  TraceFrontEndData.rankZeroModeChannelClassifiedAtHolds_of_sign_defect_classification
    normalizedSignDefectClassificationFromTheorems

def normalizedS2B1NoStripRankPoleClassifiedFromTheorems : Prop :=
  TraceFrontEndData.S2B1NoStripRankPoleClassified
    (RouteInputs.ofExpandedSourcePackage normalizedSourceObjectPackageFromTheorems)
    (SourceBackedFixedSTest.ofExpandedSourcePackage
      normalizedSourceObjectPackageFromTheorems normalizedFixedFrontEndFromTheorems)
    normalizedTraceFrontEndFromTheorems.lambda
    normalizedRouteLedgersFromTheorems

theorem normalizedS2B1NoStripRankPoleClassifiedHoldsFromTheorems :
    normalizedS2B1NoStripRankPoleClassifiedFromTheorems :=
  TraceFrontEndData.noStripPostQRemainderRankPoleClassifiedAtHolds_of_sign_defect_classification
    normalizedSignDefectClassificationFromTheorems

def normalizedS2B1EndpointStripBulkClassifiedIntoCdefFromTheorems : Prop :=
  TraceFrontEndData.S2B1EndpointStripBulkClassifiedIntoCdef
    (RouteInputs.ofExpandedSourcePackage normalizedSourceObjectPackageFromTheorems)
    (SourceBackedFixedSTest.ofExpandedSourcePackage
      normalizedSourceObjectPackageFromTheorems normalizedFixedFrontEndFromTheorems)
    normalizedTraceFrontEndFromTheorems.lambda

theorem normalizedS2B1EndpointStripBulkClassifiedIntoCdefHoldsFromTheorems :
    normalizedS2B1EndpointStripBulkClassifiedIntoCdefFromTheorems :=
  TraceFrontEndData.endpointStripBulkClassifiedIntoCdefAtHolds_of_sign_defect_classification
    normalizedSignDefectClassificationFromTheorems

def normalizedS2B1EndpointStripBoundaryTermsClassifiedFromTheorems : Prop :=
  TraceFrontEndData.S2B1EndpointStripBoundaryTermsClassified
    (RouteInputs.ofExpandedSourcePackage normalizedSourceObjectPackageFromTheorems)
    (SourceBackedFixedSTest.ofExpandedSourcePackage
      normalizedSourceObjectPackageFromTheorems normalizedFixedFrontEndFromTheorems)
    normalizedTraceFrontEndFromTheorems.lambda

theorem normalizedS2B1EndpointStripBoundaryTermsClassifiedHoldsFromTheorems :
    normalizedS2B1EndpointStripBoundaryTermsClassifiedFromTheorems :=
  TraceFrontEndData.endpointStripBoundaryTermsClassifiedAtHolds_of_sign_defect_classification
    normalizedSignDefectClassificationFromTheorems

def normalizedS2B1SourceSeriesTailClassifiedIntoCdefFromTheorems : Prop :=
  TraceFrontEndData.S2B1SourceSeriesTailClassifiedIntoCdef
    (RouteInputs.ofExpandedSourcePackage normalizedSourceObjectPackageFromTheorems)
    (SourceBackedFixedSTest.ofExpandedSourcePackage
      normalizedSourceObjectPackageFromTheorems normalizedFixedFrontEndFromTheorems)
    normalizedTraceFrontEndFromTheorems.lambda
    normalizedRouteLedgersFromTheorems

theorem normalizedS2B1SourceSeriesTailClassifiedIntoCdefHoldsFromTheorems :
    normalizedS2B1SourceSeriesTailClassifiedIntoCdefFromTheorems :=
  TraceFrontEndData.sourceSeriesTailClassifiedIntoCdefAtHolds_of_sign_defect_classification
    normalizedSignDefectClassificationFromTheorems

def normalizedS2B1CdefExhaustionOwnsEndpointStripFromTheorems : Prop :=
  TraceFrontEndData.S2B1CdefExhaustionOwnsEndpointStrip
    (RouteInputs.ofExpandedSourcePackage normalizedSourceObjectPackageFromTheorems)
    (SourceBackedFixedSTest.ofExpandedSourcePackage
      normalizedSourceObjectPackageFromTheorems normalizedFixedFrontEndFromTheorems)
    normalizedTraceFrontEndFromTheorems.lambda
    normalizedRouteLedgersFromTheorems

theorem normalizedS2B1CdefExhaustionOwnsEndpointStripHoldsFromTheorems :
    normalizedS2B1CdefExhaustionOwnsEndpointStripFromTheorems :=
  TraceFrontEndData.cdefExhaustionOwnsEndpointStripAtHolds_of_sign_defect_classification
    normalizedSignDefectClassificationFromTheorems

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

structure NormalizedRestrictedToFullThresholdPackageInput where
  threshold :
    RestrictedToFullQWLargeLambdaThreshold
      (RouteInputs.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems)
      (SourceBackedFixedSTest.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems
        normalizedFixedFrontEndFromTheorems)
      normalizedSourceObjectPackageFromTheorems.commonTest.sourceConvolutionSquare

structure NormalizedRestrictedToFullThresholdRowsInput where
  lambda0 : ℝ
  oneLtLambda0 : 1 < lambda0
  thresholdPackage :
    Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
      (RouteInputs.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems).ccm25.weilSymbols
      (SourceBackedFixedSTest.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems
        normalizedFixedFrontEndFromTheorems).weilTest
      lambda0
  thresholdTuple :
    SourceCommonTestTupleContract
      (RouteInputs.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems)
      (SourceBackedFixedSTest.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems
        normalizedFixedFrontEndFromTheorems)
      lambda0
      normalizedSourceObjectPackageFromTheorems.commonTest.sourceConvolutionSquare
      thresholdPackage
  supportThresholdAtLarge :
    ∀ lambda : ℝ,
      lambda0 ≤ lambda →
        FixedTestSupportThresholdAtLarge
          (RouteInputs.ofExpandedSourcePackage
            normalizedSourceObjectPackageFromTheorems)
          (SourceBackedFixedSTest.ofExpandedSourcePackage
            normalizedSourceObjectPackageFromTheorems
            normalizedFixedFrontEndFromTheorems)
          lambda
  primePowerAtomStabilizationAtLarge :
    ∀ lambda : ℝ,
      lambda0 ≤ lambda →
        ∀ pkg :
          Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
            (RouteInputs.ofExpandedSourcePackage
              normalizedSourceObjectPackageFromTheorems).ccm25.weilSymbols
            (SourceBackedFixedSTest.ofExpandedSourcePackage
              normalizedSourceObjectPackageFromTheorems
              normalizedFixedFrontEndFromTheorems).weilTest
            lambda,
          SourceCommonTestTupleContract
            (RouteInputs.ofExpandedSourcePackage
              normalizedSourceObjectPackageFromTheorems)
            (SourceBackedFixedSTest.ofExpandedSourcePackage
              normalizedSourceObjectPackageFromTheorems
              normalizedFixedFrontEndFromTheorems)
            lambda
            normalizedSourceObjectPackageFromTheorems.commonTest.sourceConvolutionSquare
            pkg →
            PrimePowerAtomStabilizationAtLarge
              (RouteInputs.ofExpandedSourcePackage
                normalizedSourceObjectPackageFromTheorems)
              (SourceBackedFixedSTest.ofExpandedSourcePackage
                normalizedSourceObjectPackageFromTheorems
                normalizedFixedFrontEndFromTheorems)
              lambda
              pkg
  scalarRestrictionAtLarge :
    ∀ lambda : ℝ,
      lambda0 ≤ lambda →
        ∀ pkg :
          Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
            (RouteInputs.ofExpandedSourcePackage
              normalizedSourceObjectPackageFromTheorems).ccm25.weilSymbols
            (SourceBackedFixedSTest.ofExpandedSourcePackage
              normalizedSourceObjectPackageFromTheorems
              normalizedFixedFrontEndFromTheorems).weilTest
            lambda,
          SourceCommonTestTupleContract
            (RouteInputs.ofExpandedSourcePackage
              normalizedSourceObjectPackageFromTheorems)
            (SourceBackedFixedSTest.ofExpandedSourcePackage
              normalizedSourceObjectPackageFromTheorems
              normalizedFixedFrontEndFromTheorems)
            lambda
            normalizedSourceObjectPackageFromTheorems.commonTest.sourceConvolutionSquare
            pkg →
            RestrictedToFullQWScalarRestrictionWitness
              (RouteInputs.ofExpandedSourcePackage
                normalizedSourceObjectPackageFromTheorems)
              (SourceBackedFixedSTest.ofExpandedSourcePackage
                normalizedSourceObjectPackageFromTheorems
                normalizedFixedFrontEndFromTheorems)
              lambda
              normalizedSourceObjectPackageFromTheorems.commonTest.sourceConvolutionSquare
              pkg

def normalizedRestrictedToFullArchimedeanBalanceRowsInputFromTheorems :
    NormalizedRestrictedToFullArchimedeanBalanceRowsProvider
      normalizedBaseFromTheorems normalizedCommonFromTheorems
      normalizedCCM24FromTheorems normalizedSeedFromTheorems
      normalizedRemaindersFromTheorems normalizedRhExitFromTheorems
      normalizedBridgesFromTheorems normalizedFixedDataFromTheorems
      normalizedTraceDataFromTheorems where
  archimedeanBalanceRowsAtLarge := by
    intro lambda _habove pkg _hcommon
    exact
      { scopedBalance :=
          normalizedCommonFinitePrimeArithmeticSourceDataFromTheorems.scopedArchimedeanContributionBalance
            lambda pkg }

noncomputable def normalizedRestrictedToFullAsymptoticRowsInputFromTheorems :
    NormalizedRestrictedToFullAsymptoticRowsProvider
      normalizedBaseFromTheorems normalizedCommonFromTheorems
      normalizedCCM24FromTheorems normalizedSeedFromTheorems
      normalizedRemaindersFromTheorems normalizedRhExitFromTheorems
      normalizedBridgesFromTheorems normalizedFixedDataFromTheorems
      normalizedTraceDataFromTheorems :=
  normalized_restricted_to_full_asymptotic_rows_of_archimedean_balance
    normalizedBaseFromTheorems normalizedCommonFromTheorems
    normalizedCCM24FromTheorems normalizedSeedFromTheorems
    normalizedRemaindersFromTheorems normalizedRhExitFromTheorems
    normalizedBridgesFromTheorems normalizedFixedDataFromTheorems
    normalizedTraceDataFromTheorems
    normalizedRestrictedToFullArchimedeanBalanceRowsInputFromTheorems

noncomputable def normalizedRestrictedToFullAsymptoticThresholdFromTheorems :
    RestrictedToFullQWLargeLambdaThreshold
      (RouteInputs.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems)
      (SourceBackedFixedSTest.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems
        normalizedFixedFrontEndFromTheorems)
      normalizedSourceObjectPackageFromTheorems.commonTest.sourceConvolutionSquare :=
  normalized_restricted_to_full_threshold_of_asymptotic_rows
    normalizedBaseFromTheorems normalizedCommonFromTheorems
    normalizedCCM24FromTheorems normalizedSeedFromTheorems
    normalizedRemaindersFromTheorems normalizedRhExitFromTheorems
    normalizedBridgesFromTheorems normalizedFixedDataFromTheorems
    normalizedTraceDataFromTheorems
    normalizedRestrictedToFullAsymptoticRowsInputFromTheorems

noncomputable def normalizedRestrictedToFullThresholdRowsInputFromTheorems :
    NormalizedRestrictedToFullThresholdRowsInput where
  lambda0 := normalizedRestrictedToFullAsymptoticThresholdFromTheorems.lambda0
  oneLtLambda0 :=
    normalizedRestrictedToFullAsymptoticThresholdFromTheorems.oneLtLambda0
  thresholdPackage :=
    normalizedRestrictedToFullAsymptoticThresholdFromTheorems.thresholdPackage
  thresholdTuple :=
    normalizedRestrictedToFullAsymptoticThresholdFromTheorems.thresholdTuple
  supportThresholdAtLarge :=
    normalizedRestrictedToFullAsymptoticThresholdFromTheorems.supportThresholdAtLarge
  primePowerAtomStabilizationAtLarge :=
    normalizedRestrictedToFullAsymptoticThresholdFromTheorems.primePowerAtomStabilizationAtLarge
  scalarRestrictionAtLarge :=
    normalizedRestrictedToFullAsymptoticThresholdFromTheorems.scalarRestrictionAtLarge

noncomputable def normalizedRestrictedToFullThresholdPackageInputFromTheorems :
    NormalizedRestrictedToFullThresholdPackageInput where
  threshold :=
    { lambda0 :=
        normalizedRestrictedToFullThresholdRowsInputFromTheorems.lambda0
      oneLtLambda0 :=
        normalizedRestrictedToFullThresholdRowsInputFromTheorems.oneLtLambda0
      thresholdPackage :=
        normalizedRestrictedToFullThresholdRowsInputFromTheorems.thresholdPackage
      thresholdTuple :=
        normalizedRestrictedToFullThresholdRowsInputFromTheorems.thresholdTuple
      supportThresholdAtLarge :=
        normalizedRestrictedToFullThresholdRowsInputFromTheorems.supportThresholdAtLarge
      primePowerAtomStabilizationAtLarge :=
        normalizedRestrictedToFullThresholdRowsInputFromTheorems.primePowerAtomStabilizationAtLarge
      scalarRestrictionAtLarge :=
        normalizedRestrictedToFullThresholdRowsInputFromTheorems.scalarRestrictionAtLarge }

structure NormalizedRestrictedToFullCurrentCutoffInput where
  currentAboveThreshold :
    normalizedRestrictedToFullThresholdPackageInputFromTheorems.threshold.lambda0 ≤
      normalizedTraceFrontEndFromTheorems.lambda

structure NormalizedRestrictedToFullCurrentCutoffRowsInput where
  currentAboveThreshold :
    normalizedRestrictedToFullThresholdRowsInputFromTheorems.lambda0 ≤
      normalizedTraceFrontEndFromTheorems.lambda

noncomputable def normalizedRestrictedToFullCurrentCutoffRowsInputFromTheorems :
    NormalizedRestrictedToFullCurrentCutoffRowsInput where
  currentAboveThreshold := le_rfl


noncomputable def normalizedRestrictedToFullCurrentCutoffInputFromTheorems :
    NormalizedRestrictedToFullCurrentCutoffInput where
  currentAboveThreshold :=
    normalizedRestrictedToFullCurrentCutoffRowsInputFromTheorems.currentAboveThreshold

structure NormalizedRestrictedToFullThresholdSourceInput where
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

noncomputable def normalizedRestrictedToFullThresholdSourceInputFromTheorems :
    NormalizedRestrictedToFullThresholdSourceInput where
  threshold :=
    normalizedRestrictedToFullThresholdPackageInputFromTheorems.threshold
  currentAboveThreshold :=
    normalizedRestrictedToFullCurrentCutoffInputFromTheorems.currentAboveThreshold

noncomputable def normalizedRestrictedToFullThresholdBridgePackageFromTheorems :
    RestrictedToFullThresholdBridgePackage
      (RouteInputs.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems)
      (SourceBackedFixedSTest.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems
        normalizedFixedFrontEndFromTheorems)
      normalizedTraceFrontEndFromTheorems.lambda
      normalizedSourceObjectPackageFromTheorems.commonTest.sourceConvolutionSquare
      normalizedRouteLedgersFromTheorems
      normalizedTraceFrontEndFromTheorems.ccm25ArithmeticPackage :=
  restricted_to_full_threshold_bridge_package_of_sign_defect
    normalizedRestrictedToFullThresholdSourceInputFromTheorems.threshold
    normalizedRestrictedToFullThresholdSourceInputFromTheorems.currentAboveThreshold
    normalizedCommonTupleFromTheorems
    normalizedSignDefectClassificationFromTheorems

noncomputable def normalizedRestrictedToFullLargeLambdaThresholdFromTheorems :
    RestrictedToFullQWLargeLambdaThreshold
      (RouteInputs.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems)
      (SourceBackedFixedSTest.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems
        normalizedFixedFrontEndFromTheorems)
      normalizedSourceObjectPackageFromTheorems.commonTest.sourceConvolutionSquare :=
  large_lambda_threshold_of_restricted_to_full_threshold_package
    normalizedRestrictedToFullThresholdBridgePackageFromTheorems

theorem normalizedRestrictedToFullCurrentAboveThresholdFromTheorems :
    normalizedRestrictedToFullLargeLambdaThresholdFromTheorems.lambda0 ≤
      normalizedTraceFrontEndFromTheorems.lambda :=
  current_above_threshold_of_restricted_to_full_threshold_package
    normalizedRestrictedToFullThresholdBridgePackageFromTheorems

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
  normalizedRestrictedToFullThresholdBridgePackageFromTheorems.currentCutoff

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
  restricted_to_full_bridge_contract_of_threshold_package
    normalizedRestrictedToFullThresholdBridgePackageFromTheorems

structure NormalizedScalarTraceScaleInputData where
  noExtraBulk :
    TraceFrontEndData.TraceScaleNoExtraBulkContract
      normalizedScalarSourceObjectPackageFromTheorems
      normalizedScalarFixedFrontEndFromTheorems
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
      normalizedTraceDataFromTheorems :=
  TraceFrontEndData.normalizedSupportSquareScalarNormalFormContractOfQWLambdaReadOff
    normalizedBaseFromTheorems normalizedCommonFromTheorems
    normalizedCCM24FromTheorems normalizedSeedFromTheorems
    normalizedRemaindersFromTheorems normalizedRhExitFromTheorems
    normalizedBridgesFromTheorems normalizedFixedDataFromTheorems
    normalizedTraceDataFromTheorems
    normalizedSupportSquareQWLambdaScalarReadOffFromTheorems

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
  noExtraBulk := normalizedNoExtraBulkInputDataFromTheorems.scalarContract
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

noncomputable def normalizedScalarFrontEndPackageFromTheorems :
    TraceFrontEndData.SourceFixedTraceFrontEndPackage
      normalizedScalarSourceObjectPackageFromTheorems :=
  TraceFrontEndData.source_fixed_trace_front_end_package_of_trace_data
    normalizedScalarSourceObjectPackageFromTheorems
    normalizedScalarFixedFrontEndFromTheorems
    normalizedScalarTraceDataFromTheorems

theorem normalizedScalarFrontEndPackageSourceTraceReadOffData_eq :
    normalizedScalarFrontEndPackageFromTheorems.sourceTraceReadOffData =
      TraceFrontEndData.toSourceTraceReadOffDataOfNormalizedScalarPackage
        normalizedBaseFromTheorems normalizedCommonFromTheorems
        normalizedCCM24FromTheorems normalizedScalarSeedFromTheorems
        normalizedScalarRemaindersFromTheorems
        normalizedScalarRhExitFromTheorems normalizedScalarBridgesFromTheorems
        normalizedScalarFixedDataFromTheorems
        normalizedScalarTraceDataFromTheorems :=
  rfl

noncomputable abbrev normalizedScalarTraceFrontEndFromTheorems :
    ExpandedSourceTraceReadOffFrontEnd
      normalizedScalarSourceObjectPackageFromTheorems
      normalizedScalarFixedFrontEndFromTheorems :=
  normalizedScalarFrontEndPackageFromTheorems.traceFront

theorem normalizedScalarTraceAmplitudeSquareFromTheorems :
    let scalarSourceTrace :=
      normalizedScalarFrontEndPackageFromTheorems.sourceTraceReadOffData
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
  TraceFrontEndData.normalizedSupportSquareQWLambdaSourceComparisonOfTraceAmplitudeSquare
    normalizedBaseFromTheorems normalizedCommonFromTheorems
    normalizedCCM24FromTheorems normalizedSeedFromTheorems
    normalizedRemaindersFromTheorems normalizedRhExitFromTheorems
    normalizedBridgesFromTheorems normalizedFixedDataFromTheorems
    normalizedTraceDataFromTheorems
    normalizedTraceAmplitudeSquareScalarFromTheorems

theorem normalizedSourceArchimedeanSignBridgeFromTheorems :
    SourceArchimedeanSignBridge
      (RouteInputs.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems)
      normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceTraceTest
      (SourceBackedFixedSTest.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems
        normalizedFixedFrontEndFromTheorems) :=
  source_archimedean_sign_bridge_of_source_trace_read_off
    normalizedFrontEndPackageFromTheorems.sourceTraceReadOffData

noncomputable def normalizedRouteCertificateFromTheorems :
    RouteCertificate
      (RouteInputs.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems) :=
  route_certificate_of_normalized_comparison_ledger_restricted_package
    normalizedBaseFromTheorems normalizedCommonFromTheorems
    normalizedCCM24FromTheorems normalizedSeedFromTheorems
    normalizedRemaindersFromTheorems normalizedRhExitFromTheorems
    normalizedBridgesFromTheorems normalizedFixedDataFromTheorems
    normalizedTraceDataFromTheorems normalizedComparisonFromTheorems
    normalizedNoExtraBulkContractFromTheorems
    normalizedRouteLedgerClearingInputDataFromTheorems
    normalizedRestrictedToFullThresholdBridgePackageFromTheorems
    normalizedSourceArchimedeanSignBridgeFromTheorems

noncomputable def normalizedFinalExitPackageFromTheorems :
    RouteFinalExitPackage
      (RouteInputs.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems) :=
  route_final_exit_package_of_certificate
    normalizedRouteCertificateFromTheorems

structure NormalizedNoArgumentRouteCertificatePackage where
  routeCertificate :
    RouteCertificate
      (RouteInputs.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems)
  finalExitPackage :
    RouteFinalExitPackage
      (RouteInputs.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems)
  mathlibRH : _root_.RiemannHypothesis

noncomputable def normalizedNoArgumentRouteCertificatePackageFromTheorems :
    NormalizedNoArgumentRouteCertificatePackage where
  routeCertificate := normalizedRouteCertificateFromTheorems
  finalExitPackage := normalizedFinalExitPackageFromTheorems
  mathlibRH := mathlib_rh_of_route_final_exit_package
    normalizedFinalExitPackageFromTheorems

def mathlib_rh_of_normalized_no_argument_route_certificate_package
    (pkg : NormalizedNoArgumentRouteCertificatePackage) :
    _root_.RiemannHypothesis :=
  pkg.mathlibRH

/-- Checklist item 6 compatibility outlet backed by the normalized lane. -/
abbrev sourceObjectPackageFromTheorems :
    Source.SourceObject.SourceObjectPackage :=
  normalizedSourceObjectPackageFromTheorems

/-- Checklist item 7 compatibility outlet backed by the normalized lane. -/
abbrev fixedFrontEndFromTheorems :
    ExpandedSourceFixedSTestFrontEnd sourceObjectPackageFromTheorems :=
  normalizedFixedFrontEndFromTheorems

/-- Checklist item 8 compatibility outlet backed by the normalized lane. -/
abbrev traceFrontEndFromTheorems :
    ExpandedSourceTraceReadOffFrontEnd
      sourceObjectPackageFromTheorems fixedFrontEndFromTheorems :=
  normalizedTraceFrontEndFromTheorems

def routeLedgerClearingInputDataFromTheorems :
    RouteLedgerClearingInputData where
  ledgers := normalizedRouteLedgersFromTheorems
  cleared := normalizedLedgersClearedFromTheorems

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

theorem signDefectClassificationFromTheorems :
    SourceSignDefectClassification
      (RouteInputs.ofExpandedSourcePackage sourceObjectPackageFromTheorems)
      (SourceBackedFixedSTest.ofExpandedSourcePackage
        sourceObjectPackageFromTheorems fixedFrontEndFromTheorems)
      traceFrontEndFromTheorems.lambda routeLedgersFromTheorems :=
  normalizedSignDefectClassificationFromTheorems

def commonTupleFromTheorems :
    SourceCommonTestTupleContract
      (RouteInputs.ofExpandedSourcePackage sourceObjectPackageFromTheorems)
      (SourceBackedFixedSTest.ofExpandedSourcePackage
        sourceObjectPackageFromTheorems fixedFrontEndFromTheorems)
      traceFrontEndFromTheorems.lambda
      sourceObjectPackageFromTheorems.commonTest.sourceConvolutionSquare
      traceFrontEndFromTheorems.ccm25ArithmeticPackage :=
  normalizedCommonTupleFromTheorems

noncomputable def restrictedToFullThresholdInputDataFromTheorems :
    RestrictedToFullThresholdInputData
      sourceObjectPackageFromTheorems
      (SourceBackedFixedSTest.ofExpandedSourcePackage
        sourceObjectPackageFromTheorems fixedFrontEndFromTheorems)
      traceFrontEndFromTheorems.lambda
      sourceObjectPackageFromTheorems.commonTest.sourceConvolutionSquare where
  threshold := normalizedRestrictedToFullLargeLambdaThresholdFromTheorems
  currentAboveThreshold := normalizedRestrictedToFullCurrentAboveThresholdFromTheorems

noncomputable def restrictedToFullLargeLambdaThresholdFromTheorems :
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

noncomputable def restrictedToFullQWFromTheorems :
    RestrictedToFullQWBridgeContract
      (RouteInputs.ofExpandedSourcePackage sourceObjectPackageFromTheorems)
      (SourceBackedFixedSTest.ofExpandedSourcePackage
        sourceObjectPackageFromTheorems fixedFrontEndFromTheorems)
      traceFrontEndFromTheorems.lambda
      sourceObjectPackageFromTheorems.commonTest.sourceConvolutionSquare
      routeLedgersFromTheorems
      traceFrontEndFromTheorems.ccm25ArithmeticPackage :=
  normalizedRestrictedToFullQWFromTheorems

theorem sourceArchimedeanSignBridgeFromTheorems :
    SourceArchimedeanSignBridge
      (RouteInputs.ofExpandedSourcePackage sourceObjectPackageFromTheorems)
      sourceObjectPackageFromTheorems.cc20Trace.sourceTraceTest
      (SourceBackedFixedSTest.ofExpandedSourcePackage
        sourceObjectPackageFromTheorems fixedFrontEndFromTheorems) :=
  normalizedSourceArchimedeanSignBridgeFromTheorems

noncomputable def routeCertificateFromTheorems :
    RouteCertificate
      (RouteInputs.ofExpandedSourcePackage sourceObjectPackageFromTheorems) :=
  normalizedRouteCertificateFromTheorems

theorem cc20FiniteVanishingExitFromTheorems :
    (RouteInputs.ofExpandedSourcePackage
      sourceObjectPackageFromTheorems).cc20.rhDefinitionBridge.SourceRH :=
  cc20_source_rh_of_route_certificate routeCertificateFromTheorems

theorem rhDefinitionBridgeToMathlibFromTheorems :
    _root_.RiemannHypothesis :=
  Source.RHDefinitionBridge.source_rh_to_mathlib_rh
    (RouteInputs.ofExpandedSourcePackage
      sourceObjectPackageFromTheorems).cc20.rhDefinitionBridge
    cc20FiniteVanishingExitFromTheorems

theorem unconditional_rh_skeleton : _root_.RiemannHypothesis := by
  exact final_connes_weil_rh routeCertificateFromTheorems

theorem unconditional_rh_contract_skeleton : _root_.RiemannHypothesis := by
  exact mathlib_rh_of_normalized_no_argument_route_certificate_package
    normalizedNoArgumentRouteCertificatePackageFromTheorems

end NormalizedContractBackedLane

end UnconditionalSkeleton
end Dev
end ConnesWeilRH
