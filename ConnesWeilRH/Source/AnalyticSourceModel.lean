/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.CCM24SourceModel
import ConnesWeilRH.Source.CCM25TheoremBase

/-!
# Shared analytic source-model constructors

This module connects the source-facing analytic core to the three core
source-model inputs.  It is intentionally below the route layer: the extra
inputs are the still-mathematical source-window compatibility rows needed to
build the CCM24 semilocal object.  Full CCM25 arithmetic constructors take
finite-prime arithmetic data explicitly at the point where they are needed.
-/

namespace ConnesWeilRH
namespace Source
namespace AnalyticCore

open SourceSupportWindowData

noncomputable def SourceWeilFormData.toCCM25SourceModel
    {A : SourceTestAlgebra} (W : SourceWeilFormData A) :
    CCM25SourceModel where
  qw := W.toWeilFormSymbols.qw
  convolutionStar := W.toWeilFormSymbols.convolutionStar
  psi := W.toWeilFormSymbols.psi
  qwLambda := W.toWeilFormSymbols.qwLambda
  globalPrimeIndexSet := W.toWeilFormSymbols.globalPrimeIndexSet
  restrictedPrimeIndexSet := W.toWeilFormSymbols.restrictedPrimeIndexSet
  finitePrimeTerm := W.toWeilFormSymbols.finitePrimeTerm
  archimedeanTerm := W.toWeilFormSymbols.archimedeanTerm
  poleFunctional := W.toWeilFormSymbols.poleFunctional
  polePairing := W.toWeilFormSymbols.polePairing
  primePowerPairing := W.toWeilFormSymbols.primePowerPairing
  finitePrimeNormalization := W.finite_prime_term_normalization_statement
  qw_eq_psi_convolution := W.qw_definition_statement
  psi_sign_formula := W.psi_sign_statement
  qw_lambda_formula := W.qw_lambda_formula_statement
  pole_normalization := W.pole_normalization_statement

@[simp]
theorem SourceWeilFormData.toCCM25SourceModel_toWeilFormSymbols
    {A : SourceTestAlgebra} (W : SourceWeilFormData A) :
    W.toCCM25SourceModel.toWeilFormSymbols = W.toWeilFormSymbols := by
  rfl

/--
Lightweight shared core for source-model constructors.

This record is below the route layer but does not require a full
`SourceWeilFormData`.  CCM24 reads the support/window object, CC20 reads the
trace-scale seed, and CCM25 reads the source model it actually consumes.
-/
structure SourceModelConstructorCore where
  testAlgebra : SourceTestAlgebra
  supportWindow : SourceSupportWindowData testAlgebra
  ccm25SourceModel : CCM25SourceModel
  traceScale : SourceTraceScaleData testAlgebra

namespace SourceModelConstructorCore

noncomputable def ofSourceAnalyticCore
    (core : SourceAnalyticCore) :
    SourceModelConstructorCore where
  testAlgebra := core.testAlgebra
  supportWindow := core.supportWindow
  ccm25SourceModel := core.weilForm.toCCM25SourceModel
  traceScale := core.traceScale

def toWeilFormSymbols (core : SourceModelConstructorCore) : WeilFormSymbols :=
  core.ccm25SourceModel.toWeilFormSymbols

def toSemilocalModelSymbols (core : SourceModelConstructorCore) :
    SemilocalModelSymbols :=
  core.supportWindow.toSemilocalModelSymbols

def toArchimedeanTraceSymbols (core : SourceModelConstructorCore) :
    ArchimedeanTraceSymbols :=
  core.traceScale.toArchimedeanTraceSymbols

def toNormalizedLegalSquareTraceScaleSymbols
    (core : SourceModelConstructorCore) :
    CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols :=
  core.traceScale.toNormalizedLegalSquareTraceScaleSymbols

@[simp]
theorem ofSourceAnalyticCore_supportWindow
    (core : SourceAnalyticCore) :
    (ofSourceAnalyticCore core).supportWindow = core.supportWindow := by
  rfl

@[simp]
theorem ofSourceAnalyticCore_toWeilFormSymbols
    (core : SourceAnalyticCore) :
    (ofSourceAnalyticCore core).toWeilFormSymbols = core.toWeilFormSymbols := by
  rfl

@[simp]
theorem ofSourceAnalyticCore_traceScale
    (core : SourceAnalyticCore) :
    (ofSourceAnalyticCore core).traceScale = core.traceScale := by
  rfl

end SourceModelConstructorCore

/--
One source-backed constructor input for the three core source-model bodies.

The lightweight constructor core supplies the CCM24 support/window symbols, the
CCM25 source model, and the CC20 normalized trace-scale seed.  The remaining
fields are the real proof rows not derivable from the current core definitions
alone.
-/
structure SourceModelConstructorInput where
  core : SourceModelConstructorCore
  sourceFixedWindowCoordinateRows :
    SourceSupportWindowData.SourceFixedWindowCoordinateRows
      core.supportWindow core.supportWindow.sourceSupportWindow
  sourcePlaceCarrierData :
    SourceSupportWindowData.SourcePlaceCarrierData core.supportWindow
  sourceScalingActionModelData :
    ∀ (V : core.supportWindow.PlaceSet)
      (H : SourceSupportWindowData.SourceCanonicalHilbertModelData
        core.supportWindow sourcePlaceCarrierData V),
        SourceSupportWindowData.SourceScalarCoordinateScalingData
          core.supportWindow H
  sourceFourierGradingModelData :
    ∀ (V : core.supportWindow.PlaceSet)
      (H : SourceSupportWindowData.SourceCanonicalHilbertModelData
        core.supportWindow sourcePlaceCarrierData V),
        SourceSupportWindowData.SourceFourierCoordinateGradingData
          core.supportWindow H
  sourceBoundedComparisonModelData :
    ∀ (V : core.supportWindow.PlaceSet)
      (H : SourceSupportWindowData.SourceCanonicalHilbertModelData
        core.supportWindow sourcePlaceCarrierData V),
        SourceSupportWindowData.SourceSignedCoordinateComparisonData
          core.supportWindow H

namespace SourceModelConstructorInput

noncomputable def ofIdentityFourierModelData
    (core : SourceModelConstructorCore)
    (sourceFixedWindowCoordinateRows :
      SourceSupportWindowData.SourceFixedWindowCoordinateRows
        core.supportWindow core.supportWindow.sourceSupportWindow)
    (sourcePlaceCarrierData :
      SourceSupportWindowData.SourcePlaceCarrierData core.supportWindow)
    (sourceScalingActionModelData :
      ∀ (V : core.supportWindow.PlaceSet)
        (H : SourceSupportWindowData.SourceCanonicalHilbertModelData
          core.supportWindow sourcePlaceCarrierData V),
          SourceSupportWindowData.SourceScalarCoordinateScalingData
            core.supportWindow H)
    (sourceFourierGradingModelData :
      ∀ (V : core.supportWindow.PlaceSet)
        (_H : SourceSupportWindowData.SourceCanonicalHilbertModelData
          core.supportWindow sourcePlaceCarrierData V),
          SourceSupportWindowData.SourceIdentityFourierCoordinateGradingData
            core.supportWindow (P := sourcePlaceCarrierData) V)
    (sourceBoundedComparisonModelData :
      ∀ (V : core.supportWindow.PlaceSet)
        (H : SourceSupportWindowData.SourceCanonicalHilbertModelData
          core.supportWindow sourcePlaceCarrierData V),
          SourceSupportWindowData.SourceSignedCoordinateComparisonData
            core.supportWindow H) :
    SourceModelConstructorInput where
  core := core
  sourceFixedWindowCoordinateRows := sourceFixedWindowCoordinateRows
  sourcePlaceCarrierData := sourcePlaceCarrierData
  sourceScalingActionModelData := sourceScalingActionModelData
  sourceFourierGradingModelData := by
    intro V H
    exact (sourceFourierGradingModelData V H).toFourierCoordinateGradingData (H := H)
  sourceBoundedComparisonModelData := sourceBoundedComparisonModelData

noncomputable def ofLineFourierModelData
    (core : SourceModelConstructorCore)
    (sourceFixedWindowCoordinateRows :
      SourceSupportWindowData.SourceFixedWindowCoordinateRows
        core.supportWindow core.supportWindow.sourceSupportWindow)
    (sourcePlaceCarrierData :
      SourceSupportWindowData.SourcePlaceCarrierData core.supportWindow)
    (sourceScalingActionModelData :
      ∀ (V : core.supportWindow.PlaceSet)
        (H : SourceSupportWindowData.SourceCanonicalHilbertModelData
          core.supportWindow sourcePlaceCarrierData V),
          SourceSupportWindowData.SourceScalarCoordinateScalingData
            core.supportWindow H)
    (sourceFourierGradingModelData :
      ∀ (V : core.supportWindow.PlaceSet)
        (_H : SourceSupportWindowData.SourceCanonicalHilbertModelData
          core.supportWindow sourcePlaceCarrierData V),
          SourceSupportWindowData.SourceLineFourierCoordinateGradingData
            core.supportWindow (P := sourcePlaceCarrierData) V)
    (sourceBoundedComparisonModelData :
      ∀ (V : core.supportWindow.PlaceSet)
        (H : SourceSupportWindowData.SourceCanonicalHilbertModelData
          core.supportWindow sourcePlaceCarrierData V),
          SourceSupportWindowData.SourceSignedCoordinateComparisonData
            core.supportWindow H) :
    SourceModelConstructorInput where
  core := core
  sourceFixedWindowCoordinateRows := sourceFixedWindowCoordinateRows
  sourcePlaceCarrierData := sourcePlaceCarrierData
  sourceScalingActionModelData := sourceScalingActionModelData
  sourceFourierGradingModelData := by
    intro V H
    exact (sourceFourierGradingModelData V H).toFourierCoordinateGradingData (H := H)
  sourceBoundedComparisonModelData := sourceBoundedComparisonModelData

def ofFourierCoordinateModelData
    (core : SourceModelConstructorCore)
    (sourceFixedWindowCoordinateRows :
      SourceSupportWindowData.SourceFixedWindowCoordinateRows
        core.supportWindow core.supportWindow.sourceSupportWindow)
    (sourcePlaceCarrierData :
      SourceSupportWindowData.SourcePlaceCarrierData core.supportWindow)
    (sourceScalingActionModelData :
      ∀ (V : core.supportWindow.PlaceSet)
        (H : SourceSupportWindowData.SourceCanonicalHilbertModelData
          core.supportWindow sourcePlaceCarrierData V),
          SourceSupportWindowData.SourceScalarCoordinateScalingData
            core.supportWindow H)
    (sourceFourierGradingModelData :
      ∀ (V : core.supportWindow.PlaceSet)
        (H : SourceSupportWindowData.SourceCanonicalHilbertModelData
          core.supportWindow sourcePlaceCarrierData V),
          SourceSupportWindowData.SourceFourierCoordinateGradingData
            core.supportWindow H)
    (sourceBoundedComparisonModelData :
      ∀ (V : core.supportWindow.PlaceSet)
        (H : SourceSupportWindowData.SourceCanonicalHilbertModelData
          core.supportWindow sourcePlaceCarrierData V),
          SourceSupportWindowData.SourceSignedCoordinateComparisonData
            core.supportWindow H) :
    SourceModelConstructorInput where
  core := core
  sourceFixedWindowCoordinateRows := sourceFixedWindowCoordinateRows
  sourcePlaceCarrierData := sourcePlaceCarrierData
  sourceScalingActionModelData := sourceScalingActionModelData
  sourceFourierGradingModelData := sourceFourierGradingModelData
  sourceBoundedComparisonModelData := sourceBoundedComparisonModelData

theorem sourceCanonicalModel
    (input : SourceModelConstructorInput) :
    input.core.supportWindow.canonicalHilbertModel
      input.core.supportWindow.sourcePlaceSet :=
  (input.sourcePlaceCarrierData.canonicalModelData
    input.core.supportWindow.sourcePlaceSet).canonicalHilbertModel

theorem sourceScalingActionData
    (input : SourceModelConstructorInput) :
    ∀ V : input.core.supportWindow.PlaceSet,
      input.core.supportWindow.canonicalHilbertModel V →
        input.core.supportWindow.scalingActionImplemented V := by
  intro V hCanonical
  exact
      input.core.supportWindow.scalingActionImplemented_of_scalar_coordinate_data
        (input.sourceScalingActionModelData V
          (input.sourcePlaceCarrierData.canonicalModelData V))

theorem sourceFourierGradingData
    (input : SourceModelConstructorInput) :
    ∀ V : input.core.supportWindow.PlaceSet,
      input.core.supportWindow.canonicalHilbertModel V →
        input.core.supportWindow.fourierGradingCompatible V := by
  intro V hCanonical
  exact
      input.core.supportWindow.fourierGradingCompatible_of_data
        (input.sourceFourierGradingModelData V
          (input.sourcePlaceCarrierData.canonicalModelData V))

theorem sourceBoundedComparisonData
    (input : SourceModelConstructorInput) :
    ∀ V : input.core.supportWindow.PlaceSet,
      input.core.supportWindow.canonicalHilbertModel V →
        input.core.supportWindow.boundedComparisonMap V ∧
          input.core.supportWindow.boundedComparisonInverse V := by
  intro V hCanonical
  let hMap :=
    input.core.supportWindow.boundedComparisonMap_of_data
      ((input.sourceBoundedComparisonModelData V
        (input.sourcePlaceCarrierData.canonicalModelData V)).toBoundedComparisonData)
  let hInverse :=
    input.core.supportWindow.boundedComparisonInverse_of_data
      ((input.sourceBoundedComparisonModelData V
        (input.sourcePlaceCarrierData.canonicalModelData V)).toBoundedComparisonData)
  exact ⟨hMap, hInverse⟩

theorem sourceBoundedComparisonMapData
    (input : SourceModelConstructorInput) :
    ∀ V : input.core.supportWindow.PlaceSet,
      input.core.supportWindow.canonicalHilbertModel V →
        input.core.supportWindow.boundedComparisonMap V := by
  intro V hCanonical
  exact (input.sourceBoundedComparisonData V hCanonical).1

theorem sourceBoundedComparisonInverseData
    (input : SourceModelConstructorInput) :
    ∀ V : input.core.supportWindow.PlaceSet,
      input.core.supportWindow.canonicalHilbertModel V →
        input.core.supportWindow.boundedComparisonInverse V := by
  intro V hCanonical
  exact (input.sourceBoundedComparisonData V hCanonical).2

def sourceFixedWindowCompatible
    (input : SourceModelConstructorInput) :
  input.core.supportWindow.fixedWindowExhaustionCompatible
      input.core.supportWindow.sourceSupportWindow :=
  input.core.supportWindow.fixedWindowExhaustionCompatible_of_fourier_coordinate_model_data
    input.sourceFixedWindowCoordinateRows
    input.sourcePlaceCarrierData
    input.sourceScalingActionModelData
    input.sourceFourierGradingModelData
    input.sourceBoundedComparisonModelData

theorem sourceSupportInWindow
    (input : SourceModelConstructorInput) :
    input.core.supportWindow.supportInWindow
      input.core.supportWindow.sourceTest
      input.core.supportWindow.sourceSupportWindow :=
  input.sourceFixedWindowCoordinateRows.supportInWindow

theorem sourceFourierSupportInWindow
    (input : SourceModelConstructorInput) :
    input.core.supportWindow.fourierSupportInWindow
      input.core.supportWindow.sourceTest
      input.core.supportWindow.sourceSupportWindow :=
  input.sourceFixedWindowCoordinateRows.fourierSupportInWindow

theorem sourceSupportTransported
    (input : SourceModelConstructorInput) :
    input.core.supportWindow.supportTransported
      input.core.supportWindow.sourceTest
      input.core.supportWindow.sourceSupportWindow :=
  input.sourceFixedWindowCoordinateRows.supportTransported

theorem sourceConvolutionSupportTransported
    (input : SourceModelConstructorInput) :
    input.core.supportWindow.convolutionSupportTransported
      input.core.supportWindow.sourceTest
      input.core.supportWindow.sourceSupportWindow :=
  input.sourceFixedWindowCoordinateRows.convolutionSupportTransported

theorem sourceWindowContainedInLambda
    (input : SourceModelConstructorInput) :
    ∀ lambda : ℝ, 1 < lambda →
      input.core.supportWindow.windowContainedInLambda
        input.core.supportWindow.sourceSupportWindow lambda :=
  fun _lambda hlambda =>
    windowContainedInLambda_of_coordinateWindowCarrier_subset_lambdaCarrier_of_one_lt
      (S := input.core.supportWindow)
      (I := input.core.supportWindow.sourceSupportWindow) hlambda

theorem sourceLambdaCompatible
    (input : SourceModelConstructorInput) :
    ∀ lambda : ℝ, 1 < lambda →
      input.core.supportWindow.lambdaCompatible
        input.core.supportWindow.sourceSupportWindow lambda :=
  fun _lambda hlambda =>
    lambdaCompatible_of_coordinateWindowCarrier_subset_lambdaCarrier_of_one_lt
      (S := input.core.supportWindow)
      (I := input.core.supportWindow.sourceSupportWindow) hlambda

def toSourceSemilocalRows
    (input : SourceModelConstructorInput) :
    SourceSemilocalRows input.core.supportWindow :=
  SourceSemilocalRows.ofFourierCoordinateModelData
    input.sourceFixedWindowCoordinateRows
    input.sourcePlaceCarrierData
    input.sourceScalingActionModelData
    input.sourceFourierGradingModelData
    input.sourceBoundedComparisonModelData

noncomputable def toCCM24SemilocalObjectPackage
    (input : SourceModelConstructorInput) :
    SourceObject.CCM24SemilocalObjectPackage :=
  input.core.supportWindow.toCCM24SemilocalObjectPackage input.toSourceSemilocalRows

noncomputable def toCCM25ArithmeticConstructorInput
    (input : SourceModelConstructorInput)
    (finitePrimeArithmeticSourceData :
      CCM25Concrete.FinitePrimeSourceData.CommonFinitePrimeArithmeticSourceData
        input.core.toWeilFormSymbols) :
    CCM25SourceArithmeticConstructorInput :=
  { weilSymbols := input.core.toWeilFormSymbols
    globalRows :=
      { qwDefinition :=
          ccm25_source_qw_definition input.core.ccm25SourceModel
        psiSign :=
          ccm25_source_psi_sign input.core.ccm25SourceModel }
    restrictedRows :=
      { qwLambdaFormula :=
          ccm25_source_qw_lambda_formula input.core.ccm25SourceModel }
    finitePrimeArithmeticSourceData := finitePrimeArithmeticSourceData
    poleRows :=
      { poleNormalization :=
          ccm25_source_pole_normalization input.core.ccm25SourceModel } }

noncomputable def toCCM25WeilObjectPackage
    (input : SourceModelConstructorInput)
    (finitePrimeArithmeticSourceData :
      CCM25Concrete.FinitePrimeSourceData.CommonFinitePrimeArithmeticSourceData
        input.core.toWeilFormSymbols) :
    SourceObject.CCM25WeilObjectPackage :=
  (input.toCCM25ArithmeticConstructorInput
    finitePrimeArithmeticSourceData).toCCM25WeilObjectPackage

def toNormalizedLegalSquareTraceScaleSymbols
    (input : SourceModelConstructorInput) :
    CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols :=
  input.core.toNormalizedLegalSquareTraceScaleSymbols

noncomputable def toCCM24SourceModel
    (input : SourceModelConstructorInput) :
    CCM24SourceModel :=
  { semilocalSymbols := input.core.toSemilocalModelSymbols
    canonicalSemilocalModel := by
      intro V hModel
      exact
        ⟨input.sourceScalingActionData V hModel,
          input.sourceFourierGradingData V hModel⟩
    supportTransport := by
      intro f I hSupport hFourierSupport
      exact
        ⟨input.core.supportWindow.supportTransported_of_supportInWindow hSupport,
          input.core.supportWindow.convolutionSupportTransported_of_fourierSupportInWindow
            hFourierSupport⟩
    boundedComparison := by
      intro V hModel
      exact input.sourceBoundedComparisonData V hModel
    soninComparison := by
      intro I hSonin
      exact
        ⟨hSonin, input.sourceCanonicalModel, input.sourceScalingActionData,
          input.sourceFourierGradingData, input.sourceBoundedComparisonMapData,
          input.sourceBoundedComparisonInverseData⟩
    windowContainedInLambda := by
      intro I lambda hlambda
      exact
        windowContainedInLambda_of_coordinateWindowCarrier_subset_lambdaCarrier_of_one_lt
          (S := input.core.supportWindow) (I := I) hlambda }

noncomputable def toCCM25SourceModel
    (input : SourceModelConstructorInput) :
    CCM25SourceModel :=
  input.core.ccm25SourceModel

def toCC20TraceModel
    (input : SourceModelConstructorInput) :
    CC20TraceModel :=
  CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
    input.toNormalizedLegalSquareTraceScaleSymbols

@[simp]
theorem ccm24_symbols
    (input : SourceModelConstructorInput) :
    input.toCCM24SemilocalObjectPackage.semilocalSymbols =
      input.core.toSemilocalModelSymbols :=
  rfl

@[simp]
theorem ccm25_symbols
    (input : SourceModelConstructorInput) :
    ∀ finitePrimeArithmeticSourceData :
      CCM25Concrete.FinitePrimeSourceData.CommonFinitePrimeArithmeticSourceData
        input.core.toWeilFormSymbols,
      (input.toCCM25WeilObjectPackage
        finitePrimeArithmeticSourceData).weilSymbols =
        input.core.toWeilFormSymbols :=
  fun _ => rfl

@[simp]
theorem ccm25_source_model_symbols
    (input : SourceModelConstructorInput) :
    input.toCCM25SourceModel.toWeilFormSymbols =
      input.core.toWeilFormSymbols := by
  rfl

theorem cc20_trace_model_eq_seed
    (input : SourceModelConstructorInput) :
    input.toCC20TraceModel =
      CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
        input.toNormalizedLegalSquareTraceScaleSymbols :=
  rfl

end SourceModelConstructorInput

end AnalyticCore
end Source
end ConnesWeilRH
