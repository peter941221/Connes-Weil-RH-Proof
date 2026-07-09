/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.AnalyticCore
import ConnesWeilRH.Source.Objects

/-!
# CCM24 source model

This module gives Goal 1B a source-facing model for the CCM24 fixed-`S`
semilocal row. The model carries the concrete semilocal symbols and the named
source laws needed by the theorem-base record. It does not import
`SourceObligation.Holds` or reviewer decisions.
-/

namespace ConnesWeilRH
namespace Source

namespace AnalyticCore

open SourceSupportWindowData

noncomputable def SourceSupportWindowData.toCCM24SemilocalObjectPackage
    {A : SourceTestAlgebra}
    (S : SourceSupportWindowData A)
    (rows : SourceSemilocalRows S) :
    SourceObject.CCM24SemilocalObjectPackage where
  sourceModel :=
    { semilocalSymbols := S.toSemilocalModelSymbols
      canonicalSemilocalModel := rows.sourceCanonicalSemilocalModel
      supportTransport := rows.sourceSupportAndFourierSupportTransport
      boundedComparison := rows.sourceBoundedComparisonTraceClassTransport
      soninComparison := rows.sourceFixedWindowSoninExhaustion
      windowContainedInLambda := fun I lambda hlambda =>
        have hSubset :
            S.coordinateWindowCarrier I ⊆ S.lambdaCarrier lambda :=
          coordinateWindowCarrier_subset_lambdaCarrier
            (S := S) (I := I) hlambda
        windowContainedInLambda_of_coordinateWindowCarrier_subset_lambdaCarrier
          hSubset }
  sourceSupportWindow := S.sourceSupportWindow
  sourceFourierSupportInvolutionGeometryData :=
    rows.sourceFixedWindowCoordinateRows.fourierSupportInvolutionGeometryData
      |>.toSemilocalFourierSupportInvolutionGeometryData
  sourceSoninSpaceComparisonData := rows.sourceSoninSpaceComparison
  sourceBackedBoundedComparisonData :=
    SourceSupportWindowData.SourceBoundedComparisonData S
      (rows.canonicalModelData S.sourcePlaceSet)
  sourceBackedBoundedComparisonDataWitness :=
    (rows.sourceBoundedComparisonModelData S.sourcePlaceSet
      (rows.canonicalModelData S.sourcePlaceSet)).toBoundedComparisonData
  sourceBackedBoundedComparisonMap := by
    intro D
    exact SourceSupportWindowData.boundedComparisonMap_of_data D
  sourceBackedBoundedComparisonInverse := by
    intro D
    exact SourceSupportWindowData.boundedComparisonInverse_of_data D

noncomputable def SourceSupportWindowData.toCCM24SemilocalObjectPackageOfCoordinateRows
    {A : SourceTestAlgebra}
    (S : SourceSupportWindowData A)
    (coordinateRows :
      SourceSupportWindowData.SourceFixedWindowCoordinateRows
        S S.sourceSupportWindow)
    (placeCarrierData : SourceSupportWindowData.SourcePlaceCarrierData S)
    (scalingActionModelData :
      ∀ (V : S.PlaceSet)
        (H : SourceSupportWindowData.SourceCanonicalHilbertModelData
          S placeCarrierData V),
          SourceSupportWindowData.SourceScalarCoordinateScalingData S H)
    (fourierGradingModelData :
      ∀ (V : S.PlaceSet)
        (H : SourceSupportWindowData.SourceCanonicalHilbertModelData
          S placeCarrierData V),
          SourceSupportWindowData.SourceFourierCoordinateGradingData S H)
    (boundedComparisonModelData :
      ∀ (V : S.PlaceSet)
        (H : SourceSupportWindowData.SourceCanonicalHilbertModelData
          S placeCarrierData V),
          SourceSupportWindowData.SourceSignedCoordinateComparisonData S H) :
    SourceObject.CCM24SemilocalObjectPackage where
  sourceModel :=
    { semilocalSymbols := S.toSemilocalModelSymbols
      canonicalSemilocalModel := by
        exact
          (SourceSemilocalRows.ofFourierCoordinateModelData coordinateRows placeCarrierData
            scalingActionModelData fourierGradingModelData
            boundedComparisonModelData).sourceCanonicalSemilocalModel
      supportTransport :=
        (SourceSemilocalRows.ofFourierCoordinateModelData coordinateRows placeCarrierData
          scalingActionModelData fourierGradingModelData
          boundedComparisonModelData).sourceSupportAndFourierSupportTransport
      boundedComparison :=
        (SourceSemilocalRows.ofFourierCoordinateModelData coordinateRows placeCarrierData
          scalingActionModelData fourierGradingModelData
          boundedComparisonModelData).sourceBoundedComparisonTraceClassTransport
      soninComparison :=
        (SourceSemilocalRows.ofFourierCoordinateModelData coordinateRows placeCarrierData
          scalingActionModelData fourierGradingModelData
          boundedComparisonModelData).sourceFixedWindowSoninExhaustion
      windowContainedInLambda := fun I lambda hlambda =>
        have hSubset :
            S.coordinateWindowCarrier I ⊆ S.lambdaCarrier lambda :=
          coordinateWindowCarrier_subset_lambdaCarrier
            (S := S) (I := I) hlambda
        windowContainedInLambda_of_coordinateWindowCarrier_subset_lambdaCarrier
          hSubset }
  sourceSupportWindow := S.sourceSupportWindow
  sourceFourierSupportInvolutionGeometryData :=
    coordinateRows.fourierSupportInvolutionGeometryData
      |>.toSemilocalFourierSupportInvolutionGeometryData
  sourceSoninSpaceComparisonData :=
    coordinateRows.soninSpaceComparison
  sourceBackedBoundedComparisonData :=
    SourceSupportWindowData.SourceBoundedComparisonData S
      ((SourceSemilocalRows.ofFourierCoordinateModelData coordinateRows placeCarrierData
        scalingActionModelData fourierGradingModelData boundedComparisonModelData)
        |>.canonicalModelData S.sourcePlaceSet)
  sourceBackedBoundedComparisonDataWitness :=
    (boundedComparisonModelData S.sourcePlaceSet
      ((SourceSemilocalRows.ofFourierCoordinateModelData coordinateRows placeCarrierData
        scalingActionModelData fourierGradingModelData boundedComparisonModelData)
        |>.canonicalModelData S.sourcePlaceSet)).toBoundedComparisonData
  sourceBackedBoundedComparisonMap := by
    intro D
    exact SourceSupportWindowData.boundedComparisonMap_of_data D
  sourceBackedBoundedComparisonInverse := by
    intro D
    exact SourceSupportWindowData.boundedComparisonInverse_of_data D

end AnalyticCore

end Source
end ConnesWeilRH
