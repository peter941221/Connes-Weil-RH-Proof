/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorSingleChannelFactorization

/-!
# Recovering the renewed channel from the packed physical factor

The first coordinate of every Proof 625 physical factor is a renewed
single-channel factor with no norm loss.  Together with the explicit packing
in `SingleChannelFactorization`, this gives the exact comparison

```text
Physical(bound)  -> SingleChannel(bound),
SingleChannel(bound) -> Physical(17 * bound).
```

Consequently the existence of some family-uniform bound is equivalent in the
two coordinates, although a fixed-bound equivalence is deliberately not
claimed.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorSingleChannelFactorization

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCausalMarkov
open CCM24FiniteSCompletedJuliaAmbientDefectFactorization
open CCM24FiniteSCompletedJuliaRawPhysicalFactorization
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorAmbientPhysicalFactorization
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorPhysicalFactorization
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorReverseIntertwining
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorRouteValidFactorization
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeAntiresonantReduction
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierLeakageExpansion
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierReduction
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSProjectionTrace
open CCM24FiniteSSchurMarkovPairing

noncomputable local instance singleChannelRecoverySourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace
      (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

local notation "SourceToFinite" lambda =>
  sourceSoninCarrier lambda →L[ℂ] finiteSCarrier

/-! ## Coordinate extraction -/

/-- The ambient-loss coordinate of a packed physical factor. -/
noncomputable def physicalFactorFirstCoordinate
    {lambda : CCM24SoninScale}
    (factor : sourceSoninCarrier lambda →L[ℂ]
      suffixEulerFrameAmbientBoundaryCarrier) :
    SourceToFinite lambda :=
  WithLp.fstL (p := 2) (𝕜 := ℂ)
    (α := finiteSCarrier) (β := finiteSCarrier) ∘L factor

private noncomputable def physicalFactorSecondCoordinate
    {lambda : CCM24SoninScale}
    (factor : sourceSoninCarrier lambda →L[ℂ]
      suffixEulerFrameAmbientBoundaryCarrier) :
    SourceToFinite lambda :=
  WithLp.sndL (p := 2) (𝕜 := ℂ)
    (α := finiteSCarrier) (β := finiteSCarrier) ∘L factor

private theorem withLpFstL_eq_leftEmbedding_adjoint :
    WithLp.fstL (p := 2) (𝕜 := ℂ)
        (α := finiteSCarrier) (β := finiteSCarrier) =
      suffixEulerFrameAmbientBoundaryLeftEmbedding† := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).2
  intro x y
  rw [suffixEulerFrameAmbientBoundaryLeftEmbedding_apply,
    WithLp.prod_inner_apply]
  simp

private theorem withLpSndL_eq_rightEmbedding_adjoint :
    WithLp.sndL (p := 2) (𝕜 := ℂ)
        (α := finiteSCarrier) (β := finiteSCarrier) =
      suffixEulerFrameAmbientBoundaryRightEmbedding† := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).2
  intro x y
  rw [suffixEulerFrameAmbientBoundaryRightEmbedding_apply,
    WithLp.prod_inner_apply]
  simp

private theorem newFrameAdjoint_comp_newRangeComplement_eq_zero
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    (suffixEulerFrameSchurStep lambda p S).newFrame† ∘L
        suffixEulerFrameNewRangeComplement lambda p S = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  have hpoint := DFunLike.congr_fun
    (suffixEulerFrameSchurStep lambda p S).newFrame_isometry
    (ContinuousLinearMap.adjoint
      (suffixEulerFrameSchurStep lambda p S).newFrame x)
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply] at hpoint
  simp only [suffixEulerFrameNewRangeComplement,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.zero_apply, ContinuousLinearMap.id_apply, map_sub]
  rw [hpoint]
  simp

set_option maxHeartbeats 4000000 in
-- Adjointing the packed decomposition crosses the concrete Sonin carrier.
set_option synthInstance.maxHeartbeats 200000 in
private theorem oldCarrierAnalysis_adjoint_comp_factor_eq_coordinates
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime)
    (factor : sourceSoninCarrier lambda →L[ℂ]
      suffixEulerFrameAmbientBoundaryCarrier) :
    (suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S)† ∘L
        factor =
      primeEulerAmbientLossFactor p ∘L
          physicalFactorFirstCoordinate factor +
        normalizedPrimeEulerFrameTransport p ∘L
          suffixEulerFrameNewRangeComplement lambda p S ∘L
            physicalFactorSecondCoordinate factor := by
  let ambientRow :=
    factor† ∘L suffixEulerFrameAmbientBoundaryLeftEmbedding
  let boundaryRow :=
    factor† ∘L suffixEulerFrameAmbientBoundaryRightEmbedding
  have hcomponents :=
    suffixEulerFrameAmbientBoundaryReadoutOfRows_components_eq (factor†)
  have hreadout :
      factor† ∘L
          suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S =
        ambientRow ∘L (primeEulerAmbientLossFactor p)† +
          boundaryRow ∘L
            suffixEulerFrameNewRangeComplement lambda p S ∘L
              (normalizedPrimeEulerFrameTransport p)† := by
    calc
      factor† ∘L
          suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S =
        suffixEulerFrameAmbientBoundaryReadoutOfRows
            ambientRow boundaryRow ∘L
          suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S := by
        rw [hcomponents]
      _ =
        ambientRow ∘L (primeEulerAmbientLossFactor p)† +
          boundaryRow ∘L
            ((ContinuousLinearMap.id ℂ finiteSCarrier -
                (suffixEulerFrameSchurStep lambda p S).newFrame ∘L
                  (suffixEulerFrameSchurStep lambda p S).newFrame†) ∘L
              (normalizedPrimeEulerFrameTransport p)†) :=
        suffixEulerFrameAmbientBoundaryReadoutOfRows_comp_oldCarrierAnalysis
          p S ambientRow boundaryRow
      _ =
        ambientRow ∘L (primeEulerAmbientLossFactor p)† +
          boundaryRow ∘L
            suffixEulerFrameNewRangeComplement lambda p S ∘L
              (normalizedPrimeEulerFrameTransport p)† := by
        rfl
  have hadjoint := congrArg ContinuousLinearMap.adjoint hreadout
  rw [ContinuousLinearMap.adjoint.map_add] at hadjoint
  simp only [ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint, physicalFactorFirstCoordinate,
    physicalFactorSecondCoordinate, ambientRow, boundaryRow,
    ContinuousLinearMap.comp_assoc] at hadjoint ⊢
  have hcomplementAdjoint :=
    (suffixEulerFrameNewRangeComplement_isStarProjection
      lambda p S).isSelfAdjoint
  change (suffixEulerFrameNewRangeComplement lambda p S)† =
    suffixEulerFrameNewRangeComplement lambda p S at hcomplementAdjoint
  rw [hcomplementAdjoint] at hadjoint
  rw [withLpFstL_eq_leftEmbedding_adjoint,
    withLpSndL_eq_rightEmbedding_adjoint]
  exact hadjoint

theorem physicalFactorFirstCoordinate_norm_le
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {bound : ℝ}
    (data : SuffixRawOldCarrierAntiresonantInteriorPhysicalFactorData
      owner lambda p S bound) :
    ‖physicalFactorFirstCoordinate data.factor‖ ≤ bound := by
  apply ContinuousLinearMap.opNorm_le_bound _ data.bound_nonneg
  intro x
  calc
    ‖physicalFactorFirstCoordinate data.factor x‖ ≤
        ‖data.factor x‖ := by
      simpa only [physicalFactorFirstCoordinate,
        ContinuousLinearMap.comp_apply] using
        (WithLp.norm_fst_le
          (α := finiteSCarrier) (β := finiteSCarrier)
          (p := 2) (data.factor x))
    _ ≤ ‖data.factor‖ * ‖x‖ :=
      data.factor.le_opNorm x
    _ ≤ bound * ‖x‖ :=
      mul_le_mul_of_nonneg_right data.factor_norm_le (norm_nonneg x)

set_option maxHeartbeats 4000000 in
-- Keep the complete physical cancellation intact until both coordinates meet.
theorem physicalFactorFirstCoordinate_factorization
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {bound : ℝ}
    (data : SuffixRawOldCarrierAntiresonantInteriorPhysicalFactorData
      owner lambda p S bound) :
    (suffixActualBandCompleteBoundaryReverseIntertwiningDefect
        owner lambda p S)† ∘L suffixEulerFrameTransition lambda p S =
      (suffixEulerFrameSchurStep lambda p S).newFrame† ∘L
        normalizedPrimeEulerInverse p ∘L
          primeEulerAmbientLossFactor p ∘L
            physicalFactorFirstCoordinate data.factor := by
  apply ContinuousLinearMap.ext
  intro x
  have hrho : (primeSchurMarkovScalar p : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr
      (ne_of_gt (primeSchurMarkovScalar_pos p))
  have hphysical :=
    SuffixRawOldCarrierAntiresonantInteriorPhysicalFactorData.ambient_factorization
      data
  have hphysicalPoint := DFunLike.congr_fun hphysical x
  simp only [
    suffixActualBandAntiresonantInteriorAmbientPhysicalCofactorResponse,
    ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply] at hphysicalPoint
  have hnormalized := congrArg
    (fun y : finiteSCarrier => normalizedPrimeEulerInverse p y)
    hphysicalPoint
  simp only [map_smul] at hnormalized
  let responseValue :=
    ContinuousLinearMap.adjoint
      (suffixActualBandCompleteBoundaryReverseIntertwiningDefect
        owner lambda p S)
      (suffixEulerFrameTransition lambda p S x)
  let analysisValue :=
    ContinuousLinearMap.adjoint
      (suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S)
      (data.factor x)
  change
    normalizedPrimeEulerInverse p
        (normalizedPrimeEulerFrameTransport p
          ((suffixEulerFrameSchurStep lambda p S).newFrame responseValue)) =
      (primeSchurMarkovScalar p : ℂ) •
        normalizedPrimeEulerInverse p analysisValue at hnormalized
  have hNUPoint := DFunLike.congr_fun
    (normalizedPrimeEulerInverse_comp_frameTransport p)
    ((suffixEulerFrameSchurStep lambda p S).newFrame responseValue)
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply] at hNUPoint
  rw [hNUPoint] at hnormalized
  have hjoint :
      (suffixEulerFrameSchurStep lambda p S).newFrame responseValue =
        normalizedPrimeEulerInverse p analysisValue := by
    have hzero :
        (primeSchurMarkovScalar p : ℂ) •
            ((suffixEulerFrameSchurStep lambda p S).newFrame responseValue -
              normalizedPrimeEulerInverse p analysisValue) = 0 := by
      rw [smul_sub, hnormalized]
      simp
    exact sub_eq_zero.mp
      ((smul_eq_zero.mp hzero).resolve_left hrho)
  have hframePoint := DFunLike.congr_fun
    (suffixEulerFrameSchurStep lambda p S).newFrame_isometry
    responseValue
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply] at hframePoint
  have hjointAdjoint := congrArg
    (fun y : finiteSCarrier =>
      ContinuousLinearMap.adjoint
        (suffixEulerFrameSchurStep lambda p S).newFrame y)
    hjoint
  change
    ContinuousLinearMap.adjoint
        (suffixEulerFrameSchurStep lambda p S).newFrame
        ((suffixEulerFrameSchurStep lambda p S).newFrame responseValue) =
      ContinuousLinearMap.adjoint
        (suffixEulerFrameSchurStep lambda p S).newFrame
        (normalizedPrimeEulerInverse p analysisValue) at hjointAdjoint
  rw [hframePoint] at hjointAdjoint
  have hdecompPoint := DFunLike.congr_fun
    (oldCarrierAnalysis_adjoint_comp_factor_eq_coordinates
      lambda p S data.factor)
    x
  change analysisValue = _ at hdecompPoint
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.add_apply] at hdecompPoint
  have hcollapse := congrArg
    (fun y : finiteSCarrier =>
      ContinuousLinearMap.adjoint
        (suffixEulerFrameSchurStep lambda p S).newFrame
        (normalizedPrimeEulerInverse p y))
    hdecompPoint
  simp only [map_add] at hcollapse
  have hNUComplement := DFunLike.congr_fun
    (normalizedPrimeEulerInverse_comp_frameTransport p)
    (suffixEulerFrameNewRangeComplement lambda p S
      (physicalFactorSecondCoordinate data.factor x))
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply] at hNUComplement
  rw [hNUComplement] at hcollapse
  have hJComplement := DFunLike.congr_fun
    (newFrameAdjoint_comp_newRangeComplement_eq_zero lambda p S)
    (physicalFactorSecondCoordinate data.factor x)
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.zero_apply] at hJComplement
  simp only [map_smul, hJComplement, smul_zero,
    add_zero] at hcollapse
  exact hjointAdjoint.trans hcollapse

/-- Projecting a physical factor to its first coordinate loses no norm. -/
noncomputable def
    SuffixRawOldCarrierAntiresonantInteriorPhysicalFactorData.toSingleChannelFactorData
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {bound : ℝ}
    (data : SuffixRawOldCarrierAntiresonantInteriorPhysicalFactorData
      owner lambda p S bound) :
    SuffixRawOldCarrierAntiresonantInteriorSingleChannelFactorData
      owner lambda p S bound :=
  { bound_nonneg := data.bound_nonneg
    factor := physicalFactorFirstCoordinate data.factor
    factor_norm_le := physicalFactorFirstCoordinate_norm_le data
    factorization := physicalFactorFirstCoordinate_factorization data }

/-! ## Existence and uniform-family equivalences -/

theorem exists_boundedSingleChannelFactor_iff_exists_boundedPhysicalFactor
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    (∃ bound : ℝ, Nonempty
        (SuffixRawOldCarrierAntiresonantInteriorSingleChannelFactorData
          owner lambda p S bound)) ↔
      ∃ bound : ℝ, Nonempty
        (SuffixRawOldCarrierAntiresonantInteriorPhysicalFactorData
          owner lambda p S bound) := by
  constructor
  · rintro ⟨bound, ⟨data⟩⟩
    exact ⟨17 * bound, ⟨data.toPhysicalFactorData⟩⟩
  · rintro ⟨bound, ⟨data⟩⟩
    exact ⟨bound, ⟨
      SuffixRawOldCarrierAntiresonantInteriorPhysicalFactorData.toSingleChannelFactorData
        data⟩⟩

/-- One common renewed-channel bound on all prime/suffix pairs. -/
structure SuffixRawOldCarrierAntiresonantInteriorUniformSingleChannelFactorData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (bound : ℝ) where
  bound_nonneg : 0 ≤ bound
  factor : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
    SuffixRawOldCarrierAntiresonantInteriorSingleChannelFactorData
      owner lambda p S bound

noncomputable def
    SuffixRawOldCarrierAntiresonantInteriorUniformSingleChannelFactorData.toUniformPhysicalFactorData
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {bound : ℝ}
    (data :
      SuffixRawOldCarrierAntiresonantInteriorUniformSingleChannelFactorData
        owner lambda bound) :
    SuffixRawOldCarrierAntiresonantInteriorUniformPhysicalFactorData
      owner lambda (17 * bound) :=
  { bound_nonneg := mul_nonneg (by norm_num) data.bound_nonneg
    factor := fun p S => (data.factor p S).toPhysicalFactorData }

noncomputable def
    SuffixRawOldCarrierAntiresonantInteriorUniformPhysicalFactorData.toUniformSingleChannelFactorData
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {bound : ℝ}
    (data : SuffixRawOldCarrierAntiresonantInteriorUniformPhysicalFactorData
      owner lambda bound) :
    SuffixRawOldCarrierAntiresonantInteriorUniformSingleChannelFactorData
      owner lambda bound :=
  { bound_nonneg := data.bound_nonneg
    factor := fun p S =>
      SuffixRawOldCarrierAntiresonantInteriorPhysicalFactorData.toSingleChannelFactorData
        (data.factor p S) }

theorem exists_uniformSingleChannelFactor_iff_exists_uniformPhysicalFactor
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    (∃ bound : ℝ, Nonempty
        (SuffixRawOldCarrierAntiresonantInteriorUniformSingleChannelFactorData
          owner lambda bound)) ↔
      ∃ bound : ℝ, Nonempty
        (SuffixRawOldCarrierAntiresonantInteriorUniformPhysicalFactorData
          owner lambda bound) := by
  constructor
  · rintro ⟨bound, ⟨data⟩⟩
    exact ⟨17 * bound, ⟨data.toUniformPhysicalFactorData⟩⟩
  · rintro ⟨bound, ⟨data⟩⟩
    exact ⟨bound, ⟨
      SuffixRawOldCarrierAntiresonantInteriorUniformPhysicalFactorData.toUniformSingleChannelFactorData
        data⟩⟩

/-- One common renewed-channel bound on every route-valid adjacent step. -/
structure SuffixRawOldCarrierAntiresonantInteriorRouteUniformSingleChannelFactorData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (bound : ℝ) where
  bound_nonneg : 0 ≤ bound
  factor : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
    SuffixRouteValidStep p S →
      SuffixRawOldCarrierAntiresonantInteriorSingleChannelFactorData
        owner lambda p S bound

noncomputable def
    SuffixRawOldCarrierAntiresonantInteriorRouteUniformSingleChannelFactorData.toRouteUniformPhysicalFactorData
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {bound : ℝ}
    (data :
      SuffixRawOldCarrierAntiresonantInteriorRouteUniformSingleChannelFactorData
        owner lambda bound) :
    SuffixRawOldCarrierAntiresonantInteriorRouteUniformPhysicalFactorData
      owner lambda (17 * bound) :=
  { bound_nonneg := mul_nonneg (by norm_num) data.bound_nonneg
    factor := fun p S hvalid =>
      (data.factor p S hvalid).toPhysicalFactorData }

noncomputable def
    SuffixRawOldCarrierAntiresonantInteriorRouteUniformPhysicalFactorData.toRouteUniformSingleChannelFactorData
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {bound : ℝ}
    (data :
      SuffixRawOldCarrierAntiresonantInteriorRouteUniformPhysicalFactorData
        owner lambda bound) :
    SuffixRawOldCarrierAntiresonantInteriorRouteUniformSingleChannelFactorData
      owner lambda bound :=
  { bound_nonneg := data.bound_nonneg
    factor := fun p S hvalid =>
      SuffixRawOldCarrierAntiresonantInteriorPhysicalFactorData.toSingleChannelFactorData
        (data.factor p S hvalid) }

theorem
    exists_routeUniformSingleChannelFactor_iff_exists_routeUniformPhysicalFactor
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    (∃ bound : ℝ, Nonempty
        (SuffixRawOldCarrierAntiresonantInteriorRouteUniformSingleChannelFactorData
          owner lambda bound)) ↔
      ∃ bound : ℝ, Nonempty
        (SuffixRawOldCarrierAntiresonantInteriorRouteUniformPhysicalFactorData
          owner lambda bound) := by
  constructor
  · rintro ⟨bound, ⟨data⟩⟩
    exact ⟨17 * bound, ⟨data.toRouteUniformPhysicalFactorData⟩⟩
  · rintro ⟨bound, ⟨data⟩⟩
    exact ⟨bound, ⟨
      SuffixRawOldCarrierAntiresonantInteriorRouteUniformPhysicalFactorData.toRouteUniformSingleChannelFactorData
        data⟩⟩

/-- Select the renewed channel on a genuine suffix of a finite family. -/
noncomputable def
    SuffixRawOldCarrierAntiresonantInteriorRouteUniformSingleChannelFactorData.forFamilySuffix
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {bound : ℝ}
    (data :
      SuffixRawOldCarrierAntiresonantInteriorRouteUniformSingleChannelFactorData
        owner lambda bound)
    (family : FinitePrimePowerFamily)
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
    (hsuffix : p :: S <:+ family.visiblePrimes) :
    SuffixRawOldCarrierAntiresonantInteriorSingleChannelFactorData
      owner lambda p S bound :=
  data.factor p S
    (suffixRouteValidStep_of_isSuffix_visiblePrimes family p S hsuffix)

end CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorSingleChannelFactorization
end CCM25Concrete
end Source
end ConnesWeilRH
