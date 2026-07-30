/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantRadialSplit
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierMovingMomentColumnSelector

/-!
# Response split for the antiresonant Bone 1 column

Proof 610 splits the ambient-loss column into orthogonal radial-interior and
finite-window boundary pieces.  This module applies one and the same
hypothetical Bone 1 readout to both pieces before making any estimate:

```text
reducedRow * newFrame = interiorResponse + boundaryResponse.
```

The boundary response is bounded by the ambient-loss scalar and hence tends
to zero along the arithmetic primes, uniformly in the suffix.  Thus any
family-uniform Bone 1 factor must make the radial-interior response
asymptotically equal to the complete reduced-row column.

This is a necessary consequence of a supplied response factor.  It does not
construct that factor, control the interior antiresonance, close Gate 3U,
prove the finite-S sign, supply Burnol's identity, or prove RH.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantResponseSplit

open scoped InnerProduct InnerProductSpace Topology

open CC20Concrete
open CCM24FiniteSActualJuliaRangeSineAmbientScaleGuard
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCompletedJuliaAmbientDefectFactorization
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantRadialSplit
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeAntiresonantReduction
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeJointGapResponseReadout
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierMovingMomentColumnSelector
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierReduction
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSProjectionTrace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace
      (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! ## The two responses with a shared readout -/

/-- The response of a supplied Bone 1 factor to the radial-interior column. -/
noncomputable def newFrameAntiresonantRadialInteriorResponse
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {bound : ℝ}
    (data : SuffixRawOldCarrierCoframeJointGapResponseReadoutData owner
      lambda p S bound) :
    sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
  newFrameAntiresonantReadout data ∘L
    newFrameAntiresonantRadialInterior lambda p S

/-- The response of the same supplied Bone 1 factor to the completed radial
boundary crossing. -/
noncomputable def newFrameAntiresonantRadialBoundaryResponse
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {bound : ℝ}
    (data : SuffixRawOldCarrierCoframeJointGapResponseReadoutData owner
      lambda p S bound) :
    sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
  newFrameAntiresonantReadout data ∘L
    newFrameAntiresonantRadialBoundary lambda p S

/-- Exact response split.  Both summands use the same readout, so no signed
cancellation is discarded. -/
theorem reducedRow_comp_newFrame_eq_radialResponses
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {bound : ℝ}
    (data : SuffixRawOldCarrierCoframeJointGapResponseReadoutData owner
      lambda p S bound) :
    suffixActualBandRawPhysicalReducedRow owner lambda p S ∘L
        newSuffixFrame lambda S =
      newFrameAntiresonantRadialInteriorResponse data +
        newFrameAntiresonantRadialBoundaryResponse data := by
  apply ContinuousLinearMap.ext
  intro x
  have hfactor := DFunLike.congr_fun
    (newFrameAntiresonantReadout_factorization data) x
  have hsplit := DFunLike.congr_fun
    (newFrameAntiresonantColumn_eq_radialInterior_add_boundary lambda p S) x
  have hfactor' :
      newFrameAntiresonantReadout data
          (newFrameAntiresonantColumn lambda p S x) =
        suffixActualBandRawPhysicalReducedRow owner lambda p S
          (newSuffixFrame lambda S x) := by
    simpa only [newFrameAntiresonantColumn, newSuffixFrame,
      ContinuousLinearMap.comp_apply] using hfactor
  have hsplit' :
      newFrameAntiresonantColumn lambda p S x =
        newFrameAntiresonantRadialInterior lambda p S x +
          newFrameAntiresonantRadialBoundary lambda p S x := by
    simpa only [ContinuousLinearMap.add_apply] using hsplit
  simp only [newFrameAntiresonantRadialInteriorResponse,
    newFrameAntiresonantRadialBoundaryResponse,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply]
  rw [← hfactor', hsplit', map_add]

/-- The completed-boundary response inherits both the common readout bound
and the ambient-loss scale. -/
theorem norm_newFrameAntiresonantRadialBoundaryResponse_le
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {bound : ℝ}
    (data : SuffixRawOldCarrierCoframeJointGapResponseReadoutData owner
      lambda p S bound) :
    ‖newFrameAntiresonantRadialBoundaryResponse data‖ ≤
      (2 * bound) * primeEulerAmbientLossScale p := by
  unfold newFrameAntiresonantRadialBoundaryResponse
  calc
    ‖newFrameAntiresonantReadout data ∘L
        newFrameAntiresonantRadialBoundary lambda p S‖ ≤
      ‖newFrameAntiresonantReadout data‖ *
        ‖newFrameAntiresonantRadialBoundary lambda p S‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (2 * bound) *
        ‖newFrameAntiresonantRadialBoundary lambda p S‖ := by
      exact mul_le_mul_of_nonneg_right
        (newFrameAntiresonantReadout_norm_le data) (norm_nonneg _)
    _ ≤ (2 * bound) * primeEulerAmbientLossScale p := by
      exact mul_le_mul_of_nonneg_left
        (newFrameAntiresonantRadialBoundary_norm_le_scale lambda p S)
        (mul_nonneg (by norm_num) data.bound_nonneg)

/-- Removing the interior response leaves exactly the completed-boundary
response. -/
theorem reducedRow_comp_newFrame_sub_radialInteriorResponse_eq_boundary
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {bound : ℝ}
    (data : SuffixRawOldCarrierCoframeJointGapResponseReadoutData owner
      lambda p S bound) :
    suffixActualBandRawPhysicalReducedRow owner lambda p S ∘L
          newSuffixFrame lambda S -
        newFrameAntiresonantRadialInteriorResponse data =
      newFrameAntiresonantRadialBoundaryResponse data := by
  rw [reducedRow_comp_newFrame_eq_radialResponses data]
  abel

theorem norm_reducedRow_comp_newFrame_sub_radialInteriorResponse_le
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {bound : ℝ}
    (data : SuffixRawOldCarrierCoframeJointGapResponseReadoutData owner
      lambda p S bound) :
    ‖suffixActualBandRawPhysicalReducedRow owner lambda p S ∘L
          newSuffixFrame lambda S -
        newFrameAntiresonantRadialInteriorResponse data‖ ≤
      (2 * bound) * primeEulerAmbientLossScale p := by
  rw [reducedRow_comp_newFrame_sub_radialInteriorResponse_eq_boundary data]
  exact norm_newFrameAntiresonantRadialBoundaryResponse_le data

/-! ## Arithmetic-prime decay of the boundary response -/

theorem primeEulerAmbientLossScale_le_sqrt_coefficient
    (p : CCM24VisiblePrime) :
    primeEulerAmbientLossScale p ≤
      Real.sqrt (ccm24PrimeEulerCoefficient p) := by
  have hq : 0 ≤ ccm24PrimeEulerCoefficient p :=
    (ccm24PrimeEulerCoefficient_pos p).le
  have hden : 0 < 1 + ccm24PrimeEulerCoefficient p := by linarith
  unfold primeEulerAmbientLossScale
  apply (div_le_iff₀ hden).2
  calc
    Real.sqrt (ccm24PrimeEulerCoefficient p) =
        Real.sqrt (ccm24PrimeEulerCoefficient p) * 1 := by ring
    _ ≤ Real.sqrt (ccm24PrimeEulerCoefficient p) *
        (1 + ccm24PrimeEulerCoefficient p) := by
      exact mul_le_mul_of_nonneg_left (by linarith)
        (Real.sqrt_nonneg _)

theorem tendsto_primeEulerAmbientLossScale_arithmeticVisiblePrimeSequence :
    Filter.Tendsto
      (fun n => primeEulerAmbientLossScale
        (arithmeticVisiblePrimeSequence n))
      Filter.atTop (𝓝 0) := by
  have hcoeff :=
    tendsto_ccm24PrimeEulerCoefficient_arithmeticVisiblePrimeSequence
  have hsqrt : Filter.Tendsto
      (fun n => Real.sqrt (ccm24PrimeEulerCoefficient
        (arithmeticVisiblePrimeSequence n)))
      Filter.atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto 0).comp hcoeff
  exact squeeze_zero
    (fun n => primeEulerAmbientLossScale_nonneg
      (arithmeticVisiblePrimeSequence n))
    (fun n => primeEulerAmbientLossScale_le_sqrt_coefficient
      (arithmeticVisiblePrimeSequence n))
    hsqrt

/-- Under a supplied family-uniform Bone 1 factor, the completed radial
boundary response tends to zero for every moving suffix sequence. -/
theorem tendsto_norm_radialBoundaryResponse_arithmeticVisiblePrimeSequence
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {bound : ℝ}
    (data : SuffixRawOldCarrierCoframeUniformJointGapResponseReadoutData
      owner lambda bound)
    (S : ℕ → List CCM24VisiblePrime) :
    Filter.Tendsto
      (fun n => ‖newFrameAntiresonantRadialBoundaryResponse
        (data.factor (arithmeticVisiblePrimeSequence n) (S n))‖)
      Filter.atTop (𝓝 0) := by
  have hupper : ∀ n,
      ‖newFrameAntiresonantRadialBoundaryResponse
          (data.factor (arithmeticVisiblePrimeSequence n) (S n))‖ ≤
        (2 * bound) * primeEulerAmbientLossScale
          (arithmeticVisiblePrimeSequence n) := by
    intro n
    exact norm_newFrameAntiresonantRadialBoundaryResponse_le
      (data.factor (arithmeticVisiblePrimeSequence n) (S n))
  have hlimit : Filter.Tendsto
      (fun n => (2 * bound) * primeEulerAmbientLossScale
        (arithmeticVisiblePrimeSequence n))
      Filter.atTop (𝓝 0) := by
    simpa only [mul_zero] using
      tendsto_primeEulerAmbientLossScale_arithmeticVisiblePrimeSequence.const_mul
        (2 * bound)
  exact squeeze_zero (fun n => norm_nonneg _) hupper hlimit

/-- Equivalently, under a supplied uniform factor the hard radial-interior
response is asymptotically the complete reduced-row column. -/
theorem tendsto_norm_reducedRow_sub_radialInteriorResponse
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {bound : ℝ}
    (data : SuffixRawOldCarrierCoframeUniformJointGapResponseReadoutData
      owner lambda bound)
    (S : ℕ → List CCM24VisiblePrime) :
    Filter.Tendsto
      (fun n =>
        ‖suffixActualBandRawPhysicalReducedRow owner lambda
              (arithmeticVisiblePrimeSequence n) (S n) ∘L
            newSuffixFrame lambda (S n) -
          newFrameAntiresonantRadialInteriorResponse
            (data.factor (arithmeticVisiblePrimeSequence n) (S n))‖)
      Filter.atTop (𝓝 0) := by
  have hboundary :=
    tendsto_norm_radialBoundaryResponse_arithmeticVisiblePrimeSequence data S
  refine hboundary.congr' (Filter.Eventually.of_forall fun n => ?_)
  exact congrArg norm
    (reducedRow_comp_newFrame_sub_radialInteriorResponse_eq_boundary
      (data.factor (arithmeticVisiblePrimeSequence n) (S n))).symm

end CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantResponseSplit
end CCM25Concrete
end Source
end ConnesWeilRH
