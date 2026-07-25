/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalFactorization

/-!
# Kernel consequences of the component-row readout

Proof 532--535 identify the source-specific Gate 3U producer with two
component rows on the actual ambient-plus-boundary physical carrier.  This
module records the immediate kernel consequences of that interface.

The point is bookkeeping, but useful bookkeeping: a component-row producer
does not merely give an abstract existence equivalence.  It kills the raw
four-term adjoint on the actual physical-analysis kernel, and therefore also
kills the complete polar/raw mismatch there.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedJuliaComponentKernel

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCompletedJuliaAmbientDefectFactorization
open CCM24FiniteSCompletedJuliaMismatchFactorization
open CCM24FiniteSCompletedJuliaRawPhysicalFactorization
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSProjectionTrace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) :
      CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

local notation "SourceOp" lambda =>
  sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda

/-! ## Physical kernel and co-defect kernel -/

/-- The packed physical-analysis norm is exactly the adjacent left-co-defect
norm. -/
theorem suffixEulerFrameAmbientBoundaryAnalysis_norm_eq_leftCoDefect
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (x : sourceSoninCarrier lambda) :
    ‖suffixEulerFrameAmbientBoundaryAnalysis lambda p S x‖ =
      ‖(suffixEulerFrameSchurStep lambda p S).leftCoDefect x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  exact suffixEulerFrameAmbientBoundaryAnalysis_normSq_eq_leftCoDefect
    lambda p S x

/-- Component rows bound the raw four-term adjoint against the actual
left-co-defect norm, not only against the packed carrier norm. -/
theorem componentReadout_rawAdjoint_norm_le_leftCoDefect
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {ambientBound boundaryBound : ℝ}
    (data : SuffixRawAmbientBoundaryComponentReadoutData
      owner lambda p S ambientBound boundaryBound)
    (x : sourceSoninCarrier lambda) :
    ‖((suffixActualBandRawQuadraticIntertwiningDefect
        owner lambda p S)†) x‖ ≤
      (ambientBound + boundaryBound) *
        ‖(suffixEulerFrameSchurStep lambda p S).leftCoDefect x‖ := by
  have hnorm :=
    suffixEulerFrameAmbientBoundaryAnalysis_norm_eq_leftCoDefect
      lambda p S x
  calc
    ‖((suffixActualBandRawQuadraticIntertwiningDefect
        owner lambda p S)†) x‖ ≤
        (ambientBound + boundaryBound) *
          ‖suffixEulerFrameAmbientBoundaryAnalysis lambda p S x‖ :=
      data.rawAdjoint_norm_le x
    _ = (ambientBound + boundaryBound) *
          ‖(suffixEulerFrameSchurStep lambda p S).leftCoDefect x‖ := by
      rw [hnorm]

/-- On the physical-analysis kernel, the component-row factorization kills
the raw four-term adjoint. -/
theorem componentReadout_rawAdjoint_eq_zero_of_analysis_eq_zero
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {ambientBound boundaryBound : ℝ}
    (data : SuffixRawAmbientBoundaryComponentReadoutData
      owner lambda p S ambientBound boundaryBound)
    (x : sourceSoninCarrier lambda)
    (hx : suffixEulerFrameAmbientBoundaryAnalysis lambda p S x = 0) :
    ((suffixActualBandRawQuadraticIntertwiningDefect
      owner lambda p S)†) x = 0 := by
  have hfactor := congrArg (fun operator : SourceOp lambda => operator x)
    data.toRawReadout.factorization
  simpa only [ContinuousLinearMap.comp_apply, hx, map_zero] using hfactor.symm

/-- The same raw vanishing can be read from the adjacent left-co-defect
kernel. -/
theorem componentReadout_rawAdjoint_eq_zero_of_leftCoDefect_eq_zero
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {ambientBound boundaryBound : ℝ}
    (data : SuffixRawAmbientBoundaryComponentReadoutData
      owner lambda p S ambientBound boundaryBound)
    (x : sourceSoninCarrier lambda)
    (hx : (suffixEulerFrameSchurStep lambda p S).leftCoDefect x = 0) :
    ((suffixActualBandRawQuadraticIntertwiningDefect
      owner lambda p S)†) x = 0 := by
  apply componentReadout_rawAdjoint_eq_zero_of_analysis_eq_zero data x
  exact
    (suffixEulerFrameAmbientBoundaryAnalysis_eq_zero_iff_leftCoDefect_eq_zero
      lambda p S x).mpr hx

/-- Component rows also kill the complete polar/raw mismatch on the physical
analysis kernel. -/
theorem componentReadout_mismatchAdjoint_eq_zero_of_analysis_eq_zero
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {ambientBound boundaryBound : ℝ}
    (data : SuffixRawAmbientBoundaryComponentReadoutData
      owner lambda p S ambientBound boundaryBound)
    (x : sourceSoninCarrier lambda)
    (hx : suffixEulerFrameAmbientBoundaryAnalysis lambda p S x = 0) :
    ((suffixActualBandRoutePolarRawMismatchIntertwiningDefect
      owner lambda p S)†) x = 0 := by
  have hkernel :=
    suffixMismatchIntertwining_adjoint_on_ambientBoundaryKernel
      owner lambda p S x hx
  have hraw :=
    componentReadout_rawAdjoint_eq_zero_of_analysis_eq_zero data x hx
  rw [hkernel, hraw, neg_zero]

/-- The complete mismatch vanishing can equivalently be read from the
left-co-defect kernel. -/
theorem componentReadout_mismatchAdjoint_eq_zero_of_leftCoDefect_eq_zero
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {ambientBound boundaryBound : ℝ}
    (data : SuffixRawAmbientBoundaryComponentReadoutData
      owner lambda p S ambientBound boundaryBound)
    (x : sourceSoninCarrier lambda)
    (hx : (suffixEulerFrameSchurStep lambda p S).leftCoDefect x = 0) :
    ((suffixActualBandRoutePolarRawMismatchIntertwiningDefect
      owner lambda p S)†) x = 0 := by
  apply componentReadout_mismatchAdjoint_eq_zero_of_analysis_eq_zero data x
  exact
    (suffixEulerFrameAmbientBoundaryAnalysis_eq_zero_iff_leftCoDefect_eq_zero
      lambda p S x).mpr hx

/-! ## Uniform-family versions -/

/-- The uniform component package gives the raw adjoint estimate at every
visible-prime/suffix step against the actual left co-defect. -/
theorem uniformComponentReadout_rawAdjoint_norm_le_leftCoDefect
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {ambientBound boundaryBound : ℝ}
    (data : SuffixRawAmbientBoundaryUniformComponentReadoutData
      owner lambda ambientBound boundaryBound)
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
    (x : sourceSoninCarrier lambda) :
    ‖((suffixActualBandRawQuadraticIntertwiningDefect
        owner lambda p S)†) x‖ ≤
      (ambientBound + boundaryBound) *
        ‖(suffixEulerFrameSchurStep lambda p S).leftCoDefect x‖ :=
  componentReadout_rawAdjoint_norm_le_leftCoDefect
    (data.readout p S) x

/-- A uniform component package kills every raw four-term adjoint on every
physical-analysis kernel. -/
theorem uniformComponentReadout_rawAdjoint_eq_zero_of_analysis_eq_zero
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {ambientBound boundaryBound : ℝ}
    (data : SuffixRawAmbientBoundaryUniformComponentReadoutData
      owner lambda ambientBound boundaryBound)
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
    (x : sourceSoninCarrier lambda)
    (hx : suffixEulerFrameAmbientBoundaryAnalysis lambda p S x = 0) :
    ((suffixActualBandRawQuadraticIntertwiningDefect
      owner lambda p S)†) x = 0 :=
  componentReadout_rawAdjoint_eq_zero_of_analysis_eq_zero
    (data.readout p S) x hx

/-- A uniform component package kills every complete mismatch adjoint on every
physical-analysis kernel. -/
theorem uniformComponentReadout_mismatchAdjoint_eq_zero_of_analysis_eq_zero
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {ambientBound boundaryBound : ℝ}
    (data : SuffixRawAmbientBoundaryUniformComponentReadoutData
      owner lambda ambientBound boundaryBound)
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
    (x : sourceSoninCarrier lambda)
    (hx : suffixEulerFrameAmbientBoundaryAnalysis lambda p S x = 0) :
    ((suffixActualBandRoutePolarRawMismatchIntertwiningDefect
      owner lambda p S)†) x = 0 :=
  componentReadout_mismatchAdjoint_eq_zero_of_analysis_eq_zero
    (data.readout p S) x hx

end CCM24FiniteSCompletedJuliaComponentKernel
end CCM25Concrete
end Source
end ConnesWeilRH
