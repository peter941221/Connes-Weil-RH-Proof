/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3SourceCompressedRootKernel
import ConnesWeilRH.Dev.C1G8R3ScaleDetectorRootSquareSum

/-!
# Prolate correction energy for the direct S3 kernel

The direct source-compressed root has the exact decomposition
`HardyCorner - J† R C J`, where `R` is the committed source-prolate
remainder.  This leaf proves that the correction term `J† R C J` is
Hilbert--Schmidt on every named source basis.  It uses only the already
proved prolate Hilbert--Schmidt factor and bounded ideal calculus; no
estimate on the Hardy corner is smuggled in.
-/

namespace ConnesWeilRH
namespace Dev

open Source
open Source.CC20Concrete
open Source.CCM25Concrete
open Source.CCM25Concrete.CCM24FiniteSProjectionTrace
open Source.CCM25Concrete.CCM24FiniteSGramResponse
open Source.CCM25Concrete.CCM24FiniteSBandTrace
open Source.CCM25Concrete.CCM24SourceProlateTrace
open Source.CCM25Concrete.SelectedWeilSquare
open scoped InnerProductSpace

local notation "Carrier" => finiteSCarrier

noncomputable local instance prolateTermEnergyCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

set_option maxHeartbeats 4000000 in
/-- The prolate correction in the one-sided source-root decomposition has
square-summable columns on every named source basis. -/
theorem sourceCompressedRoot_prolateTerm_sourceBasis_normSq_summable
    (owner : SelectedWeilSquareOwner) (lambda : CCM24SoninScale)
    {rho : Type*}
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda)) :
    Summable fun i : rho =>
      ‖(((sourceInclusion lambda).adjoint ∘L
          sourceProlateRemainder lambda ∘L
          rootConvolution owner ∘L sourceInclusion lambda)
        (sourceBasis i))‖ ^ 2 := by
  obtain ⟨w, globalBasis, hglobal⟩ := exists_hilbertBasis ℂ Carrier
  let K := sourceProlateHilbertSchmidtFactor lambda
  let C := rootConvolution owner
  let J := sourceInclusion lambda
  have hK : Summable fun i => ‖K (globalBasis i)‖ ^ 2 :=
    sourceProlateHilbertSchmidtFactor_summable_all_scales globalBasis lambda
  have hKCJ : Summable fun i : rho =>
      ‖(K ∘L C ∘L J) (sourceBasis i)‖ ^ 2 := by
    exact PositiveTrace.summable_normSq_precomp globalBasis globalBasis
      sourceBasis K (C ∘L J) hK
  have hR : sourceProlateRemainder lambda = K.adjoint ∘L K := by
    simpa only [K] using
      (sourceProlateHilbertSchmidtFactor_adjoint_comp_self lambda).symm
  have hRK : Summable fun i : rho =>
      ‖(K.adjoint ∘L K ∘L C ∘L J) (sourceBasis i)‖ ^ 2 := by
    exact PositiveTrace.summable_normSq_postcomp sourceBasis
      (K ∘L C ∘L J) K.adjoint hKCJ
  have hfinal : Summable fun i : rho =>
      ‖(J.adjoint ∘L K.adjoint ∘L K ∘L C ∘L J)
        (sourceBasis i)‖ ^ 2 := by
    exact PositiveTrace.summable_normSq_postcomp sourceBasis
      (K.adjoint ∘L K ∘L C ∘L J) J.adjoint hRK
  simpa only [hR, K, C, J, ContinuousLinearMap.comp_assoc] using hfinal

set_option maxHeartbeats 4000000 in
/-- After removing the already Hilbert--Schmidt prolate correction, the direct
source-root square-sum is exactly the square-sum problem for the Hardy corner.
This is an iff, so no one-sided implication is hidden in the reduction. -/
theorem sourceCompressedRoot_squareSum_iff_hardyCorner_squareSum
    (owner : SelectedWeilSquareOwner) (lambda : CCM24SoninScale)
    {rho : Type*}
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda)) :
    (Summable fun i : rho =>
      ‖sourceCompressedRoot owner lambda (sourceBasis i)‖ ^ 2) ↔
    (Summable fun i : rho =>
      ‖(((sourceInclusion lambda).adjoint ∘L
          (radialSupportProjection lambda ∘L
            sourceFourierSupportProjection lambda ∘L
            radialSupportProjection lambda) ∘L
          rootConvolution owner ∘L sourceInclusion lambda)
        (sourceBasis i))‖ ^ 2) := by
  let correction :=
    (sourceInclusion lambda).adjoint ∘L sourceProlateRemainder lambda ∘L
      rootConvolution owner ∘L sourceInclusion lambda
  let corner :=
    (sourceInclusion lambda).adjoint ∘L
      (radialSupportProjection lambda ∘L
        sourceFourierSupportProjection lambda ∘L
        radialSupportProjection lambda) ∘L
      rootConvolution owner ∘L sourceInclusion lambda
  have hcorrection : Summable fun i : rho =>
      ‖correction (sourceBasis i)‖ ^ 2 := by
    simpa only [correction] using
      sourceCompressedRoot_prolateTerm_sourceBasis_normSq_summable
        owner lambda sourceBasis
  have hdecomp : sourceCompressedRoot owner lambda = corner - correction := by
    simpa only [corner, correction] using
      sourceCompressedRoot_eq_hardyCorner_sub_prolate_term owner lambda
  constructor
  · intro hroot
    have hsum := PositiveTrace.summable_normSq_add sourceBasis
      (sourceCompressedRoot owner lambda) correction hroot hcorrection
    refine hsum.congr (fun i => ?_)
    have hi := congrArg (fun T : sourceSoninCarrier lambda →L[ℂ]
        sourceSoninCarrier lambda => T (sourceBasis i)) hdecomp
    have hi' : sourceCompressedRoot owner lambda (sourceBasis i) =
        corner (sourceBasis i) - correction (sourceBasis i) := by
      simpa only [ContinuousLinearMap.sub_apply] using hi
    simp only [ContinuousLinearMap.add_apply]
    rw [hi']
    simp only [sub_add_cancel]
    rfl
  · intro hcorner
    have hneg : Summable fun i : rho =>
        ‖(-correction) (sourceBasis i)‖ ^ 2 := by
      exact hcorrection.congr (fun i => by simp)
    have hsum := PositiveTrace.summable_normSq_add sourceBasis
      corner (-correction) hcorner hneg
    refine hsum.congr (fun i => ?_)
    have hi := congrArg (fun T : sourceSoninCarrier lambda →L[ℂ]
        sourceSoninCarrier lambda => T (sourceBasis i)) hdecomp
    have hi' : sourceCompressedRoot owner lambda (sourceBasis i) =
        corner (sourceBasis i) - correction (sourceBasis i) := by
      simpa only [ContinuousLinearMap.sub_apply] using hi
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.neg_apply]
    rw [← sub_eq_add_neg]
    rw [hi'.symm]

end Dev
end ConnesWeilRH
