/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFrameLossRadialPhysicalOwnerCompression

/-!
# Complementary radial physical-owner readout

Proof 678 completes the two-sided carrier ledger for the signed radial owner.
The upper-support compression keeps the three-branch interior channel, while
the complementary compression keeps the one-sided boundary channel.

These are exact identities only; no branchwise estimate is introduced.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace AntiresonantFrameLossRadialPhysicalOwnerComplement

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open AntiresonantFrameLossRadialBoundarySplit
open AntiresonantFrameLossRadialReduction
open AntiresonantFrameLossRadialPhysicalOwner
open AntiresonantFrameLossRadialInteriorPhysicalExpansion
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantRadialBlockRecurrence
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorAdjacentProjectionGap
open CCM24FiniteSProjectionTrace
open CCM24UnitScaleProlateAlignment
open CCM24FiniteSParameterizedSoninProjection

/-! ## Complementary radial carriers -/

/-- The complementary radial projection annihilates the upper radial
projection. -/
theorem radialComplement_comp_radialSupportProjection_eq_zero
    (lambda : CCM24SoninScale) :
    radialComplement lambda ∘L radialSupportProjection lambda = 0 := by
  have hprojection :
      radialSupportProjection lambda ∘L radialSupportProjection lambda =
        radialSupportProjection lambda := by
    simpa only [ContinuousLinearMap.mul_def] using
      (radialSupportProjection_isStarProjection lambda).isIdempotentElem
  apply ContinuousLinearMap.ext
  intro u
  simp only [radialComplement, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]
  have hu := DFunLike.congr_fun hprojection u
  simp only [ContinuousLinearMap.comp_apply] at hu
  rw [hu]
  exact sub_self _

/-! ## Interior and boundary outputs -/

/-- The complementary radial projection kills the compressed interior
commutator. -/
theorem radialComplement_comp_radialInteriorSoninCommutator_eq_zero
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime) :
    radialComplement unitSoninScale ∘L
        radialInteriorSoninCommutator p S = 0 := by
  apply ContinuousLinearMap.ext
  intro u
  have hfirst := DFunLike.congr_fun
    (radialComplement_comp_radialSupportProjection_eq_zero unitSoninScale)
    ((cc20GlobalLogTranslation (Real.log p)).toContinuousLinearMap
      (radialSupportProjection unitSoninScale
        (newSuffixRangeProjection unitSoninScale S u)))
  have hsecond := DFunLike.congr_fun
    (radialComplement_comp_newSuffixRangeProjection_eq_zero
      unitSoninScale S)
    (radialCompressedPositiveTranslation p u)
  have hfirst' :
      radialComplement unitSoninScale
          (radialSupportProjection unitSoninScale
            ((cc20GlobalLogTranslation (Real.log p)).toContinuousLinearMap
              (radialSupportProjection unitSoninScale
                (newSuffixRangeProjection unitSoninScale S u)))) = 0 := by
    simpa only [ContinuousLinearMap.comp_apply] using hfirst
  have hsecond' :
      radialComplement unitSoninScale
          (newSuffixRangeProjection unitSoninScale S
            (radialCompressedPositiveTranslation p u)) = 0 := by
    simpa only [ContinuousLinearMap.comp_apply] using hsecond
  have hsecond'' :
      radialComplement unitSoninScale
          (newSuffixRangeProjection unitSoninScale S
            (radialSupportProjection unitSoninScale
              ((cc20GlobalLogTranslation (Real.log p)).toContinuousLinearMap
                (radialSupportProjection unitSoninScale u)))) = 0 := by
    simpa only [radialCompressedPositiveTranslation,
      ContinuousLinearMap.comp_apply] using hsecond'
  simp only [radialInteriorSoninCommutator, radialCompressedPositiveTranslation,
    cc20Commutator, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, map_sub] at ⊢
  rw [hfirst', hsecond'']
  exact sub_self _

/-- The complementary radial projection fixes the boundary channel. -/
theorem radialComplement_comp_radialSoninBoundaryCrossing_eq_self
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime) :
    radialComplement unitSoninScale ∘L
        radialSoninBoundaryCrossing p S =
      radialSoninBoundaryCrossing p S := by
  have hprojection :
      radialComplement unitSoninScale ∘L radialComplement unitSoninScale =
        radialComplement unitSoninScale := by
    simpa only [ContinuousLinearMap.mul_def, radialComplement] using
      (radialSupportProjection_isStarProjection unitSoninScale).one_sub.isIdempotentElem
  apply ContinuousLinearMap.ext
  intro u
  have hu := DFunLike.congr_fun hprojection
    ((cc20GlobalLogTranslation (Real.log p)).toContinuousLinearMap
      (newSuffixRangeProjection unitSoninScale S u))
  simpa only [radialSoninBoundaryCrossing,
    ContinuousLinearMap.comp_apply] using hu

/-! ## Complementary owner readback -/

/-- The complementary radial compression of the complete owner is exactly
the radial boundary channel. -/
theorem radialComplement_comp_radialSignedPhysicalOwner_eq_boundary
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime) :
    radialComplement unitSoninScale ∘L
        radialSignedPhysicalOwner p S =
      radialSoninBoundaryCrossing p S := by
  have hinterior :=
    radialComplement_comp_radialInteriorSoninCommutator_eq_zero p S
  have hthree :
      radialComplement unitSoninScale ∘L
          (-cc20ThreeBranchCommutator
            (radialSupportProjection unitSoninScale)
            (parameterizedFourierSupportProjection unitSoninScale 1 S
              (by norm_num))
            (parameterizedProlateRemainder unitSoninScale 1 S (by norm_num))
            (radialCompressedPositiveTranslation p)) = 0 := by
    rw [← radialInteriorSoninCommutator_eq_neg_threeBranch p S]
    exact hinterior
  unfold radialSignedPhysicalOwner
  apply ContinuousLinearMap.ext
  intro u
  have hthreePoint := DFunLike.congr_fun hthree u
  have hthreePoint' :
      radialComplement unitSoninScale
          ((-cc20ThreeBranchCommutator
            (radialSupportProjection unitSoninScale)
            (parameterizedFourierSupportProjection unitSoninScale 1 S
              (by norm_num))
            (parameterizedProlateRemainder unitSoninScale 1 S (by norm_num))
            (radialCompressedPositiveTranslation p)) u) = 0 := by
    simpa only [ContinuousLinearMap.comp_apply] using hthreePoint
  have hboundaryPoint := DFunLike.congr_fun
    (radialComplement_comp_radialSoninBoundaryCrossing_eq_self p S) u
  have hboundaryPoint' :
      radialComplement unitSoninScale
          (radialSoninBoundaryCrossing p S u) =
        radialSoninBoundaryCrossing p S u := by
    simpa only [ContinuousLinearMap.comp_apply] using hboundaryPoint
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.add_apply, map_add] at ⊢
  rw [hthreePoint']
  simpa only [zero_add] using hboundaryPoint'

end AntiresonantFrameLossRadialPhysicalOwnerComplement
end CCM25Concrete
end Source
end ConnesWeilRH
