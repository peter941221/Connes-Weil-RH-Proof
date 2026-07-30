/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFrameLossRadialPhysicalOwner

/-!
# Radial physical-owner compression

Proof 677 records the carrier distinction for the signed radial owner.  The
boundary channel is genuinely outside the upper radial carrier, so left
compression by the upper-support projection removes it exactly.  The
uncompressed owner still contains that channel.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace AntiresonantFrameLossRadialPhysicalOwnerCompression

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open AntiresonantFrameLossRadialBoundarySplit
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantRadialBlockRecurrence
open AntiresonantFrameLossRadialReduction
open AntiresonantFrameLossRadialPhysicalOwner
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorAdjacentProjectionGap
open CCM24FiniteSParameterizedSoninProjection
open CCM24FiniteSProjectionTrace
open CCM24UnitScaleProlateAlignment

/-! ## Orthogonal radial carriers -/

/-- The upper radial projection annihilates its complementary projection. -/
theorem radialSupportProjection_comp_radialComplement_eq_zero
    (lambda : CCM24SoninScale) :
    radialSupportProjection lambda ∘L radialComplement lambda = 0 := by
  have hprojection :
      radialSupportProjection lambda ∘L radialSupportProjection lambda =
        radialSupportProjection lambda := by
    simpa only [ContinuousLinearMap.mul_def] using
      (radialSupportProjection_isStarProjection lambda).isIdempotentElem
  apply ContinuousLinearMap.ext
  intro u
  simp only [radialComplement, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, map_sub]
  have hu := DFunLike.congr_fun hprojection u
  simp only [ContinuousLinearMap.comp_apply] at hu
  rw [hu]
  exact sub_self _

/-- The radial boundary channel has no upper-radial output. -/
theorem radialSupportProjection_comp_radialSoninBoundaryCrossing_eq_zero
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime) :
    radialSupportProjection unitSoninScale ∘L
        radialSoninBoundaryCrossing p S = 0 := by
  apply ContinuousLinearMap.ext
  intro u
  have hzero := DFunLike.congr_fun
    (radialSupportProjection_comp_radialComplement_eq_zero unitSoninScale)
    ((cc20GlobalLogTranslation (Real.log p)).toContinuousLinearMap
      (newSuffixRangeProjection unitSoninScale S u))
  simpa only [radialSoninBoundaryCrossing,
    ContinuousLinearMap.comp_apply] using hzero

/-! ## Compressed owner readback -/

/-- After left compression to the upper radial carrier, the signed physical
owner is exactly its negative three-branch interior component. -/
theorem radialSupportProjection_comp_radialSignedPhysicalOwner_eq_neg_threeBranch
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime) :
    radialSupportProjection unitSoninScale ∘L
        radialSignedPhysicalOwner p S =
      radialSupportProjection unitSoninScale ∘L
        (-cc20ThreeBranchCommutator
          (radialSupportProjection unitSoninScale)
          (parameterizedFourierSupportProjection unitSoninScale 1 S
            (by norm_num))
          (parameterizedProlateRemainder unitSoninScale 1 S (by norm_num))
          (radialCompressedPositiveTranslation p)) := by
  have hboundary :=
    radialSupportProjection_comp_radialSoninBoundaryCrossing_eq_zero p S
  unfold radialSignedPhysicalOwner
  apply ContinuousLinearMap.ext
  intro u
  have hboundaryPoint := DFunLike.congr_fun hboundary u
  simp only [ContinuousLinearMap.comp_apply] at hboundaryPoint
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.add_apply, map_add]
  rw [hboundaryPoint]
  simp

end AntiresonantFrameLossRadialPhysicalOwnerCompression
end CCM25Concrete
end Source
end ConnesWeilRH
