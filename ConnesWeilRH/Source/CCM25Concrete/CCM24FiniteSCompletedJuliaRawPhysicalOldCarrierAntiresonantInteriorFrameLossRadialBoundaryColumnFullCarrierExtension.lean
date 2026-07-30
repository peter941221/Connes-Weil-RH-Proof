/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFrameLossRadialBoundaryColumnPairAlignment

/-!
# Extend the radial boundary column to the ambient carrier

Proof 687 uses the actual polar-frame range projection.  Since
`newSuffixRangeProjection = newSuffixFrame * newSuffixFrame†`, a source-side
factorization of the radial boundary channel extends to all of
`finiteSCarrier` by precomposing with `newSuffixFrame†`.  The projection on the
right is idempotent, so the extension is exact and keeps the `32 * bound` norm
cost.

This is a bounded full-carrier channel factorization only.  It does not turn
the channel into a Hilbert--Schmidt pair, and it supplies no Gate 3U estimate.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace AntiresonantFrameLossRadialBoundaryColumnFullCarrierExtension

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open AntiresonantFrameLossRadialBoundaryColumnBridge
open AntiresonantFrameLossRadialBoundarySplit
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorAdjacentProjectionGap
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFiniteRadialBlockColumn
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantRadialSplit
open CCM24FiniteSFixedSourcePolar
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSProjectionTrace
open CCM24UnitScaleProlateAlignment

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! ## The polar range projection is idempotent -/

theorem newSuffixRangeProjection_comp_self_eq
    (S : List CCM24VisiblePrime) :
    newSuffixRangeProjection unitSoninScale S ∘L
        newSuffixRangeProjection unitSoninScale S =
      newSuffixRangeProjection unitSoninScale S := by
  apply ContinuousLinearMap.ext
  intro u
  have hframe := DFunLike.congr_fun
    (parameterizedSoninPolarFrame_adjoint_comp_self
      unitSoninScale 1 S (by norm_num))
    (ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S) u)
  have hframe' :
      ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S)
          (newSuffixFrame unitSoninScale S
            (ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S) u)) =
        ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S) u := by
    simpa only [newSuffixFrame, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] using hframe
  simpa only [newSuffixRangeProjection,
    ContinuousLinearMap.comp_apply] using
    congrArg (newSuffixFrame unitSoninScale S) hframe'

theorem radialSoninBoundaryCrossing_comp_newSuffixRangeProjection_eq_self
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime) :
    radialSoninBoundaryCrossing p S ∘L
        newSuffixRangeProjection unitSoninScale S =
      radialSoninBoundaryCrossing p S := by
  apply ContinuousLinearMap.ext
  intro u
  have hprojection := DFunLike.congr_fun
    (newSuffixRangeProjection_comp_self_eq S) u
  simp only [radialSoninBoundaryCrossing, ContinuousLinearMap.comp_apply]
    at hprojection ⊢
  rw [hprojection]

/-! ## Exact full-carrier extension -/

/-- The source factorization readout, extended through the adjoint polar frame
to the complete finite-S carrier. -/
noncomputable def fullCarrierBoundaryChannelReadout
    {p : CCM24VisiblePrime} {S : List CCM24VisiblePrime}
    {N : ℕ} {bound : ℝ}
    (data : RadialBoundarySourceColumnFactorizationData p S N bound) :
  finiteSCarrier →L[ℂ] finiteSCarrier :=
  data.readout ∘L
    finitePrimeEulerRadialGeometricBoundaryColumn
      unitSoninScale p S N ∘L
    ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S)

theorem fullCarrierBoundaryChannelReadout_eq_radialSoninBoundaryCrossing
    {p : CCM24VisiblePrime} {S : List CCM24VisiblePrime}
    {N : ℕ} {bound : ℝ}
    (data : RadialBoundarySourceColumnFactorizationData p S N bound) :
    fullCarrierBoundaryChannelReadout data =
      radialSoninBoundaryCrossing p S := by
  apply ContinuousLinearMap.ext
  intro u
  have hfactor := DFunLike.congr_fun data.factorization
    (ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S) u)
  have hprojection := DFunLike.congr_fun
    (radialSoninBoundaryCrossing_comp_newSuffixRangeProjection_eq_self p S) u
  have hprojectionPoint :
      radialSoninBoundaryCrossing p S
          (newSuffixRangeProjection unitSoninScale S u) =
        radialSoninBoundaryCrossing p S u := by
    simpa only [ContinuousLinearMap.comp_apply] using hprojection
  change data.readout
      (finitePrimeEulerRadialGeometricBoundaryColumn
        unitSoninScale p S N
          (ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S) u)) =
    radialSoninBoundaryCrossing p S u
  rw [← hprojectionPoint]
  simpa only [newSuffixRangeProjection,
    ContinuousLinearMap.comp_apply] using hfactor

/-! ## The full-carrier relative readout -/

theorem norm_fullCarrierBoundaryChannelReadout_apply_le
    {p : CCM24VisiblePrime} {S : List CCM24VisiblePrime}
    {N : ℕ} {bound : ℝ}
    (data : RadialBoundarySourceColumnFactorizationData p S N bound)
    (u : finiteSCarrier) :
    ‖fullCarrierBoundaryChannelReadout data u‖ ≤
      (32 * bound) *
        ‖newFrameAntiresonantColumn unitSoninScale p S
          (ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S) u)‖ := by
  rw [fullCarrierBoundaryChannelReadout_eq_radialSoninBoundaryCrossing data]
  have hprojection := DFunLike.congr_fun
    (radialSoninBoundaryCrossing_comp_newSuffixRangeProjection_eq_self p S) u
  have hprojectionPoint :
      radialSoninBoundaryCrossing p S
          (newSuffixRangeProjection unitSoninScale S u) =
        radialSoninBoundaryCrossing p S u := by
    simpa only [ContinuousLinearMap.comp_apply] using hprojection
  have hbound :=
    norm_radialSoninBoundaryCrossing_comp_newSuffixFrame_apply_le_of_data
      data (ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S) u)
  calc
    ‖radialSoninBoundaryCrossing p S u‖ =
        ‖radialSoninBoundaryCrossing p S
          (newSuffixRangeProjection unitSoninScale S u)‖ := by
      rw [hprojectionPoint]
    _ = ‖radialSoninBoundaryCrossing p S
          (newSuffixFrame unitSoninScale S
            (ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S) u))‖ := by
      rfl
    _ ≤ (32 * bound) *
        ‖newFrameAntiresonantColumn unitSoninScale p S
          (ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S) u)‖ := hbound

end AntiresonantFrameLossRadialBoundaryColumnFullCarrierExtension
end CCM25Concrete
end Source
end ConnesWeilRH
