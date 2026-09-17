/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3CompositeBoundaryEnergy

namespace ConnesWeilRH
namespace Dev

open Source
open Source.CC20Concrete
open Source.CCM25Concrete
open Source.CCM25Concrete.CCM24FiniteSGramResponse
open Source.CCM25Concrete.CCM24FiniteSProjectionTrace
open Source.CCM25Concrete.CCM24RadialBoundaryPairTransport
open scoped InnerProduct InnerProductSpace

local notation "Carrier" => finiteSCarrier

noncomputable local instance wideHardyFourierBridgeCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

set_option maxHeartbeats 1000000 in
/-- Hardy-wide radial support is exactly Fourier support at the same widened
scale.  This is the projection-level form of the Hardy involution and is the
preferred producer interface for the B4 tail estimate. -/
theorem wideHardySupport_iff_wideFourierSupport
    (lambda : CCM24SoninScale) (s : ℝ) (A : Carrier →L[ℂ] Carrier) :
    radialSupportProjection (wideRadialScale lambda s) ∘L
        archimedeanHardyTitchmarshOperator ∘L A =
      archimedeanHardyTitchmarshOperator ∘L A ↔
    sourceFourierSupportProjection (wideRadialScale lambda s) ∘L A = A := by
  constructor
  · intro h
    apply ContinuousLinearMap.ext
    intro u
    have hAt := congrArg archimedeanHardyTitchmarshOperator
      (DFunLike.congr_fun h u)
    have hAt' : archimedeanHardyTitchmarshOperator
          (radialSupportProjection (wideRadialScale lambda s)
            (archimedeanHardyTitchmarshOperator (A u))) = A u := by
      simpa only [ContinuousLinearMap.comp_apply,
        archimedeanHardyTitchmarshOperator_involutive] using hAt
    rw [sourceFourierSupportProjection_eq_hardyTitchmarsh_conjugation]
    simpa only [ContinuousLinearMap.comp_apply] using hAt'
  · intro h
    apply ContinuousLinearMap.ext
    intro u
    have hAt := congrArg archimedeanHardyTitchmarshOperator
      (DFunLike.congr_fun h u)
    rw [sourceFourierSupportProjection_eq_hardyTitchmarsh_conjugation] at hAt
    simpa only [ContinuousLinearMap.comp_apply,
      archimedeanHardyTitchmarshOperator_involutive] using hAt

end ConnesWeilRH.Dev
