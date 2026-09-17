/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3WideHardyFourierSupportBridge

namespace ConnesWeilRH
namespace Dev

open Source
open Source.CC20Concrete
open Source.CCM25Concrete
open Source.CCM25Concrete.CCM24FiniteSGramResponse
open Source.CCM25Concrete.CCM24FiniteSBandTrace
open Source.CCM25Concrete.SelectedWeilSquare
open Source.CCM25Concrete.CCM24FiniteSProjectionTrace
open Source.CCM25Concrete.CCM24RadialBoundaryPairTransport

local notation "Carrier" => finiteSCarrier

set_option maxHeartbeats 1000000 in
/-- The B4 internal-gap consumer in its Fourier form.  A same-scale Fourier
support certificate for the actual source column is exactly the Hardy support
premise required by the existing composite gap estimate. -/
theorem compositeGapLeg_sourceColumn_normSq_summable_of_wideFourierSupport
    (owner : SelectedWeilSquareOwner) (lambda : CCM24SoninScale) (s : ℝ)
    (hs : 0 ≤ s)
    (A : sourceSoninCarrier lambda →L[ℂ] Carrier)
    (N : sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda)
    {ρ : Type*} (sourceBasis : HilbertBasis ρ ℂ
      (sourceSoninCarrier lambda))
    (hFourier : sourceFourierSupportProjection (wideRadialScale lambda s) ∘L A = A) :
    Summable fun i : ρ =>
      ‖(((radialSupportProjection lambda - sourceSoninProjection lambda) ∘L
          radialSupportProjection lambda ∘L rootConvolution owner ∘L A) ∘L N)
        (sourceBasis i)‖ ^ 2 := by
  apply compositeGapLeg_sourceColumn_normSq_summable owner lambda s hs A N
    sourceBasis
  exact (wideHardySupport_sourceColumn_iff_wideFourierSupport lambda s A).mpr
    hFourier

end Dev
end ConnesWeilRH
