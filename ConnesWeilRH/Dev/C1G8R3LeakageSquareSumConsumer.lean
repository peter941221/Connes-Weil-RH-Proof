/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3LeakageDoubledShift
import ConnesWeilRH.Dev.C1G8R3ShiftedHardyKernelReduction

/-!
# Direct square-sum consumer for the completed detector-root leakage

The shifted-Hardy reduction already proves square-summability of the raw
doubled-shift support crossing.  This leaf transports that estimate through
the selected convolution root and the two unitary log translations in the
exact leakage normal form.  It is the first direct consumer of that estimate
at the actual finite-S source owner.
-/

namespace ConnesWeilRH
namespace Dev

open Source
open Source.CC20Concrete
open Source.CC20Concrete.PositiveTrace
open Source.CCM25Concrete
open Source.CCM25Concrete.CCM24FiniteSBandTrace
open Source.CCM25Concrete.CCM24FiniteSProjectionTrace
open Source.CCM25Concrete.CCM24FiniteSRootCompletedFirstJet
open Source.CCM25Concrete.CCM24UnitScaleProlateAlignment

local notation "Carrier" =>
  Source.CCM25Concrete.CCM24FiniteSProjectionTrace.finiteSCarrier

theorem sourceRootCompletedRightCommutatorLeftLeg_sourceBasis_normSq_summable_of_complementCorner
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) {ι : Type*}
    (basis : HilbertBasis ι ℂ Carrier) :
    (hcorner : Summable fun i : ι =>
      ‖(doubledShiftRadialProjection (Real.log lambda) ∘L
        (ContinuousLinearMap.id ℂ Carrier -
          sourceFourierSupportProjection unitSoninScale) ∘L
        doubledShiftRadialProjection (Real.log lambda)) (basis i)‖ ^ 2) →
    Summable fun i : ι =>
      ‖sourceRootCompletedRightCommutatorLeftLeg owner lambda
        (basis i)‖ ^ 2 := by
  let b : ℝ := Real.log lambda
  intro hcorner
  let corner : Carrier →L[ℂ] Carrier :=
    doubledShiftRadialProjection b ∘L
      (ContinuousLinearMap.id ℂ Carrier -
      sourceFourierSupportProjection unitSoninScale) ∘L
      doubledShiftRadialProjection b
  have hroot : Summable fun i : ι =>
      ‖(rootConvolution owner ∘L corner) (basis i)‖ ^ 2 := by
    exact PositiveTrace.summable_normSq_postcomp basis corner
      (rootConvolution owner) (by simpa only [corner, b] using hcorner)
  have htranslated : Summable fun i : ι =>
      ‖(rootConvolution owner ∘L corner ∘L
        (cc20GlobalLogTranslation (-b)).toContinuousLinearMap)
          (basis i)‖ ^ 2 := by
    exact PositiveTrace.summable_normSq_precomp basis basis basis
      (rootConvolution owner ∘L corner)
      (cc20GlobalLogTranslation (-b)).toContinuousLinearMap (by
        exact hroot)
  rw [sourceRootCompletedRightCommutatorLeftLeg_eq_translated_complement_corner]
  simpa only [b, ContinuousLinearMap.comp_assoc] using
    (PositiveTrace.summable_normSq_postcomp basis
      (rootConvolution owner ∘L corner ∘L
        (cc20GlobalLogTranslation (-b)).toContinuousLinearMap)
      (cc20GlobalLogTranslation b).toContinuousLinearMap htranslated)

end Dev
end ConnesWeilRH
