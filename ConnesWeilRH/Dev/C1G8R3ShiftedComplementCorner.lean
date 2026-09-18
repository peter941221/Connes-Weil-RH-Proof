/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3LeakageDoubledShift
import ConnesWeilRH.Dev.C1G8R3RelativeDefectCrossing

/-!
# Fixed-half-line form of the S3 complement corner

The translated complement corner is expressed in the fixed positive
half-line coordinates as `P - P K_b P K_b P`, where `K_b` is the shifted
Hardy involution.  This is an exact coordinate identity; it is not the
already controlled interior compression and it supplies no Schatten estimate.
-/

namespace ConnesWeilRH
namespace Dev

open Source
open Source.CC20Concrete
open Source.CCM25Concrete
open Source.CCM25Concrete.CCM24FiniteSProjectionTrace
open Source.CCM25Concrete.CCM24UnitScaleProlateAlignment
open Source.C1SemilocalHardyTitchmarshUnitarityReduction

local notation "Carrier" =>
  Source.CCM25Concrete.CCM24FiniteSProjectionTrace.finiteSCarrier
local notation "Op" => Carrier →L[ℂ] Carrier

theorem sourceFourierSupportProjection_unit_eq_translated_shiftedHardy_apply
    (b : ℝ) (x : Carrier) :
    ((cc20GlobalLogTranslation (2 * b)).toContinuousLinearMap ∘L
        sourceFourierSupportProjection unitSoninScale ∘L
          (cc20GlobalLogTranslation (-2 * b)).toContinuousLinearMap) x =
      (doubledShiftHardy b ∘L cc20PositiveHalfLineProjection ∘L
        doubledShiftHardy b) x := by
  let T : Op := (cc20GlobalLogTranslation (2 * b)).toContinuousLinearMap
  let Tm : Op := (cc20GlobalLogTranslation (-2 * b)).toContinuousLinearMap
  let H : Op := ccm24ArchimedeanHardyTitchmarsh
  let P : Op := cc20PositiveHalfLineProjection
  let Q : Op := sourceFourierSupportProjection unitSoninScale
  let K : Op := doubledShiftHardy b
  have hHTm : H (Tm x) = T (H x) := by
    have h := archimedeanHardyTitchmarsh_comp_globalLogTranslation (-(2 * b))
    have hx := congrArg (fun L : Op => L x) h
    simpa only [T, Tm, H, ContinuousLinearMap.comp_apply,
      show -2 * b = -(2 * b) by ring,
      show -(-(2 * b)) = 2 * b by ring] using hx
  change (T ∘L Q ∘L Tm) x = (K ∘L P ∘L K) x
  rw [show Q = H ∘L P ∘L H by
    dsimp [Q, H, P]
    simpa only [ContinuousLinearMap.comp_assoc] using
      sourceFourierSupportProjection_unit_eq_hardy_conjugation]
  change T (H (P (H (Tm x)))) = K (P (K x))
  rw [hHTm]
  rfl

theorem sourceFourierSupportProjection_unit_eq_translated_shiftedHardy
    (b : ℝ) :
    (cc20GlobalLogTranslation (2 * b)).toContinuousLinearMap ∘L
        sourceFourierSupportProjection unitSoninScale ∘L
          (cc20GlobalLogTranslation (-2 * b)).toContinuousLinearMap =
      doubledShiftHardy b ∘L cc20PositiveHalfLineProjection ∘L
        doubledShiftHardy b := by
  apply ContinuousLinearMap.ext
  intro x
  exact sourceFourierSupportProjection_unit_eq_translated_shiftedHardy_apply b x

end Dev
end ConnesWeilRH
