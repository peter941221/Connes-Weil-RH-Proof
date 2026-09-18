/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3ComplementCornerHardyNormalForm
import ConnesWeilRH.Dev.C1G8R3LeakageSquareSumConsumer

/-!
# P-side Hardy defect consumer for S3

This leaf closes the coordinate transport left open by the Hardy normal form:
square-summability of the P-side defect is transported back to the actual
finite-S complement corner and then consumed by the existing leakage theorem.
The premise is deliberately analytic and remains open.
-/

namespace ConnesWeilRH
namespace Dev

open Source
open Source.CC20Concrete
open Source.CC20Concrete.PositiveTrace
open Source.CCM25Concrete
open Source.CCM25Concrete.CCM24FiniteSProjectionTrace
open Source.CCM25Concrete.CCM24FiniteSRootCompletedFirstJet
open Source.CCM25Concrete.CCM24UnitScaleProlateAlignment

local notation "Carrier" =>
  Source.CCM25Concrete.CCM24FiniteSProjectionTrace.finiteSCarrier
local notation "Op" => Carrier →L[ℂ] Carrier

theorem sourceRootCompletedRightCommutatorLeftLeg_sourceBasis_normSq_summable_of_hardyDefect
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) {ι : Type*}
    (basis : HilbertBasis ι ℂ Carrier)
    (hdefect : Summable fun i : ι =>
      ‖(cc20PositiveHalfLineProjection -
        (cc20PositiveHalfLineProjection ∘L doubledShiftHardy (Real.log lambda) ∘L
          cc20PositiveHalfLineProjection ∘L doubledShiftHardy (Real.log lambda) ∘L
          cc20PositiveHalfLineProjection)) (basis i)‖ ^ 2) :
    Summable fun i : ι =>
      ‖sourceRootCompletedRightCommutatorLeftLeg owner lambda
        (basis i)‖ ^ 2 := by
  let b : ℝ := Real.log lambda
  let T : Op := doubledShiftCarrierTranslation b
  let Tm : Op := doubledShiftCarrierTranslationInv b
  let P : Op := cc20PositiveHalfLineProjection
  let K : Op := doubledShiftHardy b
  let corner : Op :=
    doubledShiftRadialProjection b ∘L
      (ContinuousLinearMap.id ℂ Carrier -
        sourceFourierSupportProjection unitSoninScale) ∘L
      doubledShiftRadialProjection b
  let defect : Op := P - P ∘L K ∘L P ∘L K ∘L P
  have hdefect' : Summable fun i : ι => ‖defect (basis i)‖ ^ 2 := by
    simpa only [defect, b, P, K] using hdefect
  have hpre : Summable fun i : ι =>
      ‖(defect ∘L T) (basis i)‖ ^ 2 := by
    exact PositiveTrace.summable_normSq_precomp basis basis basis
      defect T hdefect'
  have hpost : Summable fun i : ι =>
      ‖(Tm ∘L defect ∘L T) (basis i)‖ ^ 2 := by
    exact PositiveTrace.summable_normSq_postcomp basis
      (defect ∘L T) Tm hpre
  have hcorner : corner = Tm ∘L defect ∘L T := by
    have hnormal :=
      doubledShiftComplementCorner_conjugate_eq_hardyDefect b
    have hleft : Tm ∘L T = ContinuousLinearMap.id ℂ Carrier := by
      simpa only [T, Tm] using doubledShiftCarrierTranslationInv_comp b
    have hright : T ∘L Tm = ContinuousLinearMap.id ℂ Carrier := by
      simpa only [T, Tm] using doubledShiftCarrierTranslation_comp_inv b
    have hnormal' : T ∘L corner ∘L Tm = defect := by
      simpa only [corner, defect, T, Tm, P, K, b] using hnormal
    calc
      corner = (Tm ∘L T) ∘L corner ∘L (Tm ∘L T) := by
        rw [hleft]
        simp only [ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id]
      _ = Tm ∘L (T ∘L corner ∘L Tm) ∘L T := by
        simp only [ContinuousLinearMap.comp_assoc]
      _ = Tm ∘L defect ∘L T := by
        rw [hnormal']
  have hcorner' : Summable fun i : ι => ‖corner (basis i)‖ ^ 2 := by
    rw [hcorner]
    simpa only [ContinuousLinearMap.comp_assoc] using hpost
  apply sourceRootCompletedRightCommutatorLeftLeg_sourceBasis_normSq_summable_of_complementCorner
    owner lambda basis
  simpa only [corner, b] using hcorner'

end Dev
end ConnesWeilRH
