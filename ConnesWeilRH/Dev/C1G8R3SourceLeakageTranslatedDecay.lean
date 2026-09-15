/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3LeakageRootPointwiseDecay

/-!
# R3 source leakage: translated defect-step decay

The doubled-shift leakage normal form is conjugated by the global-log
translation at the selected scale.  This leaf transports the pointwise
rooted defect-step decay through that conjugation, so the result is stated
for the actual source leakage owner.

The result is still pointwise.  It is not a Hilbert--Schmidt, trace-class, or
Weil-sign theorem.
-/

namespace ConnesWeilRH
namespace Dev

open Source
open Source.CC20Concrete
open Source.CCM25Concrete
open Source.CCM25Concrete.CCM24FiniteSBandTrace
open Source.CCM25Concrete.CCM24FiniteSCausalMarkov
open Source.CCM25Concrete.CCM24FiniteSProjectionTrace
open Source.CCM25Concrete.CCM24FiniteSRootCompletedFirstJet

local notation "Carrier" =>
  Source.CCM25Concrete.CCM24FiniteSProjectionTrace.finiteSCarrier
local notation "Op" => Carrier →L[ℂ] Carrier

theorem sourceRootCompletedRightCommutatorLeftLeg_apply_translated_defect_step_norm_tendsto_zero
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (v : Carrier) :
    Filter.Tendsto
      (fun n : ℕ =>
        ‖sourceRootCompletedRightCommutatorLeftLeg owner lambda
          ((cc20GlobalLogTranslation (Real.log lambda)).toContinuousLinearMap
            (((doubledShiftAlternatingProduct (Real.log lambda)) ^ (n + 1)) v))‖)
      Filter.atTop (nhds 0) := by
  let b : ℝ := Real.log lambda
  let Uplus : Op :=
    (cc20GlobalLogTranslation b).toContinuousLinearMap
  let Uminus : Op :=
    (cc20GlobalLogTranslation (-b)).toContinuousLinearMap
  have hcancel (w : Carrier) : Uminus (Uplus w) = w := by
    dsimp [Uminus, Uplus]
    rw [cc20GlobalLogTranslation_add_apply]
    have hzero : -b + b = 0 := by ring
    rw [hzero, cc20GlobalLogTranslation_zero_apply]
  have hfactor :
      sourceRootCompletedRightCommutatorLeftLeg owner lambda ∘L Uplus =
        Uplus ∘L rootConvolution owner ∘L
          (doubledShiftRadialProjection b -
            doubledShiftAlternatingProduct b) := by
    rw [sourceRootCompletedRightCommutatorLeftLeg_eq_translated_doubledShift_defect]
    apply ContinuousLinearMap.ext
    intro w
    simp only [ContinuousLinearMap.comp_apply]
    rw [show Real.log lambda = b by rfl, hcancel]
  have happly (n : ℕ) :
      sourceRootCompletedRightCommutatorLeftLeg owner lambda
          (Uplus (((doubledShiftAlternatingProduct b) ^ (n + 1)) v)) =
        Uplus
          (rootConvolution owner
            (((doubledShiftRadialProjection b -
                doubledShiftAlternatingProduct b) *
                (doubledShiftAlternatingProduct b) ^ (n + 1)) v)) := by
    have h := congrArg
      (fun L : Op => L (((doubledShiftAlternatingProduct b) ^ (n + 1)) v))
      hfactor
    simpa only [ContinuousLinearMap.comp_apply] using h
  have hroot :=
    rootConvolution_apply_doubledShiftDefect_step_norm_tendsto_zero
      owner b v
  have hupper (n : ℕ) :
      ‖sourceRootCompletedRightCommutatorLeftLeg owner lambda
          (Uplus (((doubledShiftAlternatingProduct b) ^ (n + 1)) v))‖ ≤
        ‖rootConvolution owner
          (((doubledShiftRadialProjection b -
              doubledShiftAlternatingProduct b) *
              (doubledShiftAlternatingProduct b) ^ (n + 1)) v)‖ := by
    rw [happly]
    exact le_of_eq (by
      simpa only [Uplus, ContinuousLinearMap.coe_coe] using
        (cc20GlobalLogTranslation b).norm_map
          (rootConvolution owner
            (((doubledShiftRadialProjection b -
                doubledShiftAlternatingProduct b) *
                (doubledShiftAlternatingProduct b) ^ (n + 1)) v)))
  have hbound :
      Filter.Tendsto
        (fun n : ℕ =>
          ‖sourceRootCompletedRightCommutatorLeftLeg owner lambda
            (Uplus (((doubledShiftAlternatingProduct b) ^ (n + 1)) v))‖)
        Filter.atTop (nhds 0) := by
    apply squeeze_zero (fun n => norm_nonneg _)
      hupper hroot
  simpa only [b, Uplus] using hbound

end Dev
end ConnesWeilRH
