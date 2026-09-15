/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3LeakageDefectTelescoping

/-!
# R3 leakage: pointwise decay after the selected root

The no-gap power limit and the leakage defect telescoping identity combine to
show that the selected convolution root sends every adjacent alternating-power
defect step to a vector tending to zero.

This is a pointwise strong statement only.  It is a named input for the
healthy CompactLog, B5-shaped detector-specific trace route; it does not
assert Hilbert--Schmidt or trace-class summability.
-/

namespace ConnesWeilRH
namespace Dev

open Source
open Source.CC20Concrete
open Source.CCM25Concrete
open Source.CCM25Concrete.CCM24FiniteSBandTrace
open Source.CCM25Concrete.CCM24FiniteSProjectionTrace
open Source.CCM25Concrete.CCM24FiniteSRootCompletedFirstJet

local notation "Carrier" =>
  Source.CCM25Concrete.CCM24FiniteSProjectionTrace.finiteSCarrier
local notation "Op" => Carrier →L[ℂ] Carrier

theorem rootConvolution_apply_doubledShiftDefect_step_norm_tendsto_zero
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (b : ℝ) (v : Carrier) :
    Filter.Tendsto
      (fun n : ℕ =>
        ‖rootConvolution owner
          (((doubledShiftRadialProjection b -
              doubledShiftAlternatingProduct b) *
              (doubledShiftAlternatingProduct b) ^ (n + 1)) v)‖)
      Filter.atTop (nhds 0) := by
  have hpow :
      Filter.Tendsto
        (fun n : ℕ => ((doubledShiftAlternatingProduct b) ^ n) v)
        Filter.atTop
        (nhds (doubledShiftSoninIntersectionProjection b v)) :=
    doubledShiftAlternatingProduct_tendsto_intersectionProjection_no_gap b v
  have hpow_succ :
      Filter.Tendsto
        (fun n : ℕ => ((doubledShiftAlternatingProduct b) ^ (n + 1)) v)
        Filter.atTop
        (nhds (doubledShiftSoninIntersectionProjection b v)) := by
    simpa only [Function.comp_apply] using
      hpow.comp (Filter.tendsto_add_atTop_nat 1)
  have hpow_succ_two :
      Filter.Tendsto
        (fun n : ℕ => ((doubledShiftAlternatingProduct b) ^ (n + 2)) v)
        Filter.atTop
        (nhds (doubledShiftSoninIntersectionProjection b v)) := by
    simpa only [Function.comp_apply] using
      hpow.comp (Filter.tendsto_add_atTop_nat 2)
  have hdiff :
      Filter.Tendsto
        (fun n : ℕ =>
          ((doubledShiftAlternatingProduct b) ^ (n + 1)) v -
            ((doubledShiftAlternatingProduct b) ^ (n + 2)) v)
        Filter.atTop (nhds 0) := by
    simpa only [sub_self] using hpow_succ.sub hpow_succ_two
  have hroot :
      Filter.Tendsto
        (fun w : Carrier => rootConvolution owner w)
        (nhds 0) (nhds 0) := by
    simpa only [map_zero] using (rootConvolution owner).continuous.tendsto 0
  have hnorm :
      Filter.Tendsto
        (fun n : ℕ =>
          ‖rootConvolution owner
            (((doubledShiftAlternatingProduct b) ^ (n + 1)) v -
              ((doubledShiftAlternatingProduct b) ^ (n + 2)) v)‖)
        Filter.atTop (nhds 0) :=
    tendsto_norm_zero.comp (hroot.comp hdiff)
  apply hnorm.congr'
  filter_upwards [] with n
  rw [doubledShiftRadialProjection_sub_alternatingProduct_apply_pow_succ_eq_step]
  simp only [ContinuousLinearMap.sub_apply]

end Dev
end ConnesWeilRH
