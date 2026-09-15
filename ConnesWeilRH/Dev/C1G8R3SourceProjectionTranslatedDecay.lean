/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3LeakageOrthonormalOrbit

/-!
# Decay of the translated leakage orbit after source-Sonin projection

The ambient translated orbit used for the leakage lower bound has vanishing
projection onto the unit-scale source-Sonin carrier. Thus normalizing its
source projections cannot transfer the ambient lower bound to the G8
same-source-basis energy sum.
-/

namespace ConnesWeilRH
namespace Dev

open Filter
open Source.CC20Concrete
open Source.CC20YoshidaConvolution
open Source.CCM25Concrete
open Source.CCM25Concrete.CCM24FiniteSProjectionTrace
open Source.CCM25Concrete.CCM24UnitScaleProlateAlignment
open scoped Topology

local notation "Carrier" => finiteSCarrier

noncomputable local instance sourceSoninIntersectionCompleteSpace
    (lambda : CCM24SoninScale) :
    CompleteSpace
      (↑(((ccm24LogRadialSupportClosedSubspace lambda).toSubmodule) ⊓
        ((ccm24ArchimedeanFourierSupportClosedSubspace lambda).toSubmodule))) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

private theorem sourceSoninProjection_comp_sourceFourierSupportProjection
    (lambda : CCM24SoninScale) :
    sourceSoninProjection lambda ∘L sourceFourierSupportProjection lambda =
      sourceSoninProjection lambda := by
  have hmul : sourceSoninProjection lambda *
      sourceFourierSupportProjection lambda = sourceSoninProjection lambda := by
    simpa [sourceFourierSupportProjection, sourceSoninProjection,
      ccm24ArchimedeanSoninClosedSubspace,
      ContinuousLinearMap.mul_def] using
      (_root_.ConnesWeilRH.CC20Concrete.intersection_absorbs_right_starProjection
        (ccm24LogRadialSupportClosedSubspace lambda).toSubmodule
        (ccm24ArchimedeanFourierSupportClosedSubspace lambda).toSubmodule)
  simpa only [ContinuousLinearMap.mul_def] using hmul

private theorem selectedSourceTranslationSpacing_positive
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) :
    0 < selectedSourceTranslationSpacing owner := by
  unfold selectedSourceTranslationSpacing
  exact Nat.succ_pos _

private theorem selectedSourceTranslationCenter_eq_mul_spacing
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) (n : ℕ) :
    selectedSourceTranslationCenter owner n =
      ((n * selectedSourceTranslationSpacing owner : ℕ) : ℝ) := by
  simp [selectedSourceTranslationCenter, Nat.cast_mul]

/-- The source-Sonin projection of the separated positive translates of the
selected compact source test tends to zero in ambient L2 norm. -/
theorem sourceSoninProjection_selectedSourceTranslationOrbit_norm_tendsto_zero
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) :
    Tendsto
      (fun n : ℕ => ‖sourceSoninProjection unitSoninScale
        (selectedSourceTranslationOrbit owner n)‖)
      atTop (𝓝 0) := by
  let u : Carrier := owner.sourceTest.test.toLp 2
  let Q : Carrier →L[ℂ] Carrier :=
    sourceFourierSupportProjection unitSoninScale
  let P : Carrier →L[ℂ] Carrier := sourceSoninProjection unitSoninScale
  have hspacing : 0 < selectedSourceTranslationSpacing owner :=
    selectedSourceTranslationSpacing_positive owner
  have hindex : Tendsto
      (fun n : ℕ => n * selectedSourceTranslationSpacing owner) atTop atTop := by
    apply Filter.tendsto_atTop.2
    intro N
    filter_upwards [eventually_ge_atTop N] with n hn
    exact le_trans hn
      (Nat.le_mul_of_pos_right n hspacing)
  have hQbase :=
    sourceFourierSupportProjection_unit_globalLogTranslation_neg_tendsto_zero u
  have hQorbit : Tendsto
      (fun n : ℕ => Q (selectedSourceTranslationOrbit owner n))
      atTop (𝓝 0) := by
    have hscaled := hQbase.comp hindex
    have hsequence :
        (fun n : ℕ => Q (selectedSourceTranslationOrbit owner n)) =
          (fun n : ℕ => Q (cc20GlobalLogTranslation
            (-((n * selectedSourceTranslationSpacing owner : ℕ) : ℝ)) u)) := by
      funext n
      rw [selectedSourceTranslationOrbit,
        selectedSourceTranslationCenter_eq_mul_spacing]
    rw [hsequence]
    simpa only [Q] using hscaled
  have hQnorm : Tendsto
      (fun n : ℕ => ‖Q (selectedSourceTranslationOrbit owner n)‖)
      atTop (𝓝 0) := by
    simpa only [norm_zero] using
      (continuous_norm.tendsto (0 : Carrier)).comp hQorbit
  have hPQ := sourceSoninProjection_comp_sourceFourierSupportProjection
    unitSoninScale
  have hPnorm : ‖P‖ ≤ 1 :=
    IsStarProjection.norm_le _ (sourceSoninProjection_isStarProjection unitSoninScale)
  apply Metric.tendsto_nhds.2
  intro ε hε
  filter_upwards [Metric.tendsto_nhds.1 hQnorm ε hε] with n hn
  have hproj : P (selectedSourceTranslationOrbit owner n) =
      P (Q (selectedSourceTranslationOrbit owner n)) := by
    have h := congrArg (fun T : Carrier →L[ℂ] Carrier =>
      T (selectedSourceTranslationOrbit owner n)) hPQ
    simpa only [ContinuousLinearMap.comp_apply] using h.symm
  have hbound : ‖P (selectedSourceTranslationOrbit owner n)‖ ≤
      ‖Q (selectedSourceTranslationOrbit owner n)‖ := by
    rw [hproj]
    calc
      ‖P (Q (selectedSourceTranslationOrbit owner n))‖ ≤
          ‖P‖ * ‖Q (selectedSourceTranslationOrbit owner n)‖ :=
        P.le_opNorm _
      _ ≤ 1 * ‖Q (selectedSourceTranslationOrbit owner n)‖ :=
        mul_le_mul_of_nonneg_right hPnorm (norm_nonneg _)
      _ = ‖Q (selectedSourceTranslationOrbit owner n)‖ := by ring
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at hn ⊢
  exact lt_of_le_of_lt hbound hn

end Dev
end ConnesWeilRH
