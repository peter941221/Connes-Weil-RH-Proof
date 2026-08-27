/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1CC20DisplacementReadback
import Mathlib.MeasureTheory.Group.Prod

/-!
# Product integrability for the CC20 displacement correlation

The Fubini readback for the CC20 displacement kernel deliberately carries an
explicit integrability premise for

    (v, x) |-> a(v) * eta(x) * xi(x + v).

This leaf discharges that premise from the analytic data used in paper
equation (121): an `L1` displacement profile and two `L2` factors.  The proof
uses the product-integrability characterization in the displacement-first
coordinate order.  Each fixed displacement slice is integrable by Holder, and
its norm integral is uniformly dominated by the `L2` product times `||a(v)||`.

No numerical profile certificate, operator-norm conclusion, or RH-level sign
claim is made here.
-/

namespace ConnesWeilRH
namespace Source
namespace C1CC20ProductIntegrability

open MeasureTheory
open C1CC20DisplacementReadback C1CC20DisplacementKernel
open C1CC20LpOperator C1CC20TranslateInvariance C1CC20UniformSlice

/-- The displacement-first correlation integrand is a.e. strongly measurable
on the product Lebesgue space.  The `xi(x + v)` factor uses the additive
product map, which is quasi-measure-preserving. -/
theorem aestronglyMeasurable_displacementCorrelationIntegrand
    {a eta xi : ℝ -> ℂ} (ha : AEStronglyMeasurable a volume)
    (heta : MemLp eta (ENNReal.ofReal 2))
    (hxi : MemLp xi (ENNReal.ofReal 2)) :
    AEStronglyMeasurable
      (Function.uncurry (displacementCorrelationIntegrand a eta xi))
      (volume.prod volume) := by
  have ha' : AEStronglyMeasurable (fun p : ℝ × ℝ => a p.1)
      (volume.prod volume) := ha.comp_fst
  have heta' : AEStronglyMeasurable (fun p : ℝ × ℝ => eta p.2)
      (volume.prod volume) := heta.1.comp_snd
  have hxi' : AEStronglyMeasurable (fun p : ℝ × ℝ => xi (p.2 + p.1))
      (volume.prod volume) := by
    have h := hxi.1.comp_quasiMeasurePreserving
      (quasiMeasurePreserving_add volume volume)
    simpa [add_comm] using h
  simpa only [Function.uncurry, displacementCorrelationIntegrand] using
    ha'.mul (heta'.mul hxi')

/-- The Fubini premise for the displacement correlation is automatic from an
`L1` profile and `L2` factors.  This is the absolute-integrability form of the
Holder step underlying paper equation (121). -/
theorem integrable_displacementCorrelationIntegrand
    {a eta xi : ℝ -> ℂ} (ha : AEStronglyMeasurable a volume)
    (haint : Integrable (fun v => ‖a v‖) volume)
    (heta : MemLp eta (ENNReal.ofReal 2))
    (hxi : MemLp xi (ENNReal.ofReal 2)) :
    Integrable (Function.uncurry (displacementCorrelationIntegrand a eta xi))
      (volume.prod volume) := by
  have hD : AEStronglyMeasurable
      (Function.uncurry (displacementCorrelationIntegrand a eta xi))
      (volume.prod volume) :=
    aestronglyMeasurable_displacementCorrelationIntegrand ha heta hxi
  have hholder : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  letI : ENNReal.HolderConjugate (ENNReal.ofReal 2) (ENNReal.ofReal 2) :=
    hholder.ennrealOfReal
  refine (integrable_prod_iff hD).mpr ⟨?_, ?_⟩
  · filter_upwards with v
    have hslice : Integrable (fun x : ℝ => eta x * xi (x + v)) volume := by
      simpa only [Pi.mul_apply] using
        heta.integrable_mul (memLp_shift hxi v)
    simpa only [Function.uncurry, displacementCorrelationIntegrand] using
      hslice.const_mul (a v)
  · let K : ℝ :=
      (∫ x : ℝ, ‖eta x‖ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) *
        (∫ x : ℝ, ‖xi x‖ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)
    have hmassEta : 0 ≤ ∫ x : ℝ, ‖eta x‖ ^ (2 : ℝ) :=
      integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
    have hmassXi : 0 ≤ ∫ x : ℝ, ‖xi x‖ ^ (2 : ℝ) :=
      integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
    have hKnonneg : 0 ≤ K :=
      mul_nonneg (Real.rpow_nonneg hmassEta _) (Real.rpow_nonneg hmassXi _)
    have hsliceNorm : ∀ v : ℝ,
        (∫ x : ℝ, ‖displacementCorrelationIntegrand a eta xi v x‖) ≤
          K * ‖a v‖ := by
      intro v
      have hholderBound :
          (∫ x : ℝ, ‖eta x‖ * ‖xi (x + v)‖) ≤ K := by
        have hraw := MeasureTheory.integral_mul_norm_le_Lp_mul_Lq hholder heta
          (memLp_shift hxi v)
        rw [mass_shift_real hxi v] at hraw
        simpa only [K] using hraw
      calc
        (∫ x : ℝ, ‖displacementCorrelationIntegrand a eta xi v x‖) =
            ‖a v‖ * ∫ x : ℝ, ‖eta x‖ * ‖xi (x + v)‖ := by
              rw [← integral_const_mul]
              apply integral_congr_ae
              filter_upwards with x
              simp only [displacementCorrelationIntegrand, norm_mul]
        _ ≤ ‖a v‖ * K :=
          mul_le_mul_of_nonneg_left hholderBound (norm_nonneg _)
        _ = K * ‖a v‖ := mul_comm _ _
    have hGmeas : AEStronglyMeasurable
        (fun v : ℝ => ∫ x : ℝ,
          ‖displacementCorrelationIntegrand a eta xi v x‖) volume := by
      simpa only [Function.uncurry] using hD.norm.integral_prod_right'
    have hGint : Integrable (fun v : ℝ => K * ‖a v‖) volume :=
      haint.const_mul K
    refine hGint.mono hGmeas ?_
    filter_upwards with v
    have hleft : 0 ≤ ∫ x : ℝ,
        ‖displacementCorrelationIntegrand a eta xi v x‖ :=
      integral_nonneg fun x => norm_nonneg _
    have hright : 0 ≤ K * ‖a v‖ :=
      mul_nonneg hKnonneg (norm_nonneg _)
    change ‖∫ x : ℝ,
      ‖displacementCorrelationIntegrand a eta xi v x‖‖ ≤ ‖K * ‖a v‖‖
    rw [Real.norm_eq_abs, abs_of_nonneg hleft,
      Real.norm_eq_abs, abs_of_nonneg hright]
    exact hsliceNorm v

/-- Equation-(121) bounds the displacement-kernel pairing with no remaining
Fubini premise once the profile is integrable and both factors are in `L2`. -/
theorem norm_pairing_applyKernel_displacementKernel_le_of_l1Weight
    {a eta xi : ℝ -> ℂ} (ha : AEStronglyMeasurable a volume)
    (haint : Integrable (fun v => ‖a v‖) volume)
    (heta : MemLp eta (ENNReal.ofReal 2))
    (hxi : MemLp xi (ENNReal.ofReal 2)) :
    ‖∫ x : ℝ, eta x * applyKernel (displacementKernel a) xi x‖ ≤
      (∫ x : ℝ, ‖eta x‖ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) *
        (∫ x : ℝ, ‖xi x‖ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) * ∫ v : ℝ, ‖a v‖ := by
  exact norm_pairing_applyKernel_displacementKernel_le a eta xi heta hxi ha haint
    (integrable_displacementCorrelationIntegrand ha haint heta hxi)

end C1CC20ProductIntegrability
end Source
end ConnesWeilRH
