/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1CC20DisplacementKernel
import Mathlib.MeasureTheory.Integral.Prod

/-!
# CC20 displacement-kernel Fubini readback

This leaf supplies the Fubini layer deliberately left open by
`C1CC20DisplacementKernel`.  Under one explicit product-integrability
hypothesis for `(v, x) -> a(v) * eta(x) * xi(x + v)`, it proves that the
bilinear pairing of the displacement-kernel operator is exactly the weighted
correlation fold controlled by the equation-(121) engine.

The result is generic and does not construct the paper's finite-rank
approximant, prove a numerical L1 enclosure, or identify a windowed operator
without the appropriate zero-extension/support hypotheses.
-/

namespace ConnesWeilRH
namespace Source
namespace C1CC20DisplacementReadback

open MeasureTheory
open C1CC20CorrBridge C1CC20PairingFold C1CC20DisplacementKernel
open C1CC20LpOperator

/-- The product integrand in displacement-first coordinates.  Its first
coordinate is the CC20 displacement and its second coordinate is the source
coordinate of the correlation slice. -/
def displacementCorrelationIntegrand
    (a eta xi : ℝ -> ℂ) (v x : ℝ) : ℂ :=
  a v * (eta x * xi (x + v))

/-- Expanding `corrInnerSlice` turns the weighted correlation fold into the
displacement-first iterated integral. -/
theorem weightedCorrFold_eq_iteratedIntegral
    (a eta xi : ℝ -> ℂ) :
    (∫ v : ℝ, a v * corrInnerSlice eta xi v) =
      ∫ v : ℝ, ∫ x : ℝ, displacementCorrelationIntegrand a eta xi v x := by
  apply integral_congr_ae
  filter_upwards with v
  rw [corrInnerSlice, ← integral_const_mul]
  rfl

/-- Product integrability permits the only Fubini exchange in the bridge. -/
theorem weightedCorrFold_eq_swappedIteratedIntegral
    (a eta xi : ℝ -> ℂ)
    (hintegrable : Integrable
      (Function.uncurry (displacementCorrelationIntegrand a eta xi))
      (volume.prod volume)) :
    (∫ v : ℝ, a v * corrInnerSlice eta xi v) =
      ∫ x : ℝ, ∫ v : ℝ, displacementCorrelationIntegrand a eta xi v x := by
  calc
    (∫ v : ℝ, a v * corrInnerSlice eta xi v) =
        ∫ v : ℝ, ∫ x : ℝ, displacementCorrelationIntegrand a eta xi v x :=
      weightedCorrFold_eq_iteratedIntegral a eta xi
    _ = ∫ x : ℝ, ∫ v : ℝ, displacementCorrelationIntegrand a eta xi v x :=
      integral_integral_swap hintegrable

/-- The bilinear pairing of a displacement-kernel action reads back exactly
as the weighted correlation fold.  The caller owns the sole Fubini premise,
so no interchange of non-integrable integrals is hidden here. -/
theorem pairing_applyKernel_displacementKernel_eq_weightedCorrFold
    (a eta xi : ℝ -> ℂ)
    (hintegrable : Integrable
      (Function.uncurry (displacementCorrelationIntegrand a eta xi))
      (volume.prod volume)) :
    (∫ x : ℝ, eta x * applyKernel (displacementKernel a) xi x) =
      ∫ v : ℝ, a v * corrInnerSlice eta xi v := by
  calc
    (∫ x : ℝ, eta x * applyKernel (displacementKernel a) xi x) =
        ∫ x : ℝ, eta x * (∫ v : ℝ, a v * xi (x + v)) := by
      apply integral_congr_ae
      filter_upwards with x
      rw [applyKernel_displacementKernel_eq_translateFold]
    _ = ∫ x : ℝ, ∫ v : ℝ, displacementCorrelationIntegrand a eta xi v x := by
      apply integral_congr_ae
      filter_upwards with x
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with v
      simp only [displacementCorrelationIntegrand]
      ring
    _ = ∫ v : ℝ, ∫ x : ℝ, displacementCorrelationIntegrand a eta xi v x :=
      (integral_integral_swap hintegrable).symm
    _ = ∫ v : ℝ, a v * corrInnerSlice eta xi v :=
      (weightedCorrFold_eq_iteratedIntegral a eta xi).symm

/-- Equation-(121) now bounds the bilinear pairing of any displacement-kernel
operator whenever the explicit Fubini premise holds. -/
theorem norm_pairing_applyKernel_displacementKernel_le
    (a eta xi : ℝ -> ℂ)
    (heta : MemLp eta (ENNReal.ofReal 2))
    (hxi : MemLp xi (ENNReal.ofReal 2))
    (ha : AEStronglyMeasurable a volume)
    (haint : Integrable (fun v => ‖a v‖) volume)
    (hintegrable : Integrable
      (Function.uncurry (displacementCorrelationIntegrand a eta xi))
      (volume.prod volume)) :
    ‖∫ x : ℝ, eta x * applyKernel (displacementKernel a) xi x‖ ≤
      (∫ x : ℝ, ‖eta x‖ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) *
        (∫ x : ℝ, ‖xi x‖ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) * ∫ v : ℝ, ‖a v‖ := by
  rw [pairing_applyKernel_displacementKernel_eq_weightedCorrFold
    a eta xi hintegrable]
  exact abs_corrWeightedFold_le heta hxi ha haint

end C1CC20DisplacementReadback
end Source
end ConnesWeilRH
