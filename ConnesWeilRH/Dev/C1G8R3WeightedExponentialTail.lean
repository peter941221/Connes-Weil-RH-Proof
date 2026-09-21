/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3ScatteringPhaseSecondGrowth

/-!
# Polynomially weighted exponential tails

These are the scalar tail estimates used when the quadratic phase-growth bound
is multiplied by a critical Mellin profile.  Keeping the polynomial weight
explicit avoids hiding the W2,1 tail cost inside an unproved integrability
claim.
-/

namespace ConnesWeilRH
namespace Dev

open Set MeasureTheory Real

theorem integrableOn_sq_mul_exp_neg_mul
    {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => t ^ 2 * Real.exp (-a * t)) (Ioi 0) := by
  simpa [Real.rpow_two] using
    (integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := (1 : ℝ)) (s := (2 : ℝ)) (b := a)
      (by norm_num) (by norm_num) ha)

theorem integrableOn_sq_mul_exp_mul
    {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => t ^ 2 * Real.exp (a * t)) (Iio 0) := by
  rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (Homeomorph.neg ℝ).measurableEmbedding]
  convert integrableOn_sq_mul_exp_neg_mul ha using 1 <;>
    simp only [Function.comp_def, neg_sq, neg_preimage, neg_Iio, neg_zero]
  · funext t
    ring

end Dev
end ConnesWeilRH
