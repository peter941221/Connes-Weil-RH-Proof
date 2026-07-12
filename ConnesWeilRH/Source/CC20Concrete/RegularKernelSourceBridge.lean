/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.RegularKernelCompactMeasure

/-!
# Source-formula bridge for the CC20 regular kernel

CC20, `weil-compo.tex`, lines 803--806, writes the ordinary Schwartz kernel
piecewise as `Q delta (u / v)` for `u >= v` and `Q delta (v / u)` for
`v >= u`.  The diagonal Dirac mass is not part of this function.
-/

namespace ConnesWeilRH
namespace Source
namespace CC20Concrete

open MeasureTheory

/-- The two source branches of the ordinary CC20 kernel.  At equality we use
the continuous representative of the regular part; changing one diagonal
value does not encode the separate Dirac distribution. -/
noncomputable def cc20SourceRegularKernel
    (p : PositiveCoordinate × PositiveCoordinate) : ℝ :=
  if (p.1 : ℝ) ≤ p.2 then
    cc20QDeltaRegularExtension ((p.2 : ℝ) / p.1)
  else
    cc20QDeltaRegularExtension ((p.1 : ℝ) / p.2)

theorem ratioRadius_eq_snd_div_fst_of_le
    (p : PositiveCoordinate × PositiveCoordinate)
    (h : (p.1 : ℝ) ≤ p.2) :
    ratioRadius p = (p.2 : ℝ) / p.1 := by
  rw [ratioRadius, max_eq_right]
  apply (div_le_div_iff₀ p.2.property p.1.property).2
  nlinarith [mul_self_le_mul_self (le_of_lt p.1.property) h]

theorem ratioRadius_eq_fst_div_snd_of_le
    (p : PositiveCoordinate × PositiveCoordinate)
    (h : (p.2 : ℝ) ≤ p.1) :
    ratioRadius p = (p.1 : ℝ) / p.2 := by
  rw [ratioRadius, max_eq_left]
  apply (div_le_div_iff₀ p.1.property p.2.property).2
  nlinarith [mul_self_le_mul_self (le_of_lt p.2.property) h]

/-- The source's piecewise kernel is exactly the existing continuous regular
kernel.  This is a scalar-kernel identity, not yet the theorem identifying an
operator with CC20's `K_I`. -/
theorem cc20SourceRegularKernel_eq_cc20RegularKernel
    (p : PositiveCoordinate × PositiveCoordinate) :
    cc20SourceRegularKernel p = cc20RegularKernel p := by
  by_cases h : (p.1 : ℝ) ≤ p.2
  · rw [cc20SourceRegularKernel, if_pos h, cc20RegularKernel,
      ratioRadius_eq_snd_div_fst_of_le p h]
  · have h' : (p.2 : ℝ) ≤ p.1 := le_of_not_ge h
    rw [cc20SourceRegularKernel, if_neg h, cc20RegularKernel,
      ratioRadius_eq_fst_div_snd_of_le p h']

theorem cc20SourceRegularKernel_of_fst_lt_snd
    (p : PositiveCoordinate × PositiveCoordinate)
    (h : (p.1 : ℝ) < p.2) :
    cc20SourceRegularKernel p =
      multiplicativeQ cc20DeltaRegular ((p.2 : ℝ) / p.1) := by
  rw [cc20SourceRegularKernel, if_pos h.le]
  have hratio : 1 < (p.2 : ℝ) / p.1 :=
    (lt_div_iff₀ p.1.property).2 (by simpa using h)
  rw [cc20QDeltaRegularExtension_of_ne_one (ne_of_gt hratio)]
  exact (multiplicativeQ_cc20DeltaRegular_of_one_lt hratio).symm

theorem cc20SourceRegularKernel_of_snd_lt_fst
    (p : PositiveCoordinate × PositiveCoordinate)
    (h : (p.2 : ℝ) < p.1) :
    cc20SourceRegularKernel p =
      multiplicativeQ cc20DeltaRegular ((p.1 : ℝ) / p.2) := by
  rw [cc20SourceRegularKernel, if_neg (not_le_of_gt h)]
  have hratio : 1 < (p.1 : ℝ) / p.2 :=
    (lt_div_iff₀ p.2.property).2 (by simpa using h)
  rw [cc20QDeltaRegularExtension_of_ne_one (ne_of_gt hratio)]
  exact (multiplicativeQ_cc20DeltaRegular_of_one_lt hratio).symm

/-- The ordinary source kernel acting on a continuous complex input with the
exact multiplicative Haar measure.  Continuity and the full `L2` extension are
separate downstream obligations. -/
noncomputable def cc20CompactSourceHaarAction
    (f : ContinuousMap CC20CompactInterval ℂ)
    (x : CC20CompactInterval) : ℂ :=
  ∫ y, (cc20CompactRegularKernel (x, y) : ℂ) * f y
    ∂cc20CompactHaarMeasure

/-- The source action is literally integration against `d rho / rho`. -/
theorem cc20CompactSourceHaarAction_eq_weighted
    (f : ContinuousMap CC20CompactInterval ℂ)
    (x : CC20CompactInterval) :
    cc20CompactSourceHaarAction f x =
      ∫ y, (1 / (y : ℝ)) •
        ((cc20CompactRegularKernel (x, y) : ℂ) * f y)
        ∂cc20CompactMeasure := by
  exact integral_cc20CompactHaarMeasure_eq_smul _

end CC20Concrete
end Source
end ConnesWeilRH
