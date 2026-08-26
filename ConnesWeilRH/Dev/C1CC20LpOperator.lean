/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# CC20 integral operator on L² (foundation for `kf_I`)

CC20's endpoint argument acts on the windowed space `L²(I)` through the
integral operator with kernel `k`, written `kf_I`.  Its boundedness rests on
the Hilbert--Schmidt estimate: an `L²` kernel applied to an `L²` input is a
bounded map, with the pointwise output controlled by the kernel's row mass and
the input norm.

This leaf supplies that foundation in its raw integral form (not via the
abstract `Lp` type), matching the owner-preserving idiom already used on this
branch.  The first theorem is the pointwise Cauchy--Schwarz estimate

    ‖(Af)(x)‖ ≤ ‖k(·, x)‖₂ · ‖f‖₂,

where `(Af)(x) = ∫ k(x, y) f(y) dy`.  The integrated operator-norm form
`‖Af‖₂ ≤ ‖k‖_{L²(ℝ²)} · ‖f‖₂` is the immediate next brick; it requires
integrating this pointwise bound over `x`, which needs an extra round of
Fubini and integral-monotonicity plumbing.

This file contains no RH-level sign or coverage claim.
-/

namespace ConnesWeilRH
namespace Source
namespace C1CC20LpOperator

open MeasureTheory

/-- Apply an integral kernel `k : ℝ × ℝ → ℂ` to a function `f : ℝ → ℂ`, giving
a complex-valued function of the first variable: `(Af)(x) = ∫_y k(x, y) f(y) dy`. -/
noncomputable def applyKernel (k : ℝ × ℝ → ℂ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ y, k (x, y) * f y

/-- Pointwise Hilbert--Schmidt bound.  For a fixed output coordinate `x`, the
value of the kernel-applied function is controlled by the `L²` mass of the
kernel's `x`-row times the `L²` norm of the input.

This is exactly Cauchy--Schwarz for the pairing `(u, v) ↦ ∫ u(y) v(y) dy`, with
the kernel row `y ↦ k(x, y)` playing the role of one factor and `f` the other.
The two `MemLp` hypotheses say precisely that both factors lie in `L²`. -/
theorem applyKernel_pointwise_l2_bound {k : ℝ × ℝ → ℂ} {f : ℝ → ℂ} (x : ℝ)
    (hrow : MemLp (fun y => k (x, y)) (ENNReal.ofReal (2 : ℝ)))
    (hf : MemLp f (ENNReal.ofReal (2 : ℝ))) :
    ‖applyKernel k f x‖ ≤
      (∫ y, ‖k (x, y)‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
        (∫ y, ‖f y‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
  have hholder : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  -- Cauchy--Schwarz for the product of the two `L²` factors.
  have hraw :
      (∫ y, ‖k (x, y)‖ * ‖f y‖) ≤
        (∫ y, ‖k (x, y)‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
          (∫ y, ‖f y‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
    exact MeasureTheory.integral_mul_norm_le_Lp_mul_Lq hholder hrow hf
  calc
    ‖applyKernel k f x‖ ≤ ∫ y, ‖k (x, y) * f y‖ := by
      rw [applyKernel]
      exact MeasureTheory.norm_integral_le_integral_norm _
    _ = ∫ y, ‖k (x, y)‖ * ‖f y‖ := by
      apply integral_congr_ae
      filter_upwards with y
      rw [norm_mul]
    _ ≤ (∫ y, ‖k (x, y)‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
          (∫ y, ‖f y‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := hraw

end C1CC20LpOperator
end Source
end ConnesWeilRH
