/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.GlobalLogConvolution
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The common whole-line convolution/crossing operator

This file only records the bounded operator composition.  It does not identify
its trace with a scalar; that remains a separate same-object kernel theorem.
-/

namespace ConnesWeilRH
namespace Source
namespace CC20Concrete

open scoped InnerProduct InnerProductSpace

noncomputable def cc20GlobalConvolutionPositive
    (h : SchwartzMap ℝ ℂ) :
    cc20GlobalLogCrossingL2 →L[ℂ] cc20GlobalLogCrossingL2 :=
  (cc20GlobalLogConvolution h)† ∘L cc20GlobalLogConvolution h

noncomputable def cc20GlobalConvolutionCrossing
    (h : SchwartzMap ℝ ℂ) (b : ℝ) :
    cc20GlobalLogCrossingL2 →L[ℂ] cc20GlobalLogCrossingL2 :=
  cc20GlobalConvolutionPositive h ∘L cc20SingleCrossingOperator b

theorem cc20GlobalConvolutionPositive_apply
    (h : SchwartzMap ℝ ℂ) (u : cc20GlobalLogCrossingL2) :
    cc20GlobalConvolutionPositive h u =
      ((cc20GlobalLogConvolution h)†) (cc20GlobalLogConvolution h u) := by
  rfl

theorem cc20GlobalConvolutionCrossing_apply
    (h : SchwartzMap ℝ ℂ) (b : ℝ) (u : cc20GlobalLogCrossingL2) :
    cc20GlobalConvolutionCrossing h b u =
      ((cc20GlobalLogConvolution h)†)
        (cc20GlobalLogConvolution h
          (cc20SingleCrossingOperator b u)) := by
  rfl

theorem cc20GlobalConvolutionPositive_inner_re_eq_norm_sq
    (h : SchwartzMap ℝ ℂ) (u : cc20GlobalLogCrossingL2) :
    ‖cc20GlobalLogConvolution h u‖ ^ 2 =
      (⟪u, cc20GlobalConvolutionPositive h u⟫_ℂ).re := by
  exact ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right
    (cc20GlobalLogConvolution h) u

theorem cc20GlobalConvolutionPositive_inner_re_nonnegative
    (h : SchwartzMap ℝ ℂ) (u : cc20GlobalLogCrossingL2) :
    0 ≤ (⟪u, cc20GlobalConvolutionPositive h u⟫_ℂ).re := by
  rw [← cc20GlobalConvolutionPositive_inner_re_eq_norm_sq h u]
  exact sq_nonneg _

end CC20Concrete
end Source
end ConnesWeilRH
