/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3SchwartzQuadraticDecay
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSBandTrace

/-!
# Selected-root Schwartz bridge

The selected root is a genuine global convolution operator.  On the dense
Schwartz core its L2 output is exactly the Schwartz convolution with the
involuted compact root.  This makes the quadratic Fourier-decay brick usable
for the actual owner, while making no claim about arbitrary source-carrier
basis vectors or the missing Hardy multiplier regularity.
-/

namespace ConnesWeilRH
namespace Dev

open MeasureTheory
open Source
open Source.CC20Concrete
open Source.CCM25Concrete
open Source.CCM25Concrete.CCM24FiniteSBandTrace
open scoped FourierTransform

noncomputable def selectedRootSchwartzOutput
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (u : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.convolution (ContinuousLinearMap.mul ℝ ℂ)
    owner.sourceTest.involution.test u

theorem rootConvolution_apply_schwartz
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (u : SchwartzMap ℝ ℂ) :
    rootConvolution owner (u.toLp 2) =
      (selectedRootSchwartzOutput owner u).toLp 2 := by
  unfold rootConvolution selectedRootSchwartzOutput
  exact cc20GlobalLogConvolution_toLp
    owner.sourceTest.involution.test u

theorem rootConvolution_schwartz_quadratic_decay
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (u : SchwartzMap ℝ ℂ) (x : ℝ) :
    ‖x‖ ^ 2 * ‖𝓕 (selectedRootSchwartzOutput owner u) x‖ ≤
      ∫ t : ℝ,
        ‖deriv (deriv (selectedRootSchwartzOutput owner u : ℝ → ℂ)) t‖ ∂volume := by
  exact fourier_norm_mul_sq_le_schwartz_second_deriv
    (selectedRootSchwartzOutput owner u) x

theorem rootConvolution_schwartz_fourier_normSq_summable
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (u : SchwartzMap ℝ ℂ) :
    Summable (fun n : ℕ =>
      ‖𝓕 (selectedRootSchwartzOutput owner u) (n : ℝ)‖ ^ 2) := by
  exact summable_schwartz_fourier_normSq_on_unit_annuli
    (selectedRootSchwartzOutput owner u)

end Dev
end ConnesWeilRH
