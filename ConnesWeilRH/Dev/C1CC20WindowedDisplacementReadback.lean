/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1CC20KernelLpLift
import ConnesWeilRH.Dev.C1CC20DisplacementKernel

/-!
# CC20 square-window displacement readback

The raw displacement kernel acts on the whole real line.  The concrete CC20
kernel is instead restricted to the square window in both variables.  This
leaf proves the exact owner-preserving relation between them:

    K_I f = 1_I * K (1_I * f).

Here multiplication by `1_I` is represented by a set indicator, so it is both
the restriction to the window and the zero extension back to the ambient line.
The statement is pointwise and uses no integrability premise.  It therefore
does not identify any quotient operators or invoke the equation-(121) pairing
bound; those are separate, later lifts.
-/

namespace ConnesWeilRH
namespace Source
namespace C1CC20WindowedDisplacementReadback

open MeasureTheory
open C1CC20DisplacementKernel C1CC20KernelLpLift C1CC20LpOperator
  C1CC20RawKernelMass

/-- Restrict a function to the CC20 window and extend it by zero on the
ambient line. -/
noncomputable def cc20WindowZeroExtend (r : ℝ) (f : ℝ -> ℂ) : ℝ -> ℂ :=
  (cc20Window r).indicator f

/-- A square-window displacement kernel acts by zero-extending the input,
applying the raw displacement kernel, and zero-extending the output. -/
theorem applyKernel_windowedDisplacementKernel_eq_zeroExtend
    (a f : ℝ -> ℂ) (r : ℝ) :
    applyKernel (windowedDisplacementKernel a r) f =
      cc20WindowZeroExtend r
        (applyKernel (displacementKernel a) (cc20WindowZeroExtend r f)) := by
  funext x
  by_cases hx : x ∈ cc20Window r
  · rw [cc20WindowZeroExtend, Set.indicator_of_mem hx]
    have hrow :
        applyKernel (windowedDisplacementKernel a r) f x =
          applyKernel (displacementKernel a) (cc20WindowZeroExtend r f) x := by
      unfold applyKernel windowedDisplacementKernel displacementKernel cc20WindowZeroExtend
      apply integral_congr_ae
      filter_upwards with y
      by_cases hy : y ∈ cc20Window r
      · simp [cc20WindowPair, hx, hy]
      · simp [cc20WindowPair, hx, hy]
    exact hrow
  · rw [cc20WindowZeroExtend, Set.indicator_of_notMem hx]
    unfold applyKernel windowedDisplacementKernel
    apply integral_eq_zero_of_ae
    filter_upwards with y
    have hxy : (x, y) ∉ cc20WindowPair r := by
      simp [cc20WindowPair, hx]
    rw [Set.indicator_of_notMem hxy]
    simp

/-- The square-window action in displacement coordinates.  This is the
pointwise bridge into the equation-(121) translation form. -/
theorem applyKernel_windowedDisplacementKernel_eq_windowedTranslateFold
    (a f : ℝ -> ℂ) (r x : ℝ) :
    applyKernel (windowedDisplacementKernel a r) f x =
      cc20WindowZeroExtend r
        (fun z => ∫ v : ℝ, a v * cc20WindowZeroExtend r f (z + v)) x := by
  rw [applyKernel_windowedDisplacementKernel_eq_zeroExtend]
  congr 1
  funext z
  exact applyKernel_displacementKernel_eq_translateFold
    a (cc20WindowZeroExtend r f) z

/-- The concrete CC20 endpoint square-window operator has the same
zero-extension readback as its displacement-kernel presentation. -/
theorem applyKernel_endpointKernelOnSquare_eq_zeroExtend
    (data : CC20Concrete.CC20EndpointSpectralData) (f : ℝ -> ℂ) (r : ℝ) :
    applyKernel (endpointKernelOnSquare data r) f =
      cc20WindowZeroExtend r
        (applyKernel (displacementKernel (endpointDisplacementProfile data))
          (cc20WindowZeroExtend r f)) := by
  rw [endpointKernelOnSquare_eq_windowedDisplacementKernel]
  exact applyKernel_windowedDisplacementKernel_eq_zeroExtend
    (endpointDisplacementProfile data) f r

/-- Concrete CC20 endpoint action in the translated, windowed form consumed
by the subsequent pairing analysis. -/
theorem applyKernel_endpointKernelOnSquare_eq_windowedTranslateFold
    (data : CC20Concrete.CC20EndpointSpectralData) (f : ℝ -> ℂ) (r x : ℝ) :
    applyKernel (endpointKernelOnSquare data r) f x =
      cc20WindowZeroExtend r
        (fun z => ∫ v : ℝ,
          endpointDisplacementProfile data v * cc20WindowZeroExtend r f (z + v)) x := by
  rw [endpointKernelOnSquare_eq_windowedDisplacementKernel]
  exact applyKernel_windowedDisplacementKernel_eq_windowedTranslateFold
    (endpointDisplacementProfile data) f r x

/-- The bounded `L2` operator induced by a square-window displacement kernel
has the zero-extension representative almost everywhere.  The raw
translation-invariant kernel is deliberately not lifted as a global `L2`
operator: on the whole plane it need not have finite Hilbert--Schmidt mass. -/
theorem coeFn_applyKernelLp_windowedDisplacementKernel_eq_zeroExtend_ae
    (a : ℝ -> ℂ) (r : ℝ)
    (hk : MemLp (windowedDisplacementKernel a r) 2 volume)
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ((applyKernelLp (windowedDisplacementKernel a r) hk f :
        Lp ℂ 2 (volume : Measure ℝ)) : ℝ -> ℂ) =ᵐ[volume]
      cc20WindowZeroExtend r
        (applyKernel (displacementKernel a)
          (cc20WindowZeroExtend r (f : ℝ -> ℂ))) := by
  have hquot :
      ((applyKernelLp (windowedDisplacementKernel a r) hk f :
          Lp ℂ 2 (volume : Measure ℝ)) : ℝ -> ℂ) =ᵐ[volume]
        applyKernel (windowedDisplacementKernel a r) (f : ℝ -> ℂ) := by
    change
      ((memLp_applyKernel_two hk (Lp.memLp f)).toLp
        (applyKernel (windowedDisplacementKernel a r) (f : ℝ -> ℂ)) : ℝ -> ℂ)
        =ᵐ[volume] _
    exact (memLp_applyKernel_two hk (Lp.memLp f)).coeFn_toLp
  filter_upwards [hquot] with x hx
  rw [hx]
  exact congrFun
    (applyKernel_windowedDisplacementKernel_eq_zeroExtend a (f : ℝ -> ℂ) r) x

/-- Concrete CC20 endpoint version of the a.e. `L2` representative readback. -/
theorem coeFn_applyKernelLp_endpointKernelOnSquare_eq_zeroExtend_ae
    (data : CC20Concrete.CC20EndpointSpectralData) (r : ℝ)
    (hk : MemLp (endpointKernelOnSquare data r) 2 volume)
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ((applyKernelLp (endpointKernelOnSquare data r) hk f :
        Lp ℂ 2 (volume : Measure ℝ)) : ℝ -> ℂ) =ᵐ[volume]
      cc20WindowZeroExtend r
        (applyKernel (displacementKernel (endpointDisplacementProfile data))
          (cc20WindowZeroExtend r (f : ℝ -> ℂ))) := by
  exact coeFn_applyKernelLp_windowedDisplacementKernel_eq_zeroExtend_ae
    (endpointDisplacementProfile data) r hk f

end C1CC20WindowedDisplacementReadback
end Source
end ConnesWeilRH
