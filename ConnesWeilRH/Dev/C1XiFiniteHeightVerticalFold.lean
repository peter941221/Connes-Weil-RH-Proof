import ConnesWeilRH.Dev.C1XiFiniteHeightRectangle

/-!
# C1XiFiniteHeightVerticalFold - fold finite critical-strip vertical sides

For a finite zero-free critical-strip rectangle, the functional equation folds
the left vertical xi-contour integral onto the right vertical line.  The result
uses `xiRightLineKernel`, whose reflected weight is introduced only after the
two sides have been combined.

No horizontal-edge decay, contour limit, arithmetic readback, explicit-formula
equality, or RH claim is made here.
-/

namespace ConnesWeilRH
namespace Source
namespace C1XiFiniteHeightVerticalFold

open MeasureTheory
open Set
open CC20ZetaCounting
open CCM25Concrete.CompactLogConvolution
open C1XiFiniteHeightRectangle
open C1XiResidue
open C1XiVerticalFunctional
open scoped Interval

/-- The two oriented vertical sides of a finite zero-free critical-strip
rectangle fold to the single right-line integrand. -/
theorem criticalStripVerticalBoundaryIntegral_eq_rightLineIntegral
    (F : CompactLogTest) (T : Real) (hT : 0 < T)
    (hheight : xiHeightBoundaryAvoidsZeros T) :
    Complex.I • (∫ t : Real in (-T)..T,
        xiContourKernel F (verticalPoint 1 t)) -
      Complex.I • (∫ t : Real in (-T)..T,
        xiContourKernel F (verticalPoint 0 t)) =
      ∫ t : Real in (-T)..T, verticalIntegrand F 1 t := by
  have hboundary := xiRectangleBoundaryAvoidsZeros_criticalStripRectangle T hheight
  have hright_nonzero : ∀ t ∈ [[-T, T]],
      completedRiemannXi (verticalPoint 1 t) ≠ 0 := by
    intro t ht
    have h := hboundary.2.2.1 t (by
      simpa only [criticalStripRectangleLower_im, criticalStripRectangleUpper_im] using ht)
    simpa [verticalPoint] using h
  have hleft_nonzero : ∀ t ∈ [[-T, T]],
      completedRiemannXi (verticalPoint 0 t) ≠ 0 := by
    intro t ht
    have h := hboundary.2.2.2 t (by
      simpa only [criticalStripRectangleLower_im, criticalStripRectangleUpper_im] using ht)
    simpa [verticalPoint] using h
  have hright_map : Continuous (fun t : Real => verticalPoint 1 t) := by
    unfold verticalPoint
    fun_prop
  have hleft_reflected_map : Continuous (fun t : Real => verticalPoint 0 (-t)) := by
    unfold verticalPoint
    fun_prop
  have hright_integrable : IntervalIntegrable
      (fun t : Real => xiContourKernel F (verticalPoint 1 t)) volume (-T) T := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    simpa only [Function.comp_apply] using
      (differentiableAt_xiContourKernel_of_completedRiemannXi_ne_zero F
        (hright_nonzero t ht)).continuousAt.comp_continuousWithinAt
          hright_map.continuousAt.continuousWithinAt
  have hleft_reflected_nonzero : ∀ t ∈ [[-T, T]],
      completedRiemannXi (verticalPoint 0 (-t)) ≠ 0 := by
    intro t ht
    apply hleft_nonzero (-t)
    rw [uIcc_of_le (by linarith : -T ≤ T)] at ht ⊢
    constructor <;> linarith [ht.1, ht.2]
  have hleft_reflected_integrable : IntervalIntegrable
      (fun t : Real => xiContourKernel F (verticalPoint 0 (-t))) volume (-T) T := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    have hcontinuous : ContinuousAt
        (fun u : Real => xiContourKernel F (verticalPoint 0 (-u))) t :=
      (differentiableAt_xiContourKernel_of_completedRiemannXi_ne_zero F
        (hleft_reflected_nonzero t ht)).continuousAt.comp'
          (f := fun u : Real => verticalPoint 0 (-u)) (x := t)
          hleft_reflected_map.continuousAt
    exact hcontinuous.continuousWithinAt
  have hleft_change :
      (∫ t : Real in (-T)..T, xiContourKernel F (verticalPoint 0 t)) =
        ∫ t : Real in (-T)..T, xiContourKernel F (verticalPoint 0 (-t)) := by
    simpa using (intervalIntegral.integral_comp_neg
      (f := fun t : Real => xiContourKernel F (verticalPoint 0 t))
      (a := -T) (b := T)).symm
  have hsub :
      (∫ t : Real in (-T)..T,
          xiContourKernel F (verticalPoint 1 t) -
            xiContourKernel F (verticalPoint 0 (-t))) =
        (∫ t : Real in (-T)..T, xiContourKernel F (verticalPoint 1 t)) -
          ∫ t : Real in (-T)..T, xiContourKernel F (verticalPoint 0 (-t)) :=
    intervalIntegral.integral_sub hright_integrable hleft_reflected_integrable
  have hkernel :
      (∫ t : Real in (-T)..T,
          xiContourKernel F (verticalPoint 1 t) -
            xiContourKernel F (verticalPoint 0 (-t))) =
        ∫ t : Real in (-T)..T, xiRightLineKernel F (verticalPoint 1 t) := by
    apply intervalIntegral.integral_congr
    intro t _
    change xiContourKernel F (verticalPoint 1 t) -
      xiContourKernel F (verticalPoint 0 (-t)) =
        xiRightLineKernel F (verticalPoint 1 t)
    have hreflect : verticalPoint 0 (-t) = 1 - verticalPoint 1 t := by
      simpa using (verticalPoint_reflection (1 : Real) t)
    rw [hreflect]
    exact (xiRightLineKernel_eq_xiContourKernel_sub_reflected
      F (verticalPoint 1 t)).symm
  have hdifference :
      (∫ t : Real in (-T)..T, xiContourKernel F (verticalPoint 1 t)) -
          ∫ t : Real in (-T)..T, xiContourKernel F (verticalPoint 0 t) =
        ∫ t : Real in (-T)..T, xiRightLineKernel F (verticalPoint 1 t) := by
    calc
      (∫ t : Real in (-T)..T, xiContourKernel F (verticalPoint 1 t)) -
          ∫ t : Real in (-T)..T, xiContourKernel F (verticalPoint 0 t) =
          (∫ t : Real in (-T)..T, xiContourKernel F (verticalPoint 1 t)) -
            ∫ t : Real in (-T)..T, xiContourKernel F (verticalPoint 0 (-t)) := by
            rw [hleft_change]
      _ = ∫ t : Real in (-T)..T,
          xiContourKernel F (verticalPoint 1 t) -
            xiContourKernel F (verticalPoint 0 (-t)) := hsub.symm
      _ = ∫ t : Real in (-T)..T, xiRightLineKernel F (verticalPoint 1 t) := hkernel
  calc
    Complex.I • (∫ t : Real in (-T)..T, xiContourKernel F (verticalPoint 1 t)) -
        Complex.I • (∫ t : Real in (-T)..T, xiContourKernel F (verticalPoint 0 t)) =
        Complex.I * ((∫ t : Real in (-T)..T, xiContourKernel F (verticalPoint 1 t)) -
          ∫ t : Real in (-T)..T, xiContourKernel F (verticalPoint 0 t)) := by
          simp only [smul_eq_mul]
          ring
    _ = Complex.I * ∫ t : Real in (-T)..T,
        xiRightLineKernel F (verticalPoint 1 t) := by rw [hdifference]
    _ = (∫ t : Real in (-T)..T,
        xiRightLineKernel F (verticalPoint 1 t)) * Complex.I := by ring
    _ = ∫ t : Real in (-T)..T, verticalIntegrand F 1 t := by
        rw [← intervalIntegral.integral_mul_const]
        rfl

end C1XiFiniteHeightVerticalFold
end Source
end ConnesWeilRH
