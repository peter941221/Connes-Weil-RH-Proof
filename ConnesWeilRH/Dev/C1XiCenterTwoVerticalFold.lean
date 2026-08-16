import ConnesWeilRH.Dev.C1XiCenterTwoFiniteRectangle

/-!
# C1XiCenterTwoVerticalFold - fold the `[-1,2]` rectangle to `Re(s)=2`

The functional equation sends the left line `Re(s)=-1` to the right line
`Re(s)=2`.  After reversing the height parameter, the two oriented vertical
sides become the existing symmetrized right-line integrand at the fixed,
absolutely convergent abscissa `c=2`.
-/

namespace ConnesWeilRH
namespace Source
namespace C1XiCenterTwoVerticalFold

open MeasureTheory
open Set
open CC20ZetaCounting
open CCM25Concrete.CompactLogConvolution
open C1XiCenterTwoFiniteRectangle
open C1XiFiniteRectangleBoundary
open C1XiResidue
open C1XiVerticalFunctional
open scoped Interval

/-- The two oriented vertical sides of the wide rectangle fold to the fixed
right-line integrand on `Re(s)=2`. -/
theorem centerTwoVerticalBoundaryIntegral_eq_rightLineIntegral
    (F : CompactLogTest) (T : Real) (hT : 0 < T)
    (hheight : centerTwoHeightBoundaryAvoidsZeros T) :
    Complex.I • (∫ t : Real in (-T)..T,
        xiContourKernel F (verticalPoint 2 t)) -
      Complex.I • (∫ t : Real in (-T)..T,
        xiContourKernel F (verticalPoint (-1) t)) =
      ∫ t : Real in (-T)..T, verticalIntegrand F 2 t := by
  have hboundary :=
    xiRectangleBoundaryAvoidsZeros_centerTwoRectangle T hheight
  have hright_nonzero : ∀ t ∈ [[-T, T]],
      completedRiemannXi (verticalPoint 2 t) ≠ 0 := by
    intro t ht
    have h := hboundary.2.2.1 t (by
      simpa only [centerTwoRectangleLower_im, centerTwoRectangleUpper_im]
        using ht)
    simpa [verticalPoint] using h
  have hleft_nonzero : ∀ t ∈ [[-T, T]],
      completedRiemannXi (verticalPoint (-1) t) ≠ 0 := by
    intro t ht
    have h := hboundary.2.2.2 t (by
      simpa only [centerTwoRectangleLower_im, centerTwoRectangleUpper_im]
        using ht)
    simpa [verticalPoint] using h
  have hright_map : Continuous (fun t : Real => verticalPoint 2 t) := by
    unfold verticalPoint
    fun_prop
  have hleft_reflected_map :
      Continuous (fun t : Real => verticalPoint (-1) (-t)) := by
    unfold verticalPoint
    fun_prop
  have hright_integrable : IntervalIntegrable
      (fun t : Real => xiContourKernel F (verticalPoint 2 t))
      volume (-T) T := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    simpa only [Function.comp_apply] using
      (differentiableAt_xiContourKernel_of_completedRiemannXi_ne_zero F
        (hright_nonzero t ht)).continuousAt.comp_continuousWithinAt
          hright_map.continuousAt.continuousWithinAt
  have hleft_reflected_nonzero : ∀ t ∈ [[-T, T]],
      completedRiemannXi (verticalPoint (-1) (-t)) ≠ 0 := by
    intro t ht
    apply hleft_nonzero (-t)
    rw [uIcc_of_le (by linarith : -T ≤ T)] at ht ⊢
    constructor <;> linarith [ht.1, ht.2]
  have hleft_reflected_integrable : IntervalIntegrable
      (fun t : Real => xiContourKernel F (verticalPoint (-1) (-t)))
      volume (-T) T := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    have hcontinuous : ContinuousAt
        (fun u : Real => xiContourKernel F (verticalPoint (-1) (-u))) t :=
      (differentiableAt_xiContourKernel_of_completedRiemannXi_ne_zero F
        (hleft_reflected_nonzero t ht)).continuousAt.comp'
          (f := fun u : Real => verticalPoint (-1) (-u)) (x := t)
          hleft_reflected_map.continuousAt
    exact hcontinuous.continuousWithinAt
  have hleft_change :
      (∫ t : Real in (-T)..T,
          xiContourKernel F (verticalPoint (-1) t)) =
        ∫ t : Real in (-T)..T,
          xiContourKernel F (verticalPoint (-1) (-t)) := by
    simpa using (intervalIntegral.integral_comp_neg
      (f := fun t : Real => xiContourKernel F (verticalPoint (-1) t))
      (a := -T) (b := T)).symm
  have hsub :
      (∫ t : Real in (-T)..T,
          xiContourKernel F (verticalPoint 2 t) -
            xiContourKernel F (verticalPoint (-1) (-t))) =
        (∫ t : Real in (-T)..T,
          xiContourKernel F (verticalPoint 2 t)) -
          ∫ t : Real in (-T)..T,
            xiContourKernel F (verticalPoint (-1) (-t)) :=
    intervalIntegral.integral_sub hright_integrable
      hleft_reflected_integrable
  have hkernel :
      (∫ t : Real in (-T)..T,
          xiContourKernel F (verticalPoint 2 t) -
            xiContourKernel F (verticalPoint (-1) (-t))) =
        ∫ t : Real in (-T)..T,
          xiRightLineKernel F (verticalPoint 2 t) := by
    apply intervalIntegral.integral_congr
    intro t _
    change xiContourKernel F (verticalPoint 2 t) -
      xiContourKernel F (verticalPoint (-1) (-t)) =
        xiRightLineKernel F (verticalPoint 2 t)
    have hreflect : verticalPoint (-1) (-t) =
        1 - verticalPoint 2 t := by
      apply Complex.ext <;> simp [verticalPoint] <;> ring
    rw [hreflect]
    exact (xiRightLineKernel_eq_xiContourKernel_sub_reflected
      F (verticalPoint 2 t)).symm
  have hdifference :
      (∫ t : Real in (-T)..T,
          xiContourKernel F (verticalPoint 2 t)) -
          ∫ t : Real in (-T)..T,
            xiContourKernel F (verticalPoint (-1) t) =
        ∫ t : Real in (-T)..T,
          xiRightLineKernel F (verticalPoint 2 t) := by
    calc
      (∫ t : Real in (-T)..T,
          xiContourKernel F (verticalPoint 2 t)) -
          ∫ t : Real in (-T)..T,
            xiContourKernel F (verticalPoint (-1) t) =
          (∫ t : Real in (-T)..T,
            xiContourKernel F (verticalPoint 2 t)) -
            ∫ t : Real in (-T)..T,
              xiContourKernel F (verticalPoint (-1) (-t)) := by
            rw [hleft_change]
      _ = ∫ t : Real in (-T)..T,
          xiContourKernel F (verticalPoint 2 t) -
            xiContourKernel F (verticalPoint (-1) (-t)) := hsub.symm
      _ = ∫ t : Real in (-T)..T,
          xiRightLineKernel F (verticalPoint 2 t) := hkernel
  calc
    Complex.I • (∫ t : Real in (-T)..T,
        xiContourKernel F (verticalPoint 2 t)) -
        Complex.I • (∫ t : Real in (-T)..T,
          xiContourKernel F (verticalPoint (-1) t)) =
        Complex.I * ((∫ t : Real in (-T)..T,
          xiContourKernel F (verticalPoint 2 t)) -
          ∫ t : Real in (-T)..T,
            xiContourKernel F (verticalPoint (-1) t)) := by
          simp only [smul_eq_mul]
          ring
    _ = Complex.I * ∫ t : Real in (-T)..T,
        xiRightLineKernel F (verticalPoint 2 t) := by rw [hdifference]
    _ = (∫ t : Real in (-T)..T,
        xiRightLineKernel F (verticalPoint 2 t)) * Complex.I := by ring
    _ = ∫ t : Real in (-T)..T, verticalIntegrand F 2 t := by
      rw [← intervalIntegral.integral_mul_const]
      rfl

end C1XiCenterTwoVerticalFold
end Source
end ConnesWeilRH
