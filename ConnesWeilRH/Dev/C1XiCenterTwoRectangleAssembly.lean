import ConnesWeilRH.Dev.C1XiCenterTwoVerticalFold

/-!
# C1XiCenterTwoRectangleAssembly - finite wide rectangle equation

The center-`2` finite-factor readout and the functional-equation fold are
assembled at one selected height.  The only remaining finite-height term is
the explicit pair of horizontal sides already controlled by quartic decay.
-/

namespace ConnesWeilRH
namespace Source
namespace C1XiCenterTwoRectangleAssembly

open MeasureTheory
open CCM25Concrete.CompactLogConvolution
open C1SpectralWeil
open C1XiCenterTwoFiniteRectangle
open C1XiCenterTwoHorizontal
open C1XiCenterTwoHorizontalBoundary
open C1XiCenterTwoVerticalFold
open C1XiFiniteRectangleBoundary
open C1XiVerticalFunctional
open scoped Interval

/-- The folded right-line integral on the fixed absolutely convergent line
`Re(s)=2`. -/
noncomputable def centerTwoFoldedRightLineIntegral
    (F : CompactLogTest) (T : Real) : Complex :=
  ∫ t : Real in (-T)..T, verticalIntegrand F 2 t

/-- The wide rectangle boundary is its two horizontal sides plus the folded
right-line integral. -/
theorem xiRectangleBoundaryIntegral_eq_wideHorizontal_add_centerTwoRightLine
    (F : CompactLogTest) (T : Real) (hT : 0 < T)
    (hheight : centerTwoHeightBoundaryAvoidsZeros T) :
    xiRectangleBoundaryIntegral (xiContourKernel F)
      (centerTwoRectangleLower T) (centerTwoRectangleUpper T) =
      wideHorizontalBoundaryIntegral F T +
        centerTwoFoldedRightLineIntegral F T := by
  have hvertical :
      Complex.I • (∫ y : Real in (centerTwoRectangleLower T).im..
          (centerTwoRectangleUpper T).im,
          xiContourKernel F
            ((centerTwoRectangleUpper T).re + y * Complex.I)) -
        Complex.I • (∫ y : Real in (centerTwoRectangleLower T).im..
          (centerTwoRectangleUpper T).im,
          xiContourKernel F
            ((centerTwoRectangleLower T).re + y * Complex.I)) =
        centerTwoFoldedRightLineIntegral F T := by
    simpa [centerTwoFoldedRightLineIntegral, verticalPoint] using
      (centerTwoVerticalBoundaryIntegral_eq_rightLineIntegral
        F T hT hheight)
  unfold centerTwoFoldedRightLineIntegral at hvertical
  unfold xiRectangleBoundaryIntegral wideHorizontalBoundaryIntegral
    centerTwoFoldedRightLineIntegral
  simp only [centerTwoRectangleLower_re, centerTwoRectangleLower_im,
    centerTwoRectangleUpper_re, centerTwoRectangleUpper_im,
    verticalPoint] at hvertical ⊢
  rw [← hvertical]
  ring

/-- One selected center-`2` owner supplies the complete finite-height wide
rectangle equation. -/
theorem DyadicCenterTwoHorizontalData.wideHorizontal_add_centerTwoRightLine_eq
    {n : Nat} (H : DyadicCenterTwoHorizontalData n) (F : CompactLogTest) :
    wideHorizontalBoundaryIntegral F H.height +
        centerTwoFoldedRightLineIntegral F H.height =
      -(2 * (Real.pi : Complex) * Complex.I *
        finiteSpectralSum F H.height) := by
  calc
    wideHorizontalBoundaryIntegral F H.height +
        centerTwoFoldedRightLineIntegral F H.height =
        xiRectangleBoundaryIntegral (xiContourKernel F)
          (centerTwoRectangleLower H.height)
          (centerTwoRectangleUpper H.height) :=
      (xiRectangleBoundaryIntegral_eq_wideHorizontal_add_centerTwoRightLine
        F H.height H.height_pos
        (C1XiCenterTwoFiniteRectangle.DyadicCenterTwoHorizontalData.centerTwoHeightBoundaryAvoidsZeros
          H)).symm
    _ = -(2 * (Real.pi : Complex) * Complex.I *
        finiteSpectralSum F H.height) :=
      C1XiCenterTwoFiniteRectangle.DyadicCenterTwoHorizontalData.centerTwoRectangleBoundaryIntegral_readout
        H F

end C1XiCenterTwoRectangleAssembly
end Source
end ConnesWeilRH
