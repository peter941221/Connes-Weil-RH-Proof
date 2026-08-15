import ConnesWeilRH.Dev.C1XiFiniteHeightVerticalFold

/-!
# C1XiFiniteHeightRectangleAssembly - finite rectangle decomposition

The finite critical-strip rectangle already reads its boundary as a finite
spectral sum, and its two vertical sides now fold to one right-line integral.
This module keeps those facts on the same height-specific factor owner and
leaves the two horizontal edges explicit.

No horizontal-edge decay, xi logarithmic-derivative estimate, contour limit,
arithmetic readback, explicit-formula equality, or RH claim is made here.
-/

namespace ConnesWeilRH
namespace Source
namespace C1XiFiniteHeightRectangleAssembly

open MeasureTheory
open CCM25Concrete.CompactLogConvolution
open C1SpectralWeil
open C1XiFiniteHeightRectangle
open C1XiFiniteHeightVerticalFold
open C1XiFiniteRectangleBoundary
open C1XiVerticalFunctional
open scoped Interval

/-- The two oriented horizontal edges of the finite critical-strip rectangle.
They remain explicit because their decay is a separate analytic problem. -/
noncomputable def criticalStripHorizontalBoundaryIntegral
    (F : CompactLogTest) (T : Real) : Complex :=
  (∫ x : Real in (criticalStripRectangleLower T).re..
      (criticalStripRectangleUpper T).re,
      xiContourKernel F (x + (criticalStripRectangleLower T).im * Complex.I)) -
    ∫ x : Real in (criticalStripRectangleLower T).re..
      (criticalStripRectangleUpper T).re,
      xiContourKernel F (x + (criticalStripRectangleUpper T).im * Complex.I)

/-- The right vertical integral after the functional-equation fold. -/
noncomputable def criticalStripFoldedRightLineIntegral
    (F : CompactLogTest) (T : Real) : Complex :=
  ∫ t : Real in (-T)..T, verticalIntegrand F 1 t

/-- The finite rectangle boundary is its explicit horizontal contribution plus
the folded right-line contribution. -/
theorem xiRectangleBoundaryIntegral_eq_horizontal_add_foldedRightLine
    (F : CompactLogTest) (T : Real) (hT : 0 < T)
    (hheight : xiHeightBoundaryAvoidsZeros T) :
    xiRectangleBoundaryIntegral (xiContourKernel F)
      (criticalStripRectangleLower T) (criticalStripRectangleUpper T) =
      criticalStripHorizontalBoundaryIntegral F T +
        criticalStripFoldedRightLineIntegral F T := by
  have hvertical :
      Complex.I • (∫ y : Real in (criticalStripRectangleLower T).im..
          (criticalStripRectangleUpper T).im,
          xiContourKernel F ((criticalStripRectangleUpper T).re + y * Complex.I)) -
        Complex.I • (∫ y : Real in (criticalStripRectangleLower T).im..
          (criticalStripRectangleUpper T).im,
          xiContourKernel F ((criticalStripRectangleLower T).re + y * Complex.I)) =
        criticalStripFoldedRightLineIntegral F T := by
    simpa [criticalStripFoldedRightLineIntegral, verticalPoint] using
      (criticalStripVerticalBoundaryIntegral_eq_rightLineIntegral F T hT hheight)
  unfold criticalStripFoldedRightLineIntegral at hvertical
  unfold xiRectangleBoundaryIntegral criticalStripHorizontalBoundaryIntegral
    criticalStripFoldedRightLineIntegral
  rw [← hvertical]
  ring

/-- One finite-height factor owner supplies the full finite rectangle equation:
horizontal edges plus the folded right line equal its finite zero spectrum. -/
theorem XiHeightRectangleFactorData.horizontal_add_foldedRightLine_eq_neg_finiteSpectralSum
    (D : XiHeightRectangleFactorData) (F : CompactLogTest) :
    criticalStripHorizontalBoundaryIntegral F D.height +
        criticalStripFoldedRightLineIntegral F D.height =
      -(2 * (Real.pi : Complex) * Complex.I * finiteSpectralSum F D.height) := by
  calc
    criticalStripHorizontalBoundaryIntegral F D.height +
        criticalStripFoldedRightLineIntegral F D.height =
        xiRectangleBoundaryIntegral (xiContourKernel F)
          (criticalStripRectangleLower D.height)
          (criticalStripRectangleUpper D.height) :=
      (xiRectangleBoundaryIntegral_eq_horizontal_add_foldedRightLine F D.height
        D.height_pos D.boundary_avoids).symm
    _ = -(2 * (Real.pi : Complex) * Complex.I * finiteSpectralSum F D.height) :=
      D.xiRectangleBoundaryIntegral_readout F

end C1XiFiniteHeightRectangleAssembly
end Source
end ConnesWeilRH
