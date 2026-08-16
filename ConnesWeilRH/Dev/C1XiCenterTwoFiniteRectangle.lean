import ConnesWeilRH.Dev.C1XiCenterTwoHorizontalBoundary
import ConnesWeilRH.Dev.C1XiFiniteRectangleSupportReindex

/-!
# C1XiCenterTwoFiniteRectangle - the fixed `[-1,2]` xi rectangle

The center-`2` Borel owner contains the wider rectangle with real interval
`[-1,2]`.  Its horizontal sides are zero-free by the selected dyadic tubes;
its vertical sides are zero-free because every xi zero has real part strictly
between `0` and `1`.  The same finite factor therefore reads the rectangle as
the usual symmetric finite-height spectral sum.
-/

namespace ConnesWeilRH
namespace Source
namespace C1XiCenterTwoFiniteRectangle

open Filter
open Set
open CC20YoshidaNearZeros
open CC20ZetaCounting
open CCM25Concrete.CompactLogConvolution
open C1SpectralWeil
open C1XiCenterTwoHorizontal
open C1XiCofactorBorel
open C1XiFiniteHeightRectangle
open C1XiFiniteFactor
open C1XiFiniteRectangleBoundary
open C1XiFiniteRectanglePrincipalPart
open C1XiFiniteRectangleSupportReindex
open C1XiFiniteSupportReindex
open C1XiQuantitativeHeight
open C1XiVerticalFunctional
open scoped BigOperators Interval Topology

noncomputable section

/-- Lower-left and upper-right corners of the fixed wide rectangle. -/
noncomputable def centerTwoRectangleLower (T : Real) : Complex :=
  (-1 : Complex) - T * Complex.I

noncomputable def centerTwoRectangleUpper (T : Real) : Complex :=
  (2 : Complex) + T * Complex.I

@[simp] theorem centerTwoRectangleLower_re (T : Real) :
    (centerTwoRectangleLower T).re = -1 := by
  simp [centerTwoRectangleLower]

@[simp] theorem centerTwoRectangleLower_im (T : Real) :
    (centerTwoRectangleLower T).im = -T := by
  simp [centerTwoRectangleLower]

@[simp] theorem centerTwoRectangleUpper_re (T : Real) :
    (centerTwoRectangleUpper T).re = 2 := by
  simp [centerTwoRectangleUpper]

@[simp] theorem centerTwoRectangleUpper_im (T : Real) :
    (centerTwoRectangleUpper T).im = T := by
  simp [centerTwoRectangleUpper]

/-- Zero-freeness of the two horizontal sides of the wide rectangle. -/
def centerTwoHeightBoundaryAvoidsZeros (T : Real) : Prop :=
  (∀ x ∈ Icc (-1 : Real) 2,
    completedRiemannXi (verticalPoint x (-T)) ≠ 0) ∧
  ∀ x ∈ Icc (-1 : Real) 2,
    completedRiemannXi (verticalPoint x T) ≠ 0

theorem standardRectangle_centerTwoRectangle {T : Real} (hT : 0 < T) :
    standardRectangle (centerTwoRectangleLower T)
      (centerTwoRectangleUpper T) := by
  constructor
  · simpa using (show (-1 : Real) < 2 by norm_num)
  · simpa using (show -T < T by linarith)

/-- The selected tubes give the complete wide horizontal guard. -/
theorem DyadicCenterTwoHorizontalData.centerTwoHeightBoundaryAvoidsZeros
    {n : Nat} (H : DyadicCenterTwoHorizontalData n) :
    centerTwoHeightBoundaryAvoidsZeros H.height := by
  constructor
  · intro x _
    exact H.lower_tube x _
      (Metric.mem_ball_self (dyadicXiHeightTubeRadius_pos n))
  · intro x _
    exact H.upper_tube x _
      (Metric.mem_ball_self (dyadicXiHeightTubeRadius_pos n))

/-- Horizontal tube guards plus the known critical-strip location of xi zeros
exclude zeros from all four sides of the wide rectangle. -/
theorem xiRectangleBoundaryAvoidsZeros_centerTwoRectangle
    (T : Real) (hheight : centerTwoHeightBoundaryAvoidsZeros T) :
    xiRectangleBoundaryAvoidsZeros
      (centerTwoRectangleLower T) (centerTwoRectangleUpper T) := by
  constructor
  · intro x hx
    have hx' : x ∈ Icc (-1 : Real) 2 := by
      simpa only [centerTwoRectangleLower_re, centerTwoRectangleUpper_re,
        uIcc_of_le (by norm_num : (-1 : Real) ≤ 2)] using hx
    simpa only [centerTwoRectangleLower_im, verticalPoint] using
      hheight.1 x hx'
  constructor
  · intro x hx
    have hx' : x ∈ Icc (-1 : Real) 2 := by
      simpa only [centerTwoRectangleLower_re, centerTwoRectangleUpper_re,
        uIcc_of_le (by norm_num : (-1 : Real) ≤ 2)] using hx
    simpa only [centerTwoRectangleUpper_im, verticalPoint] using
      hheight.2 x hx'
  constructor
  · intro y _ hzero
    have hsource := sourceNontrivialZero_of_completedRiemannXi_eq_zero hzero
    have : (2 : Real) < 1 := by
      simpa [centerTwoRectangleUpper] using
        sourceNontrivialZero_re_lt_one hsource
    norm_num at this
  · intro y _ hzero
    have hsource := sourceNontrivialZero_of_completedRiemannXi_eq_zero hzero
    have : (0 : Real) < -1 := by
      simpa [centerTwoRectangleLower] using
        sourceNontrivialZero_zero_lt_re hsource
    norm_num at this

/-- The complete wide rectangle lies strictly inside the center-`2` factor
ball selected at the same dyadic scale. -/
theorem DyadicCenterTwoHorizontalData.centerTwoRectangle_subset_factorBall
    {n : Nat} (H : DyadicCenterTwoHorizontalData n) :
    Complex.Rectangle (centerTwoRectangleLower H.height)
        (centerTwoRectangleUpper H.height) ⊆
      Metric.ball (2 : Complex) (dyadicCofactorFactorRadius n) := by
  intro z hz
  have hzcoords : z.re ∈ Icc (-1 : Real) 2 ∧
      z.im ∈ Icc (-H.height) H.height := by
    rw [Complex.Rectangle, Complex.mem_reProdIm] at hz
    constructor
    · simpa only [centerTwoRectangleLower_re, centerTwoRectangleUpper_re,
        uIcc_of_le (by norm_num : (-1 : Real) ≤ 2)] using hz.1
    · simpa only [centerTwoRectangleLower_im, centerTwoRectangleUpper_im,
        uIcc_of_le (by linarith [H.height_pos] : -H.height ≤ H.height)] using hz.2
  have hre : |z.re - 2| ≤ 3 := by
    rw [abs_le]
    constructor <;> linarith [hzcoords.1.1, hzcoords.1.2]
  have him : |z.im| ≤ H.height := abs_le.mpr hzcoords.2
  have hnorm := Complex.norm_le_abs_re_add_abs_im (z - (2 : Complex))
  rw [Metric.mem_ball, dist_eq_norm]
  calc
    ‖z - (2 : Complex)‖ ≤ |z.re - 2| + |z.im| := by
      simpa using hnorm
    _ ≤ 3 + H.height := add_le_add hre him
    _ < dyadicCofactorFactorRadius n := by
      unfold dyadicCofactorFactorRadius
      linarith [H.height_upper]

/-- A source zero strictly inside the wide rectangle belongs to the standard
closed symmetric-height truncation. -/
theorem mem_finiteHeightZeros_of_strictlyInsideRectangle_centerTwo
    (T : Real) (rho : sourceNontrivialZeroSet)
    (hinside : strictlyInsideRectangle
      (centerTwoRectangleLower T) (centerTwoRectangleUpper T) rho.1) :
    rho ∈ finiteHeightZeros T := by
  rw [mem_finiteHeightZeros_iff]
  apply abs_le.mpr
  constructor
  · simpa using hinside.2.2.1.le
  · simpa using hinside.2.2.2.le

/-- Every source zero strictly below a guarded height is interior to the wide
rectangle; the real-coordinate inequalities use the stronger known strip
`0 < Re(rho) < 1`. -/
theorem strictlyInsideRectangle_centerTwo_of_abs_im_lt
    {T : Real} (rho : sourceNontrivialZeroSet) (hheight : |rho.1.im| < T) :
    strictlyInsideRectangle
      (centerTwoRectangleLower T) (centerTwoRectangleUpper T) rho.1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using (show (-1 : Real) < rho.1.re by
      linarith [sourceNontrivialZero_zero_lt_re rho.2])
  · simpa using (show rho.1.re < (2 : Real) by
      linarith [sourceNontrivialZero_re_lt_one rho.2])
  · simpa using (abs_lt.mp hheight).1
  · simpa using (abs_lt.mp hheight).2

/-- Filtering one factor's divisor support by the wide rectangle gives
exactly the usual finite-height zero family. -/
theorem xiClosedBallSourceZerosInsideCenterTwoRectangle_eq_finiteHeightZeros
    {c : Complex} {R T : Real}
    (hT : 0 < T)
    (hrectangle : Complex.Rectangle (centerTwoRectangleLower T)
      (centerTwoRectangleUpper T) ⊆ Metric.ball c |R|)
    (hheight : xiHeightBoundaryAvoidsZeros T) :
    xiClosedBallSourceZerosInsideRectangle c R
      (centerTwoRectangleLower T) (centerTwoRectangleUpper T) =
      finiteHeightZeros T := by
  apply Finset.ext
  intro rho
  constructor
  · intro hrho
    exact mem_finiteHeightZeros_of_strictlyInsideRectangle_centerTwo T rho
      ((mem_xiClosedBallSourceZerosInsideRectangle_iff c R
        (centerTwoRectangleLower T) (centerTwoRectangleUpper T) rho).mp hrho).2
  · intro hrho
    apply (mem_xiClosedBallSourceZerosInsideRectangle_iff c R
      (centerTwoRectangleLower T) (centerTwoRectangleUpper T) rho).mpr
    have hinside := strictlyInsideRectangle_centerTwo_of_abs_im_lt rho
      (abs_im_lt_of_mem_finiteHeightZeros_of_xiHeightBoundaryAvoidsZeros
        hheight rho hrho)
    refine ⟨?_, hinside⟩
    have hball : rho.1 ∈ Metric.ball c |R| := by
      apply hrectangle
      rw [Complex.Rectangle, Complex.mem_reProdIm]
      constructor
      · rw [uIcc_of_le (standardRectangle_centerTwoRectangle hT).1.le]
        exact ⟨hinside.1.le, hinside.2.1.le⟩
      · rw [uIcc_of_le (standardRectangle_centerTwoRectangle hT).2.le]
        exact ⟨hinside.2.2.1.le, hinside.2.2.2.le⟩
    have hsupport : rho.1 ∈ (xiClosedBallDivisor c R).support :=
      (xiClosedBallDivisor_mem_support_iff c R
        (Metric.ball_subset_closedBall hball)).mpr
        (completedRiemannXi_eq_zero_of_sourceNontrivialZero rho.2)
    exact (xiClosedBallDivisor_support_finite c R).mem_toFinset.mpr hsupport

/-- The same center-`2` owner reads its wide rectangle as the exact finite
source spectral sum. -/
theorem DyadicCenterTwoHorizontalData.centerTwoRectangleBoundaryIntegral_readout
    {n : Nat} (H : DyadicCenterTwoHorizontalData n) (F : CompactLogTest) :
    xiRectangleBoundaryIntegral (xiContourKernel F)
      (centerTwoRectangleLower H.height)
      (centerTwoRectangleUpper H.height) =
      -(2 * (Real.pi : Complex) * Complex.I *
        finiteSpectralSum F H.height) := by
  have hRabs : |dyadicCofactorFactorRadius n| =
      dyadicCofactorFactorRadius n :=
    abs_of_pos (dyadicCofactorFactorRadius_pos n)
  have hrectangle : Complex.Rectangle (centerTwoRectangleLower H.height)
      (centerTwoRectangleUpper H.height) ⊆
      Metric.ball (2 : Complex) |dyadicCofactorFactorRadius n| := by
    simpa only [hRabs] using
      DyadicCenterTwoHorizontalData.centerTwoRectangle_subset_factorBall H
  rw [xiRectangleBoundaryIntegral_xiContourKernel_eq_neg_finiteSourceSpectralSum_of_factor_support
    F (by simpa only [hRabs] using H.factorData.cofactor_analytic)
      (by
        intro q
        exact H.factorData.cofactor_nonzero
          ⟨q.1, by simpa only [hRabs] using q.2⟩)
      (by simpa only [hRabs] using H.factorData.factorization)
      hrectangle (standardRectangle_centerTwoRectangle H.height_pos)
      (xiRectangleBoundaryAvoidsZeros_centerTwoRectangle H.height
        (DyadicCenterTwoHorizontalData.centerTwoHeightBoundaryAvoidsZeros H))]
  rw [xiClosedBallSourceZerosInsideCenterTwoRectangle_eq_finiteHeightZeros
    H.height_pos hrectangle H.boundary_avoids]
  rfl

end
end C1XiCenterTwoFiniteRectangle
end Source
end ConnesWeilRH
