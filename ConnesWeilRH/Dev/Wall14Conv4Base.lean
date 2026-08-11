import ConnesWeilRH.Dev.WallBridge
import ConnesWeilRH.Dev.Wall14PlateauExplicitF
import ConnesWeilRH.Dev.Wall14PlateauFDeriv

/-!
# Wall14Conv4Base - 4-fold convolution square: real, even, integral

conv4B := bumpPlateauTest.convolutionSquare (the 2-fold real bump, since the
explicit plateau test is real-even, so bumpPlateauTest.involution = id).  Its real
convolution square conv4F := (conv4B.convolutionSquare.test).re equals
integral t, bumpF t * bumpF (y - t); real-even, nonnegative, bounded by A4 := conv4F 0.
Feeds the 4-fold hI bound.  RH NOT claimed.
-/

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace Wall14Conv4

open MeasureTheory
open scoped Topology ComplexConjugate
open Filter Set
open Wall14Plateau
open ConnesWeilRH.Source.CCM25Concrete.CompactLogConvolution

noncomputable abbrev conv4B : CompactLogTest := bumpPlateauTest.convolutionSquare

noncomputable def conv4F (y : Real) : Real := (conv4B.convolutionSquare.test y).re

theorem conv4B_test_eq_bumpF (y : Real) :
    conv4B.test y = (bumpF y : Complex) := by
  unfold conv4B
  change (bumpPlateauOwner.convolutionSquare.test y) = (bumpF y : Complex)
  rw [bumpOwnerConvSquare_eq_real]
  congr 1
  symm
  exact bumpF_eq_conv y

theorem conv4B_test_re_bumpF (y : Real) : (conv4B.test y).re = bumpF y := by
  rw [conv4B_test_eq_bumpF]
  simp

theorem conv4B_test_im_zero (y : Real) : (conv4B.test y).im = 0 := by
  rw [conv4B_test_eq_bumpF]
  simp

theorem conv4B_test_even (y : Real) : conv4B.test (-y) = conv4B.test y := by
  rw [conv4B_test_eq_bumpF, conv4B_test_eq_bumpF]
  simp [bumpF_symm]

theorem conv4B_involution_self (y : Real) : conv4B.involution.test y = conv4B.test y := by
  calc
    conv4B.involution.test y = star (conv4B.test (-y)) := by rw [CompactLogTest.involution_apply]
    _ = star (conv4B.test y) := by rw [conv4B_test_even]
    _ = (bumpF y : Complex) := by
        rw [conv4B_test_eq_bumpF]
        simp
    _ = conv4B.test y := (conv4B_test_eq_bumpF y).symm

theorem conv4B_test_mul (y t : Real) :
    conv4B.test t * conv4B.test (y - t) = (bumpF t * bumpF (y - t) : Complex) := by
  rw [conv4B_test_eq_bumpF, conv4B_test_eq_bumpF]


/-- The 4-fold convolution-square integrand collapses to the plain real-even self-convolution. -/
theorem conv4B_convolutionSquare_reduce (y : Real) :
    conv4B.convolutionSquare.test y =
      ∫ (t : Real), conv4B.test t * conv4B.test (y - t) := by
  rw [CompactLogTest.convolutionSquare_apply]
  apply integral_congr_ae
  filter_upwards with t
  have hstar : star (conv4B.test (-t)) = conv4B.test t := by
    rw [conv4B_test_even]
    rw [conv4B_test_eq_bumpF]
    simp
  rw [hstar]

/-- Real-even: the 4-fold convolution square viewed as a complex integral of bumpF.bumpF. -/
theorem conv4B_convolutionSquare_eq_real_conv (y : Real) :
    conv4B.convolutionSquare.test y =
      ((∫ t : Real, bumpF t * bumpF (y - t) : Real) : Complex) := by
  rw [conv4B_convolutionSquare_reduce]
  have hpoint : (fun t : Real => conv4B.test t * conv4B.test (y - t)) =
      fun t : Real => (bumpF t * bumpF (y - t) : Complex) := by
    funext t
    exact conv4B_test_mul y t
  rw [hpoint]
  simpa using (integral_ofReal (𝕜 := Complex)
    (f := fun t : Real => bumpF t * bumpF (y - t)) (μ := volume))

/-- conv4F y = the real integral of bumpF.bumpF. -/
theorem conv4F_eq_integral_small (y : Real) :
    conv4F y = ∫ (t : Real), bumpF t * bumpF (y - t) := by
  unfold conv4F
  rw [conv4B_convolutionSquare_eq_real_conv]
  simp


noncomputable abbrev A4 : Real := conv4F 0

/-- conv4F is even. -/
theorem conv4F_even (y : Real) : conv4F (-y) = conv4F y := by
  unfold conv4F
  rw [CompactLogTest.convolutionSquare_neg]
  simp

/-- The total mass (conv4F at 0) is nonnegative. -/
theorem A4_nonneg : 0 <= A4 := by
  unfold A4 conv4F
  exact CompactLogTest.convolutionSquare_zero_re_nonnegative conv4B

/-- conv4F is pointwise nonnegative. -/
theorem conv4F_nonneg (y : Real) : 0 <= conv4F y := by
  rw [conv4F_eq_integral_small]
  exact integral_nonneg (fun t : Real => mul_nonneg (bumpF_nonneg t) (bumpF_nonneg (y - t)))

/-- Compact-root support: conv4F vanishes once |y| is not below 4. -/
theorem conv4F_eq_zero_of_four_le_abs (y : Real) (hy : 4 <= |y|) : conv4F y = 0 := by
  rw [conv4F_eq_integral_small]
  apply integral_eq_zero_of_ae
  filter_upwards with t
  by_cases ht : |t| < 2
  · have hb : 2 <= |y - t| := by
      have hin : |y| - |t| <= |y - t| := by
        exact abs_sub_abs_le_abs_sub y t
      linarith
    rw [bumpF_eq_zero_of_two_le_abs (y - t) hb]
    simp
  · have ht2 : (2 : Real) <= |t| := le_of_not_gt ht
    rw [bumpF_eq_zero_of_two_le_abs t ht2]
    simp

/-- Rewrites the e^(y/2) factor into the two factors at t and y-t (gateway to the crux bound). -/
theorem conv4F_mul_exp_half (y : Real) :
    Real.exp (y / 2) * conv4F y =
      (∫ t : Real, (Real.exp (t / 2) * bumpF t) * (Real.exp ((y - t) / 2) * bumpF (y - t))) := by
  rw [conv4F_eq_integral_small]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  have hsplit : y / 2 = t / 2 + (y - t) / 2 := by ring
  rw [hsplit, Real.exp_add]
  ring

end Wall14Conv4
end Dev
end Source
end ConnesWeilRH

