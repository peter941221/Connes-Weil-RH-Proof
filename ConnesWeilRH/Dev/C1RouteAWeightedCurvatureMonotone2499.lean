import ConnesWeilRH.Dev.C1RouteAOwnerWeightedFamily2488

/-! Record 2499: monotonicity door for replacing exact exponential bounds.

The exponential split supplies an upper bound for the zero-order bump term.
This lemma packages the monotonic propagation through the three inputs of
`weightedCurvature2348`, so the future cell proof need only establish three
nonnegative rational-factor inequalities.
-/

namespace ConnesWeilRH.Dev

theorem weightedCurvature2348_mono_bounds2499
    (sigma radius zeroLower zeroUpper firstLower firstUpper secondLower secondUpper : ℝ)
    (hzero : zeroLower ≤ zeroUpper)
    (hfirst : firstLower ≤ firstUpper)
    (hsecond : secondLower ≤ secondUpper) :
    weightedCurvature2348 sigma radius zeroLower firstLower secondLower ≤
      weightedCurvature2348 sigma radius zeroUpper firstUpper secondUpper := by
  unfold weightedCurvature2348
  have hfirst_factor : 0 ≤ 2 * |sigma| := by positivity
  have hsecond_term : secondLower + 2 * |sigma| * firstLower ≤
      secondUpper + 2 * |sigma| * firstUpper := by
    gcongr
  have hzero_factor : 0 ≤ sigma ^ 2 := sq_nonneg sigma
  have hsum : secondLower + 2 * |sigma| * firstLower + sigma ^ 2 * zeroLower ≤
      secondUpper + 2 * |sigma| * firstUpper + sigma ^ 2 * zeroUpper := by
    gcongr
  exact mul_le_mul_of_nonneg_left hsum (Real.exp_nonneg _)

end ConnesWeilRH.Dev
