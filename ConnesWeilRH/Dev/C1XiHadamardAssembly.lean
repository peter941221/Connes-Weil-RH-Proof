import ConnesWeilRH.Dev.C1XiGlobalDifference
import Mathlib.Analysis.Complex.Liouville

/-!
# C1XiHadamardAssembly - H-A4/H-A5 constant assembly

The global extension is entire, but an `O(R)` or `O(R log R)` estimate is only
an affine-growth statement.  It does not imply constancy: `G z = z` is the
basic counterexample.  This module therefore keeps the missing mathematical
inputs explicit.

* a genuinely bounded global extension is consumed by Liouville;
* an affine representation is consumed together with an explicit zero-slope
  proof; and
* either route yields the H-A5 constant-difference identity on the ordinary
  xi zero-free domain.

Neither the affine representation nor its slope-zero proof is produced here.
They remain the load-bearing global Hadamard/minimum-modulus analysis.
-/

namespace ConnesWeilRH
namespace Source
namespace C1XiHadamardAssembly

open C1XiGlobalDifference
open C1XiGlobalWeightedZeroSum
open CC20ZetaCounting
open Bornology

noncomputable section

/-- H-A4 data: an explicit affine representation of the global entire
difference.  A linear-growth estimate alone does not construct this data. -/
structure XiGlobalDifferenceAffineContract where
  slope : Complex
  intercept : Complex
  affine_formula : ∀ z : Complex,
    xiGlobalWeightedDifference z = slope * z + intercept

/-- H-A4b/H-A5 consumer: affine growth plus a separately proved zero slope
collapses the global extension to one constant. -/
theorem xiGlobalWeightedDifference_eq_constant_of_affine_and_slope_zero
    (H : XiGlobalDifferenceAffineContract) (hslope : H.slope = 0) :
    ∀ z : Complex, xiGlobalWeightedDifference z = H.intercept := by
  intro z
  rw [H.affine_formula z, hslope, zero_mul, zero_add]

/-- A bounded global entire difference is constant by Liouville's theorem. -/
theorem xiGlobalWeightedDifference_exists_const_of_bounded
    (hbounded : IsBounded (Set.range xiGlobalWeightedDifference)) :
    ∃ c : Complex, ∀ z : Complex,
      xiGlobalWeightedDifference z = c := by
  have hdiff : Differentiable Complex xiGlobalWeightedDifference :=
    (Complex.analyticOnNhd_univ_iff_differentiable).mp
      xiGlobalWeightedDifference_analyticOnNhd
  exact hdiff.exists_const_forall_eq_of_bounded hbounded

/-- H-A5 readback from the bounded route: the raw logarithmic derivative
difference equals one constant at every xi-nonzero point. -/
theorem xiLogDerivWeightedDifference_exists_const_of_bounded
    (hbounded : IsBounded (Set.range xiGlobalWeightedDifference)) :
    ∃ c : Complex, ∀ s : Complex, completedRiemannXi s ≠ 0 →
      xiLogDerivWeightedDifferenceRaw s = c := by
  obtain ⟨c, hc⟩ := xiGlobalWeightedDifference_exists_const_of_bounded hbounded
  refine ⟨c, ?_⟩
  intro s hs
  rw [← xiGlobalWeightedDifference_eq_raw hs]
  exact hc s

/-- H-A5 readback from the affine+slope-zero route. -/
theorem xiLogDerivWeightedDifference_eq_constant_of_affine_and_slope_zero
    (H : XiGlobalDifferenceAffineContract) (hslope : H.slope = 0)
    {s : Complex} (hs : completedRiemannXi s ≠ 0) :
    xiLogDerivWeightedDifferenceRaw s = H.intercept := by
  rw [← xiGlobalWeightedDifference_eq_raw hs]
  exact xiGlobalWeightedDifference_eq_constant_of_affine_and_slope_zero H hslope s

/-- The H1 constant-difference identity on two ordinary points, obtained from
the bounded Liouville route. -/
theorem xi_logDeriv_weightedRegularizedSum_constant_diff_of_bounded
    (hbounded : IsBounded (Set.range xiGlobalWeightedDifference))
    {s s0 : Complex} (hs : completedRiemannXi s ≠ 0)
    (hs0 : completedRiemannXi s0 ≠ 0) :
    logDeriv completedRiemannXi s - weightedRegularizedZeroSum s =
      logDeriv completedRiemannXi s0 - weightedRegularizedZeroSum s0 := by
  obtain ⟨c, hc⟩ := xiGlobalWeightedDifference_exists_const_of_bounded hbounded
  change xiLogDerivWeightedDifferenceRaw s =
    xiLogDerivWeightedDifferenceRaw s0
  rw [← xiGlobalWeightedDifference_eq_raw hs,
    ← xiGlobalWeightedDifference_eq_raw hs0, hc, hc]

/-- The H1 constant-difference identity on two ordinary points, obtained from
the affine+slope-zero route. -/
theorem xi_logDeriv_weightedRegularizedSum_constant_diff_of_affine_and_slope_zero
    (H : XiGlobalDifferenceAffineContract) (hslope : H.slope = 0)
    {s s0 : Complex} (hs : completedRiemannXi s ≠ 0)
    (hs0 : completedRiemannXi s0 ≠ 0) :
    logDeriv completedRiemannXi s - weightedRegularizedZeroSum s =
      logDeriv completedRiemannXi s0 - weightedRegularizedZeroSum s0 := by
  change xiLogDerivWeightedDifferenceRaw s =
    xiLogDerivWeightedDifferenceRaw s0
  rw [← xiGlobalWeightedDifference_eq_raw hs,
    ← xiGlobalWeightedDifference_eq_raw hs0]
  rw [xiGlobalWeightedDifference_eq_constant_of_affine_and_slope_zero H hslope,
    xiGlobalWeightedDifference_eq_constant_of_affine_and_slope_zero H hslope]

end
end C1XiHadamardAssembly
end Source
end ConnesWeilRH
