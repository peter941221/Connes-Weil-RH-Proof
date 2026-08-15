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

/-- A global linear-growth input for the entire H-A1 difference.  The
constants are kept nonnegative so the Cauchy estimate can use them as real
majorants without introducing hidden sign assumptions. -/
structure XiGlobalDifferenceLinearGrowthContract where
  linear_constant : Real
  linear_constant_nonneg : 0 ≤ linear_constant
  additive_constant : Real
  additive_constant_nonneg : 0 ≤ additive_constant
  global_bound : ∀ z : Complex,
    ‖xiGlobalWeightedDifference z‖ ≤
      linear_constant * ‖z‖ + additive_constant

/-- H-A4 data: an explicit affine representation of the global entire
difference.  A linear-growth estimate alone does not construct this data. -/
structure XiGlobalDifferenceAffineContract where
  slope : Complex
  intercept : Complex
  affine_formula : ∀ z : Complex,
    xiGlobalWeightedDifference z = slope * z + intercept

/-- An entire function with a global linear bound has vanishing second
derivative.  The proof is the quantitative Cauchy estimate on a circle
centered at an arbitrary point, followed by a radius choice making the
resulting `O(1 / R)` bound smaller than any positive epsilon. -/
theorem iteratedDeriv_two_eq_zero_of_analyticOnNhd_of_linear_growth
    {G : Complex → Complex}
    (hG : AnalyticOnNhd Complex G Set.univ)
    {A B : Real} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hbound : ∀ z : Complex, ‖G z‖ ≤ A * ‖z‖ + B) :
    ∀ c : Complex, iteratedDeriv 2 G c = 0 := by
  have hdiff : Differentiable Complex G :=
    (Complex.analyticOnNhd_univ_iff_differentiable).mp hG
  intro c
  refine norm_le_zero_iff.1 (le_of_forall_gt_imp_ge_of_dense fun ε hε => ?_)
  let K : Real := 2 * (A * (‖c‖ + 1) + B)
  let R : Real := max 1 (K / ε + 1)
  have hRone : 1 ≤ R := le_max_left _ _
  have hRlarge : K / ε + 1 ≤ R := le_max_right _ _
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one hRone
  have hK_eq : ε * (K / ε + 1) = K + ε := by
    field_simp [ne_of_gt hε]
  have hmul : ε * (K / ε + 1) ≤ ε * R :=
    mul_le_mul_of_nonneg_left hRlarge hε.le
  have hK_lt : K < ε * R := by
    rw [hK_eq] at hmul
    linarith
  have hC : ∀ z ∈ Metric.sphere c R,
      ‖G z‖ ≤ A * (‖c‖ + R) + B := by
    intro z hz
    have hzdist : ‖z - c‖ = R := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hz
    have hznorm : ‖z‖ ≤ ‖c‖ + R := by
      calc
        ‖z‖ = ‖(z - c) + c‖ := by rw [sub_add_cancel]
        _ ≤ ‖z - c‖ + ‖c‖ := norm_add_le _ _
        _ = ‖c‖ + R := by rw [hzdist]; ring
    exact (hbound z).trans
      (add_le_add (mul_le_mul_of_nonneg_left hznorm hA) le_rfl)
  have hCauchy :=
    Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
      (f := G) (c := c) (R := R)
      (C := A * (‖c‖ + R) + B) 2 hR hdiff.diffContOnCl hC
  have hCauchy' :
      ‖iteratedDeriv 2 G c‖ ≤
        2 * (A * (‖c‖ + R) + B) / R ^ 2 := by
    simpa using hCauchy
  have hcnonneg : 0 ≤ ‖c‖ := norm_nonneg c
  have hcmul : ‖c‖ ≤ ‖c‖ * R := by
    simpa only [mul_one] using
      (mul_le_mul_of_nonneg_left hRone hcnonneg)
  have hsum : ‖c‖ + R ≤ (‖c‖ + 1) * R := by
    calc
      ‖c‖ + R ≤ ‖c‖ * R + R := add_le_add hcmul le_rfl
      _ = (‖c‖ + 1) * R := by ring
  have hAterm : A * (‖c‖ + R) ≤ A * ((‖c‖ + 1) * R) :=
    mul_le_mul_of_nonneg_left hsum hA
  have hBmul : B ≤ B * R := by
    simpa only [mul_one] using
      (mul_le_mul_of_nonneg_left hRone hB)
  have hnumerator :
      2 * (A * (‖c‖ + R) + B) ≤ K * R := by
    calc
      2 * (A * (‖c‖ + R) + B) ≤
          2 * (A * ((‖c‖ + 1) * R) + B * R) := by
            exact mul_le_mul_of_nonneg_left
              (add_le_add hAterm hBmul) (by norm_num)
      _ = K * R := by
        dsimp only [K]
        ring
  have hfirst :
      2 * (A * (‖c‖ + R) + B) / R ≤ K := by
    exact (div_le_iff₀ hR).2 hnumerator
  have hquot :
      2 * (A * (‖c‖ + R) + B) / R ^ 2 ≤ K / R := by
    calc
      2 * (A * (‖c‖ + R) + B) / R ^ 2 =
          (2 * (A * (‖c‖ + R) + B) / R) / R := by
            field_simp [ne_of_gt hR]
      _ ≤ K / R := div_le_div_of_nonneg_right hfirst hR.le
  have hKR : K / R < ε := (div_lt_iff₀ hR).2 hK_lt
  exact (hCauchy'.trans (hquot.trans (le_of_lt hKR)))

/-- An entire function with a global linear bound is affine. -/
theorem exists_affine_of_analyticOnNhd_of_linear_growth
    {G : Complex → Complex}
    (hG : AnalyticOnNhd Complex G Set.univ)
    {A B : Real} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hbound : ∀ z : Complex, ‖G z‖ ≤ A * ‖z‖ + B) :
    ∃ slope intercept : Complex, ∀ z : Complex,
      G z = slope * z + intercept := by
  have hdiff : Differentiable Complex G :=
    (Complex.analyticOnNhd_univ_iff_differentiable).mp hG
  have hderiv : Differentiable Complex (deriv G) :=
    (Complex.analyticOnNhd_univ_iff_differentiable).mp hG.deriv
  have hsecond :=
    iteratedDeriv_two_eq_zero_of_analyticOnNhd_of_linear_growth hG hA hB hbound
  let slope : Complex := deriv G 0
  have hslope : ∀ z : Complex, deriv G z = slope := by
    intro z
    dsimp only [slope]
    exact is_const_of_deriv_eq_zero hderiv (by
      intro w
      have hw := hsecond w
      simpa only [iteratedDeriv_succ, iteratedDeriv_one] using hw) z 0
  let F : Complex → Complex := fun z => G z - slope * z
  have hFdiff : Differentiable Complex F := by
    dsimp only [F]
    exact hdiff.sub (differentiable_id.const_mul slope)
  have hFzero : ∀ z : Complex, deriv F z = 0 := by
    intro z
    dsimp only [F]
    have hlinear : HasDerivAt (fun y : Complex => slope * y) slope z :=
      hasDerivAt_const_mul slope
    have hsub := (hdiff z).hasDerivAt.sub hlinear
    calc
      deriv (fun y : Complex => G y - slope * y) z =
          deriv G z - slope := hsub.deriv
      _ = 0 := by rw [hslope z]; ring
  refine ⟨slope, G 0, ?_⟩
  intro z
  have hz := is_const_of_deriv_eq_zero hFdiff hFzero z 0
  dsimp only [F] at hz
  calc
    G z = (G z - slope * z) + slope * z := by ring
    _ = (G 0 - slope * 0) + slope * z := by rw [hz]
    _ = slope * z + G 0 := by ring

/-- The H-A4 affine-growth consumer for the assembled xi difference. -/
noncomputable def xiGlobalWeightedDifference_affine_of_linear_growth
    (H : XiGlobalDifferenceLinearGrowthContract) :
    XiGlobalDifferenceAffineContract := by
  let hAffine :=
    exists_affine_of_analyticOnNhd_of_linear_growth
      xiGlobalWeightedDifference_analyticOnNhd
      H.linear_constant_nonneg H.additive_constant_nonneg H.global_bound
  let slope : Complex := Classical.choose hAffine
  let hIntercept : ∃ intercept : Complex, ∀ z : Complex,
      xiGlobalWeightedDifference z = slope * z + intercept := by
    simpa only [slope] using Classical.choose_spec hAffine
  let intercept : Complex := Classical.choose hIntercept
  have hformula : ∀ z : Complex,
      xiGlobalWeightedDifference z = slope * z + intercept :=
    Classical.choose_spec hIntercept
  exact { slope := slope, intercept := intercept, affine_formula := hformula }

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
