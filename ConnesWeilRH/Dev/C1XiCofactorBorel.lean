import ConnesWeilRH.Dev.C1XiAnalyticLog
import ConnesWeilRH.Dev.C1XiQuantitativePrincipalBound
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.Liouville

/-!
# C1XiCofactorBorel - quantitative center-two cofactor control

This module constructs the missing finite-factor cofactor estimate on dyadic
horizontal lines.  The factorization, its divisor mass, the analytic logarithm,
and every later derivative estimate remain tied to one closed ball centered at
the nonzero Jensen point `2`.

The first layer below is purely geometric.  It selects an outer circle with an
explicit separation from every divisor radius and bounds the exact divisor
mass by the existing Jensen multiplicity estimate.
-/

namespace ConnesWeilRH
namespace Source
namespace C1XiCofactorBorel

open Set
open Filter
open CC20ZetaCounting
open CC20YoshidaNearZeros
open C1SpectralWeil
open C1SpectralSummability
open C1XiFiniteFactor
open C1XiFiniteSupportReindex
open C1XiQuantitativeHeight
open C1XiQuantitativePrincipalBound
open C1XiVerticalFunctional
open scoped BigOperators Topology

noncomputable section

/-- The base height used by the `n`th horizontal contour. -/
noncomputable def dyadicCofactorBase (n : Nat) : Real :=
  (2 : Real) ^ (n + 2)

/-- Radius of the center-`2` finite-factor owner at dyadic scale `n`. -/
noncomputable def dyadicCofactorFactorRadius (n : Nat) : Real :=
  dyadicCofactorBase n + 5

/-- Jensen multiplicity budget for the center-`2` factor owner. -/
noncomputable def dyadicCofactorMassBound (n : Nat) : Real :=
  spectralMultiplicityConstant * (3 : Real) ^ (n + 2)

/-- Radial grid separation used for the selected outer circle. -/
noncomputable def dyadicCofactorRadialGap (n : Nat) : Real :=
  1 / (4 * (dyadicCofactorMassBound n + 2))

/-- The forbidden center-`2` radii in the full height window containing the
factor divisor support. -/
noncomputable def centerTwoForbiddenRadii (n : Nat) : Finset Real :=
  (finiteHeightZeros (dyadicCofactorFactorRadius n)).image
    (fun rho => ‖rho.1 - (2 : Complex)‖)

/-- The real divisor mass is the source analytic-multiplicity mass of the
same finite-factor owner. -/
theorem xiClosedBallDivisorMass_eq_sourceMultiplicitySum
    (c : Complex) (R : Real) :
    xiClosedBallDivisorMass c R =
      ∑ rho ∈ xiClosedBallSourceZeros c R, (xiMultiplicity rho : Real) := by
  unfold xiClosedBallDivisorMass
  rw [← sum_xiClosedBallSourceZeros_eq_sum_support c R
    (fun u => (xiClosedBallDivisor c R u : Real))]
  apply Finset.sum_congr rfl
  intro rho hrho
  have hsupp : rho.1 ∈ (xiClosedBallDivisor c R).support :=
    (xiClosedBallDivisor_support_finite c R).mem_toFinset.mp
      ((mem_xiClosedBallSourceZeros_iff c R rho).mp hrho)
  have hball : rho.1 ∈ Metric.closedBall c |R| :=
    (xiClosedBallDivisor_mem_closedBall_and_xi_eq_zero_of_mem_support
      c R hsupp).1
  have hmult : (xiMultiplicity rho : Int) =
      xiClosedBallDivisor c R rho.1 := by
    simpa only [xiClosedBallDivisor] using
      xiMultiplicity_cast_eq_divisor_of_mem_closedBall rho hball
  exact_mod_cast hmult.symm

/-- A source zero owned by the center-`2`, radius-`R` factor lies in the
symmetric height window `R`. -/
theorem xiClosedBallSourceZeros_two_subset_finiteHeightZeros
    (R : Real) (hR : 0 <= R) :
    xiClosedBallSourceZeros (2 : Complex) R ⊆ finiteHeightZeros R := by
  intro rho hrho
  rw [mem_finiteHeightZeros_iff]
  have hsupp : rho.1 ∈
      (xiClosedBallDivisor (2 : Complex) R).support :=
    (xiClosedBallDivisor_support_finite (2 : Complex) R).mem_toFinset.mp
      ((mem_xiClosedBallSourceZeros_iff (2 : Complex) R rho).mp hrho)
  have hball : rho.1 ∈ Metric.closedBall (2 : Complex) |R| :=
    (xiClosedBallDivisor_mem_closedBall_and_xi_eq_zero_of_mem_support
      (2 : Complex) R hsupp).1
  have him : |rho.1.im| <= ‖rho.1 - (2 : Complex)‖ := by
    simpa using Complex.abs_im_le_norm (rho.1 - (2 : Complex))
  rw [Metric.mem_closedBall, dist_eq_norm, abs_of_nonneg hR] at hball
  exact him.trans hball

/-- The exact center-`2` divisor mass is bounded by the multiplicity in its
containing height window. -/
theorem xiClosedBallDivisorMass_two_le_finiteHeightMultiplicity
    (R : Real) (hR : 0 <= R) :
    xiClosedBallDivisorMass (2 : Complex) R <=
      (finiteHeightMultiplicity R : Real) := by
  rw [xiClosedBallDivisorMass_eq_sourceMultiplicitySum]
  calc
    (∑ rho ∈ xiClosedBallSourceZeros (2 : Complex) R,
        (xiMultiplicity rho : Real)) <=
        ∑ rho ∈ finiteHeightZeros R, (xiMultiplicity rho : Real) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
            (xiClosedBallSourceZeros_two_subset_finiteHeightZeros R hR)
          intro rho _ _
          exact Nat.cast_nonneg _
    _ = (finiteHeightMultiplicity R : Real) := by
      simp only [finiteHeightMultiplicity, Nat.cast_sum]

theorem dyadicCofactorBase_ge_four (n : Nat) :
    4 <= dyadicCofactorBase n := by
  unfold dyadicCofactorBase
  have hpow : (1 : Real) <= (2 : Real) ^ n := one_le_pow₀ (by norm_num)
  calc
    4 = 4 * 1 := by norm_num
    _ <= 4 * (2 : Real) ^ n := by gcongr
    _ = (2 : Real) ^ (n + 2) := by
      rw [pow_add]
      ring

theorem dyadicCofactorFactorRadius_pos (n : Nat) :
    0 < dyadicCofactorFactorRadius n := by
  unfold dyadicCofactorFactorRadius
  linarith [dyadicCofactorBase_ge_four n]

/-- The center-`2` factor ball fits in the next-next Jensen dyadic window. -/
theorem dyadicCofactorFactorRadius_le (n : Nat) :
    dyadicCofactorFactorRadius n <= (2 : Real) ^ (n + 4) := by
  have hbase := dyadicCofactorBase_ge_four n
  calc
    dyadicCofactorFactorRadius n = dyadicCofactorBase n + 5 := rfl
    _ <= 4 * dyadicCofactorBase n := by nlinarith
    _ = (2 : Real) ^ (n + 4) := by
      unfold dyadicCofactorBase
      rw [show n + 4 = (n + 2) + 2 by omega, pow_add]
      ring

/-- The exact divisor mass of the center-`2` factor owner is `O(3^n)`. -/
theorem xiClosedBallDivisorMass_two_dyadic_le (n : Nat) :
    xiClosedBallDivisorMass (2 : Complex) (dyadicCofactorFactorRadius n) <=
      dyadicCofactorMassBound n := by
  have hR : 0 <= dyadicCofactorFactorRadius n :=
    (dyadicCofactorFactorRadius_pos n).le
  have hmono := finiteHeightMultiplicity_mono
    (dyadicCofactorFactorRadius_le n)
  calc
    xiClosedBallDivisorMass (2 : Complex) (dyadicCofactorFactorRadius n) <=
        (finiteHeightMultiplicity (dyadicCofactorFactorRadius n) : Real) :=
      xiClosedBallDivisorMass_two_le_finiteHeightMultiplicity _ hR
    _ <= (finiteHeightMultiplicity ((2 : Real) ^ (n + 4)) : Real) := by
      exact_mod_cast hmono
    _ <= dyadicCofactorMassBound n := by
      simpa only [dyadicCofactorMassBound, show n + 4 = (n + 2) + 2 by omega] using
        finiteHeightMultiplicity_dyadic_le (n + 2)

/-- The number of forbidden radii is controlled by the same dyadic
multiplicity budget. -/
theorem centerTwoForbiddenRadii_card_le (n : Nat) :
    ((centerTwoForbiddenRadii n).card : Real) <=
      dyadicCofactorMassBound n := by
  have hcard : (centerTwoForbiddenRadii n).card <=
      finiteHeightMultiplicity (dyadicCofactorFactorRadius n) := by
    calc
      (centerTwoForbiddenRadii n).card <=
          (finiteHeightZeros (dyadicCofactorFactorRadius n)).card := by
        unfold centerTwoForbiddenRadii
        exact Finset.card_image_le
      _ <= finiteHeightMultiplicity (dyadicCofactorFactorRadius n) := by
        unfold finiteHeightMultiplicity
        rw [Finset.card_eq_sum_ones]
        apply Finset.sum_le_sum
        intro rho _
        exact Nat.succ_le_iff.mpr (xiMultiplicity_pos rho)
  calc
    ((centerTwoForbiddenRadii n).card : Real) <=
        (finiteHeightMultiplicity (dyadicCofactorFactorRadius n) : Real) := by
      exact_mod_cast hcard
    _ <= (finiteHeightMultiplicity ((2 : Real) ^ (n + 4)) : Real) := by
      exact_mod_cast finiteHeightMultiplicity_mono
        (dyadicCofactorFactorRadius_le n)
    _ <= dyadicCofactorMassBound n := by
      simpa only [dyadicCofactorMassBound, show n + 4 = (n + 2) + 2 by omega] using
        finiteHeightMultiplicity_dyadic_le (n + 2)

theorem dyadicCofactorMassBound_nonneg (n : Nat) :
    0 <= dyadicCofactorMassBound n := by
  unfold dyadicCofactorMassBound
  exact mul_nonneg spectralMultiplicityConstant_nonneg (by positivity)

theorem dyadicCofactorRadialGap_pos (n : Nat) :
    0 < dyadicCofactorRadialGap n := by
  unfold dyadicCofactorRadialGap
  have hmass := dyadicCofactorMassBound_nonneg n
  positivity

theorem dyadicCofactorRadialGap_le_gridGap (n : Nat) :
    dyadicCofactorRadialGap n <=
      gridGap (centerTwoForbiddenRadii n).card := by
  have hcard := centerTwoForbiddenRadii_card_le n
  have hdenom_pos : 0 < 4 * (((centerTwoForbiddenRadii n).card : Real) + 2) := by
    positivity
  have hdenom_le :
      4 * (((centerTwoForbiddenRadii n).card : Real) + 2) <=
        4 * (dyadicCofactorMassBound n + 2) := by
    nlinarith
  unfold dyadicCofactorRadialGap
  rw [gridGap_eq]
  norm_num only [Nat.cast_add, Nat.cast_ofNat]
  exact one_div_le_one_div_of_le hdenom_pos hdenom_le

/-- Select an outer circle in `(B_n + 3, B_n + 4)` that is explicitly
separated from every radius in the factor's full height window. -/
theorem exists_dyadic_centerTwo_outerRadius (n : Nat) :
    ∃ q : Real,
      dyadicCofactorBase n + 3 < q ∧
      q < dyadicCofactorBase n + 4 ∧
      q < dyadicCofactorFactorRadius n ∧
      ∀ rho ∈ finiteHeightZeros (dyadicCofactorFactorRadius n),
        dyadicCofactorRadialGap n <=
          |q - ‖rho.1 - (2 : Complex)‖| := by
  classical
  let S := centerTwoForbiddenRadii n
  obtain ⟨q, hq, hsep⟩ :=
    exists_point_Ioo_away_from_finset S (dyadicCofactorBase n + 3)
  refine ⟨q, hq.1, ?_, ?_, ?_⟩
  · linarith [hq.2]
  · unfold dyadicCofactorFactorRadius
    linarith [hq.2]
  · intro rho hrho
    have hmem : ‖rho.1 - (2 : Complex)‖ ∈ S := by
      dsimp only [S, centerTwoForbiddenRadii]
      exact Finset.mem_image.mpr ⟨rho, hrho, rfl⟩
    exact (dyadicCofactorRadialGap_le_gridGap n).trans
      (hsep _ hmem)

/-- Radial separation gives an ordinary Euclidean distance lower bound from
the selected circle to every zero in the factor window. -/
theorem centerTwo_circle_distance_le
    {q delta : Real} {z : Complex}
    (hz : ‖z - (2 : Complex)‖ = q)
    {rho : sourceNontrivialZeroSet}
    (hsep : delta <= |q - ‖rho.1 - (2 : Complex)‖|) :
    delta <= ‖z - rho.1‖ := by
  calc
    delta <= |q - ‖rho.1 - (2 : Complex)‖| := hsep
    _ = |‖z - (2 : Complex)‖ - ‖rho.1 - (2 : Complex)‖| := by rw [hz]
    _ <= ‖(z - (2 : Complex)) - (rho.1 - (2 : Complex))‖ :=
      abs_norm_sub_norm_le _ _
    _ = ‖z - rho.1‖ := by
      congr 1
      ring

/-- Away from the divisor support, the logarithm of the finite factor norm is
the multiplicity-weighted sum of the logarithmic distances to its zeros. -/
theorem real_log_norm_xiClosedBallFactor_eq_sum
    (c : Complex) (R : Real) {z : Complex}
    (hz : z ∉ (xiClosedBallDivisor c R).support) :
    Real.log ‖xiClosedBallFactor c R z‖ =
      ∑ u ∈ (xiClosedBallDivisor_support_finite c R).toFinset,
        (xiClosedBallDivisor c R u : Real) * Real.log ‖z - u‖ := by
  classical
  rw [xiClosedBallFactor_eq_product_support]
  simp only [Complex.norm_prod, Complex.norm_zpow]
  rw [Real.log_prod]
  · apply Finset.sum_congr rfl
    intro u hu
    rw [Real.log_zpow]
  · intro u hu
    apply zpow_ne_zero
    rw [norm_ne_zero_iff]
    exact sub_ne_zero.mpr fun hzu => hz (by
      rw [hzu]
      exact (xiClosedBallDivisor_support_finite c R).mem_toFinset.mp hu)

/-- A uniform lower distance from every divisor point gives a lower bound for
the logarithm of the finite factor norm. -/
theorem divisorMass_mul_log_le_real_log_norm_xiClosedBallFactor
    (c : Complex) (R delta : Real) {z : Complex} (hdelta : 0 < delta)
    (hsep : ∀ u ∈ (xiClosedBallDivisor_support_finite c R).toFinset,
      delta <= ‖z - u‖) :
    xiClosedBallDivisorMass c R * Real.log delta <=
      Real.log ‖xiClosedBallFactor c R z‖ := by
  have hzsupport : z ∉ (xiClosedBallDivisor c R).support := by
    intro hz
    have hzmem : z ∈ (xiClosedBallDivisor_support_finite c R).toFinset :=
      (xiClosedBallDivisor_support_finite c R).mem_toFinset.mpr hz
    have hle := hsep z hzmem
    simp only [sub_self, norm_zero] at hle
    exact (not_le_of_gt hdelta) hle
  rw [real_log_norm_xiClosedBallFactor_eq_sum c R hzsupport]
  unfold xiClosedBallDivisorMass
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro u hu
  apply mul_le_mul_of_nonneg_left
  · exact Real.log_le_log hdelta (hsep u hu)
  · exact_mod_cast xiClosedBallDivisor_nonneg c R u

/-- A uniform upper distance to every divisor point gives the corresponding
upper bound for the logarithm of the finite factor norm. -/
theorem real_log_norm_xiClosedBallFactor_le_divisorMass_mul_log
    (c : Complex) (R D : Real) {z : Complex} (_hD : 0 < D)
    (hzsupport : z ∉ (xiClosedBallDivisor c R).support)
    (hupper : ∀ u ∈ (xiClosedBallDivisor_support_finite c R).toFinset,
      ‖z - u‖ <= D) :
    Real.log ‖xiClosedBallFactor c R z‖ <=
      xiClosedBallDivisorMass c R * Real.log D := by
  rw [real_log_norm_xiClosedBallFactor_eq_sum c R hzsupport]
  unfold xiClosedBallDivisorMass
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro u hu
  apply mul_le_mul_of_nonneg_left
  · have hzu : 0 < ‖z - u‖ := by
      rw [norm_pos_iff, sub_ne_zero]
      intro hzu
      apply hzsupport
      rw [hzu]
      exact (xiClosedBallDivisor_support_finite c R).mem_toFinset.mp hu
    exact Real.log_le_log hzu (hupper u hu)
  · exact_mod_cast xiClosedBallDivisor_nonneg c R u

theorem dyadicCofactorRadialGap_le_one (n : Nat) :
    dyadicCofactorRadialGap n <= 1 := by
  have hmass := dyadicCofactorMassBound_nonneg n
  have hden : 0 < 4 * (dyadicCofactorMassBound n + 2) := by positivity
  unfold dyadicCofactorRadialGap
  apply (div_le_iff₀ hden).mpr
  nlinarith

theorem dyadicCofactorFactorRadius_one_le (n : Nat) :
    1 <= dyadicCofactorFactorRadius n := by
  unfold dyadicCofactorFactorRadius
  linarith [dyadicCofactorBase_ge_four n]

theorem xiClosedBallFactor_ne_zero_of_not_mem_support
    (c : Complex) (R : Real) {z : Complex}
    (hz : z ∉ (xiClosedBallDivisor c R).support) :
    xiClosedBallFactor c R z ≠ 0 := by
  rw [xiClosedBallFactor]
  apply Function.FactorizedRational.ne_zero
  simpa only [Function.mem_support, not_not] using hz

/-- On the selected outer circle, the same center-`2` finite factor has the
explicit logarithmic lower bound dictated by the dyadic radial gap. -/
theorem exists_dyadic_centerTwo_outerRadius_factor_lower (n : Nat) :
    ∃ q : Real,
      dyadicCofactorBase n + 3 < q ∧
      q < dyadicCofactorBase n + 4 ∧
      q < dyadicCofactorFactorRadius n ∧
      ∀ z : Complex, ‖z - (2 : Complex)‖ = q →
        xiClosedBallFactor (2 : Complex)
          (dyadicCofactorFactorRadius n) z ≠ 0 ∧
          dyadicCofactorMassBound n * Real.log (dyadicCofactorRadialGap n) <=
            Real.log ‖xiClosedBallFactor (2 : Complex)
              (dyadicCofactorFactorRadius n) z‖ := by
  classical
  obtain ⟨q, hqLower, hqUpper, hqFactor, hsep⟩ :=
    exists_dyadic_centerTwo_outerRadius n
  refine ⟨q, hqLower, hqUpper, hqFactor, ?_⟩
  intro z hz
  have hdistance : ∀ u ∈
      (xiClosedBallDivisor_support_finite (2 : Complex)
        (dyadicCofactorFactorRadius n)).toFinset,
      dyadicCofactorRadialGap n <= ‖z - u‖ := by
    intro u hu
    let uSupport :
        ((xiClosedBallDivisor_support_finite (2 : Complex)
          (dyadicCofactorFactorRadius n)).toFinset : Set Complex) :=
      ⟨u, hu⟩
    let rho : sourceNontrivialZeroSet :=
      xiClosedBallSupportToSourceZero (2 : Complex)
        (dyadicCofactorFactorRadius n) uSupport
    have hrhoOwner : rho ∈ xiClosedBallSourceZeros (2 : Complex)
        (dyadicCofactorFactorRadius n) := by
      rw [mem_xiClosedBallSourceZeros_iff]
      exact hu
    have hrhoHeight : rho ∈
        finiteHeightZeros (dyadicCofactorFactorRadius n) :=
      xiClosedBallSourceZeros_two_subset_finiteHeightZeros
        (dyadicCofactorFactorRadius n)
        (dyadicCofactorFactorRadius_pos n).le hrhoOwner
    exact centerTwo_circle_distance_le hz (hsep rho hrhoHeight)
  have hzsupport : z ∉ (xiClosedBallDivisor (2 : Complex)
      (dyadicCofactorFactorRadius n)).support := by
    intro hzsupp
    have hzmem : z ∈
        (xiClosedBallDivisor_support_finite (2 : Complex)
          (dyadicCofactorFactorRadius n)).toFinset :=
      (xiClosedBallDivisor_support_finite (2 : Complex)
        (dyadicCofactorFactorRadius n)).mem_toFinset.mpr hzsupp
    have hle := hdistance z hzmem
    simp only [sub_self, norm_zero] at hle
    exact (not_le_of_gt (dyadicCofactorRadialGap_pos n)) hle
  refine ⟨xiClosedBallFactor_ne_zero_of_not_mem_support
    (2 : Complex) (dyadicCofactorFactorRadius n) hzsupport, ?_⟩
  have hfactor :=
    divisorMass_mul_log_le_real_log_norm_xiClosedBallFactor
      (2 : Complex) (dyadicCofactorFactorRadius n)
      (dyadicCofactorRadialGap n) (dyadicCofactorRadialGap_pos n) hdistance
  have hlogNonpos : Real.log (dyadicCofactorRadialGap n) <= 0 :=
    Real.log_nonpos (dyadicCofactorRadialGap_pos n).le
      (dyadicCofactorRadialGap_le_one n)
  calc
    dyadicCofactorMassBound n * Real.log (dyadicCofactorRadialGap n) <=
        xiClosedBallDivisorMass (2 : Complex) (dyadicCofactorFactorRadius n) *
          Real.log (dyadicCofactorRadialGap n) :=
      mul_le_mul_of_nonpos_right (xiClosedBallDivisorMass_two_dyadic_le n)
        hlogNonpos
    _ <= Real.log ‖xiClosedBallFactor (2 : Complex)
        (dyadicCofactorFactorRadius n) z‖ := hfactor

/-- At the normalization point `2`, the finite factor has the matching
logarithmic upper bound. -/
theorem real_log_norm_centerTwoFactor_at_two_le (n : Nat) :
    Real.log ‖xiClosedBallFactor (2 : Complex)
      (dyadicCofactorFactorRadius n) 2‖ <=
        dyadicCofactorMassBound n *
          Real.log (dyadicCofactorFactorRadius n) := by
  have htwoSupport : (2 : Complex) ∉
      (xiClosedBallDivisor (2 : Complex)
        (dyadicCofactorFactorRadius n)).support := by
    intro htwo
    exact completedRiemannXi_two_ne_zero
      (xiClosedBallDivisor_mem_closedBall_and_xi_eq_zero_of_mem_support
        (2 : Complex) (dyadicCofactorFactorRadius n) htwo).2
  have hupper : ∀ u ∈
      (xiClosedBallDivisor_support_finite (2 : Complex)
        (dyadicCofactorFactorRadius n)).toFinset,
      ‖(2 : Complex) - u‖ <= dyadicCofactorFactorRadius n := by
    intro u hu
    have hball :=
      (xiClosedBallDivisor_mem_closedBall_and_xi_eq_zero_of_mem_support
        (2 : Complex) (dyadicCofactorFactorRadius n)
        ((xiClosedBallDivisor_support_finite (2 : Complex)
          (dyadicCofactorFactorRadius n)).mem_toFinset.mp hu)).1
    rw [Metric.mem_closedBall, dist_eq_norm,
      abs_of_pos (dyadicCofactorFactorRadius_pos n)] at hball
    simpa only [norm_sub_rev] using hball
  have hraw := real_log_norm_xiClosedBallFactor_le_divisorMass_mul_log
    (2 : Complex) (dyadicCofactorFactorRadius n)
    (dyadicCofactorFactorRadius n) (dyadicCofactorFactorRadius_pos n)
    htwoSupport hupper
  calc
    Real.log ‖xiClosedBallFactor (2 : Complex)
        (dyadicCofactorFactorRadius n) 2‖ <=
        xiClosedBallDivisorMass (2 : Complex) (dyadicCofactorFactorRadius n) *
          Real.log (dyadicCofactorFactorRadius n) := hraw
    _ <= dyadicCofactorMassBound n *
          Real.log (dyadicCofactorFactorRadius n) := by
      exact mul_le_mul_of_nonneg_right
        (xiClosedBallDivisorMass_two_dyadic_le n)
        (Real.log_nonneg (dyadicCofactorFactorRadius_one_le n))

/-- Sharp `R log R` xi growth on every selected center-`2` outer circle. -/
theorem norm_completedRiemannXi_le_on_dyadic_centerTwo_outerCircle
    (n : Nat) {q : Real}
    (hq : q < dyadicCofactorBase n + 4) {z : Complex}
    (hz : ‖z - (2 : Complex)‖ = q) :
    ‖completedRiemannXi z‖ <=
      Real.exp (xiDyadicRLogRGrowthExponent n) := by
  have hzNorm : ‖z‖ <= q + 2 := by
    calc
      ‖z‖ = ‖(z - (2 : Complex)) + 2‖ := by ring_nf
      _ <= ‖z - (2 : Complex)‖ + ‖(2 : Complex)‖ := norm_add_le _ _
      _ = q + 2 := by rw [hz]; norm_num
  obtain ⟨u, huRe, huNorm, huXi⟩ :=
    exists_half_le_re_norm_le_add_one_and_norm_completedRiemannXi_eq z
  rw [← huXi]
  apply norm_completedRiemannXi_le_exp_of_halfplane_dyadic_rlogr n huRe
  have hbase := dyadicCofactorBase_ge_four n
  have huBound : ‖u‖ < dyadicCofactorBase n + 7 := by
    calc
      ‖u‖ <= ‖z‖ + 1 := huNorm
      _ <= q + 3 := by linarith
      _ < dyadicCofactorBase n + 7 := by linarith
  calc
    ‖u‖ <= dyadicCofactorBase n + 7 := huBound.le
    _ <= 4 * dyadicCofactorBase n := by nlinarith
    _ = (2 : Real) ^ (n + 4) := by
      unfold dyadicCofactorBase
      rw [show n + 4 = (n + 2) + 2 by omega, pow_add]
      ring

/-- Real-part identity for a chosen analytic logarithm, normalized at the
center of its ball. -/
theorem analyticLog_sub_center_re_eq_log_norm_sub
    {g L : Complex -> Complex} {c : Complex} {R : Real}
    (hLexp : EqOn (Complex.exp ∘ L) g (Metric.ball c R))
    {z : Complex} (hz : z ∈ Metric.ball c R)
    (hc : c ∈ Metric.ball c R) :
    (L z - L c).re = Real.log ‖g z‖ - Real.log ‖g c‖ := by
  have hlogz : Real.log ‖g z‖ = (L z).re := by
    rw [← hLexp hz]
    simp only [Function.comp_apply, Complex.norm_exp, Real.log_exp]
  have hlogc : Real.log ‖g c‖ = (L c).re := by
    rw [← hLexp hc]
    simp only [Function.comp_apply, Complex.norm_exp, Real.log_exp]
  rw [Complex.sub_re, hlogz, hlogc]

/-- Pointwise factorization reads the cofactor norm as the quotient of xi by
the same finite factor. -/
theorem real_log_norm_cofactor_eq_xi_sub_factor
    {c : Complex} {R : Real} {g : Complex -> Complex}
    (hanalytic : AnalyticOnNhd Complex g (Metric.closedBall c |R|))
    (hnonzero : ∀ u : Metric.closedBall c |R|, g u ≠ 0)
    (hfactor : completedRiemannXi =ᶠ[codiscreteWithin
      (Metric.closedBall c |R|)] xiClosedBallFactor c R • g)
    {z : Complex} (hzball : z ∈ Metric.ball c |R|)
    (hzfactor : xiClosedBallFactor c R z ≠ 0) :
    Real.log ‖g z‖ = Real.log ‖completedRiemannXi z‖ -
      Real.log ‖xiClosedBallFactor c R z‖ := by
  have hg : g z ≠ 0 := hnonzero ⟨z, Metric.ball_subset_closedBall hzball⟩
  have heq := xiClosedBall_factorization_eq_of_mem_ball
    hanalytic hfactor hzball
  rw [heq, Complex.norm_mul, Real.log_mul
    (norm_ne_zero_iff.mpr hzfactor) (norm_ne_zero_iff.mpr hg)]
  ring

/-- Explicit real-part budget for the normalized center-`2` analytic
cofactor logarithm. -/
noncomputable def dyadicCofactorBorelRealBound (n : Nat) : Real :=
  xiDyadicRLogRGrowthExponent n +
    |Real.log ‖completedRiemannXi 2‖| +
    dyadicCofactorMassBound n *
      (Real.log (dyadicCofactorFactorRadius n) -
        Real.log (dyadicCofactorRadialGap n))

theorem dyadicCofactorBorelRealBound_pos (n : Nat) :
    0 < dyadicCofactorBorelRealBound n := by
  have hxiExponent : 0 < xiDyadicRLogRGrowthExponent n := by
    unfold xiDyadicRLogRGrowthExponent
    have hfixed := xiGrowthFixedConstant_nonneg
    positivity
  have hRlog : 0 <= Real.log (dyadicCofactorFactorRadius n) :=
    Real.log_nonneg (dyadicCofactorFactorRadius_one_le n)
  have hgapLog : Real.log (dyadicCofactorRadialGap n) <= 0 :=
    Real.log_nonpos (dyadicCofactorRadialGap_pos n).le
      (dyadicCofactorRadialGap_le_one n)
  unfold dyadicCofactorBorelRealBound
  exact add_pos_of_pos_of_nonneg
    (add_pos_of_pos_of_nonneg hxiExponent (abs_nonneg _))
    (mul_nonneg (dyadicCofactorMassBound_nonneg n)
      (sub_nonneg.mpr (hgapLog.trans hRlog)))

/-- One dyadic scale's exact center-`2` factor owner, analytic cofactor log,
and selected outer-circle estimate.  This is a `Type`-valued structure because
the radius and functions are load-bearing data. -/
structure DyadicCenterTwoCofactorData (n : Nat) where
  outerRadius : Real
  cofactor : Complex -> Complex
  analyticLog : Complex -> Complex
  outerRadius_lower : dyadicCofactorBase n + 3 < outerRadius
  outerRadius_upper : outerRadius < dyadicCofactorBase n + 4
  outerRadius_lt_factor : outerRadius < dyadicCofactorFactorRadius n
  cofactor_analytic : AnalyticOnNhd Complex cofactor
    (Metric.closedBall (2 : Complex) (dyadicCofactorFactorRadius n))
  cofactor_nonzero : ∀ u : Metric.closedBall (2 : Complex)
    (dyadicCofactorFactorRadius n), cofactor u ≠ 0
  factorization : completedRiemannXi =ᶠ[codiscreteWithin
    (Metric.closedBall (2 : Complex) (dyadicCofactorFactorRadius n))]
      xiClosedBallFactor (2 : Complex) (dyadicCofactorFactorRadius n) • cofactor
  log_analytic : AnalyticOnNhd Complex analyticLog
    (Metric.ball (2 : Complex) (dyadicCofactorFactorRadius n))
  log_continuous : ContinuousOn analyticLog
    (Metric.ball (2 : Complex) (dyadicCofactorFactorRadius n))
  exp_log_eq : EqOn (Complex.exp ∘ analyticLog) cofactor
    (Metric.ball (2 : Complex) (dyadicCofactorFactorRadius n))
  factor_boundary : ∀ z : Complex, ‖z - (2 : Complex)‖ = outerRadius →
    xiClosedBallFactor (2 : Complex) (dyadicCofactorFactorRadius n) z ≠ 0 ∧
      dyadicCofactorMassBound n * Real.log (dyadicCofactorRadialGap n) <=
        Real.log ‖xiClosedBallFactor (2 : Complex)
          (dyadicCofactorFactorRadius n) z‖

/-- The selected center-`2` finite factor and its analytic logarithm satisfy
the Borel--Caratheodory real-part hypothesis on the selected outer circle. -/
theorem exists_dyadic_centerTwo_factorization_analyticLog_boundary_bound
    (n : Nat) : Nonempty (DyadicCenterTwoCofactorData n) := by
  obtain ⟨q, hqLower, hqUpper, hqFactor, hfactorLower⟩ :=
    exists_dyadic_centerTwo_outerRadius_factor_lower n
  obtain ⟨g, L, hganalytic, hgnonzero, hfactor, hLanalytic, hLcontinuous,
      hLexp⟩ :=
    C1XiAnalyticLog.exists_xiClosedBall_factorization_with_analytic_log_on_ball
      (2 : Complex) (dyadicCofactorFactorRadius n)
      (dyadicCofactorFactorRadius_pos n)
  refine ⟨{
    outerRadius := q
    cofactor := g
    analyticLog := L
    outerRadius_lower := hqLower
    outerRadius_upper := hqUpper
    outerRadius_lt_factor := hqFactor
    cofactor_analytic := hganalytic
    cofactor_nonzero := hgnonzero
    factorization := hfactor
    log_analytic := hLanalytic
    log_continuous := hLcontinuous
    exp_log_eq := hLexp
    factor_boundary := hfactorLower }⟩

/-- A point of the selected outer circle is strictly inside its owning factor
ball. -/
theorem DyadicCenterTwoCofactorData.boundary_mem_factor_ball
    {n : Nat} (D : DyadicCenterTwoCofactorData n)
    {z : Complex} (hz : ‖z - (2 : Complex)‖ = D.outerRadius) :
    z ∈ Metric.ball (2 : Complex) (dyadicCofactorFactorRadius n) := by
  rw [Metric.mem_ball, dist_eq_norm, hz]
  exact D.outerRadius_lt_factor

theorem centerTwo_mem_dyadic_factor_ball (n : Nat) :
    (2 : Complex) ∈ Metric.ball (2 : Complex)
      (dyadicCofactorFactorRadius n) :=
  Metric.mem_ball_self (dyadicCofactorFactorRadius_pos n)

theorem centerTwoFactor_at_two_ne_zero (n : Nat) :
    xiClosedBallFactor (2 : Complex) (dyadicCofactorFactorRadius n) 2 ≠ 0 := by
  apply xiClosedBallFactor_ne_zero_of_not_mem_support
  intro htwoSupport
  exact completedRiemannXi_two_ne_zero
    (xiClosedBallDivisor_mem_closedBall_and_xi_eq_zero_of_mem_support
      (2 : Complex) (dyadicCofactorFactorRadius n) htwoSupport).2

/-- Log-norm quotient identity at a selected boundary point. -/
theorem DyadicCenterTwoCofactorData.boundary_cofactor_log_eq
    {n : Nat} (D : DyadicCenterTwoCofactorData n)
    {z : Complex} (hz : ‖z - (2 : Complex)‖ = D.outerRadius) :
    Real.log ‖D.cofactor z‖ = Real.log ‖completedRiemannXi z‖ -
      Real.log ‖xiClosedBallFactor (2 : Complex)
        (dyadicCofactorFactorRadius n) z‖ := by
  have hRabs : |dyadicCofactorFactorRadius n| =
      dyadicCofactorFactorRadius n :=
    abs_of_pos (dyadicCofactorFactorRadius_pos n)
  apply real_log_norm_cofactor_eq_xi_sub_factor
    (R := dyadicCofactorFactorRadius n)
    (by simpa only [hRabs] using D.cofactor_analytic)
    (fun u => D.cofactor_nonzero
      ⟨u.1, by simpa only [hRabs] using u.2⟩)
    (by simpa only [hRabs] using D.factorization)
    (by simpa only [hRabs] using D.boundary_mem_factor_ball hz)
  exact (D.factor_boundary z hz).1

/-- Log-norm quotient identity at the normalization point `2`. -/
theorem DyadicCenterTwoCofactorData.center_cofactor_log_eq
    {n : Nat} (D : DyadicCenterTwoCofactorData n) :
    Real.log ‖D.cofactor 2‖ = Real.log ‖completedRiemannXi 2‖ -
      Real.log ‖xiClosedBallFactor (2 : Complex)
        (dyadicCofactorFactorRadius n) 2‖ := by
  have hRabs : |dyadicCofactorFactorRadius n| =
      dyadicCofactorFactorRadius n :=
    abs_of_pos (dyadicCofactorFactorRadius_pos n)
  apply real_log_norm_cofactor_eq_xi_sub_factor
    (R := dyadicCofactorFactorRadius n)
    (by simpa only [hRabs] using D.cofactor_analytic)
    (fun u => D.cofactor_nonzero
      ⟨u.1, by simpa only [hRabs] using u.2⟩)
    (by simpa only [hRabs] using D.factorization)
    (by simpa only [hRabs] using centerTwo_mem_dyadic_factor_ball n)
  exact centerTwoFactor_at_two_ne_zero n

/-- Sharp logarithmic xi bound at a selected boundary point. -/
theorem DyadicCenterTwoCofactorData.boundary_xi_log_le
    {n : Nat} (D : DyadicCenterTwoCofactorData n)
    {z : Complex} (hz : ‖z - (2 : Complex)‖ = D.outerRadius) :
    Real.log ‖completedRiemannXi z‖ <= xiDyadicRLogRGrowthExponent n := by
  have hzBall := D.boundary_mem_factor_ball hz
  have hzFactor := (D.factor_boundary z hz).1
  have hRabs : |dyadicCofactorFactorRadius n| =
      dyadicCofactorFactorRadius n :=
    abs_of_pos (dyadicCofactorFactorRadius_pos n)
  have hanalyticAbs : AnalyticOnNhd Complex D.cofactor
      (Metric.closedBall (2 : Complex) |dyadicCofactorFactorRadius n|) := by
    simpa only [hRabs] using D.cofactor_analytic
  have hfactorAbs : completedRiemannXi =ᶠ[codiscreteWithin
      (Metric.closedBall (2 : Complex) |dyadicCofactorFactorRadius n|)]
        xiClosedBallFactor (2 : Complex) (dyadicCofactorFactorRadius n) •
          D.cofactor := by
    simpa only [hRabs] using D.factorization
  have hzBallAbs : z ∈ Metric.ball (2 : Complex)
      |dyadicCofactorFactorRadius n| := by
    simpa only [hRabs] using hzBall
  have hzXi : completedRiemannXi z ≠ 0 := by
    rw [xiClosedBall_factorization_eq_of_mem_ball
      hanalyticAbs hfactorAbs hzBallAbs]
    exact mul_ne_zero hzFactor
      (D.cofactor_nonzero ⟨z, Metric.ball_subset_closedBall hzBall⟩)
  have hxiNorm := norm_completedRiemannXi_le_on_dyadic_centerTwo_outerCircle
    n D.outerRadius_upper hz
  calc
    Real.log ‖completedRiemannXi z‖ <=
        Real.log (Real.exp (xiDyadicRLogRGrowthExponent n)) :=
      Real.log_le_log (norm_pos_iff.mpr hzXi) hxiNorm
    _ = xiDyadicRLogRGrowthExponent n := Real.log_exp _

/-- The raw factor-circle bounds in one owner imply the real-part hypothesis
for its normalized analytic logarithm. -/
theorem DyadicCenterTwoCofactorData.boundary_re
    {n : Nat} (D : DyadicCenterTwoCofactorData n)
    {z : Complex} (hz : ‖z - (2 : Complex)‖ = D.outerRadius) :
    (D.analyticLog z - D.analyticLog 2).re <=
      dyadicCofactorBorelRealBound n := by
  have hzBall := D.boundary_mem_factor_ball hz
  have htwoBall := centerTwo_mem_dyadic_factor_ball n
  have hnormalized := analyticLog_sub_center_re_eq_log_norm_sub
    D.exp_log_eq hzBall htwoBall
  have hzCofactor := D.boundary_cofactor_log_eq hz
  have htwoCofactor := D.center_cofactor_log_eq
  have hxiLog := D.boundary_xi_log_le hz
  have hzFactorLower := (D.factor_boundary z hz).2
  have hcenterFactor := real_log_norm_centerTwoFactor_at_two_le n
  have hcenterLogPenalty :
      -Real.log ‖completedRiemannXi 2‖ <=
        |Real.log ‖completedRiemannXi 2‖| := neg_le_abs _
  rw [hnormalized, hzCofactor, htwoCofactor]
  unfold dyadicCofactorBorelRealBound
  linarith

/-- Analytic logarithm translated to the origin and normalized to vanish
there, in the exact form consumed by Mathlib's Borel--Caratheodory theorem. -/
noncomputable def DyadicCenterTwoCofactorData.normalizedLog
    {n : Nat} (D : DyadicCenterTwoCofactorData n) (w : Complex) : Complex :=
  D.analyticLog (w + 2) - D.analyticLog 2

@[simp] theorem DyadicCenterTwoCofactorData.normalizedLog_zero
    {n : Nat} (D : DyadicCenterTwoCofactorData n) :
    D.normalizedLog 0 = 0 := by
  simp [DyadicCenterTwoCofactorData.normalizedLog]

theorem DyadicCenterTwoCofactorData.outerRadius_pos
    {n : Nat} (D : DyadicCenterTwoCofactorData n) :
    0 < D.outerRadius := by
  linarith [D.outerRadius_lower, dyadicCofactorBase_ge_four n]

/-- The translated normalized logarithm is differentiable on the selected
disc and continuous on its closure because that closure lies strictly inside
the larger factorization ball. -/
theorem DyadicCenterTwoCofactorData.normalizedLog_diffContOnCl
    {n : Nat} (D : DyadicCenterTwoCofactorData n) :
    DiffContOnCl Complex D.normalizedLog
      (Metric.ball (0 : Complex) D.outerRadius) := by
  apply DifferentiableOn.diffContOnCl
  rw [closure_ball (0 : Complex) (ne_of_gt D.outerRadius_pos)]
  intro w hw
  have hwNorm : ‖w‖ <= D.outerRadius := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hw
  have hmap : w + (2 : Complex) ∈ Metric.ball (2 : Complex)
      (dyadicCofactorFactorRadius n) := by
    rw [Metric.mem_ball, dist_eq_norm]
    have heq : (w + (2 : Complex)) - 2 = w := by ring
    rw [heq]
    exact lt_of_le_of_lt hwNorm D.outerRadius_lt_factor
  have htranslated : AnalyticAt Complex
      (fun v : Complex => D.analyticLog (v + 2)) w := by
    have hraw := (D.log_analytic (w + 2) hmap).comp_sub (-(2 : Complex))
    simpa [sub_neg] using hraw
  exact (htranslated.sub analyticAt_const).differentiableAt.differentiableWithinAt

/-- The outer-circle real-part estimate propagates to the open disc by the
maximum modulus principle applied to the exponential of the normalized log. -/
theorem DyadicCenterTwoCofactorData.normalizedLog_re_le_on_ball
    {n : Nat} (D : DyadicCenterTwoCofactorData n)
    {w : Complex} (hw : w ∈ Metric.ball (0 : Complex) D.outerRadius) :
    (D.normalizedLog w).re <= dyadicCofactorBorelRealBound n := by
  have hExpDiff : DiffContOnCl Complex
      (fun v : Complex => Complex.exp (D.normalizedLog v))
      (Metric.ball (0 : Complex) D.outerRadius) := by
    simpa only [Function.comp_def] using
      Complex.differentiable_exp.comp_diffContOnCl
        D.normalizedLog_diffContOnCl
  have hnorm : ‖Complex.exp (D.normalizedLog w)‖ <=
      Real.exp (dyadicCofactorBorelRealBound n) := by
    apply Complex.norm_le_of_forall_mem_frontier_norm_le
      Metric.isBounded_ball hExpDiff
    · intro v hv
      have hvSphere : ‖v‖ = D.outerRadius := by
        rw [frontier_ball (0 : Complex) (ne_of_gt D.outerRadius_pos)] at hv
        simpa [Metric.mem_sphere, dist_zero_right] using hv
      have hboundary := D.boundary_re (z := v + 2) (by
        have heq : (v + (2 : Complex)) - 2 = v := by ring
        rw [heq]
        exact hvSphere)
      simpa only [Complex.norm_exp] using Real.exp_le_exp.mpr hboundary
    · exact subset_closure hw
  exact Real.exp_le_exp.mp (by simpa only [Complex.norm_exp] using hnorm)

/-- Borel--Caratheodory bound for the normalized analytic logarithm on the
selected center-`2` disc. -/
theorem DyadicCenterTwoCofactorData.norm_normalizedLog_le_borel
    {n : Nat} (D : DyadicCenterTwoCofactorData n)
    {w : Complex} (hw : w ∈ Metric.ball (0 : Complex) D.outerRadius) :
    ‖D.normalizedLog w‖ <=
      2 * dyadicCofactorBorelRealBound n * ‖w‖ /
        (D.outerRadius - ‖w‖) := by
  apply Complex.borelCaratheodory_zero
    (dyadicCofactorBorelRealBound_pos n)
    D.normalizedLog_diffContOnCl.differentiableOn
  · intro v hv
    exact D.normalizedLog_re_le_on_ball hv
  · exact D.outerRadius_pos
  · exact hw
  · exact D.normalizedLog_zero

/-- The explicit Cauchy estimate for the logarithmic derivative of the
center-`2` cofactor.  Its scale is polynomial in the Borel real-part budget
and in the dyadic radius. -/
noncomputable def dyadicCofactorLogDerivBound (n : Nat) : Real :=
  8 * dyadicCofactorBorelRealBound n * (dyadicCofactorBase n + 3)

theorem dyadicCofactorLogDerivBound_pos (n : Nat) :
    0 < dyadicCofactorLogDerivBound n := by
  unfold dyadicCofactorLogDerivBound
  have hbase : 0 < dyadicCofactorBase n + 3 := by
    linarith [dyadicCofactorBase_ge_four n]
  exact mul_pos (mul_pos (by norm_num) (dyadicCofactorBorelRealBound_pos n))
    hbase

/-- The fixed strip `-1 <= Re(s) <= 2` and the dyadic height window fit
strictly inside the radius `B_n + 2` around the normalization point `2`.
The Euclidean estimate, rather than a coordinatewise triangle estimate, is
what retains the two-unit margin needed by the Cauchy circle. -/
theorem norm_verticalPoint_sub_two_lt_dyadic_innerRadius
    (n : Nat) {x t : Real} (hx : x ∈ Icc (-1 : Real) 2)
    (ht : |t| < dyadicCofactorBase n + 1) :
    ‖verticalPoint x t - (2 : Complex)‖ < dyadicCofactorBase n + 2 := by
  rcases hx with ⟨hxLower, hxUpper⟩
  have hbase := dyadicCofactorBase_ge_four n
  have hxAbs : |x - 2| ≤ 3 := by
    rw [abs_le]
    constructor <;> linarith
  have hxSq : (x - 2) ^ 2 ≤ (3 : Real) ^ 2 := by
    rw [← sq_abs]
    exact (sq_le_sq₀ (abs_nonneg _) (by norm_num)).2 hxAbs
  have htRadius : 0 ≤ dyadicCofactorBase n + 1 := by linarith
  have htSq : t ^ 2 < (dyadicCofactorBase n + 1) ^ 2 := by
    rw [← sq_abs]
    exact (sq_lt_sq₀ (abs_nonneg _) htRadius).2 ht
  rw [← sq_lt_sq₀ (norm_nonneg _)]
  · simp only [Complex.sq_norm, Complex.normSq_apply]
    simp [verticalPoint]
    nlinarith
  · linarith

/-- A radius-`1/2` Cauchy ball around an inner-strip point remains inside
the selected Borel disc. -/
theorem DyadicCenterTwoCofactorData.localCauchyBall_subset_outerBall
    {n : Nat} (D : DyadicCenterTwoCofactorData n) {w : Complex}
    (hw : ‖w‖ < dyadicCofactorBase n + 2) :
    Metric.ball w (1 / 2 : Real) ⊆
      Metric.ball (0 : Complex) D.outerRadius := by
  intro v hv
  rw [Metric.mem_ball, dist_zero_right]
  have hvDist : dist v w < (1 / 2 : Real) := by
    simpa only [Metric.mem_ball] using hv
  calc
    ‖v‖ = ‖(v - w) + w‖ := by rw [sub_add_cancel]
    _ ≤ ‖v - w‖ + ‖w‖ := norm_add_le _ _
    _ = dist v w + ‖w‖ := by rw [dist_eq_norm]
    _ < (1 / 2 : Real) + (dyadicCofactorBase n + 2) :=
      add_lt_add hvDist hw
    _ < D.outerRadius := by linarith [D.outerRadius_lower]

/-- The Borel estimate is uniformly bounded on the radius-`1/2` Cauchy
circle around every point in the inner dyadic disc. -/
theorem DyadicCenterTwoCofactorData.norm_normalizedLog_le_on_localCauchySphere
    {n : Nat} (D : DyadicCenterTwoCofactorData n) {w v : Complex}
    (hw : ‖w‖ < dyadicCofactorBase n + 2)
    (hv : v ∈ Metric.sphere w (1 / 2 : Real)) :
    ‖D.normalizedLog v‖ ≤
      4 * dyadicCofactorBorelRealBound n * (dyadicCofactorBase n + 3) := by
  have hvDist : dist v w = (1 / 2 : Real) := by
    simpa only [Metric.mem_sphere] using hv
  have hvNorm : ‖v‖ < dyadicCofactorBase n + (5 / 2 : Real) := by
    calc
      ‖v‖ = ‖(v - w) + w‖ := by rw [sub_add_cancel]
      _ ≤ ‖v - w‖ + ‖w‖ := norm_add_le _ _
      _ = dist v w + ‖w‖ := by rw [dist_eq_norm]
      _ < (1 / 2 : Real) + (dyadicCofactorBase n + 2) := by
        rw [hvDist]
        linarith
      _ = dyadicCofactorBase n + (5 / 2 : Real) := by ring
  have hvOuter : v ∈ Metric.ball (0 : Complex) D.outerRadius := by
    rw [Metric.mem_ball, dist_zero_right]
    linarith [D.outerRadius_lower]
  have hraw := D.norm_normalizedLog_le_borel hvOuter
  have hden : (1 / 2 : Real) < D.outerRadius - ‖v‖ := by
    linarith [D.outerRadius_lower]
  have hdenNonneg : 0 ≤ D.outerRadius - ‖v‖ := by
    linarith
  have hM : 0 ≤ dyadicCofactorBorelRealBound n :=
    (dyadicCofactorBorelRealBound_pos n).le
  have hbase : 0 ≤ dyadicCofactorBase n + 3 := by
    linarith [dyadicCofactorBase_ge_four n]
  calc
    ‖D.normalizedLog v‖ ≤
        2 * dyadicCofactorBorelRealBound n * ‖v‖ /
          (D.outerRadius - ‖v‖) := hraw
    _ ≤ 2 * dyadicCofactorBorelRealBound n *
          (dyadicCofactorBase n + 3) /
          (D.outerRadius - ‖v‖) := by
      apply div_le_div_of_nonneg_right _ hdenNonneg
      gcongr
      linarith
    _ ≤ 2 * dyadicCofactorBorelRealBound n *
          (dyadicCofactorBase n + 3) / (1 / 2 : Real) := by
      exact div_le_div_of_nonneg_left
        (mul_nonneg (mul_nonneg (by norm_num) hM) hbase)
        (by norm_num) hden.le
    _ = 4 * dyadicCofactorBorelRealBound n *
          (dyadicCofactorBase n + 3) := by ring

/-- Cauchy's estimate turns the Borel function-value bound into a derivative
bound throughout the inner dyadic disc. -/
theorem DyadicCenterTwoCofactorData.norm_deriv_normalizedLog_le
    {n : Nat} (D : DyadicCenterTwoCofactorData n) {w : Complex}
    (hw : ‖w‖ < dyadicCofactorBase n + 2) :
    ‖deriv D.normalizedLog w‖ ≤ dyadicCofactorLogDerivBound n := by
  have hsmall : DiffContOnCl Complex D.normalizedLog
      (Metric.ball w (1 / 2 : Real)) :=
    D.normalizedLog_diffContOnCl.mono
      (D.localCauchyBall_subset_outerBall hw)
  have hCauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (f := D.normalizedLog) (c := w) (R := (1 / 2 : Real))
    (C := 4 * dyadicCofactorBorelRealBound n *
      (dyadicCofactorBase n + 3)) (by norm_num) hsmall
    (fun v hv => D.norm_normalizedLog_le_on_localCauchySphere hw hv)
  calc
    ‖deriv D.normalizedLog w‖ ≤
        (4 * dyadicCofactorBorelRealBound n *
          (dyadicCofactorBase n + 3)) / (1 / 2 : Real) := hCauchy
    _ = dyadicCofactorLogDerivBound n := by
      unfold dyadicCofactorLogDerivBound
      ring

/-- Translation and subtraction of the normalization constant do not change
the derivative of the analytic logarithm. -/
theorem DyadicCenterTwoCofactorData.deriv_normalizedLog
    {n : Nat} (D : DyadicCenterTwoCofactorData n) (w : Complex) :
    deriv D.normalizedLog w = deriv D.analyticLog (w + 2) := by
  unfold DyadicCenterTwoCofactorData.normalizedLog
  rw [deriv_sub_const, deriv_comp_add_const]

/-- Differentiating `exp L = g` identifies the derivative of the analytic
logarithm with the ordinary logarithmic derivative of its nonvanishing
cofactor. -/
theorem DyadicCenterTwoCofactorData.deriv_analyticLog_eq_logDeriv
    {n : Nat} (D : DyadicCenterTwoCofactorData n) {s : Complex}
    (hs : s ∈ Metric.ball (2 : Complex) (dyadicCofactorFactorRadius n)) :
    deriv D.analyticLog s = logDeriv D.cofactor s := by
  have hLdiff : DifferentiableAt Complex D.analyticLog s :=
    (D.log_analytic s hs).differentiableAt
  have hvalue : Complex.exp (D.analyticLog s) = D.cofactor s := by
    simpa only [Function.comp_apply] using D.exp_log_eq hs
  have hderivEq : deriv (Complex.exp ∘ D.analyticLog) s =
      deriv D.cofactor s :=
    (D.exp_log_eq.deriv Metric.isOpen_ball) hs
  have hmul : D.cofactor s * deriv D.analyticLog s =
      deriv D.cofactor s := by
    calc
      D.cofactor s * deriv D.analyticLog s =
          Complex.exp (D.analyticLog s) * deriv D.analyticLog s := by
            rw [hvalue]
      _ = deriv (Complex.exp ∘ D.analyticLog) s := by
            symm
            simpa only [Function.comp_apply] using deriv_cexp hLdiff
      _ = deriv D.cofactor s := hderivEq
  have hnonzero : D.cofactor s ≠ 0 :=
    D.cofactor_nonzero ⟨s, Metric.ball_subset_closedBall hs⟩
  rw [logDeriv_apply, eq_div_iff hnonzero]
  calc
    deriv D.analyticLog s * D.cofactor s =
        D.cofactor s * deriv D.analyticLog s := mul_comm _ _
    _ = deriv D.cofactor s := hmul

/-- Uniform logarithmic-derivative bound for the selected center-`2`
cofactor on both horizontal lines in the fixed strip `[-1, 2]`. -/
theorem DyadicCenterTwoCofactorData.norm_logDeriv_cofactor_le_on_dyadicStrip
    {n : Nat} (D : DyadicCenterTwoCofactorData n) {x t : Real}
    (hx : x ∈ Icc (-1 : Real) 2)
    (ht : |t| < dyadicCofactorBase n + 1) :
    ‖logDeriv D.cofactor (verticalPoint x t)‖ ≤
      dyadicCofactorLogDerivBound n := by
  let w : Complex := verticalPoint x t - 2
  have hw : ‖w‖ < dyadicCofactorBase n + 2 := by
    simpa only [w] using
      norm_verticalPoint_sub_two_lt_dyadic_innerRadius n hx ht
  have hderiv := D.norm_deriv_normalizedLog_le hw
  have hpoint : w + 2 = verticalPoint x t := by
    dsimp only [w]
    ring
  have hball : verticalPoint x t ∈ Metric.ball (2 : Complex)
      (dyadicCofactorFactorRadius n) := by
    rw [Metric.mem_ball, dist_eq_norm]
    have hsub : verticalPoint x t - 2 = w := by rfl
    rw [hsub]
    unfold dyadicCofactorFactorRadius
    linarith
  rw [D.deriv_normalizedLog, hpoint,
    D.deriv_analyticLog_eq_logDeriv hball] at hderiv
  exact hderiv

end
end C1XiCofactorBorel
end Source
end ConnesWeilRH
