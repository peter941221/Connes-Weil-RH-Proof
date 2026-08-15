import ConnesWeilRH.Dev.C1XiQuantitativeHeight
import ConnesWeilRH.Dev.C1XiFiniteSupportReindex

/-!
# C1XiQuantitativePrincipalBound

The dyadic height producer supplies a zero-free tube, and the Jensen count
supplies a multiplicity budget.  This module combines exactly those two facts
for the finite principal part of a closed-ball xi factorization.  The analytic
zero-free cofactor is deliberately not estimated here.
-/

namespace ConnesWeilRH
namespace Source
namespace C1XiQuantitativePrincipalBound

open Set
open CC20ZetaCounting
open C1SpectralWeil
open C1SpectralSummability
open C1XiFiniteFactor
open C1XiFiniteHeightRectangle
open C1XiFiniteSupportReindex
open C1XiQuantitativeHeight
open scoped BigOperators

/-- The real multiplicity mass of the exact divisor support belonging to one
closed-ball xi factorization owner. -/
noncomputable def xiClosedBallDivisorMass (c : Complex) (R : Real) : Real :=
  ∑ u ∈ (xiClosedBallDivisor_support_finite c R).toFinset,
    (xiClosedBallDivisor c R u : Real)

/-- The finite logarithmic-derivative principal part owned by one closed-ball
xi factorization. -/
noncomputable def xiClosedBallPrincipalSum
    (c : Complex) (R : Real) (z : Complex) : Complex :=
  ∑ u ∈ (xiClosedBallDivisor_support_finite c R).toFinset,
    (xiClosedBallDivisor c R u : Complex) / (z - u)

/-- A finite pole sum is controlled by its divisor mass whenever every pole is
at least `r` away from the evaluation point. -/
theorem norm_xiClosedBall_principalSum_le_divisorMass_div
    (c : Complex) (R r : Real) {z : Complex} (hr : 0 < r)
    (hsep : ∀ u ∈ (xiClosedBallDivisor_support_finite c R).toFinset,
      r ≤ dist z u) :
    ‖xiClosedBallPrincipalSum c R z‖ ≤
      xiClosedBallDivisorMass c R / r := by
  let s := (xiClosedBallDivisor_support_finite c R).toFinset
  have hterm (u : Complex) (hu : u ∈ s) :
      ‖(xiClosedBallDivisor c R u : Complex) / (z - u)‖ ≤
        (xiClosedBallDivisor c R u : Real) / r := by
    have hdiv_nonneg : 0 ≤ xiClosedBallDivisor c R u :=
      xiClosedBallDivisor_nonneg c R u
    have hweight_nonneg : 0 ≤ (xiClosedBallDivisor c R u : Real) := by
      exact_mod_cast hdiv_nonneg
    have hdist : r ≤ ‖z - u‖ := by
      simpa only [dist_eq_norm] using hsep u hu
    calc
      ‖(xiClosedBallDivisor c R u : Complex) / (z - u)‖ =
          (xiClosedBallDivisor c R u : Real) / ‖z - u‖ := by
            rw [norm_div, Complex.norm_intCast]
            rw [abs_of_nonneg hweight_nonneg]
      _ ≤ (xiClosedBallDivisor c R u : Real) / r :=
        div_le_div_of_nonneg_left hweight_nonneg hr hdist
  change ‖∑ u ∈ s, (xiClosedBallDivisor c R u : Complex) / (z - u)‖ ≤
    (∑ u ∈ s, (xiClosedBallDivisor c R u : Real)) / r
  calc
    ‖∑ u ∈ s, (xiClosedBallDivisor c R u : Complex) / (z - u)‖ ≤
        ∑ u ∈ s, ‖(xiClosedBallDivisor c R u : Complex) / (z - u)‖ :=
          norm_sum_le _ _
    _ ≤ ∑ u ∈ s, (xiClosedBallDivisor c R u : Real) / r := by
      apply Finset.sum_le_sum
      intro u hu
      exact hterm u hu
    _ = (∑ u ∈ s, (xiClosedBallDivisor c R u : Real)) / r := by
      rw [Finset.sum_div]

/-- Every source zero represented by the origin-centered factor owner at
radius `T + 2` lies in the corresponding symmetric-height family. -/
theorem xiClosedBallSourceZeros_zero_subset_finiteHeightZeros
    (T : Real) (hT : 0 ≤ T) :
    xiClosedBallSourceZeros (0 : Complex) (T + 2) ⊆
      finiteHeightZeros (T + 2) := by
  intro rho hrho
  rw [mem_finiteHeightZeros_iff]
  have hsupp : rho.1 ∈ (xiClosedBallDivisor (0 : Complex) (T + 2)).support :=
    (xiClosedBallDivisor_support_finite (0 : Complex) (T + 2)).mem_toFinset.mp
      ((mem_xiClosedBallSourceZeros_iff (0 : Complex) (T + 2) rho).mp hrho)
  have hball : rho.1 ∈ Metric.closedBall (0 : Complex) |T + 2| :=
    (xiClosedBallDivisor_mem_closedBall_and_xi_eq_zero_of_mem_support
      (0 : Complex) (T + 2) hsupp).1
  rw [Metric.mem_closedBall] at hball
  have hTtwo : 0 ≤ T + 2 := by linarith
  calc
    |rho.1.im| ≤ ‖rho.1‖ := Complex.abs_im_le_norm _
    _ = dist rho.1 0 := by rw [dist_zero_right]
    _ ≤ |T + 2| := hball
    _ = T + 2 := abs_of_nonneg hTtwo

/-- The mass of the origin-centered divisor is exactly the analytic
multiplicity mass of its same-owner source-zero reindexing. -/
theorem xiClosedBallDivisorMass_zero_eq_sourceMultiplicitySum (T : Real) :
    xiClosedBallDivisorMass (0 : Complex) (T + 2) =
      ∑ rho ∈ xiClosedBallSourceZeros (0 : Complex) (T + 2),
        (xiMultiplicity rho : Real) := by
  unfold xiClosedBallDivisorMass
  rw [← sum_xiClosedBallSourceZeros_eq_sum_support (0 : Complex) (T + 2)
    (fun u => (xiClosedBallDivisor (0 : Complex) (T + 2) u : Real))]
  apply Finset.sum_congr rfl
  intro rho hrho
  have hsupp : rho.1 ∈ (xiClosedBallDivisor (0 : Complex) (T + 2)).support :=
    (xiClosedBallDivisor_support_finite (0 : Complex) (T + 2)).mem_toFinset.mp
      ((mem_xiClosedBallSourceZeros_iff (0 : Complex) (T + 2) rho).mp hrho)
  have hball : rho.1 ∈ Metric.closedBall (0 : Complex) |T + 2| :=
    (xiClosedBallDivisor_mem_closedBall_and_xi_eq_zero_of_mem_support
      (0 : Complex) (T + 2) hsupp).1
  have hmult : (xiMultiplicity rho : Int) =
      xiClosedBallDivisor (0 : Complex) (T + 2) rho.1 := by
    simpa only [xiClosedBallDivisor] using
      xiMultiplicity_cast_eq_divisor_of_mem_closedBall rho hball
  exact_mod_cast hmult.symm

/-- Jensen's existing finite-height mass controls the full divisor mass of the
origin-centered factor owner used for a height-`T` rectangle. -/
theorem xiClosedBallDivisorMass_zero_le_finiteHeightMultiplicity
    (T : Real) (hT : 0 ≤ T) :
    xiClosedBallDivisorMass (0 : Complex) (T + 2) ≤
      (finiteHeightMultiplicity (T + 2) : Real) := by
  rw [xiClosedBallDivisorMass_zero_eq_sourceMultiplicitySum]
  calc
    (∑ rho ∈ xiClosedBallSourceZeros (0 : Complex) (T + 2),
        (xiMultiplicity rho : Real)) ≤
        ∑ rho ∈ finiteHeightZeros (T + 2), (xiMultiplicity rho : Real) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
            (xiClosedBallSourceZeros_zero_subset_finiteHeightZeros T hT)
          intro rho _ _
          exact Nat.cast_nonneg _
    _ = (finiteHeightMultiplicity (T + 2) : Real) := by
      simp only [finiteHeightMultiplicity, Nat.cast_sum]

/-- A zero-free tube forces every pole of the same origin-centered finite
factorization to remain at least its tube radius from the horizontal center. -/
theorem norm_xiClosedBallPrincipalSum_zero_le_finiteHeightMultiplicity_div_of_tube
    (T r t x : Real) (hT : 0 ≤ T) (hr : 0 < r)
    (htube : ∀ y : Real, ∀ z ∈ Metric.ball ((y : Complex) + t * Complex.I) r,
      completedRiemannXi z ≠ 0) :
    ‖xiClosedBallPrincipalSum (0 : Complex) (T + 2)
      ((x : Complex) + t * Complex.I)‖ ≤
      (finiteHeightMultiplicity (T + 2) : Real) / r := by
  apply le_trans
    (norm_xiClosedBall_principalSum_le_divisorMass_div (0 : Complex) (T + 2) r hr ?_)
  · exact div_le_div_of_nonneg_right
      (xiClosedBallDivisorMass_zero_le_finiteHeightMultiplicity T hT) hr.le
  · intro u hu
    by_contra hsep
    have hlt : dist ((x : Complex) + t * Complex.I) u < r := lt_of_not_ge hsep
    have huBall : u ∈ Metric.ball ((x : Complex) + t * Complex.I) r := by
      rw [Metric.mem_ball]
      simpa only [dist_comm] using hlt
    have hsupp : u ∈ (xiClosedBallDivisor (0 : Complex) (T + 2)).support :=
      (xiClosedBallDivisor_support_finite (0 : Complex) (T + 2)).mem_toFinset.mp hu
    exact (htube x u huBall)
      (xiClosedBallDivisor_mem_closedBall_and_xi_eq_zero_of_mem_support
        (0 : Complex) (T + 2) hsupp).2

/-- The explicit dyadic tube radius is its multiplicity-controlled first
branch: the fixed half-unit cap is inactive at every scale. -/
theorem dyadicXiHeightTubeRadius_eq_reciprocal (n : Nat) :
    dyadicXiHeightTubeRadius n =
      1 / (4 * (spectralMultiplicityConstant * (3 : Real) ^ (n + 1) + 2)) := by
  unfold dyadicXiHeightTubeRadius
  apply min_eq_left
  have hmass_nonneg :
      0 ≤ spectralMultiplicityConstant * (3 : Real) ^ (n + 1) :=
    mul_nonneg spectralMultiplicityConstant_nonneg (by positivity)
  have hden_pos :
      0 < 4 * (spectralMultiplicityConstant * (3 : Real) ^ (n + 1) + 2) := by
    positivity
  apply (div_le_iff₀ hden_pos).mpr
  nlinarith

/-- A height selected from the dyadic unit window has no more analytic xi
multiplicity in its factor ball than the next Jensen dyadic window. -/
theorem finiteHeightMultiplicity_selected_dyadic_le
    (n : Nat) {T : Real}
    (hT : T < (2 : Real) ^ (n + 2) + 1) :
    (finiteHeightMultiplicity (T + 2) : Real) ≤
      spectralMultiplicityConstant * (3 : Real) ^ (n + 1) := by
  have hbase : 4 ≤ (2 : Real) ^ (n + 2) := by
    have hpow : 1 ≤ (2 : Real) ^ n := one_le_pow₀ (by norm_num)
    calc
      4 = 4 * 1 := by norm_num
      _ ≤ 4 * (2 : Real) ^ n := by gcongr
      _ = (2 : Real) ^ (n + 2) := by
        rw [pow_add]
        ring
  have hheight : T + 2 ≤ (2 : Real) ^ (n + 3) := by
    calc
      T + 2 ≤ (2 : Real) ^ (n + 2) + 3 := by linarith
      _ ≤ 2 * (2 : Real) ^ (n + 2) := by nlinarith
      _ = (2 : Real) ^ (n + 3) := by
        have hindex : n + 3 = (n + 2) + 1 := by omega
        rw [hindex, pow_succ]
        ring
  have hmono := finiteHeightMultiplicity_mono hheight
  have hdyadic := finiteHeightMultiplicity_dyadic_le (n + 1)
  have hindex : (n + 1) + 2 = n + 3 := by omega
  calc
    (finiteHeightMultiplicity (T + 2) : Real) ≤
        (finiteHeightMultiplicity ((2 : Real) ^ (n + 3)) : Real) := by
          exact_mod_cast hmono
    _ ≤ spectralMultiplicityConstant * (3 : Real) ^ (n + 1) := by
      simpa only [hindex] using hdyadic

/-- The fully explicit finite-principal-part budget at dyadic height `n`.
It grows quadratically in the Jensen multiplicity scale, hence as `O(9^n)`.
-/
noncomputable def dyadicXiPrincipalBound (n : Nat) : Real :=
  4 * (spectralMultiplicityConstant * (3 : Real) ^ (n + 1)) *
    (spectralMultiplicityConstant * (3 : Real) ^ (n + 1) + 2)

/-- The dyadic two-sided tube producer controls the complete finite principal
part of the same origin-centered factor owner by an explicit `O(9^n)` bound.
The analytic cofactor term remains outside this theorem. -/
theorem exists_dyadic_quantitative_xiHeight_tubes_principal_bound (n : Nat) :
    ∃ T : Real, (2 : Real) ^ (n + 2) < T ∧
      T < (2 : Real) ^ (n + 2) + 1 ∧ xiHeightBoundaryAvoidsZeros T ∧
      (∀ x : Real, ∀ z ∈ Metric.ball ((x : Complex) + T * Complex.I)
        (dyadicXiHeightTubeRadius n), completedRiemannXi z ≠ 0) ∧
      (∀ x : Real, ∀ z ∈ Metric.ball ((x : Complex) - T * Complex.I)
        (dyadicXiHeightTubeRadius n), completedRiemannXi z ≠ 0) ∧
      (∀ x : Real, ‖xiClosedBallPrincipalSum (0 : Complex) (T + 2)
        ((x : Complex) + T * Complex.I)‖ ≤ dyadicXiPrincipalBound n) ∧
      ∀ x : Real, ‖xiClosedBallPrincipalSum (0 : Complex) (T + 2)
        ((x : Complex) - T * Complex.I)‖ ≤ dyadicXiPrincipalBound n := by
  obtain ⟨T, hbase_lt, hT, hboundary, hupper, hlower⟩ :=
    exists_dyadic_quantitative_xiHeightBoundaryAvoidsZeros_tubes n
  have hT_nonneg : 0 ≤ T := le_trans (by positivity) hbase_lt.le
  have hradius_pos : 0 < dyadicXiHeightTubeRadius n :=
    dyadicXiHeightTubeRadius_pos n
  have hmass := finiteHeightMultiplicity_selected_dyadic_le n hT
  have hbudget :
      (finiteHeightMultiplicity (T + 2) : Real) /
        dyadicXiHeightTubeRadius n ≤ dyadicXiPrincipalBound n := by
    calc
      (finiteHeightMultiplicity (T + 2) : Real) /
          dyadicXiHeightTubeRadius n ≤
          (spectralMultiplicityConstant * (3 : Real) ^ (n + 1)) /
            dyadicXiHeightTubeRadius n :=
              div_le_div_of_nonneg_right hmass hradius_pos.le
      _ = dyadicXiPrincipalBound n := by
        rw [dyadicXiHeightTubeRadius_eq_reciprocal]
        unfold dyadicXiPrincipalBound
        simp only [div_eq_mul_inv, one_mul, inv_inv]
        ring
  have hlower' : ∀ x : Real, ∀ z ∈ Metric.ball
      ((x : Complex) + ((-T : Real) : Complex) * Complex.I)
        (dyadicXiHeightTubeRadius n),
      completedRiemannXi z ≠ 0 := by
    intro x z hz
    have hcenter : ((x : Complex) + ((-T : Real) : Complex) * Complex.I) =
        (x : Complex) - T * Complex.I := by
      push_cast
      ring
    rw [hcenter] at hz
    exact hlower x z hz
  refine ⟨T, hbase_lt, hT, hboundary, hupper, hlower, ?_, ?_⟩
  · intro x
    exact (norm_xiClosedBallPrincipalSum_zero_le_finiteHeightMultiplicity_div_of_tube
      T (dyadicXiHeightTubeRadius n) T x hT_nonneg hradius_pos hupper).trans hbudget
  · intro x
    have hbottom :=
      (norm_xiClosedBallPrincipalSum_zero_le_finiteHeightMultiplicity_div_of_tube
        T (dyadicXiHeightTubeRadius n) (-T) x hT_nonneg hradius_pos hlower').trans hbudget
    have hcenter : ((x : Complex) + ((-T : Real) : Complex) * Complex.I) =
        (x : Complex) - T * Complex.I := by
      push_cast
      ring
    rw [hcenter] at hbottom
    exact hbottom

end C1XiQuantitativePrincipalBound
end Source
end ConnesWeilRH
