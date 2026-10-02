import ConnesWeilRH.Dev.C1RouteAOwnerL1CoefficientBound2479
import ConnesWeilRH.Dev.C1RouteAOwnerLocalCurvature2475

/-  2480: weighted second-derivative interface for the actual owner.

The 2479 L1 budget bounds the owner and its first two derivatives.  This file
packages those three bounds through the existing weighted-curvature lemma, so
the cell-local consumer has a named owner-side analytic interface.  The
result is a formal baseline; it does not turn the MPFR smoke into a Lean
certificate or claim that the uniform bound is numerically sufficient. -/

namespace ConnesWeilRH.Dev

open scoped ContDiff

set_option linter.style.longLine false
set_option maxRecDepth 32768

noncomputable def ownerWeightedCurvatureL1_2480
    (sigma radius : ℝ) : ℝ :=
  weightedCurvature2348 sigma radius
    (ownerDerivativeBudgetL1_2479 0)
    (ownerDerivativeBudgetL1_2479 1)
    (ownerDerivativeBudgetL1_2479 2)

theorem ownerPanelWeightedSecondDerivBoundL1_2480
    (sigma radius coordinate : ℝ) (hcoordinate : |coordinate| ≤ radius) :
    ‖deriv (deriv (weightedFunction2348 sigma ownerPanelSumValue_2467)) coordinate‖ ≤
      ownerWeightedCurvatureL1_2480 sigma radius := by
  have hsmooth : ContDiff ℝ (2 : WithTop (WithTop ℕ)) ownerPanelSumValue_2467 := by
    have hfamily : ∀ i : Fin 30,
        ContDiff ℝ (2 : WithTop (WithTop ℕ))
          (fun x => externalFamilyValue2344 (ownerCoef_2463 i)
            (ownerMod_2463 i) (ownerRad_2463 i) x) := fun i =>
      (externalFamilyValue2344_contDiff _ _ _ (ownerRadPos_2465 i)).of_le
        (by decide)
    simpa only [ownerPanelSumValue_2467] using
      ContDiff.sum (s := Finset.univ) (fun i _ => hfamily i)
  have hzero : ‖ownerPanelSumValue_2467 coordinate‖ ≤
      ownerDerivativeBudgetL1_2479 0 := by
    simpa only [iteratedDeriv_zero] using
      ownerPanelIteratedDerivBudgetL1_2479 0 (by decide) coordinate
  have hfirst : ‖deriv ownerPanelSumValue_2467 coordinate‖ ≤
      ownerDerivativeBudgetL1_2479 1 := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
      ownerPanelIteratedDerivBudgetL1_2479 1 (by decide) coordinate
  have hsecond : ‖deriv (deriv ownerPanelSumValue_2467) coordinate‖ ≤
      ownerDerivativeBudgetL1_2479 2 := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
      ownerPanelIteratedDerivBudgetL1_2479 2 (by decide) coordinate
  unfold ownerWeightedCurvatureL1_2480
  exact weightedFunction2348_curvature_bound sigma ownerPanelSumValue_2467 hsmooth
    radius coordinate (ownerDerivativeBudgetL1_2479 0)
    (ownerDerivativeBudgetL1_2479 1) (ownerDerivativeBudgetL1_2479 2)
    hcoordinate hzero hfirst hsecond

theorem ownerPanelStripNorm_le_localCurvatureL1_2480
    (sigma radius step : ℝ) (cells : ℕ)
    (hradius : 0 ≤ radius)
    (hR : ∀ i : Fin 30, ownerRad_2463 i ≤ radius)
    (hstep : 0 < step)
    (hgrid : (cells : ℝ) * step = 2 * radius) :
    stripNorm sigma ownerPanelSumValue_2467 ≤
      compositeNodeUpper2347
        (ownerPanelNodeUpper2471 sigma radius step) step cells +
        localCurvatureRemainder2474
          (fun _ => ownerWeightedCurvatureL1_2480 sigma radius) step cells := by
  apply ownerPanelStripNorm_le_localCurvature2475 sigma radius step cells
    (fun _ => ownerWeightedCurvatureL1_2480 sigma radius) hradius hR hstep hgrid
  intro index hindex coordinate hcoordinate
  apply ownerPanelWeightedSecondDerivBoundL1_2480 sigma radius coordinate
  have hleft : -radius + (index : ℝ) * step ≤ coordinate := hcoordinate.1
  have hright : coordinate ≤ -radius + ((index + 1 : ℕ) : ℝ) * step := by
    simpa only [Nat.cast_add, Nat.cast_one] using hcoordinate.2
  have hindexnonneg : 0 ≤ (index : ℝ) := Nat.cast_nonneg index
  have hstepnonneg : 0 ≤ step := hstep.le
  have hindexsucc : (index : ℝ) + 1 ≤ (cells : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.mp hindex)
  have hindexstep : ((index : ℝ) + 1) * step ≤ (cells : ℝ) * step :=
    mul_le_mul_of_nonneg_right hindexsucc hstepnonneg
  apply abs_le.mpr
  constructor
  · have hidxprod : 0 ≤ (index : ℝ) * step :=
      mul_nonneg hindexnonneg hstepnonneg
    linarith
  · calc
      coordinate ≤ -radius + ((index : ℝ) + 1) * step := by
        simpa only [Nat.cast_add, Nat.cast_one] using hright
      _ ≤ -radius + (cells : ℝ) * step := by linarith
      _ = radius := by rw [hgrid]; ring
end ConnesWeilRH.Dev
