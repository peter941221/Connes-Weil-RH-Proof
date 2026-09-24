import ConnesWeilRH.Dev.C1HealthyYoshidaCorrectionFamily

namespace ConnesWeilRH
namespace Source
namespace C1PhysicalDerivativeControlledCorrection

open CC20YoshidaConvolution
open CC20YoshidaConvolution.CompactLogTest
open CC20YoshidaNearZeros
open CCM25Concrete.CompactLogConvolution
open CCM25Concrete.UnscaledYoshidaSelectedOwner
open C1HealthyYoshidaCorrectionFamily

noncomputable section

/-!
# C1PhysicalDerivativeControlledCorrection

This is the first Route-A selector that carries physical derivative data.
The derivative cost is a genuine Schwartz seminorm of the selected
correction's derivative; it is not the signed residual budget and does not
assume the desired gate inequality.
-/

structure SelectedPhysicalDerivativeCorrection
    (nodes : Finset Complex) (lower upper : Real) where
  value : (FiniteMellinNode nodes → Complex) → CompactLogTest
  support : ∀ y, Function.support (value y).test ⊆ Set.Ioo lower upper
  laplaceAt_value : ∀ (y : FiniteMellinNode nodes → Complex)
    (z : FiniteMellinNode nodes),
    laplaceAt (value y) z.1 = y z
  derivativeCost : (FiniteMellinNode nodes → Complex) → Real
  derivativeCost_nonneg : ∀ y, 0 ≤ derivativeCost y
  derivative_bound : ∀ (y : FiniteMellinNode nodes → Complex) (x : Real),
    ‖deriv ((value y).test : Real → Complex) x‖ ≤ derivativeCost y

noncomputable def selectedPhysicalDerivativeCorrection
    (nodes : Finset Complex) {lower upper : Real}
    (hlower : lower < 0) (hupper : 0 < upper) :
    SelectedPhysicalDerivativeCorrection nodes lower upper where
  value y := (residualCorrectionFamily nodes hlower hupper).value y
  support y := (residualCorrectionFamily nodes hlower hupper).support y
  laplaceAt_value y z :=
    (residualCorrectionFamily nodes hlower hupper).laplaceAt_value y z
  derivativeCost y :=
    SchwartzMap.seminorm ℂ 0 0
      (SchwartzMap.derivCLM ℂ ℂ
        ((residualCorrectionFamily nodes hlower hupper).value y).test)
  derivativeCost_nonneg y := by
    positivity
  derivative_bound y x := by
    let d : SchwartzMap ℝ ℂ := SchwartzMap.derivCLM ℂ ℂ
      ((residualCorrectionFamily nodes hlower hupper).value y).test
    have h := SchwartzMap.norm_le_seminorm ℂ d x
    simpa [d, SchwartzMap.derivCLM_apply] using h

@[simp] theorem selectedPhysicalDerivativeCorrection_value
    (nodes : Finset Complex) {lower upper : Real}
    (hlower : lower < 0) (hupper : 0 < upper)
    (y : FiniteMellinNode nodes → Complex) :
    (selectedPhysicalDerivativeCorrection nodes hlower hupper).value y =
      (residualCorrectionFamily nodes hlower hupper).value y := by
  rfl

theorem selectedPhysicalDerivativeCorrection_support
    (nodes : Finset Complex) {lower upper : Real}
    (hlower : lower < 0) (hupper : 0 < upper)
    (y : FiniteMellinNode nodes → Complex) :
    Function.support
        ((selectedPhysicalDerivativeCorrection nodes hlower hupper).value y).test ⊆
      Set.Ioo lower upper := by
  exact (selectedPhysicalDerivativeCorrection nodes hlower hupper).support y

theorem selectedPhysicalDerivativeCorrection_laplaceAt
    (nodes : Finset Complex) {lower upper : Real}
    (hlower : lower < 0) (hupper : 0 < upper)
    (y : FiniteMellinNode nodes → Complex)
    (z : FiniteMellinNode nodes) :
    laplaceAt
        ((selectedPhysicalDerivativeCorrection nodes hlower hupper).value y) z.1 =
      y z := by
  exact (selectedPhysicalDerivativeCorrection nodes hlower hupper).laplaceAt_value y z

theorem selectedPhysicalDerivativeCorrection_derivative_bound
    (nodes : Finset Complex) {lower upper : Real}
    (hlower : lower < 0) (hupper : 0 < upper)
    (y : FiniteMellinNode nodes → Complex) (x : Real) :
    ‖deriv
        (((selectedPhysicalDerivativeCorrection nodes hlower hupper).value y).test :
          Real → Complex) x‖ ≤
      (selectedPhysicalDerivativeCorrection nodes hlower hupper).derivativeCost y := by
  exact (selectedPhysicalDerivativeCorrection nodes hlower hupper).derivative_bound y x

end
end C1PhysicalDerivativeControlledCorrection
end Source
end ConnesWeilRH
