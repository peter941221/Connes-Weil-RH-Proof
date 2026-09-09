import ConnesWeilRH.Dev.C1HealthyYoshidaUnscaledOrbit
import ConnesWeilRH.Dev.C1P2BilateralProfile

/-!
# C1HealthyYoshidaCorrectionFamily - explicit selector/profile API

This leaf packages the existing finite-node residual-window interpolation
theorem as a parameterized correction selector and exposes the physical
bilateral profile of the selected owner.  It deliberately does not claim that
the selector is affine, canonical in a linear sense, positive, or sufficient
for the P2 gate.
-/

namespace ConnesWeilRH
namespace Source
namespace C1HealthyYoshidaCorrectionFamily

open CC20YoshidaConvolution
open CC20YoshidaConvolution.CompactLogTest
open CC20YoshidaNearZeros
open CCM25Concrete.CompactLogConvolution
open CCM25Concrete.UnscaledYoshidaSelectedOwner
open C1P2PrimePointMatching
open C1SameOwnerWeil
open C1P2BilateralProfile

noncomputable section

/-- A parameterized wrapper around the existing residual-window interpolation
existence theorem.  The fields record only the support and finite-node
readback already supplied by that theorem; no sign data is stored. -/
structure ResidualCorrectionFamily
    (nodes : Finset Complex) (lower upper : Real) where
  value : (FiniteMellinNode nodes → Complex) → CompactLogTest
  support : ∀ y, Function.support (value y).test ⊆ Set.Ioo lower upper
  laplaceAt_value : ∀ (y : FiniteMellinNode nodes → Complex)
    (z : FiniteMellinNode nodes),
    laplaceAt (value y) z.1 = y z

/-- Select one correction for each finite assignment by classical choice from
the already-proved residual-window interpolation theorem. -/
noncomputable def residualCorrectionFamily
    (nodes : Finset Complex) {lower upper : Real}
    (hlower : lower < 0) (hupper : 0 < upper) :
    ResidualCorrectionFamily nodes lower upper where
  value y :=
    Classical.choose
      (exists_residualWindow_correction nodes hlower hupper y)
  support y :=
    (Classical.choose_spec
      (exists_residualWindow_correction nodes hlower hupper y)).1
  laplaceAt_value y z :=
    (Classical.choose_spec
      (exists_residualWindow_correction nodes hlower hupper y)).2 z

@[simp] theorem residualCorrectionFamily_value_support
    (nodes : Finset Complex) {lower upper : Real}
    (hlower : lower < 0) (hupper : 0 < upper)
    (y : FiniteMellinNode nodes → Complex) :
    Function.support
        ((residualCorrectionFamily nodes hlower hupper).value y).test ⊆
      Set.Ioo lower upper := by
  exact (residualCorrectionFamily nodes hlower hupper).support y

@[simp] theorem residualCorrectionFamily_laplaceAt_value
    (nodes : Finset Complex) {lower upper : Real}
    (hlower : lower < 0) (hupper : 0 < upper)
    (y : FiniteMellinNode nodes → Complex)
    (z : FiniteMellinNode nodes) :
    laplaceAt ((residualCorrectionFamily nodes hlower hupper).value y) z.1 =
      y z := by
  exact (residualCorrectionFamily nodes hlower hupper).laplaceAt_value y z

/-- The physical profile seen by the selected same-owner square after a
residual correction is inserted.  Its argument `x` is a genuine physical
log-coordinate; it is not a Mellin-node value. -/
noncomputable def selectedOwnerBilateralProfile
    {nodes : Finset Complex} {lower upper : Real}
    (family : ResidualCorrectionFamily nodes lower upper)
    (base : CompactLogTest) (n : Nat)
    (y : FiniteMellinNode nodes → Complex) (x : Real) : Complex :=
  bilateralProfile
    (selectedOwner base (family.value y) n).convolutionSquare x

@[simp] theorem selectedOwnerBilateralProfile_eq
    {nodes : Finset Complex} {lower upper : Real}
    (family : ResidualCorrectionFamily nodes lower upper)
    (base : CompactLogTest) (n : Nat)
    (y : FiniteMellinNode nodes → Complex) (x : Real) :
    selectedOwnerBilateralProfile family base n y x =
      bilateralProfile
        (selectedOwner base (family.value y) n).convolutionSquare x := by
  rfl

/-- The finite visible-prime owner attached to the selected square for one
correction-family parameter. -/
noncomputable def selectedOwnerVisiblePrimeSet
    {nodes : Finset Complex} {lower upper : Real}
    (family : ResidualCorrectionFamily nodes lower upper)
    (base : CompactLogTest) (n : Nat)
    (y : FiniteMellinNode nodes → Complex) : Finset Nat :=
  globalPrimeIndexSet
    (selectedOwner base (family.value y) n).convolutionSquare

/-- The physical profile weighted by the exact finite-prime coefficients of
the same selected owner. -/
noncomputable def selectedOwnerVisiblePrimeProfileWeightedSum
    {nodes : Finset Complex} {lower upper : Real}
    (family : ResidualCorrectionFamily nodes lower upper)
    (base : CompactLogTest) (n : Nat)
    (y : FiniteMellinNode nodes → Complex) : Real :=
  ∑ m ∈ selectedOwnerVisiblePrimeSet family base n y,
    ArithmeticFunction.vonMangoldt m * (1 / Real.sqrt (m : Real)) *
      (selectedOwnerBilateralProfile family base n y (Real.log m)).re

theorem selectedOwnerFinitePrimeSum_eq_visibleProfileWeightedSum
    {nodes : Finset Complex} {lower upper : Real}
    (family : ResidualCorrectionFamily nodes lower upper)
    (base : CompactLogTest) (n : Nat)
    (y : FiniteMellinNode nodes → Complex) :
    finitePrimeSum
        (selectedOwner base (family.value y) n).convolutionSquare =
      selectedOwnerVisiblePrimeProfileWeightedSum family base n y := by
  simpa only [selectedOwnerVisiblePrimeProfileWeightedSum,
    selectedOwnerVisiblePrimeSet, selectedOwnerBilateralProfile] using
    (finitePrimeSum_eq_bilateralProfile_weighted_sum
      (selectedOwner base (family.value y) n).convolutionSquare)

end
end C1HealthyYoshidaCorrectionFamily
end Source
end ConnesWeilRH
