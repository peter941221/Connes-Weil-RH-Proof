import ConnesWeilRH.Dev.C1HealthyTestSpace
import ConnesWeilRH.Dev.C1XiCenterTwoArithmeticAssembly

/-!
# C1CenterTwoCriterionBridge - Gate 2 readback into the healthy criterion

Gate 2 identifies the complete same-owner Weil functional with the zero
spectral value.  This module transports that identity through the already
closed healthy `CC20TestSpace` object layer, reducing the finite-vanishing
criterion to an explicit spectral nonnegativity statement.

The spectral nonnegativity premise is intentionally not produced here. It is
the remaining RH-level sign/positive-trace input.
-/

namespace ConnesWeilRH
namespace Source
namespace C1CenterTwoCriterionBridge

open CCM25Concrete.CompactLogConvolution
open C1SameOwnerWeil
open C1SpectralWeil
open C1XiCenterTwoArithmeticAssembly

noncomputable section

/-- The center-`2` Gate 2 readback applied to one convolution square. -/
theorem qw_eq_spectralWeilValue_centerTwo (g : CompactLogTest) :
    C1SameOwnerWeil.qw g =
      C1SpectralWeil.spectralWeilValue g.convolutionSquare := by
  rw [C1SameOwnerWeil.qw_eq_psi_square]
  exact centerTwo_arithmetic_eq_spectral g.convolutionSquare

/-- The healthy finite-vanishing criterion is equivalent to nonnegativity of
the center-`2` spectral value on every square satisfying the same vanishings. -/
theorem healthyCriterionState_iff_all_vanishing_spectral_nonnegative
    (F : Finset CriticalVanishingPoint) :
    C1.healthyCriterionState F ↔
      ∀ g : CompactLogTest,
        CC20VanishesOn C1.healthyCC20TestSpace F g →
          0 ≤ C1SpectralWeil.spectralWeilValue g.convolutionSquare := by
  rw [C1.healthyCriterionState_iff_all_vanishing_qw_nonnegative]
  constructor
  · intro hqw g hvanishing
    rw [← qw_eq_spectralWeilValue_centerTwo g]
    exact hqw g hvanishing
  · intro hspectral g hvanishing
    rw [qw_eq_spectralWeilValue_centerTwo g]
    exact hspectral g hvanishing

end
end C1CenterTwoCriterionBridge
end Source
end ConnesWeilRH
