import ConnesWeilRH.Dev.C1DetectorHeightCost3095
import ConnesWeilRH.Dev.C1DetectorNearCollisionCost3096
import ConnesWeilRH.Dev.C1FourPointRowBWired2721

/-! Gate U for the row-B route.

The fixed stored row-B owner can only be used on a bounded height window.
This module packages the existing necessary-cost theorems at the row-B strip
scale and exposes the exact obligations for a rho-dependent continuation.
It is a scoped boundary result, not an RH theorem. -/

namespace ConnesWeilRH.Source.C1RouteBUniversalizationGate3105

open CC20YoshidaConvolution
open CC20YoshidaConvolution.CompactLogTest
open CC20YoshidaNearZeros
open CCM25Concrete.CompactLogConvolution
open CC20YoshidaCriticalContraction.CompactLogTest
open C1ExplicitFiniteNodeCorrection
open C1G8R0OrbitGeometry
open C1DetectorHeightCost3095
open C1DetectorNearCollisionCost3096
open C1HealthyYoshidaUnscaledOrbit
open C1P2OrbitPhysicalProfileReadback
open ConnesWeilRH.Dev

noncomputable section

def rowBStripAbsRe3105 : Real := 1

theorem fixed_owner_height_cap3105
    (f : CompactLogTest) (B : Real)
    (hB : 0 ≤ B) (hsupport : Function.support f.test ⊆ Set.Icc (-B) B)
    (s : Complex) (hre : |s.re| ≤ rowBStripAbsRe3105)
    (htarget : 1 ≤ ‖laplaceAt f s‖) :
    |s.im| ≤ Real.exp B * derivOrderL1 1 f := by
  simpa [rowBStripAbsRe3105] using
    unit_laplace_target_height_le f B rowBStripAbsRe3105 hB hsupport s hre htarget

theorem fixed_owner_unbounded_height_no_go3105
    (f : CompactLogTest) (B : Real)
    (hB : 0 ≤ B) (hsupport : Function.support f.test ⊆ Set.Icc (-B) B) :
    ¬ (∀ T : Real, ∃ s : Complex,
      |s.re| ≤ rowBStripAbsRe3105 ∧
      1 ≤ ‖laplaceAt f s‖ ∧ T < |s.im|) := by
  simpa [rowBStripAbsRe3105] using
    fixed_detector_unit_targets_not_unbounded f B rowBStripAbsRe3105 hB hsupport

theorem actual_geometry_height_cost3105
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) :
    |rho.1.im| ≤
      Real.exp (|rho.1.re - 1 / 2| * ((geometry.orbitIndex + 2 : Nat) : Real)) *
        derivOrderL1 1 g :=
  selected_detector_height_le geometry

theorem actual_geometry_inverse_gap_cost3105
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (hoff : rho.1.re ≠ 1 / 2) :
    1 / ((((geometry.orbitIndex + 2 : Nat) : Real) *
        Real.exp ((geometry.orbitIndex + 2 : Nat) : Real)) *
          |rho.1.re - 1 / 2|) ≤
      l1Mass (orbitRawFactor geometry) :=
  raw_factor_inverse_gap_mass geometry hoff

theorem fixed_rowB_caps_are_local3105
    (f : CompactLogTest) (B : Real)
    (hB : 0 ≤ B) (hsupport : Function.support f.test ⊆ Set.Icc (-B) B) :
    ¬ (∀ T : Real, ∃ s : Complex,
      |s.re| ≤ rowBStripAbsRe3105 ∧ 1 ≤ ‖laplaceAt f s‖ ∧ T < |s.im|) :=
  fixed_owner_unbounded_height_no_go3105 f B hB hsupport

end
end ConnesWeilRH.Source.C1RouteBUniversalizationGate3105
