import ConnesWeilRH.Dev.C1G8R0OrbitGeometry
import ConnesWeilRH.Dev.C1DetectorHeightCost3095
import ConnesWeilRH.Dev.C1DetectorNearCollisionCost3096
import ConnesWeilRH.Source.CCM25Concrete.UnscaledYoshidaSelectedOwner

/-! A same-owner rho-dependent package for the Route-B continuation.

The existing G8 construction already supplies an owner for each hypothetical
right-half off-line zero. This module packages the geometry and healthy data
with the very same `g`, and transports the raw source interpolation values to
the centered source test. It does not prove the semi-local gate or the three
cardinal pins. -/

namespace ConnesWeilRH.Source.C1RouteBRhoOwnerPackage3106

open CC20YoshidaConvolution
open CC20YoshidaConvolution.CompactLogTest
open CC20YoshidaNearZeros
open CC20YoshidaCriticalContraction
open CC20YoshidaCriticalContraction.CompactLogTest
open C1HealthyYoshidaDetector
open CCM25Concrete.CompactLogConvolution
open CCM25Concrete.UnscaledYoshidaSelectedOwner
open C1ExplicitFiniteNodeCorrection
open C1G8R0OrbitGeometry
open C1HealthyYoshidaUnscaledOrbit
open C1P2OrbitPhysicalProfileReadback
open C1DetectorHeightCost3095
open C1DetectorNearCollisionCost3096

noncomputable section

structure RhoOwnerPackage3106 (rho : sourceNontrivialZeroSet) where
  g : CompactLogTest
  geometry : OrbitG8Geometry rho g
  healthy : HealthyYoshidaDetectorData rho.1 g

theorem exists_rhoOwnerPackage3106
    (rho : sourceNontrivialZeroSet)
    (hoff : rho.1.re ≠ 1 / 2)
    (hright : (1 / 2 : Real) < rho.1.re) :
    Nonempty (RhoOwnerPackage3106 rho) := by
  obtain ⟨g, geometry, healthy⟩ :=
    exists_healthyOrbitG8Geometry_of_sourceNontrivialZero_right rho hoff hright
  exact ⟨⟨g, geometry, healthy⟩⟩

theorem package_same_owner_test3106
    {rho : sourceNontrivialZeroSet} (pkg : RhoOwnerPackage3106 rho) :
    pkg.g =
      (selectedOwner pkg.geometry.base pkg.geometry.correction
        pkg.geometry.orbitIndex).sourceTest :=
  pkg.geometry.selected_owner_test

theorem package_source_orbit_target3106
    {rho : sourceNontrivialZeroSet} (pkg : RhoOwnerPackage3106 rho)
    (w : FiniteMellinNode (sourceFunctionalEquationOrbit rho.1)) :
    laplaceAt pkg.g (w.1 - 1 / 2) =
      negativeSourceOrbitValue rho.1 w := by
  rw [pkg.geometry.selected_owner_test,
    selectedOwner_laplaceAt_sourceTest_centered]
  calc
    laplaceAt
          ((convolutionIterate pkg.geometry.base pkg.geometry.orbitIndex).convolution
            pkg.geometry.correction) w.1 =
        healthyUnscaledTargetValue rho.1
          ⟨w.1, Finset.mem_union_left _ w.2⟩ :=
      pkg.geometry.raw_target_values ⟨w.1, Finset.mem_union_left _ w.2⟩
    _ = negativeSourceOrbitValue rho.1 w :=
      healthyUnscaledTargetValue_of_mem_orbit rho.1 w.1 w.2

theorem package_support_bound3106
    {rho : sourceNontrivialZeroSet} (pkg : RhoOwnerPackage3106 rho) :
    Function.support pkg.g.test ⊆
      Set.Ioo (-((pkg.geometry.orbitIndex + 2 : Nat) : Real))
        (((pkg.geometry.orbitIndex + 2 : Nat) : Real)) :=
  pkg.geometry.support_bound

theorem package_height_cost3106
    {rho : sourceNontrivialZeroSet} (pkg : RhoOwnerPackage3106 rho) :
    |rho.1.im| ≤
      Real.exp (|rho.1.re - 1 / 2| *
        ((pkg.geometry.orbitIndex + 2 : Nat) : Real)) *
        derivOrderL1 1 pkg.g :=
  selected_detector_height_le pkg.geometry

theorem package_inverse_gap_cost3106
    {rho : sourceNontrivialZeroSet} (pkg : RhoOwnerPackage3106 rho)
    (hoff : rho.1.re ≠ 1 / 2) :
    1 / ((((pkg.geometry.orbitIndex + 2 : Nat) : Real) *
        Real.exp ((pkg.geometry.orbitIndex + 2 : Nat) : Real)) *
          |rho.1.re - 1 / 2|) ≤
      l1Mass (orbitRawFactor pkg.geometry) :=
  raw_factor_inverse_gap_mass pkg.geometry hoff

theorem package_has_healthy_data3106
    {rho : sourceNontrivialZeroSet} (pkg : RhoOwnerPackage3106 rho) :
    HealthyYoshidaDetectorData rho.1 pkg.g :=
  pkg.healthy

end
end ConnesWeilRH.Source.C1RouteBRhoOwnerPackage3106
