/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Dev.C1HealthyYoshidaClosedPrefix
import ConnesWeilRH.Dev.C1FourPointRowBWired2721
import ConnesWeilRH.Dev.C1RowBPrefixTransport2723
import ConnesWeilRH.Dev.C1RouteBRhoOwnerPackage3106

/-!
# Route-B prefix transport on the rho-dependent owner (record 3108)

The raw G8 package already controls square zeros in a closed ball whose radius
is `2^(tailStart+1) + 2 + dist 2 rho`.  The row-B prefix asks for zeros in the
height prefix `|Im z| < 64`.  This module supplies the missing geometric bridge:
the tail budget forces `tailStart >= 5`, so the G8 ball contains the height-64
prefix.  Target nodes outside the functional-equation orbit are handled by
the existing selected-owner target-zero theorem.

The result is owner-preserving: the same `pkg.g` is used for the target
identity, the square-zero control and the transported row-B prefix.
-/

namespace ConnesWeilRH
namespace Source
namespace C1RouteBPrefixOwnerTransport3108

open CC20YoshidaConvolution
open CC20YoshidaConvolution.CompactLogTest
open CC20YoshidaNearZeros
open CCM25Concrete.CompactLogConvolution
open CCM25Concrete.UnscaledYoshidaSelectedOwner
open C1HealthyYoshidaClosedPrefix
open C1HealthyYoshidaDetector
open C1HealthyYoshidaUnscaledOrbit
open C1HealthyYoshidaSpectralNegativity
open C1G8R0OrbitGeometry
open C1FourPointRowBWired2721
open C1FourPointSpectralPrefixTransport
open C1RouteBRhoOwnerPackage3106
open C1RowBPrefixTransport2723
open C1SpectralWeil
open C1TwoPointSpectralDecomposition
open CC20ZetaCounting
open scoped BigOperators

noncomputable section

/-- The rho-dependent G8 construction now chooses its dyadic tail index as
`max 5 tailStart`.  This exposes the lower bound needed by the row-B prefix
without adding it as an external owner premise. -/
theorem exists_rhoOwnerPackage_tailStart_ge_five3108
    (rho : sourceNontrivialZeroSet)
    (hoff : rho.1.re ≠ 1 / 2)
    (hright : (1 / 2 : Real) < rho.1.re) :
    ∃ pkg : RhoOwnerPackage3106 rho, 5 ≤ pkg.geometry.tailStart := by
  obtain ⟨g, geometry, htail⟩ :=
    exists_orbitG8Geometry_of_sourceNontrivialZero_right_tailStart_ge_five
      rho hoff hright
  have hhealthy : HealthyYoshidaDetectorData rho.1 g :=
    healthyDetectorData_of_orbitG8Geometry geometry hoff hright
  exact ⟨⟨g, geometry, hhealthy⟩, htail⟩

theorem package_hzero_prefix3108
    {rho : sourceNontrivialZeroSet} (pkg : RhoOwnerPackage3106 rho)
    (hoff : rho.1.re ≠ 1 / 2)
    (hright : (1 / 2 : Real) < rho.1.re)
    (htailStart : 5 ≤ pkg.geometry.tailStart) :
    ∀ z : sourceNontrivialZeroSet,
      z ∈ spectralHeightShellPrefix 6 →
      z.1 ∉ sourceFunctionalEquationOrbit rho.1 →
        laplaceAt pkg.g.convolutionSquare (z.1 - 1 / 2) = 0 := by
  intro z hz hnotOrbit
  have hzFinite : z ∈ finiteHeightZeros ((2 : Real) ^ 6) := by
    exact (spectralHeightShellPrefix_subset_finiteHeightZeros 6) hz
  have hball64 := mem_closedBall_about_anchor_of_mem_finiteHeightZeros
    rho.1 ((2 : Real) ^ 6) z hzFinite
  have hpow : (64 : Real) ≤ (2 : Real) ^ (pkg.geometry.tailStart + 1) := by
    have hpow' : (2 : Real) ^ 6 ≤
        (2 : Real) ^ (pkg.geometry.tailStart + 1) := by
      apply pow_right_mono₀
      · norm_num
      · omega
    norm_num at hpow'
    exact hpow'
  have hball : z.1 ∈ Metric.closedBall rho.1
      ((2 : Real) ^ (pkg.geometry.tailStart + 1) + 2 +
        dist (2 : Complex) rho.1) := by
    apply Metric.mem_closedBall.mpr
    have hball64' := Metric.mem_closedBall.mp hball64
    norm_num at hball64'
    linarith
  have hballFinset : z.1 ∈ sourceNontrivialZerosInClosedBallFinset rho.1
      ((2 : Real) ^ (pkg.geometry.tailStart + 1) + 2 +
        dist (2 : Complex) rho.1) :=
    mem_sourceNontrivialZerosInClosedBallFinset.mpr ⟨hball, z.2⟩
  have hmem : z.1 ∈
      sourceNontrivialZerosInClosedBallFinset rho.1
          ((2 : Real) ^ (pkg.geometry.tailStart + 1) + 2 +
            dist (2 : Complex) rho.1) ∪ (∅ : Finset Complex) :=
    Finset.mem_union_left _ hballFinset
  have htargetValues :
      ∀ w : FiniteMellinNode (healthyUnscaledTargetNodes rho.1),
        laplaceAt
            ((convolutionIterate pkg.geometry.base pkg.geometry.orbitIndex).convolution
              pkg.geometry.correction) w.1 =
          healthyUnscaledTargetValue rho.1 w :=
    pkg.geometry.raw_target_values
  by_cases htarget : z.1 ∈ healthyUnscaledTargetNodes rho.1
  · have hz0 := selectedOwner_laplaceAt_convolutionSquare_eq_zero_of_source_mem_target_not_mem_orbit
      pkg.geometry.base pkg.geometry.correction pkg.geometry.orbitIndex rho.1 rho.2
      hoff hright htargetValues z htarget hnotOrbit
    simpa [pkg.geometry.selected_owner_test] using hz0
  · have hz0 := pkg.geometry.square_zero_control ⟨z.1, hmem⟩ htarget
    simpa [pkg.geometry.selected_owner_test] using hz0

theorem package_rowBSpanPrefix3108
    {rho : sourceNontrivialZeroSet} (pkg : RhoOwnerPackage3106 rho)
    (hoff : rho.1.re ≠ 1 / 2)
    (hright : (1 / 2 : Real) < rho.1.re)
    (hIm : |rho.1.im| ≤ wiredRhoImCapRowB2721)
    (htailStart : 5 ≤ pkg.geometry.tailStart) :
    (∑ k ∈ Finset.range 6, ∑' z : spectralHeightShell k,
        spectralTerm
          (annihilatorDetectorSpanVector
            (fullFunctionalEquationOrbitAnnihilator pkg.g rho.1) pkg.g 24).convolutionSquare
          z.1).re ≤
      -((xiMultiplicity rho : Real) * 24 ^ 2) := by
  exact rowBSpanPrefix_of_imCap_2723 pkg.g rho hoff hIm
    (package_source_orbit_target3106 pkg)
    (package_hzero_prefix3108 pkg hoff hright htailStart)

/-- Unconditional owner-level row-B prefix transport.  The only remaining
row-B inputs are the hypothesis that the candidate zero is off the critical
line and the wired imaginary-part cap; the tail-index premise is discharged by
the construction above on the same owner. -/
theorem exists_rowBSpanPrefix_owner3108
    (rho : sourceNontrivialZeroSet)
    (hoff : rho.1.re ≠ 1 / 2)
    (hright : (1 / 2 : Real) < rho.1.re)
    (hIm : |rho.1.im| ≤ wiredRhoImCapRowB2721) :
    ∃ pkg : RhoOwnerPackage3106 rho,
      5 ≤ pkg.geometry.tailStart ∧
      (∑ k ∈ Finset.range 6, ∑' z : spectralHeightShell k,
        spectralTerm
          (annihilatorDetectorSpanVector
            (fullFunctionalEquationOrbitAnnihilator pkg.g rho.1) pkg.g 24).convolutionSquare
          z.1).re ≤
        -((xiMultiplicity rho : Real) * 24 ^ 2) := by
  obtain ⟨pkg, htailStart⟩ :=
    exists_rhoOwnerPackage_tailStart_ge_five3108 rho hoff hright
  refine ⟨pkg, htailStart, ?_⟩
  exact package_rowBSpanPrefix3108 pkg hoff hright hIm htailStart

end
end C1RouteBPrefixOwnerTransport3108
end Source
end ConnesWeilRH
