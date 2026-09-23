/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.RHDefinition
import ConnesWeilRH.Dev.C1G8R0OrbitGeometry
import ConnesWeilRH.Dev.C1C3CarrierTransport
import ConnesWeilRH.Dev.C1OrbitWindowExitComposition
import ConnesWeilRH.Dev.C1P2DirectSemiLocalGate
import ConnesWeilRH.Dev.C1B5TargetSatisfiability
import ConnesWeilRH.Dev.C1GateMatrixRepresentation
import ConnesWeilRH.Dev.C1OrbitWindowSemiLocalGate
import ConnesWeilRH.Dev.C1SameOwnerWeil
import ConnesWeilRH.Dev.C1HealthyYoshidaDetector
import ConnesWeilRH.Dev.C1HealthyYoshidaSpectralNegativity
import ConnesWeilRH.Dev.C1LaneRNarrowArch
import ConnesWeilRH.Dev.C1LaneRD3Root
import ConnesWeilRH.Dev.C1LocalConfigurationDomination

/-!
# C1: Pinned Orbit Mainline Exit to Mathlib RiemannHypothesis (Record 1903)

This module completes Step 3 of the finite-orbit mainline campaign:
1. Proves triple-vanishing preservation under linear combinations (`spanObj`),
   showing that the two-span combination between `narrowArchRoot` and the pinned
   detector `g` vanishes at `{0, 1/2, 1}`.
2. Combines the Step 2 gate inequality `orbitWindowSemiLocalGate ≤ 0` with the
   triple-vanishing bridge to establish `0 ≤ qw(g_opt)` on the optimal two-span test.
3. Formulates the master exit theorems directly connecting semi-local gate
   certificates and pinned geometry witnesses to Mathlib's canonical
   `_root_.RiemannHypothesis` via `SourceRH`.
4. Formulates the exact contradiction closure between detector negativity and
   gate nonpositivity.
-/

set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace ConnesWeilRH
namespace Source
namespace C1PinnedOrbitExit

open MeasureTheory
open CC20YoshidaConvolution
open CC20YoshidaConvolution.CompactLogTest
open CC20YoshidaNearZeros
open CCM25Concrete.CompactLogConvolution
open CCM25Concrete.UnscaledYoshidaSelectedOwner
open C1G8R0OrbitGeometry
open ConnesWeilRH.Dev.C1C3CarrierTransport
open C1GateMatrixRepresentation
open C1OrbitWindowSemiLocalGate
open C1SameOwnerWeil
open C1HealthyYoshidaDetector
open C1HealthyYoshidaSpectralNegativity
open C1B5TargetSatisfiability
open C1LaneRNarrowArch
open C1LaneRD3Root
open C1LocalConfigurationDomination
open scoped BigOperators

noncomputable section

/-- Linearity of bilateral Laplace transform on a two-dimensional test span. -/
theorem laplaceAt_spanObj_two
    (u v : CompactLogTest) (c0 c1 : Real) (s : ℂ) :
    laplaceAt (spanObj ![u, v] ![c0, c1]) s =
      (c0 : ℂ) * laplaceAt u s + (c1 : ℂ) * laplaceAt v s := by
  unfold laplaceAt
  have htest (x : ℝ) :
      (exponentialWeight (spanObj ![u, v] ![c0, c1]) s).test x =
        (c0 : ℂ) * (exponentialWeight u s).test x +
        (c1 : ℂ) * (exponentialWeight v s).test x := by
    simp only [exponentialWeight_apply, spanObj_apply]
    rw [Fin.sum_univ_two]
    dsimp
    ring
  have hcong :
      (∫ x : ℝ, (exponentialWeight (spanObj ![u, v] ![c0, c1]) s).test x) =
      ∫ x : ℝ,
        ((c0 : ℂ) * (exponentialWeight u s).test x +
         (c1 : ℂ) * (exponentialWeight v s).test x) := by
    exact integral_congr_ae (Filter.Eventually.of_forall htest)
  rw [hcong]
  have hu_int : Integrable (fun x : ℝ => (exponentialWeight u s).test x) :=
    (exponentialWeight u s).test.integrable
  have hv_int : Integrable (fun x : ℝ => (exponentialWeight v s).test x) :=
    (exponentialWeight v s).test.integrable
  have hu_scaled : Integrable (fun x : ℝ => (c0 : ℂ) * (exponentialWeight u s).test x) :=
    hu_int.const_mul (c0 : ℂ)
  have hv_scaled : Integrable (fun x : ℝ => (c1 : ℂ) * (exponentialWeight v s).test x) :=
    hv_int.const_mul (c1 : ℂ)
  rw [integral_add hu_scaled hv_scaled]
  rw [integral_const_mul, integral_const_mul]

/-- The triple vanishing property is preserved under arbitrary two-dimensional linear combinations. -/
theorem vanishesOn_cc20Triple_spanObj_two
    (u v : CompactLogTest) (c0 c1 : Real)
    (hu : CC20VanishesOn C1.healthyCC20TestSpace cc20TripleFiniteVanishingSet u)
    (hv : CC20VanishesOn C1.healthyCC20TestSpace cc20TripleFiniteVanishingSet v) :
    CC20VanishesOn C1.healthyCC20TestSpace cc20TripleFiniteVanishingSet
      (spanObj ![u, v] ![c0, c1]) := by
  intro p hp
  rw [C1.healthyMellinReadoff]
  rw [laplaceAt_spanObj_two]
  have hu_zero : laplaceAt u (criticalVanishingPointValue p) = 0 := by
    have h := hu p hp
    rwa [C1.healthyMellinReadoff] at h
  have hv_zero : laplaceAt v (criticalVanishingPointValue p) = 0 := by
    have h := hv p hp
    rwa [C1.healthyMellinReadoff] at h
  rw [hu_zero, hv_zero, mul_zero, mul_zero, add_zero]

/-- The optimal two-span combination between `narrowArchRoot` and any healthy detector `g`
    strictly vanishes on the triple vanishing set `{0, 1/2, 1}`. -/
theorem pinned_twoSpan_optimal_vanishesOn_cc20Triple
    {rho : ℂ} {g : CompactLogTest}
    (hdata : HealthyYoshidaDetectorData rho g)
    (c0 c1 : Real) :
    CC20VanishesOn C1.healthyCC20TestSpace cc20TripleFiniteVanishingSet
      (spanObj ![narrowArchRoot, g] ![c0, c1]) := by
  apply vanishesOn_cc20Triple_spanObj_two
  · simpa [narrowArchRoot] using tripleVanishingRoot_vanishesOn_cc20Triple
      (Dev.M2Width.wideTest narrowArchBaseWidth narrowArchBaseWidth_pos)
  · exact hdata.vanishesOnF

/-- Master Step 3 Theorem (Unconditional Two-Span Nonnegative Weil Energy):
    For any healthy detector `g` with support in `Ioo (-B) B` (`1 ≤ B`) and any frequency `γ`,
    the optimal two-span combination achieves a nonnegative same-owner Weil energy:
    `0 ≤ qw(g_opt)`. -/
theorem pinned_twoSpan_optimal_qw_nonneg
    {rho : ℂ} {g : CompactLogTest}
    (hdata : HealthyYoshidaDetectorData rho g)
    (B : Real) (hB : 1 ≤ B)
    (hsupport : Function.support g.test ⊆ Set.Ioo (-B) B)
    (γ : Real) :
    0 ≤ C1SameOwnerWeil.qw
      (spanObj ![narrowArchRoot, g]
        ![(1 : Real), -(ICgate (narrowArchRoot.involution.convolution g) / ICgate g.convolutionSquare)]) := by
  have hgate := orbitWindowSemiLocalGate_of_pinned_geometry_simplified hdata B hB hsupport γ
  have hvanish := pinned_twoSpan_optimal_vanishesOn_cc20Triple hdata (1 : Real)
    (-(ICgate (narrowArchRoot.involution.convolution g) / ICgate g.convolutionSquare))
  exact qw_nonneg_of_orbitWindowSemiLocalGate _ hvanish hgate

/-- Contradiction Principle: A single test function cannot simultaneously satisfy
    `HealthyYoshidaDetectorData` (which forces `qw < 0`) and `orbitWindowSemiLocalGate`
    (which forces `0 ≤ qw`). -/
theorem false_of_healthyDetectorData_and_orbitWindowSemiLocalGate
    {rho : ℂ} {g : CompactLogTest}
    (hdata : HealthyYoshidaDetectorData rho g)
    (hgate : orbitWindowSemiLocalGate g) :
    False := by
  have hnonneg : 0 ≤ C1SameOwnerWeil.qw g :=
    qw_nonneg_of_orbitWindowSemiLocalGate g hdata.vanishesOnF hgate
  have hneg : C1SameOwnerWeil.qw g < 0 :=
    qw_neg_of_healthyDetectorData hdata
  linarith

/-- Top-Level Master Exit 1: The orbit-window semi-local gate on every healthy
    detector directly proves Mathlib's canonical `_root_.RiemannHypothesis`. -/
theorem riemannHypothesis_of_orbitWindowSemiLocalGate
    (hgate : ∀ rho : sourceNontrivialZeroSet,
      (1 / 2 : Real) < rho.1.re →
        ∀ g : CompactLogTest,
          HealthyYoshidaDetectorData rho.1 g →
          orbitWindowSemiLocalGate g) :
    _root_.RiemannHypothesis := by
  exact RHDefinitionBridge.standard_source_rh_iff_mathlib.mp
    (C1OrbitWindowExitComposition.sourceRH_of_orbitWindowSemiLocalGate hgate)

/-- Top-Level Master Exit 2: Exhibiting an `OrbitG8Geometry` satisfying the semi-local
    gate for every right-hand zero directly proves Mathlib's canonical `_root_.RiemannHypothesis`. -/
theorem riemannHypothesis_of_right_orbitGeometry_orbitWindowSemiLocalGate
    (hproducer : ∀ rho : sourceNontrivialZeroSet,
      (1 / 2 : Real) < rho.1.re →
        ∃ g : CompactLogTest,
          ∃ geometry : OrbitG8Geometry rho g,
            orbitWindowSemiLocalGate g) :
    _root_.RiemannHypothesis := by
  exact RHDefinitionBridge.standard_source_rh_iff_mathlib.mp
    (C1P2DirectSemiLocalGate.sourceRH_of_right_orbitGeometry_orbitWindowSemiLocalGate hproducer)

/-- Top-Level Master Exit 3: Detector-specific nonnegativity `0 ≤ qw(g)` on every
    healthy detector directly proves Mathlib's canonical `_root_.RiemannHypothesis`. -/
theorem riemannHypothesis_of_right_detector_specific_qw_nonneg
    (hsemiLocal : ∀ rho : sourceNontrivialZeroSet,
      (1 / 2 : Real) < rho.1.re →
        ∃ g : CompactLogTest,
          HealthyYoshidaDetectorData rho.1 g ∧
            0 ≤ C1SameOwnerWeil.qw g) :
    _root_.RiemannHypothesis := by
  exact RHDefinitionBridge.standard_source_rh_iff_mathlib.mp
    (healthy_sourceRH_of_right_detector_specific_qw_nonneg hsemiLocal)

/-- Master Exit from Pinned Geometry and Gate Absorption: If the pinned geometry produced
    by Step 1 satisfies the semi-local gate, Mathlib's `_root_.RiemannHypothesis` holds. -/
theorem riemannHypothesis_of_pinned_geometry_absorption
    (habsorb : ∀ rho : sourceNontrivialZeroSet,
      (1 / 2 : Real) < rho.1.re →
        ∃ n0 : Nat, ∃ g : CompactLogTest, ∃ geometry : OrbitG8Geometry rho g,
          orbitWindowSemiLocalGate g) :
    _root_.RiemannHypothesis := by
  apply riemannHypothesis_of_right_orbitGeometry_orbitWindowSemiLocalGate
  intro rho hright
  obtain ⟨_n0, g, geometry, hgate⟩ := habsorb rho hright
  exact ⟨g, geometry, hgate⟩

end
end C1PinnedOrbitExit
end Source
end ConnesWeilRH
