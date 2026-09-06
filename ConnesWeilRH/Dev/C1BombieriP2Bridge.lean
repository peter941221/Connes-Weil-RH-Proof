/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1BombieriSection8LambdaSign
import ConnesWeilRH.Dev.C1BombieriFiniteQuadraticBridge
import ConnesWeilRH.Dev.C1HealthyYoshidaSpectralNegativity
import ConnesWeilRH.Dev.C1SameOwnerWeil

/-!
# Line-B bridge to the healthy CompactLog P2 consumer

This leaf records the exact missing bridge for the Bombieri attack line.  The
finite Wirtinger chain already proves that a real reciprocal eigenvalue times
the nonzero weighted mass is nonnegative.  A Line-B producer must identify
that quantity with the same-owner Weil value of the selected healthy detector.
The bridge is therefore an equality field, not a stored positivity result.

No Bombieri-to-detector identification is asserted here, and no RH sign is
proved.  The final theorem is the healthy-detector SourceRH consumer once a
producer supplies this equality and the finite eigen-relation data for every
right-oriented off-line zero.
-/

namespace ConnesWeilRH
namespace Source
namespace C1BombieriP2Bridge

open C1BombieriSection8LambdaSign
open C1BombieriFiniteQuadraticBridge
open C1BombieriSection7Gamma
open C1BombieriSection7H
open C1HealthyYoshidaDetector
open C1HealthyYoshidaSpectralNegativity
open C1SameOwnerWeil
open CC20YoshidaConvolution
open CC20YoshidaConvolution.CompactLogTest
open CC20YoshidaNearZeros
open CCM25Concrete.CompactLogConvolution

noncomputable section

/-- Data that a Bombieri Line-B producer must supply for one selected
`CompactLogTest`.  The field `qw_eq_mass` is the owner-changing bridge; it is
an equality to be proved from the zero configuration, not a positivity field.
-/
structure BombieriP2BridgeData (g : CompactLogTest) where
  n : Nat
  t : Real
  ht : 0 < t
  gamma : Fin n -> Real
  z : Fin n -> Complex
  Lam : Complex
  lam : Real
  hz : z ≠ 0
  heigen :
    bombieriWOfZ gamma z =
      Lam • (bombieriHMatrix gamma t).mulVec (bombieriWOfZ gamma z)
  hrecip : (lam : Complex) * Lam = 1
  qw_eq_mass : C1SameOwnerWeil.qw g = lam * bombieriWMass gamma z

/-- Direct finite-matrix form of the Line-B producer contract.  The only
owner-changing datum is the explicit equality between the healthy-owner Weil
value and the real part of the finite weighted Hermitian form. -/
structure BombieriQuadraticP2BridgeData (g : CompactLogTest) where
  n : Nat
  t : Real
  ht : 0 < t
  gamma : Fin n -> Real
  z : Fin n -> Complex
  qw_eq_quadratic : C1SameOwnerWeil.qw g =
    (star (bombieriWOfZ gamma z) ⬝ᵥ
      (bombieriHMatrix gamma t).mulVec (bombieriWOfZ gamma z)).re

/-- The Bombieri finite chain supplies a nonnegative real for the mass
product. -/
theorem qw_nonneg_of_bombieriP2BridgeData
    {g : CompactLogTest} (p : BombieriP2BridgeData g) :
    0 <= C1SameOwnerWeil.qw g := by
  obtain ⟨S, hS, hmass⟩ := lambda_mass_eq_nonneg
    p.t p.ht p.gamma p.z p.Lam p.lam p.heigen p.hrecip
  rw [p.qw_eq_mass, hmass]
  exact hS

/-- The direct quadratic-form contract supplies the same healthy-owner sign
without requiring a separate eigenvalue or reciprocal field. -/
theorem qw_nonneg_of_bombieriQuadraticP2BridgeData
    {g : CompactLogTest} (p : BombieriQuadraticP2BridgeData g) :
    0 <= C1SameOwnerWeil.qw g := by
  obtain ⟨S, hS, hform⟩ :=
    bombieriHMatrix_quadraticForm_eq_ofReal_nonneg p.t p.ht p.gamma p.z
  rw [p.qw_eq_quadratic, hform]
  simpa using hS

/-- Pointwise healthy-detector consumer for the Line-B bridge.  The healthy
data is carried explicitly so the theorem is attached to the same B5 owner
as the detector-specific contradiction. -/
theorem qw_nonneg_of_healthyDetectorData_of_bombieriP2BridgeData
    {rho : Complex} {g : CompactLogTest}
    (_hdata : HealthyYoshidaDetectorData rho g)
    (p : BombieriP2BridgeData g) :
    0 <= C1SameOwnerWeil.qw g :=
  qw_nonneg_of_bombieriP2BridgeData p

/-- Healthy-detector wrapper for the direct finite-matrix contract. -/
theorem qw_nonneg_of_healthyDetectorData_of_bombieriQuadraticP2BridgeData
    {rho : Complex} {g : CompactLogTest}
    (_hdata : HealthyYoshidaDetectorData rho g)
    (p : BombieriQuadraticP2BridgeData g) :
    0 <= C1SameOwnerWeil.qw g :=
  qw_nonneg_of_bombieriQuadraticP2BridgeData p

/-- If a Line-B producer supplies bridge data for one healthy detector at each
right-oriented off-line zero, the existing contradiction consumer yields
`SourceRH`.  All analytic content remains in the producer premise. -/
theorem sourceRH_of_right_bombieriP2BridgeData
    (hbridge : ∀ rho : sourceNontrivialZeroSet,
      (1 / 2 : Real) < rho.1.re →
        ∃ g : CompactLogTest,
          HealthyYoshidaDetectorData rho.1 g ∧
            Nonempty (BombieriP2BridgeData g)) :
    RHDefinitionBridge.standard.SourceRH := by
  apply healthy_sourceRH_of_right_detector_specific_qw_nonneg
  intro rho hright
  obtain ⟨g, hdata, hp⟩ := hbridge rho hright
  obtain ⟨p⟩ := hp
  exact ⟨g, hdata, qw_nonneg_of_healthyDetectorData_of_bombieriP2BridgeData
    hdata p⟩

/-- Direct healthy-B5 exit for a producer of the finite Hermitian-form
contract. -/
theorem sourceRH_of_right_bombieriQuadraticP2BridgeData
    (hbridge : ∀ rho : sourceNontrivialZeroSet,
      (1 / 2 : Real) < rho.1.re →
        ∃ g : CompactLogTest,
          HealthyYoshidaDetectorData rho.1 g ∧
            Nonempty (BombieriQuadraticP2BridgeData g)) :
    RHDefinitionBridge.standard.SourceRH := by
  apply healthy_sourceRH_of_right_detector_specific_qw_nonneg
  intro rho hright
  obtain ⟨g, hdata, hp⟩ := hbridge rho hright
  obtain ⟨p⟩ := hp
  exact ⟨g, hdata,
    qw_nonneg_of_healthyDetectorData_of_bombieriQuadraticP2BridgeData hdata p⟩

end
end C1BombieriP2Bridge
end Source
end ConnesWeilRH
