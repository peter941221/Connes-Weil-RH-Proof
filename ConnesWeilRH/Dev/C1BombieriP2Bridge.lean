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
open C1BombieriSection8TotalAssembly
open C1BombieriFiniteQuadraticBridge
open C1BombieriSection7Gamma
open C1BombieriSection7H
open C1HealthyYoshidaDetector
open C1HealthyYoshidaSpectralNegativity
open C1SpectralWeil
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

/-- The direct quadratic socket is a conservative re-expression of the
Line-B mass socket: the finite eigen-relation identifies `lam * mass` with
the complex quadratic form, and taking real parts supplies the required
owner-changing equality.  This is an interface adapter, not a new producer.
-/
noncomputable def BombieriQuadraticP2BridgeData.of_bombieriP2BridgeData
    {g : CompactLogTest} (p : BombieriP2BridgeData g) :
    BombieriQuadraticP2BridgeData g := by
  obtain hform := lambda_mass_eq_bombieriHMatrix_quadraticForm
    p.t p.gamma p.z p.Lam p.lam p.heigen p.hrecip
  have hreal := congrArg Complex.re hform
  refine
    { n := p.n, t := p.t, ht := p.ht, gamma := p.gamma, z := p.z
      qw_eq_quadratic := ?_ }
  rw [p.qw_eq_mass]
  simpa [Complex.mul_re] using hreal

/-- Residual-aware direct quadratic-form contract.  The finite Hermitian form
is only the main term: the producer keeps an explicit real residual, bounds
its absolute value by `tailBound`, and proves that this tail budget is no
larger than the finite quadratic form.  No `qw` sign is stored as data. -/
structure BombieriQuadraticResidualP2BridgeData (g : CompactLogTest) where
  n : Nat
  t : Real
  ht : 0 < t
  gamma : Fin n -> Real
  z : Fin n -> Complex
  residual : Real
  tailBound : Real
  qw_eq_quadratic_sub_residual : C1SameOwnerWeil.qw g =
    (star (bombieriWOfZ gamma z) ⬝ᵥ
      (bombieriHMatrix gamma t).mulVec (bombieriWOfZ gamma z)).re - residual
  residual_abs_le : |residual| ≤ tailBound
  tailBound_le_quadratic : tailBound ≤
    (star (bombieriWOfZ gamma z) ⬝ᵥ
      (bombieriHMatrix gamma t).mulVec (bombieriWOfZ gamma z)).re

/-- A residual contract whose residual is the actual high-shell remainder of
the same healthy `CompactLog` owner.  The only still-producer-facing field is
the domination of that shell norm by the finite quadratic main term. -/
structure BombieriQuadraticSpectralTailP2BridgeData (g : CompactLogTest) where
  n : Nat
  t : Real
  ht : 0 < t
  gamma : Fin n -> Real
  z : Fin n -> Complex
  N : Nat
  qw_eq_quadratic_sub_spectralTail : C1SameOwnerWeil.qw g =
    (star (bombieriWOfZ gamma z) ⬝ᵥ
      (bombieriHMatrix gamma t).mulVec (bombieriWOfZ gamma z)).re -
      (∑' m : Nat, ∑' rho : spectralHeightShell (m + N),
        spectralTerm g.convolutionSquare rho.1).re
  tailBound_le_quadratic :
    (∑' m : Nat, ∑' rho : spectralHeightShell (m + N),
      ‖spectralTerm g.convolutionSquare rho.1‖) ≤
      (star (bombieriWOfZ gamma z) ⬝ᵥ
        (bombieriHMatrix gamma t).mulVec (bombieriWOfZ gamma z)).re

/-- In the nonzero reciprocal-eigenvector branch, the finite Hermitian main
term has a strictly positive real value.  This supplies the margin that a
future same-owner tail producer must beat. -/
theorem bombieriHMatrix_quadraticForm_pos_of_eigen
    {n : Nat} (t : Real) (ht : 0 < t) (gamma : Fin n -> Real)
    (z : Fin n -> Complex) (Lam : Complex) (lam : Real) (hz : z ≠ 0)
    (heigen : bombieriWOfZ gamma z =
      Lam • (bombieriHMatrix gamma t).mulVec (bombieriWOfZ gamma z))
    (hrecip : (lam : Complex) * Lam = 1) :
    0 < (star (bombieriWOfZ gamma z) ⬝ᵥ
      (bombieriHMatrix gamma t).mulVec (bombieriWOfZ gamma z)).re := by
  have hlam : 0 < lam := lambda_pos_of_eigen t ht gamma z Lam lam hz heigen hrecip
  have hmass : 0 < bombieriWMass gamma z :=
    bombieriWMass_pos_of_ne_zero gamma z hz
  have hprod : 0 < lam * bombieriWMass gamma z := mul_pos hlam hmass
  have hform :
      (star (bombieriWOfZ gamma z) ⬝ᵥ
        (bombieriHMatrix gamma t).mulVec (bombieriWOfZ gamma z)).re =
        lam * bombieriWMass gamma z := by
    calc
      (star (bombieriWOfZ gamma z) ⬝ᵥ
          (bombieriHMatrix gamma t).mulVec (bombieriWOfZ gamma z)).re =
          (bombieriKstarGram t gamma z).re := by
            rw [bombieriHMatrix_quadraticForm_eq_KstarGram]
      _ = ((lam : Complex) * Complex.ofReal (bombieriWMass gamma z)).re := by
            rw [lambda_mass_eq_KstarGram t gamma z Lam lam heigen hrecip]
      _ = lam * bombieriWMass gamma z := by
            simp [Complex.mul_re]
  rw [hform]
  exact hprod

/-- The same nonzero reciprocal-eigenvector branch admits a shell cutoff whose
spectral norm tail is strictly smaller than the finite Bombieri main term. -/
theorem exists_spectralTail_normTail_lt_bombieriQuadraticForm_of_eigen
    (F : CompactLogTest) {n : Nat} (t : Real) (ht : 0 < t) (gamma : Fin n -> Real)
    (z : Fin n -> Complex) (Lam : Complex) (lam : Real) (hz : z ≠ 0)
    (heigen : bombieriWOfZ gamma z =
      Lam • (bombieriHMatrix gamma t).mulVec (bombieriWOfZ gamma z))
    (hrecip : (lam : Complex) * Lam = 1) :
    ∃ N : Nat,
      (∑' m : Nat, ∑' rho : spectralHeightShell (m + N),
        ‖spectralTerm F rho.1‖) <
      (star (bombieriWOfZ gamma z) ⬝ᵥ
        (bombieriHMatrix gamma t).mulVec (bombieriWOfZ gamma z)).re := by
  have hmain := bombieriHMatrix_quadraticForm_pos_of_eigen
    t ht gamma z Lam lam hz heigen hrecip
  exact exists_spectralHeightShell_normTail_lt F hmain

/-- Turn the explicit same-owner spectral tail into the generic residual
socket.  The two-sided residual estimate is supplied by the shell partition,
not stored as a positivity conclusion. -/
noncomputable def BombieriQuadraticSpectralTailP2BridgeData.toResidual
    {g : CompactLogTest} (p : BombieriQuadraticSpectralTailP2BridgeData g) :
    BombieriQuadraticResidualP2BridgeData g := by
  refine
    { n := p.n, t := p.t, ht := p.ht, gamma := p.gamma, z := p.z
      residual :=
        (∑' m : Nat, ∑' rho : spectralHeightShell (m + p.N),
          spectralTerm g.convolutionSquare rho.1).re
      tailBound :=
        ∑' m : Nat, ∑' rho : spectralHeightShell (m + p.N),
          ‖spectralTerm g.convolutionSquare rho.1‖
      qw_eq_quadratic_sub_residual := p.qw_eq_quadratic_sub_spectralTail
      residual_abs_le := ?_
      tailBound_le_quadratic := p.tailBound_le_quadratic }
  exact spectralHeightShellTail_abs_re_le_normTail g.convolutionSquare p.N

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

/-- The residual-aware direct quadratic contract yields the same-owner sign by
subtracting an explicitly dominated tail from the finite nonnegative form. -/
theorem qw_nonneg_of_bombieriQuadraticResidualP2BridgeData
    {g : CompactLogTest} (p : BombieriQuadraticResidualP2BridgeData g) :
    0 <= C1SameOwnerWeil.qw g := by
  obtain ⟨S, hS, hform⟩ :=
    bombieriHMatrix_quadraticForm_eq_ofReal_nonneg p.t p.ht p.gamma p.z
  have hformReal :
      (star (bombieriWOfZ p.gamma p.z) ⬝ᵥ
          (bombieriHMatrix p.gamma p.t).mulVec (bombieriWOfZ p.gamma p.z)).re = S := by
    rw [hform]
    simp
  have htail : 0 ≤ p.tailBound := by
    exact le_trans (abs_nonneg p.residual) p.residual_abs_le
  have hres : p.residual ≤ p.tailBound :=
    (abs_le.mp p.residual_abs_le).2
  have htailform : p.tailBound ≤ S := by
    simpa [hformReal] using p.tailBound_le_quadratic
  rw [p.qw_eq_quadratic_sub_residual, hformReal]
  linarith

/-- The explicit spectral-tail producer closes the residual-aware finite
chain once its same-owner decomposition and main-term domination are proved. -/
theorem qw_nonneg_of_bombieriQuadraticSpectralTailP2BridgeData
    {g : CompactLogTest} (p : BombieriQuadraticSpectralTailP2BridgeData g) :
    0 <= C1SameOwnerWeil.qw g :=
  qw_nonneg_of_bombieriQuadraticResidualP2BridgeData p.toResidual

/-- The direct quadratic-form contract cannot coexist with the already
strictly negative healthy detector value.  This is a route guard, not an RH
conclusion. -/
theorem not_bombieriQuadraticP2BridgeData_of_healthyDetectorData
    {rho : Complex} {g : CompactLogTest}
    (hdata : HealthyYoshidaDetectorData rho g)
    (p : BombieriQuadraticP2BridgeData g) : False := by
  have hnegativeSpectral :
      C1SpectralWeil.spectralWeilValue g.convolutionSquare < 0 :=
    (weilSquareSumPositive_iff_spectralWeilValue_neg g).mp
      hdata.weilSquareSumPositive
  have hnegative : C1SameOwnerWeil.qw g < 0 := by
    rw [C1CenterTwoCriterionBridge.qw_eq_spectralWeilValue_centerTwo]
    exact hnegativeSpectral
  exact (not_lt_of_ge (qw_nonneg_of_bombieriQuadraticP2BridgeData p)) hnegative

/-- A direct quadratic-form producer cannot coexist with a healthy detector;
this is the expected contradiction consumer for a successful P2 proof. -/
theorem not_nonempty_bombieriQuadraticP2BridgeData_of_healthyDetectorData
    {rho : Complex} {g : CompactLogTest}
    (hdata : HealthyYoshidaDetectorData rho g) :
    ¬ Nonempty (BombieriQuadraticP2BridgeData g) := by
  intro hp
  obtain ⟨p⟩ := hp
  exact not_bombieriQuadraticP2BridgeData_of_healthyDetectorData hdata p

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

/-- Healthy-detector wrapper for the residual-aware direct quadratic contract.
The detector data is retained for the same-owner consumer; the sign comes
from the finite form and the explicit residual budget. -/
theorem qw_nonneg_of_healthyDetectorData_of_bombieriQuadraticResidualP2BridgeData
    {rho : Complex} {g : CompactLogTest}
    (_hdata : HealthyYoshidaDetectorData rho g)
    (p : BombieriQuadraticResidualP2BridgeData g) :
    0 <= C1SameOwnerWeil.qw g :=
  qw_nonneg_of_bombieriQuadraticResidualP2BridgeData p

/-- Healthy-detector wrapper for the explicit same-owner spectral-tail
producer contract. -/
theorem qw_nonneg_of_healthyDetectorData_of_bombieriQuadraticSpectralTailP2BridgeData
    {rho : Complex} {g : CompactLogTest}
    (_hdata : HealthyYoshidaDetectorData rho g)
    (p : BombieriQuadraticSpectralTailP2BridgeData g) :
    0 <= C1SameOwnerWeil.qw g :=
  qw_nonneg_of_bombieriQuadraticSpectralTailP2BridgeData p

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
