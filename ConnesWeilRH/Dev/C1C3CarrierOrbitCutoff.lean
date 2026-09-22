/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1C3CarrierTransport
import ConnesWeilRH.Dev.C1G8R0OrbitGeometry

/-!
# C3' carrier phase budget on the raw orbit cutoff

This adapter instantiates the abstract carrier phase cutoff estimate with the
support-derived visible-prime cutoff exported by `OrbitG8Geometry`.  It is a
same-owner representation and budget bridge only: it proves no margin, sign,
semi-local positivity, or RH conclusion.
-/

namespace ConnesWeilRH
namespace Dev
namespace C1C3CarrierOrbitCutoff

open ConnesWeilRH.Dev.C1C3CarrierTransport
open ConnesWeilRH.Source.C1G8R0OrbitGeometry
open ConnesWeilRH.Source.CC20YoshidaNearZeros
open ConnesWeilRH.Source.C1SameOwnerWeil
open ConnesWeilRH.Source.C1OrbitWindowSemiLocalGate
open ConnesWeilRH.Source.CCM25Concrete.CompactLogConvolution

noncomputable section

theorem orbitG8Geometry_carrier_reparam
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (γ : Real) :
    ∃ u : CompactLogTest, ∃ geometry' : OrbitG8Geometry rho (carrierModulate γ u),
      carrierModulate γ u = g := by
  obtain ⟨u, hu⟩ := carrierModulate_surjective γ g
  refine ⟨u, ?_, hu⟩
  rw [hu]
  exact geometry

theorem orbitG8_visible_owner_card_le_cutoff
    {rho : sourceNontrivialZeroSet} (γ : Real) (u : CompactLogTest)
    (geometry : OrbitG8Geometry rho (carrierModulate γ u)) :
    (globalPrimeIndexSet ((carrierModulate γ u).convolutionSquare)).card ≤
      Nat.ceil (Real.exp (2 * ((geometry.orbitIndex + 2 : Nat) : Real))) + 1 := by
  let N : ℕ :=
    Nat.ceil (Real.exp (2 * ((geometry.orbitIndex + 2 : Nat) : Real))) + 1
  have hsubset := visiblePrimeSet_subset_range_of_orbitG8Geometry geometry
  have hcard :
      (globalPrimeIndexSet ((carrierModulate γ u).convolutionSquare)).card ≤
        (Finset.range N).card := Finset.card_le_card (by simpa [N] using hsubset)
  simpa [N] using hcard

theorem carrierSquarePrimePhaseSum_abs_le_orbitG8_cutoff
    {rho : sourceNontrivialZeroSet} (γ : Real) (u : CompactLogTest)
    (geometry : OrbitG8Geometry rho (carrierModulate γ u)) :
    |carrierSquarePrimePhaseSum γ u| ≤
      ((globalPrimeIndexSet
          ((carrierModulate γ u).convolutionSquare)).card : Real) *
        (2 * Real.log
          (Nat.ceil
            (Real.exp (2 * ((geometry.orbitIndex + 2 : Nat) : Real))) + 1 : Real)) *
        SchwartzMap.seminorm ℂ 0 0 u.convolutionSquare.test := by
  let N : ℕ :=
    Nat.ceil (Real.exp (2 * ((geometry.orbitIndex + 2 : Nat) : Real))) + 1
  have hN : 1 ≤ N := by
    dsimp [N]
    omega
  have hcut : ∀ n ∈ globalPrimeIndexSet
      ((carrierModulate γ u).convolutionSquare), n ≤ N := by
    intro n hn
    have hsubset := visiblePrimeSet_subset_range_of_orbitG8Geometry geometry
    have hmem : n ∈ Finset.range N := hsubset hn
    exact Nat.le_of_lt (Finset.mem_range.mp hmem)
  simpa [N] using
    (carrierSquarePrimePhaseSum_abs_le_card_log_cutoff γ u N hN hcut)

theorem orbitWindowSemiLocalGate_of_orbitG8_cutoff_margin
    {rho : sourceNontrivialZeroSet} (γ : Real) (u : CompactLogTest)
    (geometry : OrbitG8Geometry rho (carrierModulate γ u)) (δ : Real)
    (harch : archimedeanTerm (carrierModulate γ u).convolutionSquare ≤ -δ)
    (hbudget :
      ((globalPrimeIndexSet
          ((carrierModulate γ u).convolutionSquare)).card : Real) *
          (2 * Real.log
            (Nat.ceil
              (Real.exp (2 * ((geometry.orbitIndex + 2 : Nat) : Real))) + 1 : Real)) *
          SchwartzMap.seminorm ℂ 0 0 u.convolutionSquare.test ≤ δ) :
    orbitWindowSemiLocalGate (carrierModulate γ u) := by
  apply orbitWindowSemiLocalGate_carrierSquare_of_margin_bounds γ u δ harch
  exact (carrierSquarePrimePhaseSum_abs_le_orbitG8_cutoff γ u geometry).trans hbudget

theorem carrierSquarePrimePhaseSum_abs_le_orbitG8_range_budget
    {rho : sourceNontrivialZeroSet} (γ : Real) (u : CompactLogTest)
    (geometry : OrbitG8Geometry rho (carrierModulate γ u)) :
    |carrierSquarePrimePhaseSum γ u| ≤
      (Nat.ceil
          (Real.exp (2 * ((geometry.orbitIndex + 2 : Nat) : Real))) + 1 : Real) *
        (2 * Real.log
          (Nat.ceil
            (Real.exp (2 * ((geometry.orbitIndex + 2 : Nat) : Real))) + 1 : Real)) *
        SchwartzMap.seminorm ℂ 0 0 u.convolutionSquare.test := by
  let N : ℕ :=
    Nat.ceil (Real.exp (2 * ((geometry.orbitIndex + 2 : Nat) : Real))) + 1
  have hN : 1 ≤ N := by
    dsimp [N]
    omega
  have hcard :
      ((globalPrimeIndexSet
          ((carrierModulate γ u).convolutionSquare)).card : Real) ≤ N := by
    have hcardNat :
        (globalPrimeIndexSet
            ((carrierModulate γ u).convolutionSquare)).card ≤ N := by
      simpa [N] using orbitG8_visible_owner_card_le_cutoff γ u geometry
    exact_mod_cast hcardNat
  have hfactor :
      0 ≤ (2 * Real.log (N : Real)) *
        SchwartzMap.seminorm ℂ 0 0 u.convolutionSquare.test := by
    have hlog : 0 ≤ Real.log (N : Real) := by
      exact Real.log_nonneg (by exact_mod_cast hN)
    positivity
  calc
    |carrierSquarePrimePhaseSum γ u| ≤
        ((globalPrimeIndexSet
            ((carrierModulate γ u).convolutionSquare)).card : Real) *
          (2 * Real.log (N : Real)) *
          SchwartzMap.seminorm ℂ 0 0 u.convolutionSquare.test :=
      carrierSquarePrimePhaseSum_abs_le_card_log_cutoff γ u N hN (by
        intro n hn
        have hsubset := visiblePrimeSet_subset_range_of_orbitG8Geometry geometry
        exact Nat.le_of_lt (Finset.mem_range.mp (hsubset hn)))
    _ ≤ (N : Real) * (2 * Real.log (N : Real)) *
          SchwartzMap.seminorm ℂ 0 0 u.convolutionSquare.test := by
      calc
        ((globalPrimeIndexSet
            ((carrierModulate γ u).convolutionSquare)).card : Real) *
            (2 * Real.log (N : Real)) *
            SchwartzMap.seminorm ℂ 0 0 u.convolutionSquare.test =
          ((globalPrimeIndexSet
            ((carrierModulate γ u).convolutionSquare)).card : Real) *
            ((2 * Real.log (N : Real)) *
              SchwartzMap.seminorm ℂ 0 0 u.convolutionSquare.test) := by ring
        _ ≤ (N : Real) * ((2 * Real.log (N : Real)) *
              SchwartzMap.seminorm ℂ 0 0 u.convolutionSquare.test) :=
          mul_le_mul_of_nonneg_right hcard hfactor
        _ = (N : Real) * (2 * Real.log (N : Real)) *
              SchwartzMap.seminorm ℂ 0 0 u.convolutionSquare.test := by ring
    _ =
        (Nat.ceil
            (Real.exp (2 * ((geometry.orbitIndex + 2 : Nat) : Real))) + 1 : Real) *
          (2 * Real.log
            (Nat.ceil
              (Real.exp (2 * ((geometry.orbitIndex + 2 : Nat) : Real))) + 1 : Real)) *
          SchwartzMap.seminorm ℂ 0 0 u.convolutionSquare.test := by
      simp [N]

theorem orbitWindowSemiLocalGate_of_orbitG8_range_margin
    {rho : sourceNontrivialZeroSet} (γ : Real) (u : CompactLogTest)
    (geometry : OrbitG8Geometry rho (carrierModulate γ u)) (δ : Real)
    (harch : archimedeanTerm (carrierModulate γ u).convolutionSquare ≤ -δ)
    (hbudget :
      (Nat.ceil
          (Real.exp (2 * ((geometry.orbitIndex + 2 : Nat) : Real))) + 1 : Real) *
          (2 * Real.log
            (Nat.ceil
              (Real.exp (2 * ((geometry.orbitIndex + 2 : Nat) : Real))) + 1 : Real)) *
          SchwartzMap.seminorm ℂ 0 0 u.convolutionSquare.test ≤ δ) :
    orbitWindowSemiLocalGate (carrierModulate γ u) := by
  apply orbitWindowSemiLocalGate_carrierSquare_of_margin_bounds γ u δ harch
  exact (carrierSquarePrimePhaseSum_abs_le_orbitG8_range_budget γ u geometry).trans hbudget

end
end C1C3CarrierOrbitCutoff
end Dev
end ConnesWeilRH
