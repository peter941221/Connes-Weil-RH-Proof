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
open ConnesWeilRH.Source.CCM25Concrete.CompactLogConvolution

noncomputable section

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

end
end C1C3CarrierOrbitCutoff
end Dev
end ConnesWeilRH
