/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R0OrbitGeometry

/-!
# Owner-preserving prime-prefix reduction for the four-point gate

This leaf does not assert that the first prime power is visible for the
selected owner.  It isolates that obligation exactly: visibility of `n = 2`
permits an exact prefix-plus-remainder decomposition, while non-visibility
forces the corresponding real prime term to vanish.

Consumer: the signed physical-kernel / four-point same-owner budget in map
103.  The finite remainder is always the actual owner's visible set; no
ambient bump or replacement detector is introduced.
-/

namespace ConnesWeilRH
namespace Source
namespace C1FourPointPrimePrefixReduction

open C1SameOwnerWeil
open CC20YoshidaConvolution
open CC20YoshidaNearZeros
open CCM25Concrete.CompactLogConvolution
open C1G8R0OrbitGeometry
open scoped BigOperators

theorem finitePrimeSum_eq_term_add_erase_of_mem
    (F : CompactLogTest) {n : Nat}
    (hn : n ∈ globalPrimeIndexSet F) :
    finitePrimeSum F =
      finitePrimeTerm F n +
        ∑ k ∈ (globalPrimeIndexSet F).erase n, finitePrimeTerm F k := by
  unfold finitePrimeSum
  rw [← Finset.sum_erase_add _ _ hn, add_comm]

theorem finitePrimeTerm_eq_zero_of_not_mem_globalPrimeIndexSet
    (F : CompactLogTest) {n : Nat}
    (hn : n ∉ globalPrimeIndexSet F) :
    finitePrimeTerm F n = 0 := by
  have hzero : finitePrimeTermComplex F n = 0 := by
    by_contra hne
    exact hn ((mem_globalPrimeIndexSet_iff F n).mpr
      ⟨finitePrimeTermComplex_nonzero_primePower F hne, hne⟩)
  unfold finitePrimeTerm
  rw [hzero]
  rfl

theorem finitePrimeSum_eq_two_prefix_add_remainder
    {F : CompactLogTest}
    (h2 : 2 ∈ globalPrimeIndexSet F) :
    finitePrimeSum F =
      finitePrimeTerm F 2 +
        ∑ k ∈ (globalPrimeIndexSet F).erase 2, finitePrimeTerm F k :=
  finitePrimeSum_eq_term_add_erase_of_mem F h2

theorem finitePrimeTerm_two_eq_zero_of_not_visible
    {F : CompactLogTest}
    (h2 : 2 ∉ globalPrimeIndexSet F) :
    finitePrimeTerm F 2 = 0 :=
  finitePrimeTerm_eq_zero_of_not_mem_globalPrimeIndexSet F h2

theorem finitePrimeSum_eq_two_term_add_orbit_range_remainder
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g)
    (hbound : 2 <
      Nat.ceil (Real.exp (2 * ((geometry.orbitIndex + 2 : Nat) : Real))) + 1) :
    finitePrimeSum g.convolutionSquare =
      finitePrimeTerm g.convolutionSquare 2 +
        ∑ k ∈ (Finset.range
          (Nat.ceil (Real.exp (2 * ((geometry.orbitIndex + 2 : Nat) : Real))) + 1)).erase 2,
          finitePrimeTerm g.convolutionSquare k := by
  rw [finitePrimeSum_eq_sum_range_of_orbitG8Geometry geometry]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_range.mpr hbound), add_comm]

end C1FourPointPrimePrefixReduction
end Source
end ConnesWeilRH
