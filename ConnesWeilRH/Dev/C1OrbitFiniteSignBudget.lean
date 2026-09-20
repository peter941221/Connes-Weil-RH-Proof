/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 License.
-/

import ConnesWeilRH.Dev.C1G8R0OrbitGeometry
import ConnesWeilRH.Dev.C1OrbitWindowSemiLocalGate
import ConnesWeilRH.Dev.C1P2BilateralProfile

/-!
# The finite-range sign budget for one selected orbit owner

This leaf does not prove the semi-local sign.  It makes the remaining sign
obligation an exact finite weighted bilateral-profile inequality on the same
`OrbitG8Geometry` owner.  No support, prime set, or detector is replaced by a
different object.
-/

namespace ConnesWeilRH
namespace Source
namespace C1OrbitFiniteSignBudget

open C1G8R0OrbitGeometry
open C1OrbitWindowSemiLocalGate
open C1P2BilateralProfile
open C1SameOwnerWeil
open CC20YoshidaNearZeros
open CCM25Concrete.CompactLogConvolution
open scoped BigOperators

/-- Exact finite-range form of the orbit-window semi-local gate, with the
bilateral profile exposed at every visible prime-power coordinate. -/
theorem orbitWindowSemiLocalGate_iff_finiteRangeBilateralProfile
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) :
    orbitWindowSemiLocalGate g ↔
      archimedeanTerm g.convolutionSquare +
        ∑ n ∈ Finset.range
          (Nat.ceil (Real.exp (2 * ((geometry.orbitIndex + 2 : Nat) : Real))) + 1),
          ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real)) *
            (bilateralProfile g.convolutionSquare (Real.log n)).re ≤ 0 := by
  unfold orbitWindowSemiLocalGate
  rw [finitePrimeSum_eq_sum_range_of_orbitG8Geometry geometry]
  have hsum :
      (∑ n ∈ Finset.range
          (Nat.ceil (Real.exp (2 * ((geometry.orbitIndex + 2 : Nat) : Real))) + 1),
          finitePrimeTerm g.convolutionSquare n) =
        ∑ n ∈ Finset.range
          (Nat.ceil (Real.exp (2 * ((geometry.orbitIndex + 2 : Nat) : Real))) + 1),
          ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real)) *
            (bilateralProfile g.convolutionSquare (Real.log n)).re := by
    apply Finset.sum_congr rfl
    intro n hn
    exact finitePrimeTerm_eq_realCoefficient_mul_bilateralProfile_re
      g.convolutionSquare n
  rw [hsum]

end C1OrbitFiniteSignBudget
end Source
end ConnesWeilRH
