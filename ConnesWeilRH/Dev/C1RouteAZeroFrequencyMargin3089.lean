import ConnesWeilRH.Dev.C1RouteAJointSymbolNegativeNeighbourhood3088
import ConnesWeilRH.Dev.C1RouteAJointSymbolSquareScreen3082

/-!
# Route A zero-frequency margin reduction (record 3089)

This file reduces the owner-specific strict negativity at frequency zero to
the single scalar premise `0 < c3Sigma 0`.  Every visible-prime contribution
is nonnegative after multiplication by `log p`, and the joint symbol subtracts
their sum.
-/

namespace ConnesWeilRH
namespace Source
namespace C1RouteAZeroFrequencyMargin3089

open C1RouteAJointSymbolData3080
open C1RouteAJointSymbolSquareScreen3082
open C1G8R0OrbitGeometry
open CC20YoshidaNearZeros
open CC20YoshidaConvolution
open CCM25Concrete.CompactLogConvolution

noncomputable section

theorem routeAPrimePoissonSymbol_zero_nonneg (p : Nat) (hp : Nat.Prime p) :
    0 ≤ routeAPrimePoissonSymbol p 0 := by
  exact (routeAPrimePoissonSymbol_zero_frequency_pos p hp).le

theorem routeAJointSymbol_zero_neg_of_c3Sigma_zero_pos
    {rho : sourceNontrivialZeroSet}
    {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g)
    (hsigma : 0 < Dev.c3Sigma 0) :
    routeAJointSymbol geometry 0 < 0 := by
  unfold routeAJointSymbol
  have hsum : 0 ≤ ∑ p ∈ routeAVisiblePrimes geometry,
      Real.log (p : Real) * routeAPrimePoissonSymbol p 0 := by
    apply Finset.sum_nonneg
    intro p hp
    apply mul_nonneg
    · exact Real.log_nonneg (by
        have hprime : Nat.Prime p := (Finset.mem_filter.mp hp).2
        exact_mod_cast hprime.one_le)
    · exact routeAPrimePoissonSymbol_zero_nonneg p
        (Finset.mem_filter.mp hp).2
  linarith

end
end C1RouteAZeroFrequencyMargin3089
end Source
end ConnesWeilRH
