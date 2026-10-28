import ConnesWeilRH.Dev.C1RouteAPrimePowerExpansion3127
import ConnesWeilRH.Dev.C1RouteBPrimeFourierReadback3120

/-!
# Route A owner-specific prime-power residual

This module names the signed discrepancy between the infinite prime-base
Poisson expansion and the exact finite prime-power kernel of the same owner.
It proves only the coordinate-normalized finite-kernel readback and the exact
additive decomposition.  No residual sign or bound is assumed.
-/

namespace ConnesWeilRH
namespace Source
namespace C1RouteAOwnerPrimePowerResidual3128

open C1G8R0OrbitGeometry
open C1RouteAJointSymbolData3080
open C1RouteAPrimePowerExpansion3127
open C1RouteBPrimeFourierReadback3120
open C1SameOwnerWeil
open CC20YoshidaConvolution
open CC20YoshidaConvolution.CompactLogTest
open CC20YoshidaNearZeros
open CCM25Concrete.CompactLogConvolution
open scoped BigOperators

noncomputable section

def routeAInfinitePrimePowerKernel
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (xi : Real) : Real :=
  ∑ p ∈ routeAVisiblePrimes geometry,
    Real.log (p : Real) * routeAPrimePowerExpansion p xi

def routeAActualFinitePrimeKernel
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (xi : Real) : Real :=
  let _ownerAnchor := geometry
  primeKernel3120 (globalPrimeIndexSet g.convolutionSquare)
    (xi / (2 * Real.pi))

/-- The signed difference that must be priced before the physical gate can be
transported to Route A. -/
def routeAOwnerPrimePowerResidual
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (xi : Real) : Real :=
  routeAInfinitePrimePowerKernel geometry xi -
    routeAActualFinitePrimeKernel geometry xi

theorem routeAActualFinitePrimeKernel_eq_coordinateNormalizedSum
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (xi : Real) :
    routeAActualFinitePrimeKernel geometry xi =
      ∑ q ∈ globalPrimeIndexSet g.convolutionSquare,
        primeWeight3120 q * Real.cos (xi * Real.log q) := by
  unfold routeAActualFinitePrimeKernel primeKernel3120
  apply Finset.sum_congr rfl
  intro q hq
  have harg :
      2 * Real.pi * (xi / (2 * Real.pi)) * Real.log q =
        xi * Real.log q := by
    field_simp [Real.pi_ne_zero]
  rw [harg]

theorem routeAInfinitePrimePowerKernel_eq_actual_add_residual
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (xi : Real) :
    routeAInfinitePrimePowerKernel geometry xi =
      routeAActualFinitePrimeKernel geometry xi +
        routeAOwnerPrimePowerResidual geometry xi := by
  unfold routeAOwnerPrimePowerResidual
  ring

end
end C1RouteAOwnerPrimePowerResidual3128
end Source
end ConnesWeilRH
