import ConnesWeilRH.Dev.C1RouteAOwnerPrimePowerResidual3128

namespace ConnesWeilRH.Source
namespace C1RouteAOwnerResidualBound3170

open C1G8R0OrbitGeometry
open C1RouteAJointSymbolData3080
open C1RouteAPrimePowerExpansion3127
open C1RouteAOwnerPrimePowerResidual3128
open C1RouteBPrimeFourierReadback3120
open C1SameOwnerWeil
open CC20YoshidaNearZeros
open CCM25Concrete.CompactLogConvolution
open scoped BigOperators

noncomputable section

def routeAActualFinitePrimeKernelAllowance
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) : Real :=
  let _ownerAnchor := geometry
  ∑ q ∈ globalPrimeIndexSet g.convolutionSquare, |primeWeight3120 q|

def routeAOwnerResidualAllowance
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) : Real :=
  routeAJointSymbolPrimeAllowance geometry +
    routeAActualFinitePrimeKernelAllowance geometry

theorem routeAActualFinitePrimeKernel_abs_le
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (xi : Real) :
    |routeAActualFinitePrimeKernel geometry xi| ≤
      routeAActualFinitePrimeKernelAllowance geometry := by
  unfold routeAActualFinitePrimeKernelAllowance routeAActualFinitePrimeKernel
    primeKernel3120
  calc
    |∑ q ∈ globalPrimeIndexSet g.convolutionSquare,
        primeWeight3120 q * Real.cos (2 * Real.pi * (xi / (2 * Real.pi)) * Real.log q)| ≤
      ∑ q ∈ globalPrimeIndexSet g.convolutionSquare,
        |primeWeight3120 q * Real.cos (2 * Real.pi * (xi / (2 * Real.pi)) * Real.log q)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ q ∈ globalPrimeIndexSet g.convolutionSquare, |primeWeight3120 q| := by
      apply Finset.sum_le_sum
      intro q hq
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)

theorem routeAOwnerPrimePowerResidual_abs_le
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (xi : Real) :
    |routeAOwnerPrimePowerResidual geometry xi| ≤
      routeAOwnerResidualAllowance geometry := by
  unfold routeAOwnerPrimePowerResidual routeAInfinitePrimePowerKernel
    routeAOwnerResidualAllowance
  have hinf :
      |∑ p ∈ routeAVisiblePrimes geometry,
          Real.log (p : Real) * routeAPrimePowerExpansion p xi| ≤
        routeAJointSymbolPrimeAllowance geometry := by
    rw [show (∑ p ∈ routeAVisiblePrimes geometry,
        Real.log (p : Real) * routeAPrimePowerExpansion p xi) =
      ∑ p ∈ routeAVisiblePrimes geometry,
        Real.log (p : Real) * routeAPrimePoissonSymbol p xi by
      apply Finset.sum_congr rfl
      intro p hp
      exact congrArg (fun value : Real => Real.log (p : Real) * value)
        (routeAPrimePoissonSymbol_eq_primePowerExpansion p
          (Finset.mem_filter.mp hp).2 xi).symm]
    exact routeAJointSymbol_primePart_abs_le geometry xi
  have hfinite := routeAActualFinitePrimeKernel_abs_le geometry xi
  have htriangle := abs_sub_le
    (∑ p ∈ routeAVisiblePrimes geometry,
      Real.log (p : Real) * routeAPrimePowerExpansion p xi)
    0 (routeAActualFinitePrimeKernel geometry xi)
  have htriangle' :
      |(∑ p ∈ routeAVisiblePrimes geometry,
          Real.log (p : Real) * routeAPrimePowerExpansion p xi) -
          routeAActualFinitePrimeKernel geometry xi| ≤
        |∑ p ∈ routeAVisiblePrimes geometry,
          Real.log (p : Real) * routeAPrimePowerExpansion p xi| +
          |routeAActualFinitePrimeKernel geometry xi| := by
    simpa [sub_zero, zero_sub, abs_neg] using htriangle
  exact htriangle'.trans (add_le_add hinf hfinite)

end
end C1RouteAOwnerResidualBound3170
end ConnesWeilRH.Source
