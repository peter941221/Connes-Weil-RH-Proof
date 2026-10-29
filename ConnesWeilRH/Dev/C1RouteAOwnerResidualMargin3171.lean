import ConnesWeilRH.Dev.C1RouteAOwnerResidualMargin3130
import ConnesWeilRH.Dev.C1RouteAOwnerResidualBound3170

namespace ConnesWeilRH.Source
namespace C1RouteAOwnerResidualMargin3171

open C1G8R0OrbitGeometry
open C1RouteAJointSymbolData3080
open C1RouteAOwnerResidualMargin3130
open C1RouteAOwnerResidualBound3170
open C1RouteAOwnerPrimePowerResidual3128
open CC20YoshidaNearZeros
open CCM25Concrete.CompactLogConvolution

noncomputable section

theorem routeAJointSymbol_lower_bound_of_owner_residual_allowance
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (xi : Real) :
    -Dev.c3Sigma xi - routeAActualFinitePrimeKernelAllowance geometry -
        routeAOwnerResidualAllowance geometry ≤
      routeAJointSymbol geometry xi := by
  rw [routeAJointSymbol_eq_actualOwnerSymbol_sub_residual geometry xi]
  unfold routeAActualOwnerSymbol
  have hfinite := routeAActualFinitePrimeKernel_abs_le geometry xi
  have hresidual := routeAOwnerPrimePowerResidual_abs_le geometry xi
  have hfinite_upper :
      routeAActualFinitePrimeKernel geometry xi ≤
        routeAActualFinitePrimeKernelAllowance geometry :=
    (abs_le.mp hfinite).2
  have hresidual_upper :
      routeAOwnerPrimePowerResidual geometry xi ≤
        routeAOwnerResidualAllowance geometry :=
    (abs_le.mp hresidual).2
  linarith

theorem routeAJointSymbol_nonneg_of_owner_residual_margin
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (xi : Real)
    (hmargin :
      routeAActualFinitePrimeKernelAllowance geometry +
          routeAOwnerResidualAllowance geometry ≤ -Dev.c3Sigma xi) :
    0 ≤ routeAJointSymbol geometry xi := by
  have hlower :=
    routeAJointSymbol_lower_bound_of_owner_residual_allowance geometry xi
  linarith

end
end C1RouteAOwnerResidualMargin3171
end ConnesWeilRH.Source
