import ConnesWeilRH.Dev.C1RouteAJointSymbolData3080
import ConnesWeilRH.Dev.C1XiArithmeticPrimePowerReadback

/-!
# Route A Laplace/Fourier normalization bridge (record 3086)

The exact Fourier convention is already present in the prime-power readback
leaf.  This module transports it to the actual selected owner transform.
-/

namespace ConnesWeilRH
namespace Source
namespace C1RouteALaplaceFourierBridge3086

open C1RouteAJointSymbolData3080
open C1XiArithmeticPrimePowerReadback
open C1G8R0OrbitGeometry
open CC20YoshidaNearZeros
open CC20YoshidaConvolution
open CCM25Concrete.CompactLogConvolution
open scoped FourierTransform

noncomputable section

theorem routeAOrbitTransform_eq_fourierLaplace
    {rho : sourceNontrivialZeroSet}
    {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (xi : Real) :
    routeAOrbitTransform geometry xi =
      fourierLaplace g.test xi := by
  rw [routeAOrbitTransform_eq_selectedSourceLaplace geometry xi]
  rw [fourierLaplace_compactLogTest_test_eq_laplaceAt]

theorem routeAOrbitTransform_eq_fourier
    {rho : sourceNontrivialZeroSet}
    {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (xi : Real) :
    routeAOrbitTransform geometry xi =
      (FourierTransform.fourier g.test) (-(xi / (2 * Real.pi))) := by
  rw [routeAOrbitTransform_eq_fourierLaplace geometry xi]
  exact fourierLaplace_eq_fourier g.test xi

end
end C1RouteALaplaceFourierBridge3086
end Source
end ConnesWeilRH
