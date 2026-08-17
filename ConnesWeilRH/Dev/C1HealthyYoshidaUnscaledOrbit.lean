import ConnesWeilRH.Dev.C1HealthyYoshidaMinimalInterpolation
import ConnesWeilRH.Source.CCM25Concrete.UnscaledYoshidaSelectedOwner

/-!
# C1HealthyYoshidaUnscaledOrbit - coordinate adapter for the unscaled orbit

The unscaled Yoshida construction controls a raw source factor `h` at source
Mellin points.  The C1 spectral side evaluates the half-density shifted root
at `rho - 1/2`, while the healthy detector API asks that same root to detect
the source point `rho`.  This module records the exact raw values needed for
the detector fields before attempting the global spectral sign construction.
-/

namespace ConnesWeilRH
namespace Source
namespace C1HealthyYoshidaUnscaledOrbit

open CC20YoshidaConvolution
open CC20YoshidaConvolution.CompactLogTest
open CCM25Concrete.CompactLogConvolution
open CCM25Concrete.UnscaledYoshidaSelectedOwner
open C1HealthyYoshidaDetector
open C1HealthyYoshidaMinimalInterpolation

/-- The half-density shift turns raw values at `1/2`, `1`, and `3/2` into the
three healthy finite-vanishing equations.  A nonzero raw value at `rho + 1/2`
is exactly healthy detection at `rho`. -/
theorem healthyMinimalLaplaceRealizes_halfDensityShift_of_raw_values
    {rho : Complex} {h : CompactLogTest}
    (hhalf : laplaceAt h (1 / 2) = 0)
    (hone : laplaceAt h 1 = 0)
    (hthreeHalf : laplaceAt h (3 / 2) = 0)
    (hdetect : laplaceAt h (rho + 1 / 2) != 0) :
    HealthyMinimalLaplaceRealizes rho (halfDensityShift h) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [laplaceAt_halfDensityShift]
    simpa using hhalf
  · rw [laplaceAt_halfDensityShift]
    norm_num
    simpa using hone
  · rw [laplaceAt_halfDensityShift]
    norm_num
    simpa using hthreeHalf
  · rw [laplaceAt_halfDensityShift]
    simpa using hdetect

/-- Once the unscaled construction proves strict negativity of the C1 spectral
value for its shifted square, the raw-value adapter supplies healthy detector
data without transferring any sign between unrelated owners. -/
theorem healthyDetectorData_halfDensityShift_of_raw_values_of_spectral_neg
    {rho : Complex} {h : CompactLogTest}
    (hhalf : laplaceAt h (1 / 2) = 0)
    (hone : laplaceAt h 1 = 0)
    (hthreeHalf : laplaceAt h (3 / 2) = 0)
    (hdetect : laplaceAt h (rho + 1 / 2) != 0)
    (hspectral :
      C1SpectralWeil.spectralWeilValue
          (halfDensityShift h).convolutionSquare < 0) :
    HealthyYoshidaDetectorData rho (halfDensityShift h) := by
  let hminimal : HealthyMinimalLaplaceRealizes rho (halfDensityShift h) :=
    healthyMinimalLaplaceRealizes_halfDensityShift_of_raw_values
      hhalf hone hthreeHalf hdetect
  refine
    { compactSupportSmooth := C1.healthyCC20CompactSupportSmooth _
      vanishesOnF := hminimal.vanishesOn_cc20Triple
      detectsRho := hminimal.detects_rho
      weilSquareSumPositive := ?_ }
  exact
    (weilSquareSumPositive_iff_spectralWeilValue_neg (halfDensityShift h)).mpr
      hspectral

/-- The centered C1 spectral value of the shifted square is the raw
functional-equation Hermitian product.  This is the exact sign interface
consumed by the future all-zero tail estimate. -/
theorem laplaceAt_halfDensityShift_convolutionSquare_centered
    (h : CompactLogTest) (rho : Complex) :
    laplaceAt (halfDensityShift h).convolutionSquare (rho - 1 / 2) =
      star (laplaceAt h (1 - star rho)) * laplaceAt h rho := by
  rw [CompactLogTest.convolutionSquare, laplaceAt_convolution,
    laplaceAt_involution, laplaceAt_halfDensityShift,
    laplaceAt_halfDensityShift]
  congr 3 <;> simp <;> ring

end C1HealthyYoshidaUnscaledOrbit
end Source
end ConnesWeilRH
