import ConnesWeilRH.Dev.C1RouteALaplaceFourierBridge3086

/-!
# Route A owner transform nonzero value (record 3092)

The selected owner is nonzero independently of any numerical certificate:
the raw interpolation value at the source node `rho` is exactly one.  Fourier
injectivity then supplies a genuine real frequency at which the owner
transform is nonzero.  The separate entire analyticity theorem for the
compact-support Laplace transform is intentionally not asserted here.
-/

namespace ConnesWeilRH
namespace Source
namespace C1RouteAOwnerAnalyticTransform3092

open C1RouteAJointSymbolData3080
open C1RouteALaplaceFourierBridge3086
open C1G8R0OrbitGeometry
open C1HealthyYoshidaUnscaledOrbit
open CC20YoshidaConvolution
open CC20YoshidaConvolution.CompactLogTest
open CCM25Concrete.CompactLogConvolution
open CCM25Concrete.UnscaledYoshidaSelectedOwner
open CC20YoshidaNearZeros
open scoped FourierTransform

noncomputable section

theorem routeAOwnerTest_ne_zero
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) :
    g.test ≠ 0 := by
  intro hzero
  let w : FiniteMellinNode (healthyUnscaledTargetNodes rho.1) :=
    ⟨rho.1, mem_healthyUnscaledTargetNodes_rho rho.1⟩
  have hraw :
      CompactLogTest.laplaceAt
          ((convolutionIterate geometry.base geometry.orbitIndex).convolution
            geometry.correction) w.1 =
        healthyUnscaledTargetValue rho.1 w := geometry.raw_target_values w
  have hsource :
      CompactLogTest.laplaceAt g (rho.1 - 1 / 2) =
        CompactLogTest.laplaceAt
          ((convolutionIterate geometry.base geometry.orbitIndex).convolution
            geometry.correction) rho.1 := by
    simpa only [geometry.selected_owner_test] using
      (selectedOwner_laplaceAt_sourceTest_centered
        geometry.base geometry.correction geometry.orbitIndex rho.1)
  have hvalue : CompactLogTest.laplaceAt g (rho.1 - 1 / 2) = 1 := by
    rw [hsource]
    simpa [w] using hraw.trans (healthyUnscaledTargetValue_rho rho.1)
  have hzeroLaplace : CompactLogTest.laplaceAt g (rho.1 - 1 / 2) = 0 := by
    unfold CompactLogTest.laplaceAt
    simp [CompactLogTest.exponentialWeight_apply, hzero]
  rw [hzeroLaplace] at hvalue
  norm_num at hvalue

theorem routeAOrbitTransform_global_nonzero
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) :
    ∃ xi : Real, routeAOrbitTransform geometry xi ≠ 0 := by
  have howner : g.test ≠ 0 := routeAOwnerTest_ne_zero geometry
  have hfourier : FourierTransform.fourier g.test ≠ 0 := by
    intro hzero
    apply howner
    apply (FourierTransform.fourierCLE ℝ (SchwartzMap ℝ ℂ)).injective
    simpa using hzero
  have hvalue : ∃ y : Real, (FourierTransform.fourier g.test) y ≠ 0 := by
    by_contra hnone
    apply hfourier
    ext y
    by_contra hy
    exact hnone ⟨y, hy⟩
  obtain ⟨y, hy⟩ := hvalue
  refine ⟨-(2 * Real.pi * y), ?_⟩
  rw [routeAOrbitTransform_eq_fourier geometry]
  have hscale : -(-((2 : Real) * Real.pi * y) / (2 * Real.pi)) = y := by
    field_simp [Real.pi_ne_zero]
  simpa [hscale] using hy

end
end C1RouteAOwnerAnalyticTransform3092
end Source
end ConnesWeilRH
