import ConnesWeilRH.Dev.C1RouteALaplaceFourierBridge3086
import ConnesWeilRH.Dev.C1XiResidue

/-!
# Route A owner transform analyticity and nonzero value (record 3092)

The selected owner is nonzero independently of any numerical certificate:
the raw interpolation value at the source node `rho` is exactly one.  Fourier
injectivity then supplies a genuine real frequency at which the owner
transform is nonzero. The existing dominated-integral Laplace derivative
theorem gives entire complex analyticity. Restriction of scalars and the
actual imaginary-frequency map give real analyticity for the same owner.
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

theorem compactLogLaplace_analytic (g : CompactLogTest) :
    AnalyticOnNhd Complex (CompactLogTest.laplaceAt g) Set.univ := by
  intro z _
  exact (C1XiResidue.differentiable_laplaceAt g).analyticAt z

theorem routeAOrbitTransform_analytic
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) :
    AnalyticOnNhd Real (routeAOrbitTransform geometry) Set.univ := by
  have heq : routeAOrbitTransform geometry =
      (fun xi : Real => CompactLogTest.laplaceAt g ((xi : Complex) * Complex.I)) := by
    funext xi
    exact routeAOrbitTransform_eq_selectedSourceLaplace geometry xi
  rw [heq]
  intro xi _
  have hpath : AnalyticAt Real (fun x : Real => (x : Complex) * Complex.I) xi :=
    (Complex.ofRealCLM.analyticAt xi).mul analyticAt_const
  have hlaplace : AnalyticAt Real (CompactLogTest.laplaceAt g)
      ((xi : Complex) * Complex.I) :=
    (compactLogLaplace_analytic g _ (Set.mem_univ _)).restrictScalars
  exact hlaplace.comp (f := fun x : Real => (x : Complex) * Complex.I) hpath

theorem routeAOwner_laplaceAt_rho_eq_one
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) :
    CompactLogTest.laplaceAt g (rho.1 - 1 / 2) = 1 := by
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
  rw [hsource]
  simpa [w] using hraw.trans (healthyUnscaledTargetValue_rho rho.1)

theorem routeAOwnerTest_ne_zero
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) :
    g.test ≠ 0 := by
  intro hzero
  have hvalue := routeAOwner_laplaceAt_rho_eq_one geometry
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
