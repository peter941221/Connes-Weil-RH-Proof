import ConnesWeilRH.Dev.C1P2OrbitPhysicalProfileReadback

namespace ConnesWeilRH
namespace Source
namespace C1P2OrbitPhysicalKernelIntegrandBounds

open MeasureTheory
open CC20YoshidaNearZeros
open C1G8R0OrbitGeometry
open C1P2OrbitPhysicalProfileReadback
open C1SameOwnerWeil
open CCM25Concrete.CompactLogConvolution

noncomputable section

theorem orbitPhysicalKernel_re_le_integral_of_integrand_bound
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (x : Real) (E : Real → Real)
    (hkernel : Integrable
      (fun t => orbitWeightedKernelIntegrand geometry x t))
    (hE : Integrable E)
    (hpoint : ∀ᵐ t ∂(volume : Measure Real),
      (orbitWeightedKernelIntegrand geometry x t).re ≤ E t) :
    (orbitPhysicalKernel geometry x).re ≤ ∫ t, E t := by
  have hre : (orbitPhysicalKernel geometry x).re =
      ∫ t, (orbitWeightedKernelIntegrand geometry x t).re := by
    rw [orbitPhysicalKernel_eq_integral_weightedKernel geometry x]
    symm
    simpa only [Complex.reCLM_apply] using
      (Complex.reCLM.integral_comp_comm hkernel)
  rw [hre]
  exact integral_mono_ae (Complex.reCLM.integrable_comp hkernel) hE hpoint

theorem orbitPhysicalKernel_nodeTerm_le_of_integrand_bounds
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (n : Nat)
    (Eplus Eminus : Real → Real)
    (hplus : Integrable
      (fun t => orbitWeightedKernelIntegrand geometry (Real.log n) t))
    (hminus : Integrable
      (fun t => orbitWeightedKernelIntegrand geometry (-Real.log n) t))
    (hEplus : Integrable Eplus) (hEminus : Integrable Eminus)
    (hpointPlus : ∀ᵐ t ∂(volume : Measure Real),
      (orbitWeightedKernelIntegrand geometry (Real.log n) t).re ≤ Eplus t)
    (hpointMinus : ∀ᵐ t ∂(volume : Measure Real),
      (orbitWeightedKernelIntegrand geometry (-Real.log n) t).re ≤ Eminus t) :
    ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real)) *
        (orbitPhysicalKernel geometry (Real.log n) +
          orbitPhysicalKernel geometry (-Real.log n)).re ≤
      ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real)) *
        ((∫ t, Eplus t) + ∫ t, Eminus t) := by
  have hplus' := orbitPhysicalKernel_re_le_integral_of_integrand_bound
    geometry (Real.log n) Eplus hplus hEplus hpointPlus
  have hminus' := orbitPhysicalKernel_re_le_integral_of_integrand_bound
    geometry (-Real.log n) Eminus hminus hEminus hpointMinus
  have hsum :
      (orbitPhysicalKernel geometry (Real.log n) +
        orbitPhysicalKernel geometry (-Real.log n)).re ≤
        (∫ t, Eplus t) + ∫ t, Eminus t := by
    simpa only [map_add] using add_le_add hplus' hminus'
  have hcoeff : (0 : Real) ≤
      ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real)) := by
    exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
  exact mul_le_mul_of_nonneg_left hsum hcoeff

end
end C1P2OrbitPhysicalKernelIntegrandBounds
end Source
end ConnesWeilRH
