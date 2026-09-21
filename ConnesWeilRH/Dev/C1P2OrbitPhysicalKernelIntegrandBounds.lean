import ConnesWeilRH.Dev.C1P2OrbitPhysicalProfileReadback

namespace ConnesWeilRH
namespace Source
namespace C1P2OrbitPhysicalKernelIntegrandBounds

open MeasureTheory
open CC20YoshidaConvolution
open CC20YoshidaNearZeros
open C1G8R0OrbitGeometry
open C1P2OrbitPhysicalProfileReadback
open C1SameOwnerWeil
open CCM25Concrete.CompactLogConvolution

noncomputable section

theorem orbitWeightedKernelIntegrand_integrable
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (x : Real) :
    Integrable (fun t => orbitWeightedKernelIntegrand geometry x t) := by
  let raw := orbitRawFactor geometry
  let left := CompactLogTest.exponentialWeight raw.involution (-1 : Complex)
  have hconv : Integrable (fun t : Real => left.test t * raw.test (x - t)) := by
    have hex : MeasureTheory.ConvolutionExistsAt left.test raw.test x
        (ContinuousLinearMap.mul ℝ ℂ) volume := by
      exact HasCompactSupport.convolutionExists_left_of_continuous_right
        (L := ContinuousLinearMap.mul ℝ ℂ) (μ := volume)
        left.compactSupport left.test.integrable.locallyIntegrable
        (raw.test.smooth ⊤).continuous x
    exact hex
  have hrewrite :
      (fun t : Real => orbitWeightedKernelIntegrand geometry x t) =
        (fun t => Complex.exp (((x / 2 : Real) : Complex)) *
          (left.test t * raw.test (x - t))) := by
    funext t
    simp only [orbitWeightedKernelIntegrand, left, raw,
      CompactLogTest.exponentialWeight_apply,
      CompactLogTest.involution_apply]
    rw [show ((x / 2 - t : Real) : Complex) =
        ((x / 2 : Real) : Complex) + (-1 : Complex) * (t : Complex) by
          norm_num
          ring,
      Complex.exp_add]
    have hneg : Complex.exp ((-1 : Complex) * (t : Complex)) =
        Complex.exp (-(t : Complex)) := by
      congr 1
      ring
    rw [hneg]
    ring
  rw [hrewrite]
  exact hconv.const_mul _

theorem orbitPhysicalKernel_re_le_integral_of_integrand_bound
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (x : Real) (E : Real → Real)
    (hE : Integrable E)
    (hpoint : ∀ᵐ t ∂(volume : Measure Real),
      (orbitWeightedKernelIntegrand geometry x t).re ≤ E t) :
    (orbitPhysicalKernel geometry x).re ≤ ∫ t, E t := by
  have hre : (orbitPhysicalKernel geometry x).re =
      ∫ t, (orbitWeightedKernelIntegrand geometry x t).re := by
    rw [orbitPhysicalKernel_eq_integral_weightedKernel geometry x]
    symm
    simpa only [Complex.reCLM_apply] using
      (Complex.reCLM.integral_comp_comm
        (orbitWeightedKernelIntegrand_integrable geometry x))
  rw [hre]
  exact integral_mono_ae
    (Complex.reCLM.integrable_comp
      (orbitWeightedKernelIntegrand_integrable geometry x)) hE hpoint

theorem orbitPhysicalKernel_nodeTerm_le_of_integrand_bounds
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (n : Nat)
    (Eplus Eminus : Real → Real)
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
    geometry (Real.log n) Eplus hEplus hpointPlus
  have hminus' := orbitPhysicalKernel_re_le_integral_of_integrand_bound
    geometry (-Real.log n) Eminus hEminus hpointMinus
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
