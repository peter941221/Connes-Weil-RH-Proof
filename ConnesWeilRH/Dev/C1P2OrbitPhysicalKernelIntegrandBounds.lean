import ConnesWeilRH.Dev.C1P2OrbitPhysicalProfileReadback

namespace ConnesWeilRH
namespace Source
namespace C1P2OrbitPhysicalKernelIntegrandBounds

open MeasureTheory
open CC20YoshidaConvolution
open CC20YoshidaNearZeros
open C1G8R0OrbitGeometry
open C1P2OrbitPhysicalProfileReadback
open C1P2SignedBudget
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

theorem orbitPhysicalKernel_nodeTerm_le_of_plus_integrand_bound
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (n : Nat) (E : Real → Real)
    (hE : Integrable E)
    (hpoint : ∀ᵐ t ∂(volume : Measure Real),
      (orbitWeightedKernelIntegrand geometry (Real.log n) t).re ≤ E t) :
    ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real)) *
        (orbitPhysicalKernel geometry (Real.log n) +
          orbitPhysicalKernel geometry (-Real.log n)).re ≤
      ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real)) *
        (2 * (∫ t, E t)) := by
  have hplus := orbitPhysicalKernel_re_le_integral_of_integrand_bound
    geometry (Real.log n) E hE hpoint
  have hsum :
      (orbitPhysicalKernel geometry (Real.log n) +
        orbitPhysicalKernel geometry (-Real.log n)).re ≤
        2 * (∫ t, E t) := by
    rw [orbitPhysicalKernel_neg_eq_star geometry (Real.log n)]
    have hconj : orbitPhysicalKernel geometry (Real.log n) +
        star (orbitPhysicalKernel geometry (Real.log n)) =
        ((2 * (orbitPhysicalKernel geometry (Real.log n)).re : Real) : Complex) := by
      rw [Complex.star_def]
      exact Complex.add_conj _
    rw [hconj]
    norm_num
    linarith
  have hcoeff : (0 : Real) ≤
      ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real)) := by
    exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
  exact mul_le_mul_of_nonneg_left hsum hcoeff

def orbitPositiveIntegrandMajorant
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (n : Nat) : Real → Real :=
  fun t => max
    (orbitWeightedKernelIntegrand geometry (Real.log n) t).re 0

theorem orbitPositiveIntegrandMajorant_integrable
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (n : Nat) :
    Integrable (orbitPositiveIntegrandMajorant geometry n) := by
  have hreal : Integrable (fun t =>
      (orbitWeightedKernelIntegrand geometry (Real.log n) t).re) :=
    Complex.reCLM.integrable_comp
      (orbitWeightedKernelIntegrand_integrable geometry (Real.log n))
  have hmax := hreal.norm.mono_nonneg
    (by fun_prop : AEStronglyMeasurable
      (fun t : Real => max
        (orbitWeightedKernelIntegrand geometry (Real.log n) t).re 0) volume)
    (Filter.Eventually.of_forall (fun t => le_max_right _ _))
    (Filter.Eventually.of_forall (fun t =>
      max_le (le_abs_self _) (abs_nonneg _)))
  simpa [orbitPositiveIntegrandMajorant, Real.norm_eq_abs] using hmax

theorem orbitPositiveIntegrandMajorant_pointwise
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (n : Nat) :
    ∀ᵐ t ∂(volume : Measure Real),
      (orbitWeightedKernelIntegrand geometry (Real.log n) t).re ≤
        orbitPositiveIntegrandMajorant geometry n t := by
  filter_upwards with t
  exact le_max_left _ _

theorem orbitPhysicalKernel_nodeTerm_le_of_positivePart
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (n : Nat) :
    ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real)) *
        (orbitPhysicalKernel geometry (Real.log n) +
          orbitPhysicalKernel geometry (-Real.log n)).re ≤
      ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real)) *
        (2 * (∫ t, orbitPositiveIntegrandMajorant geometry n t)) := by
  exact orbitPhysicalKernel_nodeTerm_le_of_plus_integrand_bound geometry n
    (orbitPositiveIntegrandMajorant geometry n)
    (orbitPositiveIntegrandMajorant_integrable geometry n)
    (orbitPositiveIntegrandMajorant_pointwise geometry n)

structure OrbitPhysicalKernelIntegrandCertificate
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) where
  Eplus : Nat → Real → Real
  Eminus : Nat → Real → Real
  integrable_plus : ∀ n ∈ orbitVisiblePrimeRange geometry,
    Integrable (Eplus n)
  integrable_minus : ∀ n ∈ orbitVisiblePrimeRange geometry,
    Integrable (Eminus n)
  pointwise_plus : ∀ n ∈ orbitVisiblePrimeRange geometry,
    ∀ᵐ t ∂(volume : Measure Real),
      (orbitWeightedKernelIntegrand geometry (Real.log n) t).re ≤ Eplus n t
  pointwise_minus : ∀ n ∈ orbitVisiblePrimeRange geometry,
    ∀ᵐ t ∂(volume : Measure Real),
      (orbitWeightedKernelIntegrand geometry (-Real.log n) t).re ≤ Eminus n t
  arch_bound : archimedeanTerm g.convolutionSquare +
      Finset.sum (orbitVisiblePrimeRange geometry) (fun n =>
        ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real)) *
          ((∫ t, Eplus n t) + ∫ t, Eminus n t)) ≤ 0

def orbitPhysicalKernelNodeCertificate_of_integrandCertificate
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g)
    (certificate : OrbitPhysicalKernelIntegrandCertificate geometry) :
    OrbitPhysicalKernelNodeCertificate geometry := by
  let nodeBound : Nat → Real := fun n =>
    ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real)) *
      ((∫ t, certificate.Eplus n t) + ∫ t, certificate.Eminus n t)
  refine ⟨nodeBound, ?_, ?_⟩
  · simpa [nodeBound] using certificate.arch_bound
  · intro n hn
    exact orbitPhysicalKernel_nodeTerm_le_of_integrand_bounds geometry n
      (certificate.Eplus n) (certificate.Eminus n)
      (certificate.integrable_plus n hn) (certificate.integrable_minus n hn)
      (certificate.pointwise_plus n hn) (certificate.pointwise_minus n hn)

structure OrbitPhysicalKernelOneSidedIntegrandCertificate
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) where
  E : Nat → Real → Real
  integrable : ∀ n ∈ orbitVisiblePrimeRange geometry,
    Integrable (E n)
  pointwise : ∀ n ∈ orbitVisiblePrimeRange geometry,
    ∀ᵐ t ∂(volume : Measure Real),
      (orbitWeightedKernelIntegrand geometry (Real.log n) t).re ≤ E n t
  arch_bound : archimedeanTerm g.convolutionSquare +
      Finset.sum (orbitVisiblePrimeRange geometry) (fun n =>
        ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real)) *
          (2 * (∫ t, E n t))) ≤ 0

def orbitPhysicalKernelNodeCertificate_of_oneSidedIntegrandCertificate
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g)
    (certificate : OrbitPhysicalKernelOneSidedIntegrandCertificate geometry) :
    OrbitPhysicalKernelNodeCertificate geometry := by
  let nodeBound : Nat → Real := fun n =>
    ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real)) *
      (2 * (∫ t, certificate.E n t))
  refine ⟨nodeBound, ?_, ?_⟩
  · simpa [nodeBound] using certificate.arch_bound
  · intro n hn
    exact orbitPhysicalKernel_nodeTerm_le_of_plus_integrand_bound geometry n
      (certificate.E n) (certificate.integrable n hn) (certificate.pointwise n hn)

theorem sourceRH_of_right_orbitGeometry_oneSidedIntegrandCertificate
    (hproducer : ∀ rho : sourceNontrivialZeroSet,
      (1 / 2 : Real) < rho.1.re →
        ∃ g : CompactLogTest,
          ∃ geometry : OrbitG8Geometry rho g,
            Nonempty (OrbitPhysicalKernelOneSidedIntegrandCertificate geometry)) :
    RHDefinitionBridge.standard.SourceRH := by
  apply sourceRH_of_right_orbitGeometry_physicalKernel_certificate
  intro rho hright
  obtain ⟨g, geometry, ⟨certificate⟩⟩ := hproducer rho hright
  exact ⟨g, geometry, ⟨
    orbitPhysicalKernelNodeCertificate_of_oneSidedIntegrandCertificate
      geometry certificate⟩⟩

end
end C1P2OrbitPhysicalKernelIntegrandBounds
end Source
end ConnesWeilRH
