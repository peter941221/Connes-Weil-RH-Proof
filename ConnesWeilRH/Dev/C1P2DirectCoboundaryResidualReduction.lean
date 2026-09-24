import ConnesWeilRH.Dev.C1P2OrbitPhysicalKernelCoboundary

namespace ConnesWeilRH
namespace Source
namespace C1P2DirectCoboundaryResidualReduction

open MeasureTheory
open CC20YoshidaConvolution
open CC20YoshidaNearZeros
open CCM25Concrete.CompactLogConvolution
open C1G8R0OrbitGeometry
open C1P2OrbitPhysicalKernelIntegrandBounds
open C1P2OrbitPhysicalKernelCoboundary
open C1P2OrbitPhysicalProfileReadback

noncomputable section

theorem orbitWeightedKernelIntegrandDerivative_continuous
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (x : Real) :
    Continuous (fun t => orbitWeightedKernelIntegrandDerivative geometry x t) := by
  let raw := orbitRawFactor geometry
  have htest : Continuous (fun t : Real => raw.test t) := raw.test.continuous
  have hderiv : Continuous (fun t : Real => deriv (raw.test : Real → Complex) t) := by
    simpa [SchwartzMap.derivCLM_apply] using
      (SchwartzMap.derivCLM ℂ ℂ raw.test).continuous
  have hneg : Continuous (fun t : Real => raw.test (-t)) :=
    htest.comp continuous_neg
  have hnegd : Continuous (fun t : Real => deriv (raw.test : Real → Complex) (-t)) :=
    hderiv.comp continuous_neg
  have hshift : Continuous (fun t : Real => raw.test (x - t)) :=
    htest.comp (continuous_const.sub continuous_id)
  have hshiftd : Continuous (fun t : Real => deriv (raw.test : Real → Complex) (x - t)) :=
    hderiv.comp (continuous_const.sub continuous_id)
  unfold orbitWeightedKernelIntegrandDerivative
  dsimp [raw]
  fun_prop

theorem orbitFinitePhysicalKernelIntegrandDerivative_continuous
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) :
    Continuous (orbitFinitePhysicalKernelIntegrandDerivative geometry) := by
  unfold orbitFinitePhysicalKernelIntegrandDerivative
  apply continuous_finsetSum
  intro n hn
  apply Continuous.const_mul
  apply Continuous.const_mul
  exact Complex.continuous_re.comp
    (orbitWeightedKernelIntegrandDerivative_continuous geometry (Real.log n))

theorem intervalIntegral_orbitFinitePhysicalKernelIntegrand_eq_actualResidual
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) :
    ∫ t in (physicalKernelWindowLeft geometry)..
        (physicalKernelWindowRight geometry),
        orbitFinitePhysicalKernelIntegrand geometry t =
      ∫ t in (physicalKernelWindowLeft geometry)..
        (physicalKernelWindowRight geometry),
        orbitPhysicalKernelCoboundaryResidual geometry t := by
  let hderiv : Real → Real :=
    fun t => orbitFinitePhysicalKernelIntegrand geometry t -
      orbitPhysicalKernelCoboundaryResidual geometry t
  have hres_cont : Continuous
      (orbitPhysicalKernelCoboundaryResidual geometry) := by
    unfold orbitPhysicalKernelCoboundaryResidual
    simpa [Pi.mul_apply] using
      (continuous_id.mul
        (orbitFinitePhysicalKernelIntegrandDerivative_continuous geometry)).neg
  have hderiv_cont : Continuous hderiv := by
    unfold hderiv
    exact (orbitFinitePhysicalKernelIntegrand_continuous geometry).sub hres_cont
  have hres_int : IntervalIntegrable
      (orbitPhysicalKernelCoboundaryResidual geometry) volume
      (physicalKernelWindowLeft geometry) (physicalKernelWindowRight geometry) :=
    hres_cont.intervalIntegrable (μ := volume) _ _
  have hderiv_int : IntervalIntegrable hderiv volume
      (physicalKernelWindowLeft geometry) (physicalKernelWindowRight geometry) :=
    hderiv_cont.intervalIntegrable (μ := volume) _ _
  have hQ := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => by
      simpa [hderiv] using
        (hasDerivAt_orbitPhysicalKernelCoboundaryQ geometry x)) hderiv_int
  have hzero :
      ∫ t in (physicalKernelWindowLeft geometry)..
          (physicalKernelWindowRight geometry), hderiv t = 0 := by
    rw [hQ, orbitPhysicalKernelCoboundaryQ_right_boundary,
      orbitPhysicalKernelCoboundaryQ_left_boundary, sub_self]
  have hderiv_zero :
      ∫ t in (physicalKernelWindowLeft geometry)..
          (physicalKernelWindowRight geometry),
          deriv (orbitPhysicalKernelCoboundaryQ geometry) t = 0 := by
    rw [← hzero]
    apply intervalIntegral.integral_congr
    intro t ht
    simpa [hderiv] using
      (hasDerivAt_orbitPhysicalKernelCoboundaryQ geometry t).deriv
  have hQ_int : IntervalIntegrable
      (fun t => deriv (orbitPhysicalKernelCoboundaryQ geometry) t) volume
      (physicalKernelWindowLeft geometry) (physicalKernelWindowRight geometry) :=
    hderiv_int.congr (fun t ht => by
      simpa [hderiv] using
        (hasDerivAt_orbitPhysicalKernelCoboundaryQ geometry t).deriv.symm)
  have hpoint : ∀ t ∈ Set.uIcc
      (physicalKernelWindowLeft geometry) (physicalKernelWindowRight geometry),
      orbitFinitePhysicalKernelIntegrand geometry t =
        deriv (orbitPhysicalKernelCoboundaryQ geometry) t +
          orbitPhysicalKernelCoboundaryResidual geometry t := by
    intro t ht
    rw [(hasDerivAt_orbitPhysicalKernelCoboundaryQ geometry t).deriv]
    ring
  calc
    ∫ t in (physicalKernelWindowLeft geometry)..
        (physicalKernelWindowRight geometry),
        orbitFinitePhysicalKernelIntegrand geometry t =
        ∫ t in (physicalKernelWindowLeft geometry)..
          (physicalKernelWindowRight geometry),
          (deriv (orbitPhysicalKernelCoboundaryQ geometry) t +
            orbitPhysicalKernelCoboundaryResidual geometry t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      exact hpoint t ht
    _ = (∫ t in (physicalKernelWindowLeft geometry)..
          (physicalKernelWindowRight geometry),
          deriv (orbitPhysicalKernelCoboundaryQ geometry) t) +
        ∫ t in (physicalKernelWindowLeft geometry)..
          (physicalKernelWindowRight geometry),
          orbitPhysicalKernelCoboundaryResidual geometry t := by
      rw [intervalIntegral.integral_add hQ_int hres_int]
    _ = ∫ t in (physicalKernelWindowLeft geometry)..
          (physicalKernelWindowRight geometry),
          orbitPhysicalKernelCoboundaryResidual geometry t := by
      rw [hderiv_zero, zero_add]

end
end C1P2DirectCoboundaryResidualReduction
end Source
end ConnesWeilRH
