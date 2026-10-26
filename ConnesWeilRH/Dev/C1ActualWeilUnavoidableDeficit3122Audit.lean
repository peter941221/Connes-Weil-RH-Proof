import ConnesWeilRH.Dev.C1ActualWeilUnavoidableDeficit3122

namespace ConnesWeilRH.Source.C1ActualWeilUnavoidableDeficit3122

open MeasureTheory CCM25Concrete.CompactLogConvolution CC20YoshidaConvolution
open CC20YoshidaConvolution.CompactLogTest CC20YoshidaNearZeros
open C1RouteBPrimeFourierReadback3120 C1RouteBAdaptivePoweredTail3117
open C1FourPointSpectralPrefixTransport C1TwoPointSpectralDecomposition C1HealthyYoshidaDetector
open scoped FourierTransform

theorem density_zero_at_origin_of_transform_zero3122
    (g : CompactLogTest) (hzero : (𝓕 g.test) (0 : ℝ) = 0) :
    weilDensity3122 g 0 = 0 ∧ deficitDensity3122 g 0 = 0 := by
  simp [weilDensity3122, deficitDensity3122, energy3120, hzero]

theorem deficit_zero_of_zero_test3122 (g : CompactLogTest) (hg : g.test = 0) :
    (∫ xi : ℝ, deficitDensity3122 g xi) = 0 := by
  simp [deficitDensity3122, weilDensity3122, energy3120, hg]

theorem poweredFamily_span_fourier_zero3122
    (rho : sourceNontrivialZeroSet) (hright : (1 / 2 : ℝ) < rho.1.re)
    (N : ℕ) (nodes : Finset ℂ) (n : ℕ) (lambda : ℝ) :
    (𝓕 (poweredFamilySpan3117 rho.1 N nodes n lambda).test) (0 : ℝ) = 0 := by
  have hv := poweredFamily_cc20_vanishes3117 rho hright N nodes n
  have hg : laplaceAt (poweredFamilyOwner3117 rho.1 N nodes n) (0 : ℂ) = 0 := by
    simpa [C1.healthyMellinReadoff, criticalVanishingPointValue] using
      hv CriticalVanishingPoint.zero (by simp [cc20TripleFiniteVanishingSet])
  have hs : laplaceAt (poweredFamilySpan3117 rho.1 N nodes n lambda) (0 : ℂ) = 0 := by
    change laplaceAt (annihilatorDetectorSpanVector _ _ _) _ = _
    rw [laplaceAt_fullOrbitSpanVector, hg, mul_zero]
  rw [fourier_eq_cycle_laplace3120]
  simpa only [cyclePoint3120, mul_zero, Complex.ofReal_zero, zero_mul] using hs

/-- An actual vanishing frequency does not erase the positive integrated deficit. -/
theorem zero_at_origin_and_strict_deficit3122
    (rho : sourceNontrivialZeroSet) (hright : (1 / 2 : ℝ) < rho.1.re)
    (N : ℕ) (nodes : Finset ℂ) (n : ℕ) (lambda : ℝ) (hlambda : lambda ≠ 0) :
    weilDensity3122 (poweredFamilySpan3117 rho.1 N nodes n lambda) 0 = 0 ∧
      0 < ∫ xi : ℝ, deficitDensity3122 (poweredFamilySpan3117 rho.1 N nodes n lambda) xi := by
  exact ⟨(density_zero_at_origin_of_transform_zero3122 _
      (poweredFamily_span_fourier_zero3122 rho hright N nodes n lambda)).1,
    poweredFamily_deficit_integral_pos3122 rho.1 N nodes n lambda hlambda⟩

end ConnesWeilRH.Source.C1ActualWeilUnavoidableDeficit3122

open ConnesWeilRH.Source.C1ActualWeilUnavoidableDeficit3122

#check selectedOwner_deficit_integral_pos3122
#check poweredFamily_deficit_integral_pos3122
#print axioms c3Sigma_continuous3122
#print axioms gateSymbol_continuous3122
#print axioms weilDensity_continuous3122
#print axioms gateSymbol_zero_pos3122
#print axioms fourier_analytic3122
#print axioms fourier_global_nonzero3122
#print axioms exists_deficit_frequency3122
#print axioms weilDensity_integrable3122
#print axioms credit_integrable3122
#print axioms deficit_integrable3122
#print axioms deficit_integral_pos3122
#print axioms not_weilDensity_pointwise_nonneg3122
#print axioms density_eq_credit_sub_deficit3122
#print axioms qw_eq_credit_sub_deficit3122
#print axioms poweredFamily_span_test_ne_zero3122
#print axioms poweredFamily_deficit_integral_pos3122
#print axioms selectedOwner_deficit_integral_pos3122
#print axioms density_zero_at_origin_of_transform_zero3122
#print axioms deficit_zero_of_zero_test3122
#print axioms poweredFamily_span_fourier_zero3122
#print axioms zero_at_origin_and_strict_deficit3122
