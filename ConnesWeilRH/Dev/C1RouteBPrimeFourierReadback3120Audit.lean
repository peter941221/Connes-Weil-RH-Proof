import ConnesWeilRH.Dev.C1RouteBPrimeFourierReadback3120

namespace ConnesWeilRH.Source.C1RouteBPrimeFourierReadback3120

open MeasureTheory CCM25Concrete.CompactLogConvolution
open CC20YoshidaConvolution C1RouteBAdaptivePoweredTail3117 C1SameOwnerWeil

/-- Cycle-frequency inversion has unit mass normalization, including for
complex tests whose Fourier energy need not be even. -/
theorem cycle_mass_normalization3120 (g : CompactLogTest) :
    (g.convolutionSquare.test 0).re = ∫ xi : ℝ, energy3120 g xi := by
  simpa only [mul_zero, Real.cos_zero, one_mul] using
    square_re_eq_cosine_integral3120 g 0

theorem energy_integrable3120 (g : CompactLogTest) : Integrable (energy3120 g) := by
  simpa only [mul_zero, Real.cos_zero, one_mul] using cosine_energy_integrable3120 g 0

theorem primeWeight_zero3120 : primeWeight3120 0 = 0 := by
  simp [primeWeight3120]

theorem prime_zero_integral3120 (g : CompactLogTest) :
    finitePrimeTerm g.convolutionSquare 0 = 0 ∧
      (∫ xi : ℝ, primeWeight3120 0 *
        Real.cos (2 * Real.pi * xi * Real.log 0) * energy3120 g xi) = 0 := by
  constructor
  · rw [primeTerm_eq_cosine_integral3120]
    simp only [primeWeight_zero3120, zero_mul, integral_zero]
  · simp only [primeWeight_zero3120, zero_mul, integral_zero]

theorem empty_prime_kernel3120 (xi : ℝ) : primeKernel3120 ∅ xi = 0 := by
  simp only [primeKernel3120, Finset.sum_empty]

theorem empty_prime_integral3120 (g : CompactLogTest) :
    (∫ xi : ℝ, primeKernel3120 ∅ xi * energy3120 g xi) = 0 := by
  simp only [empty_prime_kernel3120, zero_mul, integral_zero]

/-- The boundary lambda=0 retains the complete complex orbit multiplier. -/
theorem zero_lambda_energy3120
    (rho : ℂ) (N : ℕ) (nodes : Finset ℂ) (n : ℕ) (xi : ℝ) :
    energy3120 (poweredFamilySpan3117 rho N nodes n 0) xi =
      ‖orbitMultiplier3120 rho xi‖ ^ 2 * energy3120 (poweredFamilyOwner3117 rho N nodes n) xi := by
  simpa only [Complex.ofReal_zero, sub_zero] using
    fullOrbit_span_energy3120 (poweredFamilyOwner3117 rho N nodes n) rho 0 xi

/-- A purely imaginary multiplier rules out replacing its norm by its real part. -/
theorem imaginary_multiplier_guard3120 :
    ‖Complex.I‖ ^ 2 = (1 : ℝ) ∧ Complex.I.re ^ 2 = (0 : ℝ) := by
  simp only [Complex.norm_I, one_pow, Complex.I_re, zero_pow (by decide : 2 ≠ 0), and_self]

end ConnesWeilRH.Source.C1RouteBPrimeFourierReadback3120

open ConnesWeilRH.Source.C1RouteBPrimeFourierReadback3120

#check poweredFamily_remainder_readback3120
#check poweredFamily_remainder_integrable3120
#print axioms fourier_eq_cycle_laplace3120
#print axioms square_fourier_eq_energy3120
#print axioms inverseIntegrand_integrable3120
#print axioms square_eq_inverse_integral3120
#print axioms inverseIntegrand_re3120
#print axioms cosine_energy_integrable3120
#print axioms square_re_eq_cosine_integral3120
#print axioms primeTerm_eq_cosine_integral3120
#print axioms primeKernel_energy_integrable3120
#print axioms sum_primeTerms_eq_integral3120
#print axioms primeRemainder_eq_integral3120
#print axioms primeCut_eq_integral3120
#print axioms finitePrimeSum_eq_integral3120
#print axioms fullOrbit_span_energy3120
#print axioms poweredFamily_remainder_readback3120
#print axioms poweredFamily_remainder_integrable3120
#print axioms cycle_mass_normalization3120
#print axioms energy_integrable3120
#print axioms primeWeight_zero3120
#print axioms prime_zero_integral3120
#print axioms empty_prime_kernel3120
#print axioms empty_prime_integral3120
#print axioms zero_lambda_energy3120
#print axioms imaginary_multiplier_guard3120
