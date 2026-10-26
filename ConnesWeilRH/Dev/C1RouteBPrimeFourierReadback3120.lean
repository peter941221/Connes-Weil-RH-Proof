import ConnesWeilRH.Dev.C1RouteBSignedPrimeCut3119
import ConnesWeilRH.Dev.C1XiArithmeticPrimePowerReadback

/-! Complete physical prime remainder as an exact Fourier integral on the
actual powered span. Frequency is cycles per unit; no extra 2*pi measure
factor is inserted. No evenness, gate sign or numerical value is assumed. -/

namespace ConnesWeilRH.Source.C1RouteBPrimeFourierReadback3120

open MeasureTheory CCM25Concrete.CompactLogConvolution
open CC20YoshidaConvolution CC20YoshidaConvolution.CompactLogTest
open C1XiArithmeticPrimePowerReadback C1HealthyYoshidaDetector C1SameOwnerWeil
open C1RouteBSignedPrimeCut3119 C1RouteBAdaptivePoweredTail3117
open C1FourPointSpectralPrefixTransport C1TwoPointSpectralDecomposition
open scoped FourierTransform BigOperators

noncomputable section

def cyclePoint3120 (xi : ℝ) : ℂ := ((-2 * Real.pi * xi : ℝ) : ℂ) * Complex.I

theorem fourier_eq_cycle_laplace3120 (g : CompactLogTest) (xi : ℝ) :
    (𝓕 g.test) xi = laplaceAt g (cyclePoint3120 xi) := by
  have h := fourierLaplace_eq_fourier g.test (-2 * Real.pi * xi)
  have harg : -((-2 * Real.pi * xi) / (2 * Real.pi)) = xi := by
    field_simp [Real.pi_ne_zero]
  rw [harg, fourierLaplace_compactLogTest_test_eq_laplaceAt] at h
  exact h.symm

theorem square_fourier_eq_energy3120 (g : CompactLogTest) (xi : ℝ) :
    (𝓕 g.convolutionSquare.test) xi = ((‖(𝓕 g.test) xi‖ ^ 2 : ℝ) : ℂ) := by
  rw [fourier_eq_cycle_laplace3120, laplaceAt_convolutionSquare]
  have hs : -star (cyclePoint3120 xi) = cyclePoint3120 xi := by
    simp [cyclePoint3120, star_mul]
    ring
  rw [hs, ← fourier_eq_cycle_laplace3120]
  simp only [Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
    Complex.normSq_eq_norm_sq, Complex.ofReal_pow]

def energy3120 (g : CompactLogTest) (xi : ℝ) : ℝ := ‖(𝓕 g.test) xi‖ ^ 2

def inverseIntegrand3120 (g : CompactLogTest) (x xi : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * xi * x : ℝ) : ℂ) * Complex.I) *
    (energy3120 g xi : ℂ)

theorem inverseIntegrand_integrable3120 (g : CompactLogTest) (x : ℝ) :
    Integrable (inverseIntegrand3120 g x) := by
  have hft : Integrable (fun xi : ℝ => (𝓕 g.convolutionSquare.test) xi) :=
    (𝓕 g.convolutionSquare.test).integrable
  have h := hft.mul_bdd
    (g := fun xi : ℝ => Complex.exp (((2 * Real.pi * xi * x : ℝ) : ℂ) * Complex.I))
    (c := 1) (by
      exact (show Continuous (fun xi : ℝ =>
        Complex.exp (((2 * Real.pi * xi * x : ℝ) : ℂ) * Complex.I)) by
          fun_prop).aestronglyMeasurable) (by
      filter_upwards with xi
      rw [Complex.norm_exp]
      simp)
  apply h.congr
  filter_upwards with xi
  simp only [inverseIntegrand3120, square_fourier_eq_energy3120, energy3120]
  ring

theorem square_eq_inverse_integral3120 (g : CompactLogTest) (x : ℝ) :
    g.convolutionSquare.test x = ∫ xi : ℝ, inverseIntegrand3120 g x xi := by
  have hinv : 𝓕⁻ (𝓕 g.convolutionSquare.test) x = g.convolutionSquare.test x := by
    simpa only [SchwartzMap.fourierInv_coe, SchwartzMap.fourier_coe] using
      (g.convolutionSquare.test.integrable.fourierInv_fourier_eq
        (𝓕 g.convolutionSquare.test).integrable g.convolutionSquare.test.continuous.continuousAt)
  rw [← hinv, SchwartzMap.fourierInv_coe, Real.fourierInv_eq']
  apply integral_congr_ae
  filter_upwards with xi
  simp only [inverseIntegrand3120, energy3120, square_fourier_eq_energy3120,
    smul_eq_mul, Real.inner_apply]
  congr 2
  push_cast
  ring

theorem inverseIntegrand_re3120 (g : CompactLogTest) (x xi : ℝ) :
    (inverseIntegrand3120 g x xi).re =
      Real.cos (2 * Real.pi * xi * x) * energy3120 g xi := by
  simp [inverseIntegrand3120, Complex.mul_re, Complex.exp_re]

theorem cosine_energy_integrable3120 (g : CompactLogTest) (x : ℝ) :
    Integrable (fun xi : ℝ => Real.cos (2 * Real.pi * xi * x) * energy3120 g xi) := by
  have h := (inverseIntegrand_integrable3120 g x).re
  change Integrable (fun xi => (inverseIntegrand3120 g x xi).re) at h
  simpa only [inverseIntegrand_re3120] using h

theorem square_re_eq_cosine_integral3120 (g : CompactLogTest) (x : ℝ) :
    (g.convolutionSquare.test x).re =
      ∫ xi : ℝ, Real.cos (2 * Real.pi * xi * x) * energy3120 g xi := by
  have h := integral_re (inverseIntegrand_integrable3120 g x)
  change (∫ xi : ℝ, (inverseIntegrand3120 g x xi).re) =
    (∫ xi : ℝ, inverseIntegrand3120 g x xi).re at h
  rw [square_eq_inverse_integral3120, ← h]
  simp only [inverseIntegrand_re3120]

def primeWeight3120 (q : ℕ) : ℝ := 2 * ArithmeticFunction.vonMangoldt q / Real.sqrt q

def primeKernel3120 (S : Finset ℕ) (xi : ℝ) : ℝ :=
  ∑ q ∈ S, primeWeight3120 q * Real.cos (2 * Real.pi * xi * Real.log q)

theorem primeTerm_eq_cosine_integral3120 (g : CompactLogTest) (q : ℕ) :
    finitePrimeTerm g.convolutionSquare q =
      ∫ xi : ℝ, primeWeight3120 q *
        Real.cos (2 * Real.pi * xi * Real.log q) * energy3120 g xi := by
  have hterm : finitePrimeTerm g.convolutionSquare q =
      primeWeight3120 q * (g.convolutionSquare.test (Real.log q)).re := by
    unfold finitePrimeTerm finitePrimeTermComplex
    rw [g.convolutionSquare_neg]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.add_re, Complex.add_im, Complex.star_def, Complex.conj_re,
      Complex.conj_im, zero_mul, sub_zero]
    unfold primeWeight3120
    ring
  rw [hterm, square_re_eq_cosine_integral3120, ← integral_const_mul]
  congr 1
  funext xi
  ring

theorem primeKernel_energy_integrable3120 (g : CompactLogTest) (S : Finset ℕ) :
    Integrable (fun xi : ℝ => primeKernel3120 S xi * energy3120 g xi) := by
  have h := integrable_finsetSum S (fun q _ =>
    (cosine_energy_integrable3120 g (Real.log q)).const_mul (primeWeight3120 q))
  simpa only [primeKernel3120, Finset.sum_mul, mul_assoc] using h

theorem sum_primeTerms_eq_integral3120 (g : CompactLogTest) (S : Finset ℕ) :
    (∑ q ∈ S, finitePrimeTerm g.convolutionSquare q) =
      ∫ xi : ℝ, primeKernel3120 S xi * energy3120 g xi := by
  calc
    _ = ∑ q ∈ S, ∫ xi : ℝ, primeWeight3120 q *
        (Real.cos (2 * Real.pi * xi * Real.log q) * energy3120 g xi) := by
      apply Finset.sum_congr rfl
      intro q _
      simpa only [mul_assoc] using primeTerm_eq_cosine_integral3120 g q
    _ = ∫ xi : ℝ, ∑ q ∈ S, primeWeight3120 q *
        (Real.cos (2 * Real.pi * xi * Real.log q) * energy3120 g xi) :=
      (integral_finsetSum S (fun q _ =>
        (cosine_energy_integrable3120 g (Real.log q)).const_mul (primeWeight3120 q))).symm
    _ = _ := by simp only [primeKernel3120, Finset.sum_mul, mul_assoc]

theorem primeRemainder_eq_integral3120 (g : CompactLogTest) (M : ℕ) :
    primeRemainder3119 g.convolutionSquare M =
      ∫ xi : ℝ, primeKernel3120
        ((globalPrimeIndexSet g.convolutionSquare).filter (fun q => M < q)) xi *
          energy3120 g xi :=
  sum_primeTerms_eq_integral3120 g _

theorem primeCut_eq_integral3120 (g : CompactLogTest) (M : ℕ) :
    primeCut3119 g.convolutionSquare M =
      ∫ xi : ℝ, primeKernel3120 (Finset.range (M + 1)) xi * energy3120 g xi :=
  sum_primeTerms_eq_integral3120 g _

theorem finitePrimeSum_eq_integral3120 (g : CompactLogTest) :
    finitePrimeSum g.convolutionSquare =
      ∫ xi : ℝ, primeKernel3120 (globalPrimeIndexSet g.convolutionSquare) xi *
        energy3120 g xi :=
  sum_primeTerms_eq_integral3120 g _

def orbitMultiplier3120 (rho : ℂ) (xi : ℝ) : ℂ :=
  (((1 - rho) - 1 / 2 - cyclePoint3120 xi) * (star rho - 1 / 2 - cyclePoint3120 xi) *
    ((1 - star rho) - 1 / 2 - cyclePoint3120 xi) * (rho - 1 / 2 - cyclePoint3120 xi))

theorem fullOrbit_span_energy3120 (g : CompactLogTest) (rho : ℂ) (lambda xi : ℝ) :
    energy3120 (annihilatorDetectorSpanVector (fullFunctionalEquationOrbitAnnihilator g rho)
      g lambda) xi = ‖orbitMultiplier3120 rho xi - (lambda : ℂ)‖ ^ 2 * energy3120 g xi := by
  simp only [energy3120, fourier_eq_cycle_laplace3120]
  rw [laplaceAt_fullOrbitSpanVector, norm_mul, mul_pow]
  rfl

theorem poweredFamily_remainder_readback3120
    (rho : ℂ) (N : ℕ) (nodes : Finset ℂ) (n : ℕ) (lambda : ℝ) (M : ℕ) :
    primeRemainder3119 (poweredFamilySpan3117 rho N nodes n lambda).convolutionSquare M =
      ∫ xi : ℝ, primeKernel3120
        ((globalPrimeIndexSet (poweredFamilySpan3117 rho N nodes n lambda).convolutionSquare).filter
          (fun q => M < q)) xi * ‖orbitMultiplier3120 rho xi - (lambda : ℂ)‖ ^ 2 *
            energy3120 (poweredFamilyOwner3117 rho N nodes n) xi := by
  rw [primeRemainder_eq_integral3120]
  apply integral_congr_ae
  filter_upwards with xi
  rw [show energy3120 (poweredFamilySpan3117 rho N nodes n lambda) xi = _ from
    fullOrbit_span_energy3120 _ rho lambda xi]
  ring

theorem poweredFamily_remainder_integrable3120
    (rho : ℂ) (N : ℕ) (nodes : Finset ℂ) (n : ℕ) (lambda : ℝ) (M : ℕ) :
    Integrable (fun xi : ℝ => primeKernel3120
      ((globalPrimeIndexSet (poweredFamilySpan3117 rho N nodes n lambda).convolutionSquare).filter
        (fun q => M < q)) xi * ‖orbitMultiplier3120 rho xi - (lambda : ℂ)‖ ^ 2 *
          energy3120 (poweredFamilyOwner3117 rho N nodes n) xi) := by
  apply (primeKernel_energy_integrable3120 (poweredFamilySpan3117 rho N nodes n lambda)
    ((globalPrimeIndexSet (poweredFamilySpan3117 rho N nodes n lambda).convolutionSquare).filter
      (fun q => M < q))).congr
  filter_upwards with xi
  rw [show energy3120 (poweredFamilySpan3117 rho N nodes n lambda) xi = _ from
    fullOrbit_span_energy3120 _ rho lambda xi]
  ring

end
end ConnesWeilRH.Source.C1RouteBPrimeFourierReadback3120
