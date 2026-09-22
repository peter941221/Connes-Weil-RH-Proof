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

theorem orbitWeightedKernelIntegrand_eq_zero_of_not_mem_raw_support_window
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (x t : Real)
    (ht : t ∉ Set.Ioo
      (-((geometry.orbitIndex + 2 : Nat) : Real))
      (((geometry.orbitIndex + 2 : Nat) : Real))) :
    orbitWeightedKernelIntegrand geometry x t = 0 := by
  let raw := orbitRawFactor geometry
  have hneg : raw.test (-t) = 0 := by
    by_contra hne
    have hmem : -t ∈ Function.support raw.test :=
      Function.mem_support.mpr hne
    have hwindow := orbitRawFactor_support_subset geometry hmem
    apply ht
    constructor <;> linarith [hwindow.1, hwindow.2]
  simp [orbitWeightedKernelIntegrand, raw, hneg]

theorem norm_orbitWeightedKernelIntegrand_le_seminorm_majorant
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (x t : Real)
    (ht : t ∈ Set.Ioo
      (-((geometry.orbitIndex + 2 : Nat) : Real))
      (((geometry.orbitIndex + 2 : Nat) : Real))) :
    ‖orbitWeightedKernelIntegrand geometry x t‖ ≤
      Real.exp (x / 2 + ((geometry.orbitIndex + 2 : Nat) : Real)) *
        (SchwartzMap.seminorm ℂ 0 0 (orbitRawFactor geometry).test) ^ 2 := by
  let raw := orbitRawFactor geometry
  let S : Real := SchwartzMap.seminorm ℂ 0 0 raw.test
  have hleft : ‖raw.test (-t)‖ ≤ S := by
    exact SchwartzMap.norm_le_seminorm ℂ raw.test (-t)
  have hright : ‖raw.test (x - t)‖ ≤ S := by
    exact SchwartzMap.norm_le_seminorm ℂ raw.test (x - t)
  have hexp : Real.exp (x / 2 - t) ≤
      Real.exp (x / 2 + ((geometry.orbitIndex + 2 : Nat) : Real)) := by
    apply Real.exp_le_exp.mpr
    linarith [ht.1]
  have hscale : ‖Complex.exp (((x / 2 - t : Real) : Complex))‖ =
      Real.exp (x / 2 - t) := by
    rw [Complex.norm_exp]
    simp
  have hS : 0 ≤ S := by
    dsimp [S]
    positivity
  calc
    ‖orbitWeightedKernelIntegrand geometry x t‖ =
        Real.exp (x / 2 - t) * ‖raw.test (-t)‖ * ‖raw.test (x - t)‖ := by
      rw [orbitWeightedKernelIntegrand, norm_mul, norm_mul, norm_star,
        Complex.norm_exp]
      simpa [raw]
    _ ≤ Real.exp (x / 2 - t) * S * S := by
      simpa only [mul_assoc] using
        (mul_le_mul_of_nonneg_left
          (mul_le_mul hleft hright (norm_nonneg _) hS) (Real.exp_pos _).le)
    _ ≤ Real.exp (x / 2 + ((geometry.orbitIndex + 2 : Nat) : Real)) * S * S := by
      simpa only [mul_assoc] using
        (mul_le_mul_of_nonneg_right hexp (mul_nonneg hS hS))
    _ = Real.exp (x / 2 + ((geometry.orbitIndex + 2 : Nat) : Real)) *
        (SchwartzMap.seminorm ℂ 0 0 raw.test) ^ 2 := by
      simp [S, pow_two, mul_assoc]

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

def orbitNegativeIntegrandMajorant
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (n : Nat) : Real → Real :=
  fun t => max
    (-(orbitWeightedKernelIntegrand geometry (Real.log n) t).re) 0

theorem orbitNegativeIntegrandMajorant_integrable
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (n : Nat) :
    Integrable (orbitNegativeIntegrandMajorant geometry n) := by
  have hreal : Integrable (fun t =>
      (orbitWeightedKernelIntegrand geometry (Real.log n) t).re) :=
    Complex.reCLM.integrable_comp
      (orbitWeightedKernelIntegrand_integrable geometry (Real.log n))
  have hneg := hreal.neg
  have hmax := hneg.norm.mono_nonneg
    (by fun_prop : AEStronglyMeasurable
      (fun t : Real => max
        (-(orbitWeightedKernelIntegrand geometry (Real.log n) t).re) 0) volume)
    (Filter.Eventually.of_forall (fun t => le_max_right _ _))
    (Filter.Eventually.of_forall (fun t =>
      max_le (le_abs_self _) (abs_nonneg _)))
  simpa [orbitNegativeIntegrandMajorant, Real.norm_eq_abs, abs_neg] using hmax

theorem orbitPositive_sub_negative_eq_integrand_re
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (n : Nat) (t : Real) :
    orbitPositiveIntegrandMajorant geometry n t -
        orbitNegativeIntegrandMajorant geometry n t =
      (orbitWeightedKernelIntegrand geometry (Real.log n) t).re := by
  by_cases h : 0 ≤ (orbitWeightedKernelIntegrand geometry (Real.log n) t).re
  · have hneg : -(orbitWeightedKernelIntegrand geometry (Real.log n) t).re ≤ 0 :=
      neg_nonpos.mpr h
    simp [orbitPositiveIntegrandMajorant, orbitNegativeIntegrandMajorant,
      max_eq_left h, max_eq_right hneg]
  · have hnonpos : (orbitWeightedKernelIntegrand geometry (Real.log n) t).re ≤ 0 :=
      le_of_not_ge h
    have hneg : 0 ≤ -(orbitWeightedKernelIntegrand geometry (Real.log n) t).re :=
      neg_nonneg.mpr hnonpos
    simp [orbitPositiveIntegrandMajorant, orbitNegativeIntegrandMajorant,
      max_eq_right hnonpos, max_eq_left hneg]

theorem orbitPhysicalKernel_re_eq_positive_sub_negative
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (n : Nat) :
    (orbitPhysicalKernel geometry (Real.log n)).re =
      (∫ t, orbitPositiveIntegrandMajorant geometry n t) -
        ∫ t, orbitNegativeIntegrandMajorant geometry n t := by
  have hpos := orbitPositiveIntegrandMajorant_integrable geometry n
  have hneg := orbitNegativeIntegrandMajorant_integrable geometry n
  have hreal : Integrable (fun t =>
      (orbitWeightedKernelIntegrand geometry (Real.log n) t).re) :=
    Complex.reCLM.integrable_comp
      (orbitWeightedKernelIntegrand_integrable geometry (Real.log n))
  have hsum :
      (∫ t, orbitPositiveIntegrandMajorant geometry n t) -
        ∫ t, orbitNegativeIntegrandMajorant geometry n t =
      ∫ t, (orbitWeightedKernelIntegrand geometry (Real.log n) t).re := by
    rw [← integral_sub hpos hneg]
    apply integral_congr_ae
    filter_upwards with t
    exact orbitPositive_sub_negative_eq_integrand_re geometry n t
  have hre : (orbitPhysicalKernel geometry (Real.log n)).re =
      ∫ t, (orbitWeightedKernelIntegrand geometry (Real.log n) t).re := by
    rw [orbitPhysicalKernel_eq_integral_weightedKernel geometry (Real.log n)]
    symm
    simpa only [Complex.reCLM_apply] using
      (Complex.reCLM.integral_comp_comm
        (orbitWeightedKernelIntegrand_integrable geometry (Real.log n)))
  exact hre.trans hsum.symm

theorem orbitPhysicalKernel_nodeTerm_eq_positive_sub_negative
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (n : Nat) :
    ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real)) *
        (orbitPhysicalKernel geometry (Real.log n) +
          orbitPhysicalKernel geometry (-Real.log n)).re =
      ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real)) *
        (2 * ((∫ t, orbitPositiveIntegrandMajorant geometry n t) -
          ∫ t, orbitNegativeIntegrandMajorant geometry n t)) := by
  have hconj : orbitPhysicalKernel geometry (Real.log n) +
      star (orbitPhysicalKernel geometry (Real.log n)) =
      ((2 * (orbitPhysicalKernel geometry (Real.log n)).re : Real) : Complex) := by
    rw [Complex.star_def]
    exact Complex.add_conj _
  rw [orbitPhysicalKernel_neg_eq_star geometry (Real.log n), hconj]
  simp only [Complex.ofReal_re]
  rw [orbitPhysicalKernel_re_eq_positive_sub_negative geometry n]

theorem finitePrimeSum_eq_positive_sub_negative_integrals
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) :
    finitePrimeSum g.convolutionSquare =
      Finset.sum (orbitVisiblePrimeRange geometry) (fun n =>
        ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real)) *
          (2 * ((∫ t, orbitPositiveIntegrandMajorant geometry n t) -
            ∫ t, orbitNegativeIntegrandMajorant geometry n t))) := by
  rw [finitePrimeSum_eq_orbitPhysicalKernel_range geometry]
  apply Finset.sum_congr rfl
  intro n _hn
  exact orbitPhysicalKernel_nodeTerm_eq_positive_sub_negative geometry n

theorem orbitWindowSemiLocalGate_iff_positive_sub_negative_integral_budget
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) :
    C1OrbitWindowSemiLocalGate.orbitWindowSemiLocalGate g ↔
      archimedeanTerm g.convolutionSquare +
          Finset.sum (orbitVisiblePrimeRange geometry) (fun n =>
            ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real)) *
              (2 * ((∫ t, orbitPositiveIntegrandMajorant geometry n t) -
                ∫ t, orbitNegativeIntegrandMajorant geometry n t))) ≤ 0 := by
  rw [orbitWindowSemiLocalGate_iff_physicalKernelBudget geometry]
  have hsum :
      Finset.sum (orbitVisiblePrimeRange geometry) (fun n =>
        ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real)) *
          (orbitPhysicalKernel geometry (Real.log n) +
            orbitPhysicalKernel geometry (-Real.log n)).re) =
      Finset.sum (orbitVisiblePrimeRange geometry) (fun n =>
        ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real)) *
          (2 * ((∫ t, orbitPositiveIntegrandMajorant geometry n t) -
            ∫ t, orbitNegativeIntegrandMajorant geometry n t))) := by
    apply Finset.sum_congr rfl
    intro n _hn
    exact orbitPhysicalKernel_nodeTerm_eq_positive_sub_negative geometry n
  rw [hsum]

def orbitFiniteSignedPhysicalIntegrand
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) : Real → Real :=
  fun t => Finset.sum (orbitVisiblePrimeRange geometry) (fun n =>
    ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real)) *
      (2 * (orbitPositiveIntegrandMajorant geometry n t -
        orbitNegativeIntegrandMajorant geometry n t)))

theorem orbitFiniteSignedPhysicalIntegrand_integrable
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) :
    Integrable (orbitFiniteSignedPhysicalIntegrand geometry) := by
  unfold orbitFiniteSignedPhysicalIntegrand
  apply MeasureTheory.integrable_finsetSum
  intro n _hn
  have hdiff :=
    (orbitPositiveIntegrandMajorant_integrable geometry n).sub
      (orbitNegativeIntegrandMajorant_integrable geometry n)
  have h := hdiff.const_mul
    (2 * (ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real))))
  convert h using 1
  funext t
  simp only [Pi.sub_apply]
  ring

theorem finitePrimeSum_eq_integral_finiteSignedPhysicalIntegrand
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) :
    finitePrimeSum g.convolutionSquare =
      ∫ t, orbitFiniteSignedPhysicalIntegrand geometry t := by
  rw [finitePrimeSum_eq_positive_sub_negative_integrals geometry]
  unfold orbitFiniteSignedPhysicalIntegrand
  symm
  rw [MeasureTheory.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro n _hn
    rw [MeasureTheory.integral_const_mul]
    rw [MeasureTheory.integral_const_mul]
    rw [MeasureTheory.integral_sub
      (orbitPositiveIntegrandMajorant_integrable geometry n)
      (orbitNegativeIntegrandMajorant_integrable geometry n)]
  · intro n _hn
    have hdiff :=
      (orbitPositiveIntegrandMajorant_integrable geometry n).sub
        (orbitNegativeIntegrandMajorant_integrable geometry n)
    have h := hdiff.const_mul
      (2 * (ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real))))
    convert h using 1
    funext t
    simp only [Pi.sub_apply]
    ring

def orbitFinitePhysicalKernelIntegrand
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) : Real → Real :=
  fun t => Finset.sum (orbitVisiblePrimeRange geometry) (fun n =>
    ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real)) *
      (2 * (orbitWeightedKernelIntegrand geometry (Real.log n) t).re))

def orbitFiniteComplexPhysicalKernelIntegrand
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) : Real → Complex :=
  fun t => Finset.sum (orbitVisiblePrimeRange geometry) (fun n =>
    ((2 * (ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real))) : Real) : Complex) *
      orbitWeightedKernelIntegrand geometry (Real.log n) t)

def orbitFiniteComplexPhysicalKernelProfile
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) : Real → Complex :=
  fun t => Finset.sum (orbitVisiblePrimeRange geometry) (fun n =>
    ((2 * (ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real))) : Real) : Complex) *
      Complex.exp (((Real.log n / 2 - t : Real) : Complex)) *
        (orbitRawFactor geometry).test (Real.log n - t))

theorem orbitFiniteComplexPhysicalKernelIntegrand_eq_common_factor_profile
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (t : Real) :
    orbitFiniteComplexPhysicalKernelIntegrand geometry t =
      star ((orbitRawFactor geometry).test (-t)) *
        orbitFiniteComplexPhysicalKernelProfile geometry t := by
  unfold orbitFiniteComplexPhysicalKernelIntegrand
    orbitFiniteComplexPhysicalKernelProfile orbitWeightedKernelIntegrand
  calc
    _ = Finset.sum (orbitVisiblePrimeRange geometry) (fun n =>
        star ((orbitRawFactor geometry).test (-t)) *
          (((2 * (ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real))) : Real) : Complex) *
            Complex.exp (((Real.log n / 2 - t : Real) : Complex)) *
              (orbitRawFactor geometry).test (Real.log n - t))) := by
      apply Finset.sum_congr rfl
      intro n _hn
      ring
    _ = _ := by rw [Finset.mul_sum]

theorem norm_orbitFiniteComplexPhysicalKernelIntegrand_eq_common_factor_profile
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (t : Real) :
    ‖orbitFiniteComplexPhysicalKernelIntegrand geometry t‖ =
      ‖(orbitRawFactor geometry).test (-t)‖ *
        ‖orbitFiniteComplexPhysicalKernelProfile geometry t‖ := by
  rw [orbitFiniteComplexPhysicalKernelIntegrand_eq_common_factor_profile geometry t]
  rw [norm_mul, norm_star]

theorem orbitFinitePhysicalKernelIntegrand_eq_re_complex
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (t : Real) :
    orbitFinitePhysicalKernelIntegrand geometry t =
      (orbitFiniteComplexPhysicalKernelIntegrand geometry t).re := by
  unfold orbitFinitePhysicalKernelIntegrand orbitFiniteComplexPhysicalKernelIntegrand
  change _ = Complex.reCLM (Finset.sum (orbitVisiblePrimeRange geometry) (fun n =>
    ((2 * (ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real))) : Real) : Complex) *
      orbitWeightedKernelIntegrand geometry (Real.log n) t))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n _hn
  simp only [Complex.reCLM_apply, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]
  ring

theorem orbitFiniteComplexPhysicalKernelIntegrand_integrable
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) :
    Integrable (orbitFiniteComplexPhysicalKernelIntegrand geometry) := by
  unfold orbitFiniteComplexPhysicalKernelIntegrand
  apply MeasureTheory.integrable_finsetSum
  intro n _hn
  exact (orbitWeightedKernelIntegrand_integrable geometry (Real.log n)).const_mul _

theorem abs_orbitFinitePhysicalKernelIntegrand_le_seminorm_budget
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (t : Real)
    (ht : t ∈ Set.Ioo
      (-((geometry.orbitIndex + 2 : Nat) : Real))
      (((geometry.orbitIndex + 2 : Nat) : Real))) :
    |orbitFinitePhysicalKernelIntegrand geometry t| ≤
      Finset.sum (orbitVisiblePrimeRange geometry) (fun n =>
        2 * (ArithmeticFunction.vonMangoldt n *
          (1 / Real.sqrt (n : Real))) *
          (Real.exp (Real.log n / 2 +
            ((geometry.orbitIndex + 2 : Nat) : Real)) *
            (SchwartzMap.seminorm ℂ 0 0 (orbitRawFactor geometry).test) ^ 2)) := by
  unfold orbitFinitePhysicalKernelIntegrand
  calc
    |(∑ n ∈ orbitVisiblePrimeRange geometry,
        ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real)) *
          (2 * (orbitWeightedKernelIntegrand geometry (Real.log n) t).re))| ≤
        ∑ n ∈ orbitVisiblePrimeRange geometry,
          |ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real)) *
            (2 * (orbitWeightedKernelIntegrand geometry (Real.log n) t).re)| :=
      Finset.abs_sum_le_sum_abs
        (s := orbitVisiblePrimeRange geometry)
        (f := fun n => ArithmeticFunction.vonMangoldt n *
          (1 / Real.sqrt (n : Real)) *
            (2 * (orbitWeightedKernelIntegrand geometry (Real.log n) t).re))
    _ ≤ ∑ n ∈ orbitVisiblePrimeRange geometry,
        2 * (ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real))) *
          (Real.exp (Real.log n / 2 +
            ((geometry.orbitIndex + 2 : Nat) : Real)) *
            (SchwartzMap.seminorm ℂ 0 0 (orbitRawFactor geometry).test) ^ 2) := by
      apply Finset.sum_le_sum
      intro n hn
      have hcoeff : 0 ≤ ArithmeticFunction.vonMangoldt n *
          (1 / Real.sqrt (n : Real)) := by
        exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
      have hreal : |(orbitWeightedKernelIntegrand geometry (Real.log n) t).re| ≤
          ‖orbitWeightedKernelIntegrand geometry (Real.log n) t‖ :=
        Complex.abs_re_le_norm _
      have htwo : |2 * (orbitWeightedKernelIntegrand
          geometry (Real.log n) t).re| ≤
          2 * ‖orbitWeightedKernelIntegrand geometry (Real.log n) t‖ := by
        rw [abs_mul, abs_of_nonneg (by norm_num)]
        exact mul_le_mul_of_nonneg_left hreal (by norm_num)
      have hnorm := norm_orbitWeightedKernelIntegrand_le_seminorm_majorant
        geometry (Real.log n) t ht
      calc
        |ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real)) *
            (2 * (orbitWeightedKernelIntegrand geometry (Real.log n) t).re)| =
            (ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real))) *
              |2 * (orbitWeightedKernelIntegrand geometry
                (Real.log n) t).re| := by
          rw [abs_mul, abs_of_nonneg hcoeff]
        _ ≤ (ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real))) *
            (2 * ‖orbitWeightedKernelIntegrand geometry (Real.log n) t‖) :=
          mul_le_mul_of_nonneg_left htwo hcoeff
        _ ≤ (ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real))) *
            (2 * (Real.exp (Real.log n / 2 +
              ((geometry.orbitIndex + 2 : Nat) : Real)) *
              (SchwartzMap.seminorm ℂ 0 0 (orbitRawFactor geometry).test) ^ 2)) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hnorm (by norm_num)) hcoeff
        _ = 2 * (ArithmeticFunction.vonMangoldt n *
              (1 / Real.sqrt (n : Real))) *
            (Real.exp (Real.log n / 2 +
              ((geometry.orbitIndex + 2 : Nat) : Real)) *
              (SchwartzMap.seminorm ℂ 0 0 (orbitRawFactor geometry).test) ^ 2) := by
          ring

theorem orbitFinitePhysicalKernelIntegrand_eq_zero_of_not_mem_raw_support_window
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (t : Real)
    (ht : t ∉ Set.Ioo
      (-((geometry.orbitIndex + 2 : Nat) : Real))
      (((geometry.orbitIndex + 2 : Nat) : Real))) :
    orbitFinitePhysicalKernelIntegrand geometry t = 0 := by
  unfold orbitFinitePhysicalKernelIntegrand
  apply Finset.sum_eq_zero
  intro n hn
  rw [orbitWeightedKernelIntegrand_eq_zero_of_not_mem_raw_support_window
    geometry (Real.log n) t ht]
  simp

theorem integral_orbitFinitePhysicalKernelIntegrand_eq_interval
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) :
    ∫ t, orbitFinitePhysicalKernelIntegrand geometry t =
      ∫ t in (-((geometry.orbitIndex + 2 : Nat) : Real))..
        (((geometry.orbitIndex + 2 : Nat) : Real)),
          orbitFinitePhysicalKernelIntegrand geometry t := by
  symm
  apply intervalIntegral.integral_eq_integral_of_support_subset
  intro t ht
  have ht_window : t ∈ Set.Ioo
      (-((geometry.orbitIndex + 2 : Nat) : Real))
      (((geometry.orbitIndex + 2 : Nat) : Real)) := by
    by_contra hnot
    have hzero := orbitFinitePhysicalKernelIntegrand_eq_zero_of_not_mem_raw_support_window
      geometry t hnot
    exact (Function.mem_support.mp ht) hzero
  exact ⟨ht_window.1, le_of_lt ht_window.2⟩

theorem orbitFinitePhysicalKernelIntegrand_eq_signed
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) :
    orbitFinitePhysicalKernelIntegrand geometry =
      orbitFiniteSignedPhysicalIntegrand geometry := by
  funext t
  unfold orbitFinitePhysicalKernelIntegrand orbitFiniteSignedPhysicalIntegrand
  apply Finset.sum_congr rfl
  intro n _hn
  rw [← orbitPositive_sub_negative_eq_integrand_re geometry n t]

theorem orbitFinitePhysicalKernelIntegrand_integrable
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) :
    Integrable (orbitFinitePhysicalKernelIntegrand geometry) := by
  rw [orbitFinitePhysicalKernelIntegrand_eq_signed geometry]
  exact orbitFiniteSignedPhysicalIntegrand_integrable geometry

theorem intervalIntegral_orbitFinitePhysicalKernelIntegrand_le_seminorm_budget
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) :
    ∫ t in (-((geometry.orbitIndex + 2 : Nat) : Real))..
        (((geometry.orbitIndex + 2 : Nat) : Real)),
        orbitFinitePhysicalKernelIntegrand geometry t ≤
      ∫ t in (-((geometry.orbitIndex + 2 : Nat) : Real))..
        (((geometry.orbitIndex + 2 : Nat) : Real)),
        Finset.sum (orbitVisiblePrimeRange geometry) (fun n =>
          2 * (ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real))) *
            (Real.exp (Real.log n / 2 +
              ((geometry.orbitIndex + 2 : Nat) : Real)) *
              (SchwartzMap.seminorm ℂ 0 0 (orbitRawFactor geometry).test) ^ 2)) := by
  apply intervalIntegral.integral_mono_on_of_le_Ioo
    (a := -((geometry.orbitIndex + 2 : Nat) : Real))
    (b := ((geometry.orbitIndex + 2 : Nat) : Real))
  all_goals first
    | positivity
    | exact (orbitFinitePhysicalKernelIntegrand_integrable geometry).intervalIntegrable
    | exact intervalIntegrable_const
    | (have hidx : 0 ≤ ((geometry.orbitIndex + 2 : Nat) : Real) := by positivity
       linarith)
    | (intro t ht
       exact (le_abs_self _).trans
         (abs_orbitFinitePhysicalKernelIntegrand_le_seminorm_budget geometry t ht))

theorem finitePrimeSum_eq_integral_finitePhysicalKernelIntegrand
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) :
    finitePrimeSum g.convolutionSquare =
      ∫ t, orbitFinitePhysicalKernelIntegrand geometry t := by
  rw [orbitFinitePhysicalKernelIntegrand_eq_signed geometry]
  exact finitePrimeSum_eq_integral_finiteSignedPhysicalIntegrand geometry

theorem finitePrimeSum_eq_re_integral_orbitFiniteComplexPhysicalKernelIntegrand
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) :
    finitePrimeSum g.convolutionSquare =
      (∫ t, orbitFiniteComplexPhysicalKernelIntegrand geometry t).re := by
  rw [finitePrimeSum_eq_integral_finitePhysicalKernelIntegrand geometry]
  rw [show (fun t => orbitFinitePhysicalKernelIntegrand geometry t) =
      (fun t => (orbitFiniteComplexPhysicalKernelIntegrand geometry t).re) by
    funext t
    exact (orbitFinitePhysicalKernelIntegrand_eq_re_complex geometry t)]
  simpa only [Complex.reCLM_apply] using
    (Complex.reCLM.integral_comp_comm
      (orbitFiniteComplexPhysicalKernelIntegrand_integrable geometry))

theorem finitePrimeSum_le_integral_common_factor_profile_norm
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) :
    finitePrimeSum g.convolutionSquare ≤
      ∫ t, ‖(orbitRawFactor geometry).test (-t)‖ *
        ‖orbitFiniteComplexPhysicalKernelProfile geometry t‖ := by
  rw [finitePrimeSum_eq_re_integral_orbitFiniteComplexPhysicalKernelIntegrand geometry]
  calc
    (∫ t, orbitFiniteComplexPhysicalKernelIntegrand geometry t).re ≤
        ‖∫ t, orbitFiniteComplexPhysicalKernelIntegrand geometry t‖ :=
      Complex.re_le_norm _
    _ ≤ ∫ t, ‖orbitFiniteComplexPhysicalKernelIntegrand geometry t‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ t, ‖(orbitRawFactor geometry).test (-t)‖ *
          ‖orbitFiniteComplexPhysicalKernelProfile geometry t‖ := by
      apply integral_congr_ae
      filter_upwards with t
      exact norm_orbitFiniteComplexPhysicalKernelIntegrand_eq_common_factor_profile
        geometry t

theorem finitePrimeSum_le_l2_common_factor_profile_mass
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g)
    (hraw : MemLp (fun t : Real => (orbitRawFactor geometry).test (-t))
      (ENNReal.ofReal 2))
    (hprofile : MemLp (orbitFiniteComplexPhysicalKernelProfile geometry)
      (ENNReal.ofReal 2)) :
    finitePrimeSum g.convolutionSquare ≤
      (∫ t, ‖(orbitRawFactor geometry).test (-t)‖ ^ (2 : Real)) ^
          (1 / (2 : Real)) *
        (∫ t, ‖orbitFiniteComplexPhysicalKernelProfile geometry t‖ ^ (2 : Real)) ^
          (1 / (2 : Real)) := by
  have hholder : (2 : Real).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hcs :
      (∫ t, ‖(orbitRawFactor geometry).test (-t)‖ *
        ‖orbitFiniteComplexPhysicalKernelProfile geometry t‖) ≤
        (∫ t, ‖(orbitRawFactor geometry).test (-t)‖ ^ (2 : Real)) ^
            (1 / (2 : Real)) *
          (∫ t, ‖orbitFiniteComplexPhysicalKernelProfile geometry t‖ ^ (2 : Real)) ^
            (1 / (2 : Real)) :=
    MeasureTheory.integral_mul_norm_le_Lp_mul_Lq hholder hraw hprofile
  exact (finitePrimeSum_le_integral_common_factor_profile_norm geometry).trans hcs

theorem orbitRawFactor_reflected_memLp_two
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) :
    MemLp (fun t : Real => (orbitRawFactor geometry).test (-t))
      (ENNReal.ofReal 2) := by
  have htest : MemLp ((orbitRawFactor geometry).test) (ENNReal.ofReal 2) := by
    simpa using (SchwartzMap.memLp (orbitRawFactor geometry).test 2)
  simpa [Function.comp_def] using
    htest.comp_measurePreserving (Measure.measurePreserving_neg volume)

theorem orbitFiniteComplexPhysicalKernelProfile_memLp_two
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) :
    MemLp (orbitFiniteComplexPhysicalKernelProfile geometry)
      (ENNReal.ofReal 2) := by
  let raw := orbitRawFactor geometry
  let weighted : SchwartzMap ℝ ℂ :=
    (CompactLogTest.exponentialWeight raw (1 : Complex)).test
  have hterm : ∀ n ∈ orbitVisiblePrimeRange geometry,
      MemLp (fun t : Real =>
        ((2 * (ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real))) : Real) : Complex) *
          Complex.exp (((Real.log n / 2 - t : Real) : Complex)) * raw.test (Real.log n - t))
        (ENNReal.ofReal 2) := by
    intro n hn
    let shifted : SchwartzMap ℝ ℂ :=
      SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        (LinearIsometryEquiv.neg ℝ (E := ℝ))
        (SchwartzMap.compSubConstCLM ℂ (-Real.log n) weighted)
    have hs : MemLp (shifted : Real → Complex) (ENNReal.ofReal 2) := by
      simpa using (SchwartzMap.memLp shifted 2)
    have hc := hs.const_mul
      (((2 * (ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real))) : Real) : Complex) *
        Complex.exp (((-Real.log n / 2 : Real) : Complex)))
    convert hc using 1
    funext t
    simp only [shifted, weighted,
      SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
      SchwartzMap.compSubConstCLM_apply, Function.comp_apply,
      CompactLogTest.exponentialWeight_apply, one_mul]
    simp [LinearIsometryEquiv.neg, LinearEquiv.neg, Complex.natCast_log]
    have hlog : (Real.log (n : Real) : Complex) = Complex.log (n : Complex) := by
      exact Complex.natCast_log
    rw [← hlog]
    have harg : -t + Real.log n = Real.log n - t := by ring
    have hcoeff :
        (2 * (ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real))) : Real) =
          ArithmeticFunction.vonMangoldt n * (Real.sqrt (n : Real))⁻¹ * 2 := by
      simp only [one_div]
      ring
    rw [harg]
    have he :
        Complex.exp (-((Real.log n : Real) : Complex) / 2) *
            Complex.exp (-(t : Complex) + ((Real.log n : Real) : Complex)) =
          Complex.exp (((Real.log n : Real) : Complex) / 2 - (t : Complex)) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    have he_target :
        Complex.exp (((Real.log n : Real) : Complex) / 2 - (t : Complex)) =
          Complex.exp (((-Real.log n / 2 : Real) : Complex)) *
            Complex.exp (((-t + Real.log n : Real) : Complex)) := by
      simpa using he.symm
    calc
      _ = ((2 * (ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real))) : Real) : Complex) *
          (Complex.exp (((-Real.log n / 2 : Real) : Complex)) *
          Complex.exp (((-t + Real.log n : Real) : Complex))) *
          raw.test (Real.log n - t) := by
        rw [he_target]
        rw [hcoeff]
        norm_num [Complex.ofReal_mul, Complex.ofReal_inv]
        ring_nf <;> simp
      _ = _ := by
        rw [hcoeff]
        norm_num [Complex.ofReal_mul, Complex.ofReal_inv]
        ring
  unfold orbitFiniteComplexPhysicalKernelProfile
  have hsum :=
    MeasureTheory.memLp_finsetSum' (orbitVisiblePrimeRange geometry) hterm
  convert hsum using 1
  ext t
  simp [Finset.sum_apply, raw]

theorem finitePrimeSum_le_l2_common_factor_profile_mass_of_profile
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g)
    (hprofile : MemLp (orbitFiniteComplexPhysicalKernelProfile geometry)
      (ENNReal.ofReal 2)) :
    finitePrimeSum g.convolutionSquare ≤
      (∫ t, ‖(orbitRawFactor geometry).test (-t)‖ ^ (2 : Real)) ^
          (1 / (2 : Real)) *
        (∫ t, ‖orbitFiniteComplexPhysicalKernelProfile geometry t‖ ^ (2 : Real)) ^
          (1 / (2 : Real)) := by
  exact finitePrimeSum_le_l2_common_factor_profile_mass geometry
    (orbitRawFactor_reflected_memLp_two geometry) hprofile

theorem orbitFiniteComplexPhysicalKernelProfile_lpNorm_le_sum_of_memLp
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g)
    (hterm : ∀ n ∈ orbitVisiblePrimeRange geometry,
      MemLp (fun t : Real =>
        ((2 * (ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real))) : Real) : Complex) *
          Complex.exp (((Real.log n / 2 - t : Real) : Complex)) *
            (orbitRawFactor geometry).test (Real.log n - t))
        (ENNReal.ofReal 2)) :
    MeasureTheory.lpNorm (orbitFiniteComplexPhysicalKernelProfile geometry) (ENNReal.ofReal 2)
        (MeasureTheory.volume : Measure Real) ≤
      ∑ n ∈ orbitVisiblePrimeRange geometry,
        MeasureTheory.lpNorm (fun t : Real =>
          ((2 * (ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real))) : Real) : Complex) *
            Complex.exp (((Real.log n / 2 - t : Real) : Complex)) *
              (orbitRawFactor geometry).test (Real.log n - t))
          (ENNReal.ofReal 2) (MeasureTheory.volume : Measure Real) := by
  have hsum := MeasureTheory.lpNorm_sum_le hterm (by norm_num : (1 : ENNReal) ≤ ENNReal.ofReal 2)
  have hprofile_eq :
      orbitFiniteComplexPhysicalKernelProfile geometry =
        ∑ n ∈ orbitVisiblePrimeRange geometry, (fun t : Real =>
          ((2 * (ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real))) : Real) : Complex) *
            Complex.exp (((Real.log n / 2 - t : Real) : Complex)) *
              (orbitRawFactor geometry).test (Real.log n - t)) := by
    funext t
    simp [orbitFiniteComplexPhysicalKernelProfile, Finset.sum_apply,
      Complex.natCast_log, Complex.ofReal_mul, Complex.ofReal_inv]
  rw [hprofile_eq]
  exact hsum

theorem orbitFiniteComplexPhysicalKernelProfile_term_lpNorm_eq_common
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g)
    (n : Nat) (hn : n ∈ orbitVisiblePrimeRange geometry) :
    MeasureTheory.lpNorm (fun t : Real =>
      ((2 * (ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real))) : Real) : Complex) *
        Complex.exp (((Real.log n / 2 - t : Real) : Complex)) *
          (orbitRawFactor geometry).test (Real.log n - t))
      (ENNReal.ofReal 2) (MeasureTheory.volume : Measure Real) =
      ‖((2 * (ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real))) : Real) : Complex) *
          Complex.exp (((-Real.log n / 2 : Real) : Complex))‖ *
        MeasureTheory.lpNorm
          ((CompactLogTest.exponentialWeight (orbitRawFactor geometry) (1 : Complex)).test : Real → Complex)
          (ENNReal.ofReal 2) (MeasureTheory.volume : Measure Real) := by
  let raw := orbitRawFactor geometry
  let weighted : SchwartzMap ℝ ℂ :=
    (CompactLogTest.exponentialWeight raw (1 : Complex)).test
  let shifted : SchwartzMap ℝ ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (LinearIsometryEquiv.neg ℝ (E := ℝ))
      (SchwartzMap.compSubConstCLM ℂ (-Real.log n) weighted)
  have hshift :
      MeasureTheory.lpNorm (shifted : Real → Complex) (ENNReal.ofReal 2)
          (MeasureTheory.volume : Measure Real) =
        MeasureTheory.lpNorm (weighted : Real → Complex) (ENNReal.ofReal 2)
          (MeasureTheory.volume : Measure Real) := by
    have hw : AEStronglyMeasurable (weighted : Real → Complex) volume :=
      (SchwartzMap.memLp weighted 2).aestronglyMeasurable
    have hmp := Measure.measurePreserving_sub_left (volume : Measure Real) (Real.log n)
    have hcomp : (shifted : Real → Complex) = fun x : Real => weighted (Real.log n - x) := by
      funext x
      simp [shifted, Function.comp_def,
        SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
        SchwartzMap.compSubConstCLM_apply, LinearIsometryEquiv.neg, LinearEquiv.neg]
      congr 1
      ring
    rw [hcomp]
    have hleft : AEStronglyMeasurable
        (fun x : Real => weighted (Real.log n - x)) volume := by
      exact (hmp.map_eq ▸ hw).comp_aemeasurable hmp.aemeasurable
    calc
      MeasureTheory.lpNorm (fun x : Real => weighted (Real.log n - x))
          (ENNReal.ofReal 2) volume =
          (MeasureTheory.eLpNorm (fun x : Real => weighted (Real.log n - x))
            (ENNReal.ofReal 2) volume).toReal :=
        (MeasureTheory.toReal_eLpNorm hleft).symm
      _ = (MeasureTheory.eLpNorm (weighted : Real → Complex)
            (ENNReal.ofReal 2) volume).toReal :=
        congrArg ENNReal.toReal (MeasureTheory.eLpNorm_comp_measurePreserving hw hmp)
      _ = MeasureTheory.lpNorm (weighted : Real → Complex)
          (ENNReal.ofReal 2) volume := MeasureTheory.toReal_eLpNorm hw
  have hfactor :
      (fun t : Real =>
        ((2 * (ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real))) : Real) : Complex) *
          Complex.exp (((Real.log n / 2 - t : Real) : Complex)) * raw.test (Real.log n - t)) =
        (fun t : Real =>
          (((2 * (ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real))) : Real) : Complex) *
            Complex.exp (((-Real.log n / 2 : Real) : Complex))) • shifted t) := by
    funext t
    simp only [shifted, weighted,
      SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
      SchwartzMap.compSubConstCLM_apply, Function.comp_apply,
      CompactLogTest.exponentialWeight_apply, one_mul]
    simp [LinearIsometryEquiv.neg, LinearEquiv.neg, Complex.natCast_log]
    have hlog : (Real.log (n : Real) : Complex) = Complex.log (n : Complex) := by
      exact Complex.natCast_log
    rw [← hlog]
    have harg : -t + Real.log n = Real.log n - t := by ring
    have hcoeff :
        (2 * (ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real))) : Real) =
          ArithmeticFunction.vonMangoldt n * (Real.sqrt (n : Real))⁻¹ * 2 := by
      simp only [one_div]
      ring
    rw [harg]
    have he :
        Complex.exp (-((Real.log n : Real) : Complex) / 2) *
            Complex.exp (-(t : Complex) + ((Real.log n : Real) : Complex)) =
          Complex.exp (((Real.log n : Real) : Complex) / 2 - (t : Complex)) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    have he_target :
        Complex.exp (((Real.log n : Real) : Complex) / 2 - (t : Complex)) =
          Complex.exp (((-Real.log n / 2 : Real) : Complex)) *
            Complex.exp (((-t + Real.log n : Real) : Complex)) := by
      simpa using he.symm
    rw [he_target]
    norm_num [Complex.ofReal_mul, Complex.ofReal_inv]
    ring_nf <;> simp [smul_eq_mul]
  rw [hfactor]
  change MeasureTheory.lpNorm
      ((((2 * (ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real))) : Real) : Complex) *
        Complex.exp (((-Real.log n / 2 : Real) : Complex))) • (shifted : Real → Complex))
      (ENNReal.ofReal 2) (MeasureTheory.volume : Measure Real) = _
  rw [MeasureTheory.lpNorm_const_smul]
  exact congrArg
    (fun x : Real =>
      ‖((2 * (ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real))) : Real) : Complex) *
          Complex.exp (((-Real.log n / 2 : Real) : Complex))‖ * x) hshift

theorem orbitFiniteComplexPhysicalKernelProfile_lpNorm_le_common_weighted_raw_mass
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g)
    (hterm : ∀ n ∈ orbitVisiblePrimeRange geometry,
      MemLp (fun t : Real =>
        ((2 * (ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real))) : Real) : Complex) *
          Complex.exp (((Real.log n / 2 - t : Real) : Complex)) *
            (orbitRawFactor geometry).test (Real.log n - t))
        (ENNReal.ofReal 2)) :
    MeasureTheory.lpNorm (orbitFiniteComplexPhysicalKernelProfile geometry)
        (ENNReal.ofReal 2) (MeasureTheory.volume : Measure Real) ≤
      (∑ n ∈ orbitVisiblePrimeRange geometry,
        ‖((2 * (ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real))) : Real) : Complex) *
            Complex.exp (((-Real.log n / 2 : Real) : Complex))‖) *
        MeasureTheory.lpNorm
          ((CompactLogTest.exponentialWeight (orbitRawFactor geometry) (1 : Complex)).test :
            Real → Complex)
          (ENNReal.ofReal 2) (MeasureTheory.volume : Measure Real) := by
  calc
    MeasureTheory.lpNorm (orbitFiniteComplexPhysicalKernelProfile geometry)
        (ENNReal.ofReal 2) (MeasureTheory.volume : Measure Real) ≤
        ∑ n ∈ orbitVisiblePrimeRange geometry,
          MeasureTheory.lpNorm (fun t : Real =>
            ((2 * (ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real))) : Real) : Complex) *
              Complex.exp (((Real.log n / 2 - t : Real) : Complex)) *
                (orbitRawFactor geometry).test (Real.log n - t))
            (ENNReal.ofReal 2) (MeasureTheory.volume : Measure Real) :=
      orbitFiniteComplexPhysicalKernelProfile_lpNorm_le_sum_of_memLp geometry
        hterm
    _ = ∑ n ∈ orbitVisiblePrimeRange geometry,
          ‖((2 * (ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real))) : Real) : Complex) *
              Complex.exp (((-Real.log n / 2 : Real) : Complex))‖ *
            MeasureTheory.lpNorm
              ((CompactLogTest.exponentialWeight (orbitRawFactor geometry) (1 : Complex)).test :
                Real → Complex)
              (ENNReal.ofReal 2) (MeasureTheory.volume : Measure Real) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact orbitFiniteComplexPhysicalKernelProfile_term_lpNorm_eq_common geometry n hn
    _ = (∑ n ∈ orbitVisiblePrimeRange geometry,
        ‖((2 * (ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real))) : Real) : Complex) *
            Complex.exp (((-Real.log n / 2 : Real) : Complex))‖) *
          MeasureTheory.lpNorm
            ((CompactLogTest.exponentialWeight (orbitRawFactor geometry) (1 : Complex)).test :
              Real → Complex)
            (ENNReal.ofReal 2) (MeasureTheory.volume : Measure Real) := by
      rw [Finset.sum_mul]

theorem orbitFiniteComplexPhysicalKernelProfile_term_coefficient_norm_le
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (n : Nat) (hn : 1 ≤ n) :
    ‖((2 * (ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real))) : Real) : Complex) *
        Complex.exp (((-Real.log n / 2 : Real) : Complex))‖ ≤
      2 * (ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real))) := by
  have hnreal : (1 : Real) ≤ n := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log (n : Real) := Real.log_nonneg hnreal
  have hcoeff : 0 ≤
      2 * (ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real))) := by
    exact mul_nonneg (by norm_num)
      (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity))
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hcoeff,
    Complex.norm_exp]
  have hexp : Real.exp (-Real.log (n : Real) / 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  have hexp' : Real.exp (((-Real.log (n : Real) / 2 : Real) : Complex).re) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    simpa only [Complex.ofReal_re] using (show -Real.log (n : Real) / 2 ≤ 0 by linarith)
  nlinarith [mul_le_mul_of_nonneg_left hexp' hcoeff]

theorem finitePrimeSum_le_intervalIntegral_common_factor_profile_norm
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) :
    finitePrimeSum g.convolutionSquare ≤
      ∫ t in (-((geometry.orbitIndex + 2 : Nat) : Real))..
        (((geometry.orbitIndex + 2 : Nat) : Real)),
        ‖(orbitRawFactor geometry).test (-t)‖ *
          ‖orbitFiniteComplexPhysicalKernelProfile geometry t‖ := by
  let F : Real → Real := fun t =>
    ‖(orbitRawFactor geometry).test (-t)‖ *
      ‖orbitFiniteComplexPhysicalKernelProfile geometry t‖
  have hF : Integrable F := by
    have hEq : F = fun t =>
        ‖orbitFiniteComplexPhysicalKernelIntegrand geometry t‖ := by
      funext t
      exact (norm_orbitFiniteComplexPhysicalKernelIntegrand_eq_common_factor_profile
        geometry t).symm
    rw [hEq]
    exact (orbitFiniteComplexPhysicalKernelIntegrand_integrable geometry).norm
  have hsupport : Function.support F ⊆ Set.Ioc
      (-((geometry.orbitIndex + 2 : Nat) : Real))
      (((geometry.orbitIndex + 2 : Nat) : Real)) := by
    intro t ht
    by_contra hnot
    have ht' : t ∉ Set.Ioo
        (-((geometry.orbitIndex + 2 : Nat) : Real))
        (((geometry.orbitIndex + 2 : Nat) : Real)) := by
      intro hmem
      exact hnot ⟨hmem.1, le_of_lt hmem.2⟩
    have hraw : (orbitRawFactor geometry).test (-t) = 0 := by
      by_contra hne
      have hmem : -t ∈ Function.support (orbitRawFactor geometry).test :=
        Function.mem_support.mpr hne
      have hwindow := orbitRawFactor_support_subset geometry hmem
      apply ht'
      constructor <;> linarith [hwindow.1, hwindow.2]
    apply (Function.mem_support.mp ht)
    simp [F, hraw]
  have hinterval : (∫ t in (-((geometry.orbitIndex + 2 : Nat) : Real))..
      (((geometry.orbitIndex + 2 : Nat) : Real)), F t) = ∫ t, F t :=
    intervalIntegral.integral_eq_integral_of_support_subset hsupport
  change finitePrimeSum g.convolutionSquare ≤
    ∫ t in (-((geometry.orbitIndex + 2 : Nat) : Real))..
      (((geometry.orbitIndex + 2 : Nat) : Real)), F t
  calc
    finitePrimeSum g.convolutionSquare ≤ ∫ t, F t := by
      exact finitePrimeSum_le_integral_common_factor_profile_norm geometry
    _ = ∫ t in (-((geometry.orbitIndex + 2 : Nat) : Real))..
        (((geometry.orbitIndex + 2 : Nat) : Real)), F t := hinterval.symm

theorem finitePrimeSum_eq_intervalIntegral_finitePhysicalKernelIntegrand
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) :
    finitePrimeSum g.convolutionSquare =
      ∫ t in (-((geometry.orbitIndex + 2 : Nat) : Real))..
        (((geometry.orbitIndex + 2 : Nat) : Real)),
          orbitFinitePhysicalKernelIntegrand geometry t := by
  exact (finitePrimeSum_eq_integral_finitePhysicalKernelIntegrand geometry).trans
    (integral_orbitFinitePhysicalKernelIntegrand_eq_interval geometry)

theorem orbitWindowSemiLocalGate_iff_finitePhysicalKernelIntervalBudget
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) :
    C1OrbitWindowSemiLocalGate.orbitWindowSemiLocalGate g ↔
      archimedeanTerm g.convolutionSquare +
          ∫ t in (-((geometry.orbitIndex + 2 : Nat) : Real))..
            (((geometry.orbitIndex + 2 : Nat) : Real)),
              orbitFinitePhysicalKernelIntegrand geometry t ≤ 0 := by
  rw [orbitWindowSemiLocalGate_iff_physicalKernelBudget geometry]
  have hsum :
      Finset.sum (orbitVisiblePrimeRange geometry) (fun n =>
        ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real)) *
          (orbitPhysicalKernel geometry (Real.log n) +
            orbitPhysicalKernel geometry (-Real.log n)).re) =
      ∫ t in (-((geometry.orbitIndex + 2 : Nat) : Real))..
        (((geometry.orbitIndex + 2 : Nat) : Real)),
          orbitFinitePhysicalKernelIntegrand geometry t := by
    exact (finitePrimeSum_eq_orbitPhysicalKernel_range geometry).symm.trans
      (finitePrimeSum_eq_intervalIntegral_finitePhysicalKernelIntegrand geometry)
  rw [hsum]

theorem orbitWindowSemiLocalGate_of_interval_common_factor_profile_norm_budget
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g)
    (hbudget : archimedeanTerm g.convolutionSquare +
        ∫ t in (-((geometry.orbitIndex + 2 : Nat) : Real))..
          (((geometry.orbitIndex + 2 : Nat) : Real)),
          ‖(orbitRawFactor geometry).test (-t)‖ *
            ‖orbitFiniteComplexPhysicalKernelProfile geometry t‖ ≤ 0) :
    C1OrbitWindowSemiLocalGate.orbitWindowSemiLocalGate g := by
  apply (orbitWindowSemiLocalGate_iff_finitePhysicalKernelIntervalBudget geometry).mpr
  have hle := finitePrimeSum_le_intervalIntegral_common_factor_profile_norm geometry
  have hraw :
      (∫ t in (-((geometry.orbitIndex + 2 : Nat) : Real))..
          (((geometry.orbitIndex + 2 : Nat) : Real)),
          orbitFinitePhysicalKernelIntegrand geometry t) ≤
        ∫ t in (-((geometry.orbitIndex + 2 : Nat) : Real))..
          (((geometry.orbitIndex + 2 : Nat) : Real)),
          ‖(orbitRawFactor geometry).test (-t)‖ *
            ‖orbitFiniteComplexPhysicalKernelProfile geometry t‖ := by
    rw [← finitePrimeSum_eq_intervalIntegral_finitePhysicalKernelIntegrand geometry]
    exact hle
  linarith

theorem orbitWindowSemiLocalGate_iff_finitePhysicalKernelIntegralBudget
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) :
    C1OrbitWindowSemiLocalGate.orbitWindowSemiLocalGate g ↔
      archimedeanTerm g.convolutionSquare +
          ∫ t, orbitFinitePhysicalKernelIntegrand geometry t ≤ 0 := by
  rw [orbitWindowSemiLocalGate_iff_physicalKernelBudget geometry]
  have hsum :
      Finset.sum (orbitVisiblePrimeRange geometry) (fun n =>
        ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real)) *
          (orbitPhysicalKernel geometry (Real.log n) +
            orbitPhysicalKernel geometry (-Real.log n)).re) =
      ∫ t, orbitFinitePhysicalKernelIntegrand geometry t := by
    exact (finitePrimeSum_eq_orbitPhysicalKernel_range geometry).symm.trans
      (finitePrimeSum_eq_integral_finitePhysicalKernelIntegrand geometry)
  rw [hsum]

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

theorem sourceRH_of_right_orbitGeometry_positivePartBudget
    (hproducer : ∀ rho : sourceNontrivialZeroSet,
      (1 / 2 : Real) < rho.1.re →
        ∃ g : CompactLogTest,
          ∃ geometry : OrbitG8Geometry rho g,
            archimedeanTerm g.convolutionSquare +
                Finset.sum (orbitVisiblePrimeRange geometry) (fun n =>
                  ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real)) *
                    (2 * (∫ t, orbitPositiveIntegrandMajorant geometry n t))) ≤ 0) :
    RHDefinitionBridge.standard.SourceRH := by
  apply sourceRH_of_right_orbitGeometry_oneSidedIntegrandCertificate
  intro rho hright
  obtain ⟨g, geometry, hbudget⟩ := hproducer rho hright
  refine ⟨g, geometry, ⟨{
    E := orbitPositiveIntegrandMajorant geometry
    integrable := fun n _hn =>
      orbitPositiveIntegrandMajorant_integrable geometry n
    pointwise := fun n _hn =>
      orbitPositiveIntegrandMajorant_pointwise geometry n
    arch_bound := hbudget
  }⟩⟩

theorem sourceRH_of_right_orbitGeometry_signedIntegralBudget
    (hproducer : ∀ rho : sourceNontrivialZeroSet,
      (1 / 2 : Real) < rho.1.re →
        ∃ g : CompactLogTest,
          ∃ geometry : OrbitG8Geometry rho g,
            archimedeanTerm g.convolutionSquare +
                Finset.sum (orbitVisiblePrimeRange geometry) (fun n =>
                  ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real)) *
                    (2 * ((∫ t, orbitPositiveIntegrandMajorant geometry n t) -
                      ∫ t, orbitNegativeIntegrandMajorant geometry n t))) ≤ 0) :
    RHDefinitionBridge.standard.SourceRH := by
  apply sourceRH_of_right_orbitGeometry_physicalKernel_nodeBounds
  intro rho hright
  obtain ⟨g, geometry, hbudget⟩ := hproducer rho hright
  let nodeBound : Nat → Real := fun n =>
    ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real)) *
      (2 * ((∫ t, orbitPositiveIntegrandMajorant geometry n t) -
        ∫ t, orbitNegativeIntegrandMajorant geometry n t))
  refine ⟨g, geometry, nodeBound, ?_, ?_⟩
  · simpa [nodeBound] using hbudget
  · intro n _hn
    exact le_of_eq (by
      simpa [nodeBound] using
        (orbitPhysicalKernel_nodeTerm_eq_positive_sub_negative geometry n))

theorem sourceRH_of_right_orbitGeometry_finitePhysicalKernelIntegralBudget
    (hproducer : ∀ rho : sourceNontrivialZeroSet,
      (1 / 2 : Real) < rho.1.re →
        ∃ g : CompactLogTest,
          ∃ geometry : OrbitG8Geometry rho g,
            archimedeanTerm g.convolutionSquare +
                ∫ t, orbitFinitePhysicalKernelIntegrand geometry t ≤ 0) :
    RHDefinitionBridge.standard.SourceRH := by
  apply sourceRH_of_right_orbitGeometry_signedIntegralBudget
  intro rho hright
  obtain ⟨g, geometry, hbudget⟩ := hproducer rho hright
  have hrewrite :
      (∫ t, orbitFinitePhysicalKernelIntegrand geometry t) =
        Finset.sum (orbitVisiblePrimeRange geometry) (fun n =>
          ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real)) *
            (2 * ((∫ t, orbitPositiveIntegrandMajorant geometry n t) -
              ∫ t, orbitNegativeIntegrandMajorant geometry n t))) := by
    exact (finitePrimeSum_eq_integral_finitePhysicalKernelIntegrand geometry).symm.trans
      (finitePrimeSum_eq_positive_sub_negative_integrals geometry)
  refine ⟨g, geometry, ?_⟩
  rw [hrewrite] at hbudget
  exact hbudget

theorem sourceRH_of_right_orbitGeometry_finitePhysicalKernelIntervalBudget
    (hproducer : ∀ rho : sourceNontrivialZeroSet,
      (1 / 2 : Real) < rho.1.re →
        ∃ g : CompactLogTest,
          ∃ geometry : OrbitG8Geometry rho g,
            archimedeanTerm g.convolutionSquare +
                ∫ t in (-((geometry.orbitIndex + 2 : Nat) : Real))..
                  (((geometry.orbitIndex + 2 : Nat) : Real)),
                  orbitFinitePhysicalKernelIntegrand geometry t ≤ 0) :
    RHDefinitionBridge.standard.SourceRH := by
  apply sourceRH_of_right_orbitGeometry_finitePhysicalKernelIntegralBudget
  intro rho hright
  obtain ⟨g, geometry, hbudget⟩ := hproducer rho hright
  have hrewrite :
      (∫ t in (-((geometry.orbitIndex + 2 : Nat) : Real))..
          (((geometry.orbitIndex + 2 : Nat) : Real)),
          orbitFinitePhysicalKernelIntegrand geometry t) =
        ∫ t, orbitFinitePhysicalKernelIntegrand geometry t :=
    (integral_orbitFinitePhysicalKernelIntegrand_eq_interval geometry).symm
  refine ⟨g, geometry, ?_⟩
  rw [hrewrite] at hbudget
  exact hbudget

theorem sourceRH_of_right_orbitGeometry_interval_common_factor_profile_norm_budget
    (hproducer : ∀ rho : sourceNontrivialZeroSet,
      (1 / 2 : Real) < rho.1.re →
        ∃ g : CompactLogTest,
          ∃ geometry : OrbitG8Geometry rho g,
            archimedeanTerm g.convolutionSquare +
                ∫ t in (-((geometry.orbitIndex + 2 : Nat) : Real))..
                  (((geometry.orbitIndex + 2 : Nat) : Real)),
                  ‖(orbitRawFactor geometry).test (-t)‖ *
                    ‖orbitFiniteComplexPhysicalKernelProfile geometry t‖ ≤ 0) :
    RHDefinitionBridge.standard.SourceRH := by
  apply sourceRH_of_right_orbitGeometry_finitePhysicalKernelIntervalBudget
  intro rho hright
  obtain ⟨g, geometry, hbudget⟩ := hproducer rho hright
  have hle := finitePrimeSum_le_intervalIntegral_common_factor_profile_norm geometry
  have hraw :
      (∫ t in (-((geometry.orbitIndex + 2 : Nat) : Real))..
          (((geometry.orbitIndex + 2 : Nat) : Real)),
          orbitFinitePhysicalKernelIntegrand geometry t) ≤
        ∫ t in (-((geometry.orbitIndex + 2 : Nat) : Real))..
          (((geometry.orbitIndex + 2 : Nat) : Real)),
          ‖(orbitRawFactor geometry).test (-t)‖ *
            ‖orbitFiniteComplexPhysicalKernelProfile geometry t‖ := by
    rw [← finitePrimeSum_eq_intervalIntegral_finitePhysicalKernelIntegrand geometry]
    exact hle
  refine ⟨g, geometry, ?_⟩
  linarith

end
end C1P2OrbitPhysicalKernelIntegrandBounds
end Source
end ConnesWeilRH
