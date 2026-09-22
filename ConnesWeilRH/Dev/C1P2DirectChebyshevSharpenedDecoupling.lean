import ConnesWeilRH.Source.RHDefinition
import ConnesWeilRH.Dev.C1G8R0OrbitGeometry
import ConnesWeilRH.Dev.C1OrbitFiniteSignBudget
import ConnesWeilRH.Dev.C1OrbitWindowSemiLocalGate
import ConnesWeilRH.Dev.C1P2BilateralProfile
import ConnesWeilRH.Dev.C1P2DirectSemiLocalGate
import ConnesWeilRH.Dev.C1P2DirectAbsorptionWitness
import ConnesWeilRH.Dev.C1P2DirectAbsorptionMajorant
import ConnesWeilRH.Dev.C1P2DirectChebyshevDecoupling
import ConnesWeilRH.Dev.C1P2OrbitPhysicalProfileReadback
import ConnesWeilRH.Dev.C1P2OrbitPhysicalKernelIntegrandBounds
import ConnesWeilRH.Dev.C1P2SignedBudget
import ConnesWeilRH.Dev.C1SameOwnerWeil
import ConnesWeilRH.Dev.C1HealthyYoshidaDetector
import ConnesWeilRH.Dev.C1HealthyYoshidaSpectralNegativity

namespace ConnesWeilRH
namespace Source
namespace C1P2DirectChebyshevSharpenedDecoupling

open C1G8R0OrbitGeometry
open C1OrbitFiniteSignBudget
open C1OrbitWindowSemiLocalGate
open C1P2BilateralProfile
open C1P2DirectSemiLocalGate
open C1P2DirectAbsorptionWitness
open C1P2DirectAbsorptionMajorant
open C1P2DirectChebyshevDecoupling
open C1P2OrbitPhysicalProfileReadback
open C1P2OrbitPhysicalKernelIntegrandBounds
open C1P2SignedBudget
open C1SameOwnerWeil
open C1HealthyYoshidaDetector
open C1HealthyYoshidaSpectralNegativity
open CC20YoshidaNearZeros
open CCM25Concrete.CompactLogConvolution
open scoped BigOperators

noncomputable section

/-- Real exponential integral over an arbitrary interval, via the Fundamental
    Theorem of Calculus. -/
theorem integral_exp_real (a b : ℝ) :
    ∫ x in a..b, Real.exp x = Real.exp b - Real.exp a :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => Real.hasDerivAt_exp x)
    (Continuous.intervalIntegrable Real.continuous_exp a b)

/-- Reflected real exponential integral over an arbitrary interval. -/
theorem integral_expNeg_real (a b : ℝ) :
    ∫ x in a..b, Real.exp (-x) = Real.exp (-a) - Real.exp (-b) := by
  have h := intervalIntegral.integral_comp_neg (f := Real.exp) (a := a) (b := b)
  rw [h]
  exact integral_exp_real (-b) (-a)

/-- Symmetric reflected exponential integral over `[-L, L]`,
    yielding `exp(L) - exp(-L) = 2 * sinh(L)`. -/
theorem integral_expNeg_symm (L : ℝ) :
    ∫ x in (-L)..L, Real.exp (-x) = Real.exp L - Real.exp (-L) := by
  have h := integral_expNeg_real (-L) L
  rw [neg_neg] at h
  exact h

/-- The sharpened Chebyshev decoupled bound factor:
    `2 * (exp(L) - exp(-L)) * S^2 = 4 * sinh(L) * S^2`.
    This sharpens the previous `4 * L * exp(L) * S^2` bound by integrating the half-density
    kernel `exp(-t)` directly instead of uniformly majorizing it by `exp(L)`. -/
def orbitChebyshevSharpenedBound
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) : ℝ :=
  2 * (Real.exp (rawFactorSupportRadius geometry) -
       Real.exp (-rawFactorSupportRadius geometry)) *
    (rawFactorSeminorm geometry) ^ 2

/-- Nonnegativity of `exp(L) - exp(-L)` for positive support radius `L > 0`. -/
theorem exp_sub_exp_neg_pos (L : ℝ) (hL : 0 < L) :
    0 < Real.exp L - Real.exp (-L) := by
  have hlt : -L < L := by linarith
  have hexp : Real.exp (-L) < Real.exp L := Real.exp_lt_exp.mpr hlt
  linarith

/-- Nonnegativity of the sharpened Chebyshev bound. -/
theorem orbitChebyshevSharpenedBound_nonneg
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) :
    0 ≤ orbitChebyshevSharpenedBound geometry := by
  unfold orbitChebyshevSharpenedBound
  have hL := rawFactorSupportRadius_pos geometry
  have hdiff := (exp_sub_exp_neg_pos (rawFactorSupportRadius geometry) hL).le
  have hS := rawFactorSeminorm_nonneg geometry
  positivity

/-- The sharpened Chebyshev bound is strictly smaller than the unintegrated bound:
    `2 * (exp(L) - exp(-L)) * S^2 ≤ 4 * L * exp(L) * S^2` for all `L ≥ 1`. -/
theorem orbitChebyshevSharpenedBound_le_decoupledBound
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) :
    orbitChebyshevSharpenedBound geometry ≤ orbitChebyshevDecoupledBound geometry := by
  unfold orbitChebyshevSharpenedBound orbitChebyshevDecoupledBound
  have hSsq : 0 ≤ (rawFactorSeminorm geometry) ^ 2 := sq_nonneg _
  have hLpos := rawFactorSupportRadius_pos geometry
  have hLge1 : (1 : ℝ) ≤ rawFactorSupportRadius geometry := by
    dsimp [rawFactorSupportRadius]
    have : 1 ≤ geometry.orbitIndex + 2 := by omega
    exact_mod_cast this
  have hdiff_le : Real.exp (rawFactorSupportRadius geometry) -
      Real.exp (-rawFactorSupportRadius geometry) ≤
      2 * rawFactorSupportRadius geometry * Real.exp (rawFactorSupportRadius geometry) := by
    have hpos_neg : 0 ≤ Real.exp (-rawFactorSupportRadius geometry) := (Real.exp_pos _).le
    calc
      Real.exp (rawFactorSupportRadius geometry) - Real.exp (-rawFactorSupportRadius geometry)
        ≤ Real.exp (rawFactorSupportRadius geometry) := by linarith
      _ = 1 * Real.exp (rawFactorSupportRadius geometry) := by ring
      _ ≤ (2 * rawFactorSupportRadius geometry) * Real.exp (rawFactorSupportRadius geometry) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        linarith
  calc
    2 * (Real.exp (rawFactorSupportRadius geometry) - Real.exp (-rawFactorSupportRadius geometry)) *
        (rawFactorSeminorm geometry) ^ 2 ≤
      2 * (2 * rawFactorSupportRadius geometry * Real.exp (rawFactorSupportRadius geometry)) *
        (rawFactorSeminorm geometry) ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ hSsq
      linarith
    _ = 4 * rawFactorSupportRadius geometry * Real.exp (rawFactorSupportRadius geometry) *
        (rawFactorSeminorm geometry) ^ 2 := by ring

/-- Pointwise cancellation with non-uniform `exp(-t)`:
    `1 / sqrt(n)` cancels against `exp(log(n) / 2) = sqrt(n)`,
    leaving `exp(-t) * S^2` inside the integral. -/
theorem cancellation_identity_with_t (n : ℕ) (t : ℝ) (S : ℝ) :
    ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : ℝ)) *
      (Real.exp (Real.log (n : ℝ) / 2 - t) * S ^ 2) =
    ArithmeticFunction.vonMangoldt n * (Real.exp (-t) * S ^ 2) := by
  by_cases h0 : n = 0
  · simp [h0]
  · have hpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero h0)
    have h0p : 0 ≤ (n : ℝ) := le_of_lt hpos
    have hlogs : Real.log (Real.sqrt (n : ℝ)) = Real.log (n : ℝ) / 2 :=
      Real.log_sqrt h0p
    have hsqrt_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hpos
    have hsqrt_exp : Real.sqrt (n : ℝ) = Real.exp (Real.log (n : ℝ) / 2) := by
      rw [← Real.exp_log hsqrt_pos, hlogs]
    have hexp_sub : Real.exp (Real.log (n : ℝ) / 2 - t) =
        Real.exp (Real.log (n : ℝ) / 2) * Real.exp (-t) := by
      rw [sub_eq_add_neg, Real.exp_add]
    rw [hexp_sub, ← hsqrt_exp]
    have hinv : (1 / Real.sqrt (n : ℝ)) * Real.sqrt (n : ℝ) = 1 :=
      one_div_mul_cancel (ne_of_gt hsqrt_pos)
    calc
      ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : ℝ)) *
          (Real.sqrt (n : ℝ) * Real.exp (-t) * S ^ 2) =
        ArithmeticFunction.vonMangoldt n *
          ((1 / Real.sqrt (n : ℝ)) * Real.sqrt (n : ℝ)) *
          (Real.exp (-t) * S ^ 2) := by ring
      _ = ArithmeticFunction.vonMangoldt n * 1 * (Real.exp (-t) * S ^ 2) := by rw [hinv]
      _ = ArithmeticFunction.vonMangoldt n * (Real.exp (-t) * S ^ 2) := by ring

/-- Pointwise integrand bound with exact `exp(-t)` profile. -/
theorem norm_orbitWeightedKernelIntegrand_le_unrelaxed
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (x t : ℝ) :
    ‖orbitWeightedKernelIntegrand geometry x t‖ ≤
      Real.exp (x / 2 - t) * (rawFactorSeminorm geometry) ^ 2 := by
  let raw := orbitRawFactor geometry
  let S : ℝ := rawFactorSeminorm geometry
  have hleft : ‖raw.test (-t)‖ ≤ S :=
    SchwartzMap.norm_le_seminorm ℂ raw.test (-t)
  have hright : ‖raw.test (x - t)‖ ≤ S :=
    SchwartzMap.norm_le_seminorm ℂ raw.test (x - t)
  have hS : 0 ≤ S := rawFactorSeminorm_nonneg geometry
  calc
    ‖orbitWeightedKernelIntegrand geometry x t‖ =
        Real.exp (x / 2 - t) * ‖raw.test (-t)‖ * ‖raw.test (x - t)‖ := by
      rw [orbitWeightedKernelIntegrand, norm_mul, norm_mul, norm_star,
        Complex.norm_exp]
      simp [raw]
    _ ≤ Real.exp (x / 2 - t) * S * S := by
      simpa only [mul_assoc] using
        (mul_le_mul_of_nonneg_left
          (mul_le_mul hleft hright (norm_nonneg _) hS) (Real.exp_pos _).le)
    _ = Real.exp (x / 2 - t) * (rawFactorSeminorm geometry) ^ 2 := by
      simp [S, pow_two, mul_assoc]

/-- Pointwise real-part bound with exact `exp(-t)` profile. -/
theorem abs_orbitWeightedKernelIntegrand_re_le
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (x t : ℝ) :
    |(orbitWeightedKernelIntegrand geometry x t).re| ≤
      Real.exp (x / 2 - t) * (rawFactorSeminorm geometry) ^ 2 :=
  (Complex.abs_re_le_norm _).trans
    (norm_orbitWeightedKernelIntegrand_le_unrelaxed geometry x t)

/-- Bound on each visible prime term in the physical integrand. -/
theorem orbitPhysicalKernel_term_le_sharpened
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (n : ℕ) (t : ℝ) :
    |ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : ℝ)) *
        (2 * (orbitWeightedKernelIntegrand geometry (Real.log n) t).re)| ≤
      ArithmeticFunction.vonMangoldt n *
        (2 * Real.exp (-t) * (rawFactorSeminorm geometry) ^ 2) := by
  have hcoeff : 0 ≤ ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : ℝ)) :=
    mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
  have hreal := abs_orbitWeightedKernelIntegrand_re_le geometry (Real.log n) t
  have htwo : |2 * (orbitWeightedKernelIntegrand geometry (Real.log n) t).re| ≤
      2 * (Real.exp (Real.log n / 2 - t) * (rawFactorSeminorm geometry) ^ 2) := by
    rw [abs_mul, abs_of_nonneg (by norm_num)]
    exact mul_le_mul_of_nonneg_left hreal (by norm_num)
  have hcancel := cancellation_identity_with_t n t (rawFactorSeminorm geometry)
  calc
    |ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : ℝ)) *
        (2 * (orbitWeightedKernelIntegrand geometry (Real.log n) t).re)| =
      (ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : ℝ))) *
        |2 * (orbitWeightedKernelIntegrand geometry (Real.log n) t).re| := by
      rw [abs_mul, abs_of_nonneg hcoeff]
    _ ≤ (ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : ℝ))) *
        (2 * (Real.exp (Real.log n / 2 - t) * (rawFactorSeminorm geometry) ^ 2)) :=
      mul_le_mul_of_nonneg_left htwo hcoeff
    _ = 2 * (ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : ℝ)) *
        (Real.exp (Real.log n / 2 - t) * (rawFactorSeminorm geometry) ^ 2)) := by ring
    _ = 2 * (ArithmeticFunction.vonMangoldt n *
        (Real.exp (-t) * (rawFactorSeminorm geometry) ^ 2)) := by rw [hcancel]
    _ = ArithmeticFunction.vonMangoldt n *
        (2 * Real.exp (-t) * (rawFactorSeminorm geometry) ^ 2) := by ring

/-- Pointwise bound on the finite physical kernel integrand by the sharpened Chebyshev profile. -/
theorem abs_orbitFinitePhysicalKernelIntegrand_le_sharpened
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (t : ℝ) :
    |orbitFinitePhysicalKernelIntegrand geometry t| ≤
      visibleChebyshevPrimeSum geometry *
        (2 * Real.exp (-t) * (rawFactorSeminorm geometry) ^ 2) := by
  unfold orbitFinitePhysicalKernelIntegrand
  calc
    |(∑ n ∈ orbitVisiblePrimeRange geometry,
        ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : ℝ)) *
          (2 * (orbitWeightedKernelIntegrand geometry (Real.log n) t).re))| ≤
      ∑ n ∈ orbitVisiblePrimeRange geometry,
        |ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : ℝ)) *
          (2 * (orbitWeightedKernelIntegrand geometry (Real.log n) t).re)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ orbitVisiblePrimeRange geometry,
        ArithmeticFunction.vonMangoldt n *
          (2 * Real.exp (-t) * (rawFactorSeminorm geometry) ^ 2) :=
      Finset.sum_le_sum (fun n _hn => orbitPhysicalKernel_term_le_sharpened geometry n t)
    _ = visibleChebyshevPrimeSum geometry *
        (2 * Real.exp (-t) * (rawFactorSeminorm geometry) ^ 2) := by
      unfold visibleChebyshevPrimeSum
      rw [← Finset.sum_mul]

/-- The sharpened master majorant: the finite visible prime sum of the genuine convolution
    square is bounded by `visibleChebyshevPrimeSum * orbitChebyshevSharpenedBound`. -/
theorem finitePrimeSum_le_chebyshev_sharpened_bound
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) :
    finitePrimeSum g.convolutionSquare ≤
      visibleChebyshevPrimeSum geometry * orbitChebyshevSharpenedBound geometry := by
  have hsum_int :
      finitePrimeSum g.convolutionSquare =
        ∫ t in (-rawFactorSupportRadius geometry)..
          (rawFactorSupportRadius geometry),
          orbitFinitePhysicalKernelIntegrand geometry t := by
    have h1 := finitePrimeSum_eq_integral_finitePhysicalKernelIntegrand geometry
    have h2 := integral_orbitFinitePhysicalKernelIntegrand_eq_interval geometry
    dsimp [rawFactorSupportRadius]
    rw [h1, h2]
  rw [hsum_int]
  let L := rawFactorSupportRadius geometry
  let S := rawFactorSeminorm geometry
  let C := visibleChebyshevPrimeSum geometry * (2 * S ^ 2)
  have hcont : Continuous (fun t : ℝ => C * Real.exp (-t)) :=
    continuous_const.mul (Real.continuous_exp.comp continuous_neg)
  have hle_pointwise : ∀ t ∈ Set.Ioo (-L) L,
      orbitFinitePhysicalKernelIntegrand geometry t ≤ C * Real.exp (-t) := by
    intro t _ht
    have habs := abs_orbitFinitePhysicalKernelIntegrand_le_sharpened geometry t
    have hle_abs : orbitFinitePhysicalKernelIntegrand geometry t ≤
        |orbitFinitePhysicalKernelIntegrand geometry t| := le_abs_self _
    have heq : visibleChebyshevPrimeSum geometry * (2 * Real.exp (-t) * S ^ 2) =
        C * Real.exp (-t) := by ring
    rw [heq] at habs
    exact hle_abs.trans habs
  have hLpos := rawFactorSupportRadius_pos geometry
  have hLle : -L ≤ L := by linarith
  have hint_mono := intervalIntegral.integral_mono_on_of_le_Ioo
    (a := -L) (b := L) hLle
    (orbitFinitePhysicalKernelIntegrand_integrable geometry).intervalIntegrable
    (hcont.intervalIntegrable (-L) L)
    hle_pointwise
  have hint_eval : (∫ t in (-L)..L, C * Real.exp (-t)) =
      visibleChebyshevPrimeSum geometry * orbitChebyshevSharpenedBound geometry := by
    rw [intervalIntegral.integral_const_mul C]
    rw [integral_expNeg_symm L]
    unfold orbitChebyshevSharpenedBound
    dsimp [C, L, S]
    ring
  rw [hint_eval] at hint_mono
  exact hint_mono

/-- Construction of an absorption witness from a sharpened Chebyshev bound. -/
def absorptionWitness_of_chebyshev_sharpened_bound
    (rho : sourceNontrivialZeroSet) (g : CompactLogTest)
    (geometry : OrbitG8Geometry rho g)
    (habsorb : visibleChebyshevPrimeSum geometry *
        orbitChebyshevSharpenedBound geometry ≤
      -archimedeanTerm g.convolutionSquare) :
    OrbitG8AbsorptionWitness rho :=
  ⟨g, geometry, (finitePrimeSum_le_chebyshev_sharpened_bound geometry).trans habsorb⟩

/-- Master theorem: existence of a sharpened Chebyshev bound for every right-hand zero
    directly implies SourceRH. -/
theorem sourceRH_of_chebyshev_sharpened_bounds
    (hproducer : ∀ rho : sourceNontrivialZeroSet,
      (1 / 2 : Real) < rho.1.re →
        ∃ g : CompactLogTest,
          ∃ geometry : OrbitG8Geometry rho g,
            visibleChebyshevPrimeSum geometry *
                orbitChebyshevSharpenedBound geometry ≤
              -archimedeanTerm g.convolutionSquare) :
    RHDefinitionBridge.standard.SourceRH := by
  apply sourceRH_of_absorptionWitnesses
  intro rho hright
  obtain ⟨g, geometry, habsorb⟩ := hproducer rho hright
  exact ⟨absorptionWitness_of_chebyshev_sharpened_bound rho g geometry habsorb⟩

/-- Master theorem: existence of a sharpened Chebyshev bound for every right-hand zero
    directly implies Mathlib's RiemannHypothesis. -/
theorem riemannHypothesis_of_chebyshev_sharpened_bounds
    (hproducer : ∀ rho : sourceNontrivialZeroSet,
      (1 / 2 : Real) < rho.1.re →
        ∃ g : CompactLogTest,
          ∃ geometry : OrbitG8Geometry rho g,
            visibleChebyshevPrimeSum geometry *
                orbitChebyshevSharpenedBound geometry ≤
              -archimedeanTerm g.convolutionSquare) :
    _root_.RiemannHypothesis := by
  apply riemannHypothesis_of_absorptionWitnesses
  intro rho hright
  obtain ⟨g, geometry, habsorb⟩ := hproducer rho hright
  exact ⟨absorptionWitness_of_chebyshev_sharpened_bound rho g geometry habsorb⟩

end
end C1P2DirectChebyshevSharpenedDecoupling
end Source
end ConnesWeilRH
