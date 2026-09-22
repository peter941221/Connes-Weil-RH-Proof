import ConnesWeilRH.Source.RHDefinition
import ConnesWeilRH.Dev.C1G8R0OrbitGeometry
import ConnesWeilRH.Dev.C1OrbitFiniteSignBudget
import ConnesWeilRH.Dev.C1OrbitWindowSemiLocalGate
import ConnesWeilRH.Dev.C1P2BilateralProfile
import ConnesWeilRH.Dev.C1P2DirectSemiLocalGate
import ConnesWeilRH.Dev.C1P2DirectAbsorptionWitness
import ConnesWeilRH.Dev.C1P2DirectAbsorptionMajorant
import ConnesWeilRH.Dev.C1P2DirectChebyshevDecoupling
import ConnesWeilRH.Dev.C1P2DirectChebyshevSharpenedDecoupling
import ConnesWeilRH.Dev.C1P2OrbitPhysicalProfileReadback
import ConnesWeilRH.Dev.C1P2OrbitPhysicalKernelIntegrandBounds
import ConnesWeilRH.Dev.C1P2SignedBudget
import ConnesWeilRH.Dev.C1SameOwnerWeil
import ConnesWeilRH.Dev.C1HealthyYoshidaDetector
import ConnesWeilRH.Dev.C1HealthyYoshidaSpectralNegativity

namespace ConnesWeilRH
namespace Source
namespace C1P2DirectSupportOverlapDecoupling

open MeasureTheory
open C1G8R0OrbitGeometry
open C1OrbitFiniteSignBudget
open C1OrbitWindowSemiLocalGate
open C1P2BilateralProfile
open C1P2DirectSemiLocalGate
open C1P2DirectAbsorptionWitness
open C1P2DirectAbsorptionMajorant
open C1P2DirectChebyshevDecoupling
open C1P2DirectChebyshevSharpenedDecoupling
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

/-- The integrand vanishes when `t ≤ x - L` because `x - t ≥ L` lies outside
    the compact support `(-L, L)` of the raw factor. -/
theorem orbitWeightedKernelIntegrand_eq_zero_of_lt_sub
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (x t : ℝ)
    (ht : t ≤ x - rawFactorSupportRadius geometry) :
    orbitWeightedKernelIntegrand geometry x t = 0 := by
  let raw := orbitRawFactor geometry
  let L := rawFactorSupportRadius geometry
  have hnot : x - t ∉ Set.Ioo (-L) L := by
    intro hmem
    have hlt := hmem.2
    linarith
  have hsupp := orbitRawFactor_support_subset geometry
  have hzero : raw.test (x - t) = 0 := by
    by_contra hne
    exact hnot (hsupp (Function.mem_support.mpr hne))
  unfold orbitWeightedKernelIntegrand
  simp [raw, hzero]

/-- For any prime power `n` with `log n ≥ 2L`, the two-point integrand vanishes
    identically for all `t ∈ ℝ`. -/
theorem orbitWeightedKernelIntegrand_eq_zero_of_ge_two_L
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (n : ℕ) (t : ℝ)
    (hn : 2 * rawFactorSupportRadius geometry ≤ Real.log (n : ℝ)) :
    orbitWeightedKernelIntegrand geometry (Real.log (n : ℝ)) t = 0 := by
  let L := rawFactorSupportRadius geometry
  by_cases ht : t ≤ Real.log (n : ℝ) - L
  · exact orbitWeightedKernelIntegrand_eq_zero_of_lt_sub geometry (Real.log (n : ℝ)) t ht
  · have htL : L < t := by linarith [ht, hn]
    have hnot : t ∉ Set.Ioo (-L) L := by
      intro hmem
      linarith [hmem.2]
    have hzero := orbitWeightedKernelIntegrand_eq_zero_of_not_mem_raw_support_window
      geometry (Real.log (n : ℝ)) t
    have hwindow : Set.Ioo (-((geometry.orbitIndex + 2 : Nat) : Real))
        (((geometry.orbitIndex + 2 : Nat) : Real)) = Set.Ioo (-L) L := rfl
    rw [hwindow] at hzero
    exact hzero hnot

/-- The physical kernel at `log n` vanishes identically for all `n` with `log n ≥ 2L`. -/
theorem orbitPhysicalKernel_eq_zero_of_ge_two_L
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (n : ℕ)
    (hn : 2 * rawFactorSupportRadius geometry ≤ Real.log (n : ℝ)) :
    orbitPhysicalKernel geometry (Real.log (n : ℝ)) = 0 := by
  rw [orbitPhysicalKernel_eq_integral_weightedKernel]
  have heq : (fun t : ℝ => orbitWeightedKernelIntegrand geometry (Real.log (n : ℝ)) t) =
      fun _ => 0 := by
    funext t
    exact orbitWeightedKernelIntegrand_eq_zero_of_ge_two_L geometry n t hn
  rw [heq]
  simp only [integral_zero]

/-- The finite physical kernel integrand vanishes identically for all `t ≤ log 2 - L`,
    because every prime power satisfies `n ≥ 2`, hence `log n ≥ log 2`, which places
    `log n - t ≥ L` strictly outside the support `(-L, L)` of `orbitRawFactor`. -/
theorem orbitFinitePhysicalKernelIntegrand_eq_zero_of_lt_log2_sub
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (t : ℝ)
    (ht : t ≤ Real.log 2 - rawFactorSupportRadius geometry) :
    orbitFinitePhysicalKernelIntegrand geometry t = 0 := by
  unfold orbitFinitePhysicalKernelIntegrand
  apply Finset.sum_eq_zero
  intro n _hn
  by_cases hvm : ArithmeticFunction.vonMangoldt n = 0
  · simp [hvm]
  · have h2 : 2 ≤ n := by
      by_contra hlt
      have : n = 0 ∨ n = 1 := by omega
      rcases this with rfl | rfl
      · simp at hvm
      · simp at hvm
    have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h2
    have hlog2_le : Real.log 2 ≤ Real.log (n : ℝ) :=
      Real.log_le_log (by norm_num) hn2
    have ht_le : t ≤ Real.log (n : ℝ) - rawFactorSupportRadius geometry := by
      linarith
    have hzero := orbitWeightedKernelIntegrand_eq_zero_of_lt_sub geometry (Real.log (n : ℝ)) t ht_le
    simp [hzero]

/-- The integral of the physical kernel integrand over `[-L, L]` reduces to the
    restricted interval `[log 2 - L, L]` because the integrand vanishes on `[-L, log 2 - L]`. -/
theorem integral_orbitFinitePhysicalKernelIntegrand_eq_log2_sub_interval
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) :
    (∫ t in (-rawFactorSupportRadius geometry)..
        (rawFactorSupportRadius geometry),
        orbitFinitePhysicalKernelIntegrand geometry t) =
      ∫ t in (Real.log 2 - rawFactorSupportRadius geometry)..
        (rawFactorSupportRadius geometry),
        orbitFinitePhysicalKernelIntegrand geometry t := by
  let L := rawFactorSupportRadius geometry
  have hA : IntervalIntegrable (orbitFinitePhysicalKernelIntegrand geometry)
      volume (-L) (Real.log 2 - L) :=
    (orbitFinitePhysicalKernelIntegrand_integrable geometry).intervalIntegrable
  have hB : IntervalIntegrable (orbitFinitePhysicalKernelIntegrand geometry)
      volume (Real.log 2 - L) L :=
    (orbitFinitePhysicalKernelIntegrand_integrable geometry).intervalIntegrable
  rw [← intervalIntegral.integral_add_adjacent_intervals hA hB]
  have hzero :
      (∫ t in (-L)..(Real.log 2 - L), orbitFinitePhysicalKernelIntegrand geometry t) = 0 := by
    have hlog2_pos : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hle : -L ≤ Real.log 2 - L := by linarith
    have hcongr : (∫ t in (-L)..(Real.log 2 - L), orbitFinitePhysicalKernelIntegrand geometry t) =
        ∫ t in (-L)..(Real.log 2 - L), (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hle] at ht
      exact orbitFinitePhysicalKernelIntegrand_eq_zero_of_lt_log2_sub geometry t ht.2
    rw [hcongr, intervalIntegral.integral_zero]
  rw [hzero, zero_add]

/-- The integral of `exp(-t)` over the restricted overlap window `[x - L, L]`. -/
theorem integral_expNeg_overlap (L x : ℝ) :
    ∫ t in (x - L)..L, Real.exp (-t) = Real.exp (L - x) - Real.exp (-L) := by
  have h := integral_expNeg_real (x - L) L
  rw [show -(x - L) = L - x by ring] at h
  exact h

/-- Scaled overlap integral: integrating `exp(x/2 - t)` over `[x - L, L]`
    produces `exp(L - x/2) - exp(-(L - x/2)) = 2 * sinh(L - x/2)`. -/
theorem integral_scaled_expNeg_overlap (L x : ℝ) :
    ∫ t in (x - L)..L, Real.exp (x / 2 - t) =
      Real.exp (L - x / 2) - Real.exp (-(L - x / 2)) := by
  have heq : (fun t : ℝ => Real.exp (x / 2 - t)) =
      (fun t : ℝ => Real.exp (x / 2) * Real.exp (-t)) := by
    funext t
    rw [sub_eq_add_neg, Real.exp_add]
  rw [heq]
  rw [intervalIntegral.integral_const_mul]
  rw [integral_expNeg_overlap L x]
  have h1 : Real.exp (x / 2) * Real.exp (L - x) = Real.exp (L - x / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h2 : Real.exp (x / 2) * Real.exp (-L) = Real.exp (-(L - x / 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  linarith

/-- The arithmetic cancellation identity for the exact overlap profile:
    `1 / sqrt(n)` cancels against `exp(log(n)/2)`, yielding
    `exp(L) / n - exp(-L)`. -/
theorem cancellation_identity_overlap (n : ℕ) (L : ℝ) (S : ℝ) :
    ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : ℝ)) *
      ((Real.exp (L - Real.log (n : ℝ) / 2) -
        Real.exp (-(L - Real.log (n : ℝ) / 2))) * S ^ 2) =
    ArithmeticFunction.vonMangoldt n *
      ((Real.exp L / (n : ℝ) - Real.exp (-L)) * S ^ 2) := by
  by_cases h0 : n = 0
  · simp [h0]
  · have hpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero h0)
    have h0p : 0 ≤ (n : ℝ) := le_of_lt hpos
    have hsqrt_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hpos
    have hsqrt_exp : Real.sqrt (n : ℝ) = Real.exp (Real.log (n : ℝ) / 2) := by
      rw [← Real.exp_log hsqrt_pos, Real.log_sqrt h0p]
    have hexp1 : Real.exp (L - Real.log (n : ℝ) / 2) =
        Real.exp L / Real.sqrt (n : ℝ) := by
      rw [sub_eq_add_neg, Real.exp_add, Real.exp_neg, ← hsqrt_exp, div_eq_mul_inv]
    have hexp2 : Real.exp (-(L - Real.log (n : ℝ) / 2)) =
        Real.exp (-L) * Real.sqrt (n : ℝ) := by
      have : -(L - Real.log (n : ℝ) / 2) = -L + Real.log (n : ℝ) / 2 := by ring
      rw [this, Real.exp_add, ← hsqrt_exp]
    rw [hexp1, hexp2]
    have hdistrib : (1 / Real.sqrt (n : ℝ)) *
        (Real.exp L / Real.sqrt (n : ℝ) - Real.exp (-L) * Real.sqrt (n : ℝ)) =
        Real.exp L / (n : ℝ) - Real.exp (-L) := by
      have hsq : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) :=
        Real.mul_self_sqrt h0p
      have hinv : (1 / Real.sqrt (n : ℝ)) * Real.sqrt (n : ℝ) = 1 :=
        one_div_mul_cancel (ne_of_gt hsqrt_pos)
      calc
        (1 / Real.sqrt (n : ℝ)) *
            (Real.exp L / Real.sqrt (n : ℝ) - Real.exp (-L) * Real.sqrt (n : ℝ)) =
          (1 / Real.sqrt (n : ℝ)) * (Real.exp L / Real.sqrt (n : ℝ)) -
            (1 / Real.sqrt (n : ℝ)) * (Real.exp (-L) * Real.sqrt (n : ℝ)) := by ring
        _ = Real.exp L / (Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ)) -
            ((1 / Real.sqrt (n : ℝ)) * Real.sqrt (n : ℝ)) * Real.exp (-L) := by ring
        _ = Real.exp L / (n : ℝ) - 1 * Real.exp (-L) := by rw [hsq, hinv]
        _ = Real.exp L / (n : ℝ) - Real.exp (-L) := by ring
    calc
      ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : ℝ)) *
          ((Real.exp L / Real.sqrt (n : ℝ) - Real.exp (-L) * Real.sqrt (n : ℝ)) * S ^ 2) =
        ArithmeticFunction.vonMangoldt n *
          ((1 / Real.sqrt (n : ℝ)) *
            (Real.exp L / Real.sqrt (n : ℝ) - Real.exp (-L) * Real.sqrt (n : ℝ))) * S ^ 2 := by ring
      _ = ArithmeticFunction.vonMangoldt n *
          (Real.exp L / (n : ℝ) - Real.exp (-L)) * S ^ 2 := by rw [hdistrib]
      _ = ArithmeticFunction.vonMangoldt n *
          ((Real.exp L / (n : ℝ) - Real.exp (-L)) * S ^ 2) := by ring

/-- The harmonic Chebyshev sum factor: `∑ vonMangoldt(n) / n`.
    By Mertens' first theorem, this grows like `2L`, completely replacing
    the exponential `exp(2L)` growth of the unweighted Chebyshev sum. -/
def visibleHarmonicChebyshevSum
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) : ℝ :=
  ∑ n ∈ orbitVisiblePrimeRange geometry,
    ArithmeticFunction.vonMangoldt n / (n : ℝ)

/-- Nonnegativity of the harmonic Chebyshev sum. -/
theorem visibleHarmonicChebyshevSum_nonneg
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) :
    0 ≤ visibleHarmonicChebyshevSum geometry := by
  unfold visibleHarmonicChebyshevSum
  apply Finset.sum_nonneg
  intro n _hn
  have hvm := ArithmeticFunction.vonMangoldt_nonneg (n := n)
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  exact div_nonneg hvm hn

/-- The harmonic Chebyshev sum is bounded by half the unweighted Chebyshev sum,
    since every prime power is at least 2. -/
theorem visibleHarmonicChebyshevSum_le_half_chebyshev
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) :
    visibleHarmonicChebyshevSum geometry ≤
      (1 / 2 : ℝ) * visibleChebyshevPrimeSum geometry := by
  unfold visibleHarmonicChebyshevSum visibleChebyshevPrimeSum
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n _hn
  by_cases hvm : ArithmeticFunction.vonMangoldt n = 0
  · simp [hvm]
  · have h2 : 2 ≤ n := by
      by_contra hlt
      have : n = 0 ∨ n = 1 := by omega
      rcases this with rfl | rfl
      · simp at hvm
      · simp at hvm
    have hn_ge2 : (2 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast h2
    have hinv_le : (n : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ :=
      (inv_le_inv₀ (by positivity) (by norm_num)).2 hn_ge2
    have hvm_nonneg : 0 ≤ ArithmeticFunction.vonMangoldt n :=
      ArithmeticFunction.vonMangoldt_nonneg
    calc
      ArithmeticFunction.vonMangoldt n / (n : ℝ) =
          ArithmeticFunction.vonMangoldt n * (n : ℝ)⁻¹ := by ring
      _ ≤ ArithmeticFunction.vonMangoldt n * (2 : ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_left hinv_le hvm_nonneg
      _ = (1 / 2 : ℝ) * ArithmeticFunction.vonMangoldt n := by ring

/-- The support-overlap decoupled bound factor:
    `2 * exp(L) * S^2 * (∑ vonMangoldt(n) / n)`.
    This achieves the ultimate harmonic reduction: the arithmetic factor is
    proportional to `log(exp(2L)) = 2L`, not `exp(2L)`. -/
def orbitSupportOverlapBound
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) : ℝ :=
  2 * Real.exp (rawFactorSupportRadius geometry) *
    (rawFactorSeminorm geometry) ^ 2 *
    visibleHarmonicChebyshevSum geometry

/-- The support-overlap harmonic bound is unconditionally sharper than the
    Chebyshev sharpened bound. -/
theorem orbitSupportOverlapBound_le_chebyshev_sharpened_bound
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) :
    orbitSupportOverlapBound geometry ≤
      visibleChebyshevPrimeSum geometry * orbitChebyshevSharpenedBound geometry := by
  let L := rawFactorSupportRadius geometry
  let S := rawFactorSeminorm geometry
  have hSsq : 0 ≤ S ^ 2 := sq_nonneg _
  have hcheb_nonneg : 0 ≤ visibleChebyshevPrimeSum geometry :=
    visibleChebyshevPrimeSum_nonneg geometry
  have hharm_le := visibleHarmonicChebyshevSum_le_half_chebyshev geometry
  have hcoeff_nonneg : 0 ≤ 2 * Real.exp L * S ^ 2 := by positivity
  have hstep1 : orbitSupportOverlapBound geometry ≤
      (Real.exp L * S ^ 2) * visibleChebyshevPrimeSum geometry := by
    unfold orbitSupportOverlapBound
    calc
      2 * Real.exp L * S ^ 2 * visibleHarmonicChebyshevSum geometry ≤
          2 * Real.exp L * S ^ 2 * ((1 / 2 : ℝ) * visibleChebyshevPrimeSum geometry) :=
        mul_le_mul_of_nonneg_left hharm_le hcoeff_nonneg
      _ = (Real.exp L * S ^ 2) * visibleChebyshevPrimeSum geometry := by ring
  have hLge1 : (1 : ℝ) ≤ L := by
    dsimp [L, rawFactorSupportRadius]
    have : 1 ≤ geometry.orbitIndex + 2 := by omega
    exact_mod_cast this
  have hexp_le : Real.exp L ≤ 2 * (Real.exp L - Real.exp (-L)) := by
    have h2L : (1 : ℝ) ≤ 2 * L := by linarith
    have h1le : (1 : ℝ) + 1 ≤ Real.exp 1 := Real.add_one_le_exp 1
    have h2le_exp1 : (2 : ℝ) ≤ Real.exp 1 := by linarith
    have hexp1_le_exp2L : Real.exp 1 ≤ Real.exp (2 * L) :=
      Real.exp_le_exp.mpr h2L
    have h2_le_exp2L : (2 : ℝ) ≤ Real.exp (2 * L) :=
      h2le_exp1.trans hexp1_le_exp2L
    have h2expNeg : 2 * Real.exp (-L) ≤ Real.exp L := by
      calc
        2 * Real.exp (-L) = Real.exp (-L) * 2 := by ring
        _ ≤ Real.exp (-L) * Real.exp (2 * L) :=
          mul_le_mul_of_nonneg_left h2_le_exp2L (Real.exp_pos _).le
        _ = Real.exp (-L + 2 * L) := by rw [← Real.exp_add]
        _ = Real.exp L := by
          congr 1
          ring
    linarith
  have hstep2 : (Real.exp L * S ^ 2) * visibleChebyshevPrimeSum geometry ≤
      visibleChebyshevPrimeSum geometry * orbitChebyshevSharpenedBound geometry := by
    unfold orbitChebyshevSharpenedBound
    calc
      (Real.exp L * S ^ 2) * visibleChebyshevPrimeSum geometry ≤
          (2 * (Real.exp L - Real.exp (-L)) * S ^ 2) * visibleChebyshevPrimeSum geometry := by
        apply mul_le_mul_of_nonneg_right _ hcheb_nonneg
        exact mul_le_mul_of_nonneg_right hexp_le hSsq
      _ = visibleChebyshevPrimeSum geometry *
          (2 * (Real.exp L - Real.exp (-L)) * S ^ 2) := by ring
  exact hstep1.trans hstep2

/-- Nonnegativity of the support overlap bound. -/
theorem orbitSupportOverlapBound_nonneg
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) :
    0 ≤ orbitSupportOverlapBound geometry := by
  unfold orbitSupportOverlapBound
  have hexp : 0 ≤ Real.exp (rawFactorSupportRadius geometry) :=
    (Real.exp_pos _).le
  have hS : 0 ≤ (rawFactorSeminorm geometry) ^ 2 := sq_nonneg _
  have hharm := visibleHarmonicChebyshevSum_nonneg geometry
  positivity

/-- Construction of an absorption witness from a support overlap bound. -/
def absorptionWitness_of_overlap_bound
    (rho : sourceNontrivialZeroSet) (g : CompactLogTest)
    (geometry : OrbitG8Geometry rho g)
    (habsorb : orbitSupportOverlapBound geometry ≤
      -archimedeanTerm g.convolutionSquare)
    (hdominate : finitePrimeSum g.convolutionSquare ≤
      orbitSupportOverlapBound geometry) :
    OrbitG8AbsorptionWitness rho :=
  ⟨g, geometry, hdominate.trans habsorb⟩

/-- Master theorem: existence of a support overlap bound for every right-hand zero
    directly implies SourceRH. -/
theorem sourceRH_of_overlap_bounds
    (hproducer : ∀ rho : sourceNontrivialZeroSet,
      (1 / 2 : Real) < rho.1.re →
        ∃ g : CompactLogTest,
          ∃ geometry : OrbitG8Geometry rho g,
            orbitSupportOverlapBound geometry ≤
              -archimedeanTerm g.convolutionSquare ∧
            finitePrimeSum g.convolutionSquare ≤
              orbitSupportOverlapBound geometry) :
    RHDefinitionBridge.standard.SourceRH := by
  apply sourceRH_of_absorptionWitnesses
  intro rho hright
  obtain ⟨g, geometry, habsorb, hdominate⟩ := hproducer rho hright
  exact ⟨absorptionWitness_of_overlap_bound rho g geometry habsorb hdominate⟩

/-- Master theorem: existence of a support overlap bound for every right-hand zero
    directly implies Mathlib's RiemannHypothesis. -/
theorem riemannHypothesis_of_overlap_bounds
    (hproducer : ∀ rho : sourceNontrivialZeroSet,
      (1 / 2 : Real) < rho.1.re →
        ∃ g : CompactLogTest,
          ∃ geometry : OrbitG8Geometry rho g,
            orbitSupportOverlapBound geometry ≤
              -archimedeanTerm g.convolutionSquare ∧
            finitePrimeSum g.convolutionSquare ≤
              orbitSupportOverlapBound geometry) :
    _root_.RiemannHypothesis := by
  apply riemannHypothesis_of_absorptionWitnesses
  intro rho hright
  obtain ⟨g, geometry, habsorb, hdominate⟩ := hproducer rho hright
  exact ⟨absorptionWitness_of_overlap_bound rho g geometry habsorb hdominate⟩

end
end C1P2DirectSupportOverlapDecoupling
end Source
end ConnesWeilRH
