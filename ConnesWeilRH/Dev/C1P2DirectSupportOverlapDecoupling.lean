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
