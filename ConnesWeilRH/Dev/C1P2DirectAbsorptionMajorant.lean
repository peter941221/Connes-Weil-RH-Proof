import ConnesWeilRH.Source.RHDefinition
import ConnesWeilRH.Dev.C1G8R0OrbitGeometry
import ConnesWeilRH.Dev.C1OrbitFiniteSignBudget
import ConnesWeilRH.Dev.C1OrbitWindowSemiLocalGate
import ConnesWeilRH.Dev.C1P2BilateralProfile
import ConnesWeilRH.Dev.C1P2DirectSemiLocalGate
import ConnesWeilRH.Dev.C1P2DirectAbsorptionWitness
import ConnesWeilRH.Dev.C1P2SignedBudget
import ConnesWeilRH.Dev.C1SameOwnerWeil
import ConnesWeilRH.Dev.C1HealthyYoshidaDetector
import ConnesWeilRH.Dev.C1HealthyYoshidaSpectralNegativity

namespace ConnesWeilRH
namespace Source
namespace C1P2DirectAbsorptionMajorant

open C1G8R0OrbitGeometry
open C1OrbitFiniteSignBudget
open C1OrbitWindowSemiLocalGate
open C1P2BilateralProfile
open C1P2DirectSemiLocalGate
open C1P2DirectAbsorptionWitness
open C1P2SignedBudget
open C1SameOwnerWeil
open C1HealthyYoshidaDetector
open C1HealthyYoshidaSpectralNegativity
open CC20YoshidaNearZeros
open CCM25Concrete.CompactLogConvolution
open scoped BigOperators

noncomputable section

/-- The total arithmetic weight of visible primes for an orbit geometry. -/
def visiblePrimeWeightSum
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) : Real :=
  ∑ n ∈ orbitVisiblePrimeRange geometry,
    ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real))

/-- The total Chebyshev weight of visible primes for an orbit geometry. -/
def visibleChebyshevPrimeSum
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) : Real :=
  ∑ n ∈ orbitVisiblePrimeRange geometry,
    ArithmeticFunction.vonMangoldt n

/-- Uniform bound on the absolute bilateral profile over visible primes. -/
def isProfileUniformBound
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (B : Real) : Prop :=
  ∀ n ∈ orbitVisiblePrimeRange geometry,
    |(bilateralProfile g.convolutionSquare (Real.log n)).re| ≤ B

/-- Each term in the visible prime weight sum is nonnegative. -/
theorem visiblePrimeWeightTerm_nonneg (n : ℕ) :
    0 ≤ ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real)) := by
  have hcoeff : 0 ≤ ArithmeticFunction.vonMangoldt n :=
    ArithmeticFunction.vonMangoldt_nonneg
  have hinv : 0 ≤ (1 / Real.sqrt (n : Real)) := by positivity
  exact mul_nonneg hcoeff hinv

/-- The visible prime weight sum is nonnegative. -/
theorem visiblePrimeWeightSum_nonneg
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) :
    0 ≤ visiblePrimeWeightSum geometry := by
  unfold visiblePrimeWeightSum
  apply Finset.sum_nonneg
  intro n _hn
  exact visiblePrimeWeightTerm_nonneg n

/-- The visible Chebyshev prime sum is nonnegative. -/
theorem visibleChebyshevPrimeSum_nonneg
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) :
    0 ≤ visibleChebyshevPrimeSum geometry := by
  unfold visibleChebyshevPrimeSum
  apply Finset.sum_nonneg
  intro n _hn
  exact ArithmeticFunction.vonMangoldt_nonneg

/-- Factoring: the weighted profile sum is bounded by the prime weight sum
    times any uniform profile bound. -/
theorem sum_weighted_profile_le_weightSum_mul_bound
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) {B : Real}
    (hB : isProfileUniformBound geometry B) :
    (∑ n ∈ orbitVisiblePrimeRange geometry,
        ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real)) *
          |(bilateralProfile g.convolutionSquare (Real.log n)).re|) ≤
      visiblePrimeWeightSum geometry * B := by
  unfold visiblePrimeWeightSum
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro n hn
  have hterm_nonneg := visiblePrimeWeightTerm_nonneg n
  have hpoint := hB n hn
  exact mul_le_mul_of_nonneg_left hpoint hterm_nonneg

/-- Construction of an absorption witness from a factored profile bound. -/
def absorptionWitness_of_uniform_profile_bound
    (rho : sourceNontrivialZeroSet) (g : CompactLogTest)
    (geometry : OrbitG8Geometry rho g) {B : Real}
    (hB : isProfileUniformBound geometry B)
    (habsorb : visiblePrimeWeightSum geometry * B ≤
      -archimedeanTerm g.convolutionSquare) :
    OrbitG8AbsorptionWitness rho := by
  apply absorptionWitness_of_range_majorant rho g geometry
  have hfactor := sum_weighted_profile_le_weightSum_mul_bound geometry hB
  exact hfactor.trans habsorb

/-- Master theorem: existence of a factored uniform profile bound for every
    right-hand zero directly implies Mathlib's RiemannHypothesis. -/
theorem riemannHypothesis_of_uniform_profile_bounds
    (hproducer : ∀ rho : sourceNontrivialZeroSet,
      (1 / 2 : Real) < rho.1.re →
        ∃ g : CompactLogTest,
          ∃ geometry : OrbitG8Geometry rho g,
            ∃ B : Real,
              isProfileUniformBound geometry B ∧
              visiblePrimeWeightSum geometry * B ≤
                -archimedeanTerm g.convolutionSquare) :
    _root_.RiemannHypothesis := by
  apply riemannHypothesis_of_absorptionWitnesses
  intro rho hright
  obtain ⟨g, geometry, B, hB, habsorb⟩ := hproducer rho hright
  exact ⟨absorptionWitness_of_uniform_profile_bound rho g geometry hB habsorb⟩

/-- The Chebyshev weight sum bounds the square-root weighted sum for n >= 1. -/
theorem visiblePrimeWeightSum_le_chebyshev
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) :
    visiblePrimeWeightSum geometry ≤ visibleChebyshevPrimeSum geometry := by
  unfold visiblePrimeWeightSum visibleChebyshevPrimeSum
  apply Finset.sum_le_sum
  intro n _hn
  by_cases h0 : n = 0
  · simp [h0]
  · have h1 : (1 : Real) ≤ (n : Real) := by
      exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero h0)
    have hsqrt : (1 : Real) ≤ Real.sqrt (n : Real) := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt h1
    have hinv : (1 / Real.sqrt (n : Real)) ≤ 1 := by
      have hpos : 0 < Real.sqrt (n : Real) := by positivity
      rw [div_le_iff₀ hpos]
      linarith
    have hcoeff : 0 ≤ ArithmeticFunction.vonMangoldt n :=
      ArithmeticFunction.vonMangoldt_nonneg
    calc
      ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real)) ≤
          ArithmeticFunction.vonMangoldt n * 1 :=
        mul_le_mul_of_nonneg_left hinv hcoeff
      _ = ArithmeticFunction.vonMangoldt n := mul_one _

/-- Construction of an absorption witness from a Chebyshev prime majorant. -/
def absorptionWitness_of_chebyshev_bound
    (rho : sourceNontrivialZeroSet) (g : CompactLogTest)
    (geometry : OrbitG8Geometry rho g) {B : Real}
    (hBnonneg : 0 ≤ B)
    (hB : isProfileUniformBound geometry B)
    (habsorb : visibleChebyshevPrimeSum geometry * B ≤
      -archimedeanTerm g.convolutionSquare) :
    OrbitG8AbsorptionWitness rho := by
  apply absorptionWitness_of_uniform_profile_bound rho g geometry hB
  have hweight := visiblePrimeWeightSum_le_chebyshev geometry
  have hmul : visiblePrimeWeightSum geometry * B ≤
      visibleChebyshevPrimeSum geometry * B :=
    mul_le_mul_of_nonneg_right hweight hBnonneg
  exact hmul.trans habsorb

/-- Master theorem: existence of a Chebyshev majorant for every right-hand zero
    directly implies Mathlib's RiemannHypothesis. -/
theorem riemannHypothesis_of_chebyshev_bounds
    (hproducer : ∀ rho : sourceNontrivialZeroSet,
      (1 / 2 : Real) < rho.1.re →
        ∃ g : CompactLogTest,
          ∃ geometry : OrbitG8Geometry rho g,
            ∃ B : Real,
              0 ≤ B ∧
              isProfileUniformBound geometry B ∧
              visibleChebyshevPrimeSum geometry * B ≤
                -archimedeanTerm g.convolutionSquare) :
    _root_.RiemannHypothesis := by
  apply riemannHypothesis_of_absorptionWitnesses
  intro rho hright
  obtain ⟨g, geometry, B, hBnonneg, hB, habsorb⟩ := hproducer rho hright
  exact ⟨absorptionWitness_of_chebyshev_bound rho g geometry hBnonneg hB habsorb⟩

end
end C1P2DirectAbsorptionMajorant
end Source
end ConnesWeilRH
