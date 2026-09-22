import ConnesWeilRH.Source.RHDefinition
import ConnesWeilRH.Dev.C1G8R0OrbitGeometry
import ConnesWeilRH.Dev.C1OrbitFiniteSignBudget
import ConnesWeilRH.Dev.C1OrbitWindowSemiLocalGate
import ConnesWeilRH.Dev.C1P2BilateralProfile
import ConnesWeilRH.Dev.C1P2DirectSemiLocalGate
import ConnesWeilRH.Dev.C1P2DirectAbsorptionWitness
import ConnesWeilRH.Dev.C1P2DirectAbsorptionMajorant
import ConnesWeilRH.Dev.C1P2OrbitPhysicalProfileReadback
import ConnesWeilRH.Dev.C1P2OrbitPhysicalKernelIntegrandBounds
import ConnesWeilRH.Dev.C1P2SignedBudget
import ConnesWeilRH.Dev.C1SameOwnerWeil
import ConnesWeilRH.Dev.C1HealthyYoshidaDetector
import ConnesWeilRH.Dev.C1HealthyYoshidaSpectralNegativity

namespace ConnesWeilRH
namespace Source
namespace C1P2DirectChebyshevDecoupling

open C1G8R0OrbitGeometry
open C1OrbitFiniteSignBudget
open C1OrbitWindowSemiLocalGate
open C1P2BilateralProfile
open C1P2DirectSemiLocalGate
open C1P2DirectAbsorptionWitness
open C1P2DirectAbsorptionMajorant
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

/-- The support radius of the raw orbit factor: `L = orbitIndex + 2`. -/
def rawFactorSupportRadius
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) : ℝ :=
  ((geometry.orbitIndex + 2 : ℕ) : ℝ)

/-- The L^∞ seminorm of the raw orbit factor. -/
def rawFactorSeminorm
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) : ℝ :=
  SchwartzMap.seminorm ℂ 0 0 (orbitRawFactor geometry).test

/-- The Chebyshev-decoupled bound factor multiplying the visible Chebyshev prime sum. -/
def orbitChebyshevDecoupledBound
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) : ℝ :=
  4 * rawFactorSupportRadius geometry *
    Real.exp (rawFactorSupportRadius geometry) *
    (rawFactorSeminorm geometry) ^ 2

/-- Positivity of the raw factor support radius. -/
theorem rawFactorSupportRadius_pos
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) :
    0 < rawFactorSupportRadius geometry := by
  dsimp [rawFactorSupportRadius]
  positivity

/-- Nonnegativity of the raw factor seminorm. -/
theorem rawFactorSeminorm_nonneg
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) :
    0 ≤ rawFactorSeminorm geometry := by
  dsimp [rawFactorSeminorm]
  positivity

/-- Nonnegativity of the Chebyshev decoupled bound. -/
theorem orbitChebyshevDecoupledBound_nonneg
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) :
    0 ≤ orbitChebyshevDecoupledBound geometry := by
  unfold orbitChebyshevDecoupledBound
  have hr : 0 ≤ rawFactorSupportRadius geometry := (rawFactorSupportRadius_pos geometry).le
  have hS : 0 ≤ rawFactorSeminorm geometry := rawFactorSeminorm_nonneg geometry
  positivity

/-- Pointwise cancellation identity: the arithmetic weight `1 / sqrt(n)` cancels
    against the half-density dilation `exp(log(n) / 2) = sqrt(n)`, eliminating all
    prime-dependent growth from the integrand bound. -/
theorem cancellation_identity (n : ℕ) (L : ℝ) (S : ℝ) :
    ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : ℝ)) *
      (Real.exp (Real.log (n : ℝ) / 2 + L) * S ^ 2) =
    ArithmeticFunction.vonMangoldt n * (Real.exp L * S ^ 2) := by
  by_cases h0 : n = 0
  · simp [h0]
  · have hpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero h0)
    have h0p : 0 ≤ (n : ℝ) := le_of_lt hpos
    have hlogs : Real.log (Real.sqrt (n : ℝ)) = Real.log (n : ℝ) / 2 :=
      Real.log_sqrt h0p
    have hsqrt_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hpos
    have hsqrt_exp : Real.sqrt (n : ℝ) = Real.exp (Real.log (n : ℝ) / 2) := by
      rw [← Real.exp_log hsqrt_pos, hlogs]
    have hexp_add : Real.exp (Real.log (n : ℝ) / 2 + L) =
        Real.exp (Real.log (n : ℝ) / 2) * Real.exp L := Real.exp_add _ _
    rw [hexp_add, ← hsqrt_exp]
    have hinv : (1 / Real.sqrt (n : ℝ)) * Real.sqrt (n : ℝ) = 1 :=
      one_div_mul_cancel (ne_of_gt hsqrt_pos)
    calc
      ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : ℝ)) *
          (Real.sqrt (n : ℝ) * Real.exp L * S ^ 2) =
        ArithmeticFunction.vonMangoldt n *
          ((1 / Real.sqrt (n : ℝ)) * Real.sqrt (n : ℝ)) *
          (Real.exp L * S ^ 2) := by ring
      _ = ArithmeticFunction.vonMangoldt n * 1 * (Real.exp L * S ^ 2) := by rw [hinv]
      _ = ArithmeticFunction.vonMangoldt n * (Real.exp L * S ^ 2) := by ring

/-- The integrand budget sum equals the visible Chebyshev prime sum multiplied
    by the constant factor `2 * exp(L) * S^2`. -/
theorem sum_seminorm_budget_eq_chebyshev_mul
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) :
    (∑ n ∈ orbitVisiblePrimeRange geometry,
      2 * (ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real))) *
        (Real.exp (Real.log n / 2 +
          ((geometry.orbitIndex + 2 : Nat) : Real)) *
          (SchwartzMap.seminorm ℂ 0 0 (orbitRawFactor geometry).test) ^ 2)) =
      visibleChebyshevPrimeSum geometry *
        (2 * Real.exp (rawFactorSupportRadius geometry) *
          (rawFactorSeminorm geometry) ^ 2) := by
  have hterm : ∀ n ∈ orbitVisiblePrimeRange geometry,
      2 * (ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real))) *
        (Real.exp (Real.log n / 2 +
          ((geometry.orbitIndex + 2 : Nat) : Real)) *
          (SchwartzMap.seminorm ℂ 0 0 (orbitRawFactor geometry).test) ^ 2) =
      ArithmeticFunction.vonMangoldt n *
        (2 * Real.exp (rawFactorSupportRadius geometry) *
          (rawFactorSeminorm geometry) ^ 2) := by
    intro n _hn
    have hcancel := cancellation_identity n
      (rawFactorSupportRadius geometry) (rawFactorSeminorm geometry)
    dsimp [rawFactorSupportRadius, rawFactorSeminorm] at hcancel ⊢
    calc
      2 * (ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real))) *
          (Real.exp (Real.log n / 2 + ((geometry.orbitIndex + 2 : Nat) : Real)) *
            (SchwartzMap.seminorm ℂ 0 0 (orbitRawFactor geometry).test) ^ 2) =
        2 * (ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real)) *
          (Real.exp (Real.log n / 2 + ((geometry.orbitIndex + 2 : Nat) : Real)) *
            (SchwartzMap.seminorm ℂ 0 0 (orbitRawFactor geometry).test) ^ 2)) := by ring
      _ = 2 * (ArithmeticFunction.vonMangoldt n *
          (Real.exp ((geometry.orbitIndex + 2 : Nat) : Real) *
            (SchwartzMap.seminorm ℂ 0 0 (orbitRawFactor geometry).test) ^ 2)) := by rw [hcancel]
      _ = ArithmeticFunction.vonMangoldt n *
          (2 * Real.exp ((geometry.orbitIndex + 2 : Nat) : Real) *
            (SchwartzMap.seminorm ℂ 0 0 (orbitRawFactor geometry).test) ^ 2) := by ring
  rw [Finset.sum_congr rfl hterm]
  rw [← Finset.sum_mul]
  rfl

/-- Master majorant: the finite visible prime sum of the genuine convolution
    square is bounded by the visible Chebyshev prime sum times the explicit
    geometry-decoupled bound factor `4 * L * exp(L) * S^2`. -/
theorem finitePrimeSum_le_chebyshev_seminorm_bound
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) :
    finitePrimeSum g.convolutionSquare ≤
      visibleChebyshevPrimeSum geometry * orbitChebyshevDecoupledBound geometry := by
  have hsum_int :
      finitePrimeSum g.convolutionSquare =
        ∫ t in (-((geometry.orbitIndex + 2 : Nat) : Real))..
          (((geometry.orbitIndex + 2 : Nat) : Real)),
          orbitFinitePhysicalKernelIntegrand geometry t := by
    rw [finitePrimeSum_eq_integral_finitePhysicalKernelIntegrand geometry]
    exact integral_orbitFinitePhysicalKernelIntegrand_eq_interval geometry
  rw [hsum_int]
  have hbudget :=
    intervalIntegral_orbitFinitePhysicalKernelIntegrand_le_seminorm_budget geometry
  have hsum_eq := sum_seminorm_budget_eq_chebyshev_mul geometry
  let C := visibleChebyshevPrimeSum geometry *
    (2 * Real.exp (rawFactorSupportRadius geometry) * (rawFactorSeminorm geometry) ^ 2)
  have hrhs :
      (∫ t in (-((geometry.orbitIndex + 2 : Nat) : Real))..
        (((geometry.orbitIndex + 2 : Nat) : Real)),
        Finset.sum (orbitVisiblePrimeRange geometry) (fun n =>
          2 * (ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real))) *
            (Real.exp (Real.log n / 2 +
              ((geometry.orbitIndex + 2 : Nat) : Real)) *
              (SchwartzMap.seminorm ℂ 0 0 (orbitRawFactor geometry).test) ^ 2))) =
        visibleChebyshevPrimeSum geometry * orbitChebyshevDecoupledBound geometry := by
    have hcongr : (fun _t : ℝ => Finset.sum (orbitVisiblePrimeRange geometry) (fun n =>
          2 * (ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real))) *
            (Real.exp (Real.log n / 2 +
              ((geometry.orbitIndex + 2 : Nat) : Real)) *
              (SchwartzMap.seminorm ℂ 0 0 (orbitRawFactor geometry).test) ^ 2))) =
        (fun _t : ℝ => C) := by
      funext _t
      exact hsum_eq
    rw [hcongr]
    have hint_const : ∫ t in (-((geometry.orbitIndex + 2 : Nat) : Real))..
        (((geometry.orbitIndex + 2 : Nat) : Real)), C =
        (2 * ((geometry.orbitIndex + 2 : Nat) : Real)) * C := by
      rw [intervalIntegral.integral_const, ← smul_eq_mul]
      ring
    rw [hint_const]
    dsimp [C, orbitChebyshevDecoupledBound, rawFactorSupportRadius]
    ring
  exact hbudget.trans (by rw [hrhs])

/-- Construction of an absorption witness from a Chebyshev seminorm bound. -/
def absorptionWitness_of_chebyshev_seminorm_bound
    (rho : sourceNontrivialZeroSet) (g : CompactLogTest)
    (geometry : OrbitG8Geometry rho g)
    (habsorb : visibleChebyshevPrimeSum geometry *
        orbitChebyshevDecoupledBound geometry ≤
      -archimedeanTerm g.convolutionSquare) :
    OrbitG8AbsorptionWitness rho :=
  ⟨g, geometry, (finitePrimeSum_le_chebyshev_seminorm_bound geometry).trans habsorb⟩

/-- Master theorem: existence of a Chebyshev seminorm majorant for every right-hand zero
    directly implies SourceRH. -/
theorem sourceRH_of_chebyshev_seminorm_bounds
    (hproducer : ∀ rho : sourceNontrivialZeroSet,
      (1 / 2 : Real) < rho.1.re →
        ∃ g : CompactLogTest,
          ∃ geometry : OrbitG8Geometry rho g,
            visibleChebyshevPrimeSum geometry *
                orbitChebyshevDecoupledBound geometry ≤
              -archimedeanTerm g.convolutionSquare) :
    RHDefinitionBridge.standard.SourceRH := by
  apply sourceRH_of_absorptionWitnesses
  intro rho hright
  obtain ⟨g, geometry, habsorb⟩ := hproducer rho hright
  exact ⟨absorptionWitness_of_chebyshev_seminorm_bound rho g geometry habsorb⟩

/-- Master theorem: existence of a Chebyshev seminorm majorant for every right-hand zero
    directly implies Mathlib's RiemannHypothesis. -/
theorem riemannHypothesis_of_chebyshev_seminorm_bounds
    (hproducer : ∀ rho : sourceNontrivialZeroSet,
      (1 / 2 : Real) < rho.1.re →
        ∃ g : CompactLogTest,
          ∃ geometry : OrbitG8Geometry rho g,
            visibleChebyshevPrimeSum geometry *
                orbitChebyshevDecoupledBound geometry ≤
              -archimedeanTerm g.convolutionSquare) :
    _root_.RiemannHypothesis := by
  apply riemannHypothesis_of_absorptionWitnesses
  intro rho hright
  obtain ⟨g, geometry, habsorb⟩ := hproducer rho hright
  exact ⟨absorptionWitness_of_chebyshev_seminorm_bound rho g geometry habsorb⟩

end
end C1P2DirectChebyshevDecoupling
end Source
end ConnesWeilRH
