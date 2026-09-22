import ConnesWeilRH.Source.RHDefinition
import ConnesWeilRH.Dev.C1G8R0OrbitGeometry
import ConnesWeilRH.Dev.C1OrbitFiniteSignBudget
import ConnesWeilRH.Dev.C1OrbitWindowSemiLocalGate
import ConnesWeilRH.Dev.C1P2BilateralProfile
import ConnesWeilRH.Dev.C1P2DirectSemiLocalGate
import ConnesWeilRH.Dev.C1P2SignedBudget
import ConnesWeilRH.Dev.C1SameOwnerWeil
import ConnesWeilRH.Dev.C1HealthyYoshidaDetector
import ConnesWeilRH.Dev.C1HealthyYoshidaSpectralNegativity

namespace ConnesWeilRH
namespace Source
namespace C1P2DirectAbsorptionWitness

open C1G8R0OrbitGeometry
open C1OrbitFiniteSignBudget
open C1OrbitWindowSemiLocalGate
open C1P2BilateralProfile
open C1P2DirectSemiLocalGate
open C1P2SignedBudget
open C1SameOwnerWeil
open C1HealthyYoshidaDetector
open C1HealthyYoshidaSpectralNegativity
open CC20YoshidaNearZeros
open CCM25Concrete.CompactLogConvolution
open scoped BigOperators

noncomputable section

/-- A packaged absorption witness for one hypothetical off-line zero:
    an explicit compact-log detector and its orbit geometry whose finite
    visible-prime sum is absorbed by the negative Archimedean margin. -/
structure OrbitG8AbsorptionWitness (rho : sourceNontrivialZeroSet) where
  g : CompactLogTest
  geometry : OrbitG8Geometry rho g
  absorption : finitePrimeSum g.convolutionSquare ≤
    - archimedeanTerm g.convolutionSquare

/-- The combined Weil geometric energy of the test's convolution square. -/
def weilGeometricEnergy (g : CompactLogTest) : Real :=
  archimedeanTerm g.convolutionSquare + finitePrimeSum g.convolutionSquare

/-- Absorption is definitionally equivalent to nonpositivity of the
    Weil geometric energy. -/
theorem absorption_iff_weilGeometricEnergy_nonpos (g : CompactLogTest) :
    (finitePrimeSum g.convolutionSquare ≤ - archimedeanTerm g.convolutionSquare) ↔
      weilGeometricEnergy g ≤ 0 := by
  unfold weilGeometricEnergy
  constructor <;> intro h <;> linarith

/-- An absorption witness satisfies the orbit-window semi-local gate. -/
theorem orbitWindowSemiLocalGate_of_absorptionWitness
    (rho : sourceNontrivialZeroSet) (w : OrbitG8AbsorptionWitness rho) :
    orbitWindowSemiLocalGate w.g := by
  unfold orbitWindowSemiLocalGate
  linarith [w.absorption]

/-- Existence of an absorption witness for every right-hand zero directly
    implies SourceRH. -/
theorem sourceRH_of_absorptionWitnesses
    (hproducer : ∀ rho : sourceNontrivialZeroSet,
      (1 / 2 : Real) < rho.1.re →
        Nonempty (OrbitG8AbsorptionWitness rho)) :
    RHDefinitionBridge.standard.SourceRH := by
  apply sourceRH_of_right_orbitGeometry_primeAbsorption
  intro rho hright
  obtain ⟨w⟩ := hproducer rho hright
  exact ⟨w.g, w.geometry, w.absorption⟩

/-- Master exit theorem: existence of an absorption witness for every right-hand
    zero directly implies Mathlib's canonical RiemannHypothesis. -/
theorem riemannHypothesis_of_absorptionWitnesses
    (hproducer : ∀ rho : sourceNontrivialZeroSet,
      (1 / 2 : Real) < rho.1.re →
        Nonempty (OrbitG8AbsorptionWitness rho)) :
    _root_.RiemannHypothesis := by
  exact RHDefinitionBridge.standard_source_rh_iff_mathlib.mp
    (sourceRH_of_absorptionWitnesses hproducer)

/-- Construction of an absorption witness via intermediate scalar margin transfer. -/
def absorptionWitness_of_margin
    (rho : sourceNontrivialZeroSet) (g : CompactLogTest)
    (geometry : OrbitG8Geometry rho g) (M : Real)
    (hprime : finitePrimeSum g.convolutionSquare ≤ M)
    (harch : M ≤ - archimedeanTerm g.convolutionSquare) :
    OrbitG8AbsorptionWitness rho :=
  ⟨g, geometry, hprime.trans harch⟩

/-- Construction of an absorption witness via norm-level prime absorption. -/
def absorptionWitness_of_norm_absorption
    (rho : sourceNontrivialZeroSet) (g : CompactLogTest)
    (geometry : OrbitG8Geometry rho g)
    (h : |finitePrimeSum g.convolutionSquare| ≤
      - archimedeanTerm g.convolutionSquare) :
    OrbitG8AbsorptionWitness rho :=
  ⟨g, geometry, (le_abs_self (finitePrimeSum g.convolutionSquare)).trans h⟩

/-- Construction of an absorption witness via finite-range absolute profile majorant. -/
def absorptionWitness_of_range_majorant
    (rho : sourceNontrivialZeroSet) (g : CompactLogTest)
    (geometry : OrbitG8Geometry rho g)
    (h : (∑ n ∈ Finset.range
            (Nat.ceil (Real.exp (2 * ((geometry.orbitIndex + 2 : Nat) : Real))) + 1),
            ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real)) *
              |(bilateralProfile g.convolutionSquare (Real.log n)).re|) ≤
          - archimedeanTerm g.convolutionSquare) :
    OrbitG8AbsorptionWitness rho := by
  refine ⟨g, geometry, ?_⟩
  rw [finitePrimeSum_eq_sum_range_of_orbitG8Geometry geometry]
  have hsum_le :
      (∑ n ∈ Finset.range
          (Nat.ceil (Real.exp (2 * ((geometry.orbitIndex + 2 : Nat) : Real))) + 1),
          finitePrimeTerm g.convolutionSquare n) ≤
        ∑ n ∈ Finset.range
          (Nat.ceil (Real.exp (2 * ((geometry.orbitIndex + 2 : Nat) : Real))) + 1),
          ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real)) *
            |(bilateralProfile g.convolutionSquare (Real.log n)).re| := by
    apply Finset.sum_le_sum
    intro n _hn
    rw [finitePrimeTerm_eq_realCoefficient_mul_bilateralProfile_re]
    have hcoeff : 0 ≤ ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real)) :=
      mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
    exact mul_le_mul_of_nonneg_left (le_abs_self _) hcoeff
  exact hsum_le.trans h

/-- Construction of an absorption witness via signed profile credit/deficit budget. -/
def absorptionWitness_of_signedBudget
    (rho : sourceNontrivialZeroSet) (g : CompactLogTest)
    (geometry : OrbitG8Geometry rho g)
    (h : archimedeanTerm g.convolutionSquare +
            signedProfileCredit g (orbitVisiblePrimeRange geometry) ≤
          signedProfileDeficit g (orbitVisiblePrimeRange geometry)) :
    OrbitG8AbsorptionWitness rho := by
  refine ⟨g, geometry, ?_⟩
  have hgate := (orbitWindowSemiLocalGate_iff_signedBudget geometry).mpr h
  unfold orbitWindowSemiLocalGate at hgate
  linarith

/-- Construction of an absorption witness via componentwise nonpositivity. -/
def absorptionWitness_of_componentwise_nonpos
    (rho : sourceNontrivialZeroSet) (g : CompactLogTest)
    (geometry : OrbitG8Geometry rho g)
    (harch : archimedeanTerm g.convolutionSquare ≤ 0)
    (hprime : finitePrimeSum g.convolutionSquare ≤ 0) :
    OrbitG8AbsorptionWitness rho :=
  ⟨g, geometry, by linarith⟩

/-- Riemann hypothesis directly from scalar margin witnesses. -/
theorem riemannHypothesis_of_marginWitnesses
    (hproducer : ∀ rho : sourceNontrivialZeroSet,
      (1 / 2 : Real) < rho.1.re →
        ∃ g : CompactLogTest,
          ∃ geometry : OrbitG8Geometry rho g,
            ∃ M : Real,
              finitePrimeSum g.convolutionSquare ≤ M ∧
              M ≤ - archimedeanTerm g.convolutionSquare) :
    _root_.RiemannHypothesis := by
  apply riemannHypothesis_of_absorptionWitnesses
  intro rho hright
  obtain ⟨g, geometry, M, hprime, harch⟩ := hproducer rho hright
  exact ⟨absorptionWitness_of_margin rho g geometry M hprime harch⟩

/-- Riemann hypothesis directly from finite-range profile majorants. -/
theorem riemannHypothesis_of_rangeMajorantWitnesses
    (hproducer : ∀ rho : sourceNontrivialZeroSet,
      (1 / 2 : Real) < rho.1.re →
        ∃ g : CompactLogTest,
          ∃ geometry : OrbitG8Geometry rho g,
            (∑ n ∈ Finset.range
                (Nat.ceil (Real.exp (2 * ((geometry.orbitIndex + 2 : Nat) : Real))) + 1),
                ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real)) *
                  |(bilateralProfile g.convolutionSquare (Real.log n)).re|) ≤
              - archimedeanTerm g.convolutionSquare) :
    _root_.RiemannHypothesis := by
  apply riemannHypothesis_of_absorptionWitnesses
  intro rho hright
  obtain ⟨g, geometry, hbound⟩ := hproducer rho hright
  exact ⟨absorptionWitness_of_range_majorant rho g geometry hbound⟩

end
end C1P2DirectAbsorptionWitness
end Source
end ConnesWeilRH
