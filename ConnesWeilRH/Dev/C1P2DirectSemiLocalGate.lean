import ConnesWeilRH.Dev.C1G8R0OrbitGeometry
import ConnesWeilRH.Dev.C1OrbitFiniteSignBudget
import ConnesWeilRH.Dev.C1OrbitWindowSemiLocalGate
import ConnesWeilRH.Dev.C1P2BilateralProfile
import ConnesWeilRH.Dev.C1P2SignedBudget
import ConnesWeilRH.Dev.C1SameOwnerWeil
import ConnesWeilRH.Dev.C1HealthyYoshidaDetector
import ConnesWeilRH.Dev.C1HealthyYoshidaSpectralNegativity

namespace ConnesWeilRH
namespace Source
namespace C1P2DirectSemiLocalGate

open C1G8R0OrbitGeometry
open C1OrbitFiniteSignBudget
open C1OrbitWindowSemiLocalGate
open C1P2BilateralProfile
open C1P2SignedBudget
open C1SameOwnerWeil
open C1HealthyYoshidaDetector
open C1HealthyYoshidaSpectralNegativity
open CC20YoshidaNearZeros
open CCM25Concrete.CompactLogConvolution
open scoped BigOperators

noncomputable section

/-- The exact equivalence: on the selected orbit geometry, the semi-local gate
    is equivalent to nonpositivity of the Archimedean term plus the finite
    visible-prime sum. -/
theorem orbitWindowSemiLocalGate_eq_archimedean_add_finitePrimeSum
    (g : CompactLogTest) :
    orbitWindowSemiLocalGate g ↔
      archimedeanTerm g.convolutionSquare + finitePrimeSum g.convolutionSquare ≤ 0 :=
  Iff.rfl

/-- Direct exit to SourceRH from the orbit-window semi-local gate:
    for each hypothetical right zero, exhibiting a same-owner geometry whose
    selected test satisfies `orbitWindowSemiLocalGate` immediately implies
    SourceRH. -/
theorem sourceRH_of_right_orbitGeometry_orbitWindowSemiLocalGate
    (hproducer : ∀ rho : sourceNontrivialZeroSet,
      (1 / 2 : Real) < rho.1.re →
        ∃ g : CompactLogTest,
          ∃ geometry : OrbitG8Geometry rho g,
            orbitWindowSemiLocalGate g) :
    RHDefinitionBridge.standard.SourceRH := by
  apply healthy_sourceRH_of_right_detector_specific_qw_nonneg
  intro rho hright
  obtain ⟨g, geometry, hgate⟩ := hproducer rho hright
  have hdata : HealthyYoshidaDetectorData rho.1 g :=
    healthyDetectorData_of_orbitG8Geometry geometry (ne_of_gt hright) hright
  refine ⟨g, hdata, ?_⟩
  exact qw_nonneg_of_orbitWindowSemiLocalGate g hdata.vanishesOnF hgate

/-- Equivalent formulation in terms of the explicit finite range sum. -/
theorem sourceRH_of_right_orbitGeometry_finiteRangeGate
    (hproducer : ∀ rho : sourceNontrivialZeroSet,
      (1 / 2 : Real) < rho.1.re →
        ∃ g : CompactLogTest,
          ∃ geometry : OrbitG8Geometry rho g,
            archimedeanTerm g.convolutionSquare +
              ∑ n ∈ Finset.range
                (Nat.ceil (Real.exp (2 * ((geometry.orbitIndex + 2 : Nat) : Real))) + 1),
                ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real)) *
                  (bilateralProfile g.convolutionSquare (Real.log n)).re ≤ 0) :
    RHDefinitionBridge.standard.SourceRH := by
  apply sourceRH_of_right_orbitGeometry_orbitWindowSemiLocalGate
  intro rho hright
  obtain ⟨g, geometry, hsum⟩ := hproducer rho hright
  refine ⟨g, geometry, ?_⟩
  exact (orbitWindowSemiLocalGate_iff_finiteRangeBilateralProfile geometry).mpr hsum

/-- Absorption formulation: if the finite prime sum is absorbed by the
    negative Archimedean margin, SourceRH follows. -/
theorem sourceRH_of_right_orbitGeometry_primeAbsorption
    (hproducer : ∀ rho : sourceNontrivialZeroSet,
      (1 / 2 : Real) < rho.1.re →
        ∃ g : CompactLogTest,
          ∃ geometry : OrbitG8Geometry rho g,
            finitePrimeSum g.convolutionSquare ≤
              - archimedeanTerm g.convolutionSquare) :
    RHDefinitionBridge.standard.SourceRH := by
  apply sourceRH_of_right_orbitGeometry_orbitWindowSemiLocalGate
  intro rho hright
  obtain ⟨g, geometry, habsorb⟩ := hproducer rho hright
  refine ⟨g, geometry, ?_⟩
  unfold orbitWindowSemiLocalGate
  linarith

/-- Componentwise nonpositivity: if both the Archimedean term and the finite
    prime sum are nonpositive on the selected geometry, SourceRH follows. -/
theorem sourceRH_of_right_orbitGeometry_archimedean_and_finitePrimeSum_nonpos
    (hproducer : ∀ rho : sourceNontrivialZeroSet,
      (1 / 2 : Real) < rho.1.re →
        ∃ g : CompactLogTest,
          ∃ geometry : OrbitG8Geometry rho g,
            archimedeanTerm g.convolutionSquare ≤ 0 ∧
            finitePrimeSum g.convolutionSquare ≤ 0) :
    RHDefinitionBridge.standard.SourceRH := by
  apply sourceRH_of_right_orbitGeometry_orbitWindowSemiLocalGate
  intro rho hright
  obtain ⟨g, geometry, harch, hprime⟩ := hproducer rho hright
  refine ⟨g, geometry, ?_⟩
  unfold orbitWindowSemiLocalGate
  linarith

/-- Pointwise nonpositivity of the bilateral profile across visible primes:
    if the Archimedean term is nonpositive and the bilateral profile is
    nonpositive at every visible prime power, SourceRH follows. -/
theorem sourceRH_of_right_orbitGeometry_bilateralProfile_nonpos
    (hproducer : ∀ rho : sourceNontrivialZeroSet,
      (1 / 2 : Real) < rho.1.re →
        ∃ g : CompactLogTest,
          ∃ geometry : OrbitG8Geometry rho g,
            archimedeanTerm g.convolutionSquare ≤ 0 ∧
            ∀ n ∈ globalPrimeIndexSet g.convolutionSquare,
              (bilateralProfile g.convolutionSquare (Real.log n)).re ≤ 0) :
    RHDefinitionBridge.standard.SourceRH := by
  apply sourceRH_of_right_orbitGeometry_archimedean_and_finitePrimeSum_nonpos
  intro rho hright
  obtain ⟨g, geometry, harch, hprof⟩ := hproducer rho hright
  refine ⟨g, geometry, harch, ?_⟩
  exact finitePrimeSum_nonpos_of_bilateralProfile_re_nonpos g.convolutionSquare hprof

/-- Margin transfer: if the finite prime sum is bounded by an intermediate
    scalar margin M which is absorbed by the negative Archimedean term,
    SourceRH follows. -/
theorem sourceRH_of_right_orbitGeometry_margin_transfer
    (hproducer : ∀ rho : sourceNontrivialZeroSet,
      (1 / 2 : Real) < rho.1.re →
        ∃ g : CompactLogTest,
          ∃ geometry : OrbitG8Geometry rho g,
            ∃ M : Real,
              finitePrimeSum g.convolutionSquare ≤ M ∧
              M ≤ - archimedeanTerm g.convolutionSquare) :
    RHDefinitionBridge.standard.SourceRH := by
  apply sourceRH_of_right_orbitGeometry_primeAbsorption
  intro rho hright
  obtain ⟨g, geometry, M, hprime, harch⟩ := hproducer rho hright
  refine ⟨g, geometry, hprime.trans harch⟩

/-- Signed budget formulation: if the Archimedean term plus positive profile
    credit is absorbed by the negative profile deficit over the visible range,
    SourceRH follows. -/
theorem sourceRH_of_right_orbitGeometry_signedBudget
    (hproducer : ∀ rho : sourceNontrivialZeroSet,
      (1 / 2 : Real) < rho.1.re →
        ∃ g : CompactLogTest,
          ∃ geometry : OrbitG8Geometry rho g,
            archimedeanTerm g.convolutionSquare +
                signedProfileCredit g (orbitVisiblePrimeRange geometry) ≤
              signedProfileDeficit g (orbitVisiblePrimeRange geometry)) :
    RHDefinitionBridge.standard.SourceRH := by
  apply sourceRH_of_right_orbitGeometry_orbitWindowSemiLocalGate
  intro rho hright
  obtain ⟨g, geometry, hbudget⟩ := hproducer rho hright
  refine ⟨g, geometry, ?_⟩
  exact (orbitWindowSemiLocalGate_iff_signedBudget geometry).mpr hbudget

/-- Norm absorption: if the absolute value of the finite prime sum is
    bounded by the negative Archimedean margin, SourceRH follows. -/
theorem sourceRH_of_right_orbitGeometry_primeAbsorb_norm
    (hproducer : ∀ rho : sourceNontrivialZeroSet,
      (1 / 2 : Real) < rho.1.re →
        ∃ g : CompactLogTest,
          ∃ geometry : OrbitG8Geometry rho g,
            |finitePrimeSum g.convolutionSquare| ≤
              - archimedeanTerm g.convolutionSquare) :
    RHDefinitionBridge.standard.SourceRH := by
  apply sourceRH_of_right_orbitGeometry_primeAbsorption
  intro rho hright
  obtain ⟨g, geometry, habs⟩ := hproducer rho hright
  refine ⟨g, geometry, ?_⟩
  have hle := le_abs_self (finitePrimeSum g.convolutionSquare)
  exact hle.trans habs

/-- Range majorant: if the sum of absolute values of the finite range profile
    terms is absorbed by the negative Archimedean margin, SourceRH follows. -/
theorem sourceRH_of_right_orbitGeometry_primeRange_majorant
    (hproducer : ∀ rho : sourceNontrivialZeroSet,
      (1 / 2 : Real) < rho.1.re →
        ∃ g : CompactLogTest,
          ∃ geometry : OrbitG8Geometry rho g,
            (∑ n ∈ Finset.range
                (Nat.ceil (Real.exp (2 * ((geometry.orbitIndex + 2 : Nat) : Real))) + 1),
                ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real)) *
                  |(bilateralProfile g.convolutionSquare (Real.log n)).re|) ≤
              - archimedeanTerm g.convolutionSquare) :
    RHDefinitionBridge.standard.SourceRH := by
  apply sourceRH_of_right_orbitGeometry_primeAbsorption
  intro rho hright
  obtain ⟨g, geometry, hbound⟩ := hproducer rho hright
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
    have hcoeff_nonneg : 0 ≤ ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real)) :=
      mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
    exact mul_le_mul_of_nonneg_left (le_abs_self _) hcoeff_nonneg
  exact hsum_le.trans hbound

end
end C1P2DirectSemiLocalGate
end Source
end ConnesWeilRH
