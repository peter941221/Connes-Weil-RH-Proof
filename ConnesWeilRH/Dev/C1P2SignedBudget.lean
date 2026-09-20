import ConnesWeilRH.Dev.C1G8R0OrbitGeometry
import ConnesWeilRH.Dev.C1OrbitFiniteSignBudget
import ConnesWeilRH.Dev.C1P2BilateralProfileExit

/-!
# P2 signed compensation budget

This leaf names the remaining producer obligation after the pointwise-profile
shortcut has been ruled out.  It is an exact positive-credit minus
negative-deficit decomposition of the same finite visible-prime aggregate;
it does not add a sign assumption or change the owner.
-/

namespace ConnesWeilRH
namespace Source
namespace C1P2SignedBudget

open C1G8R0OrbitGeometry
open C1OrbitFiniteSignBudget
open C1OrbitWindowSemiLocalGate
open C1P2BilateralProfile
open C1P2BilateralProfileExit
open C1SameOwnerWeil
open C1HealthyYoshidaDetector
open C1HealthyYoshidaSpectralNegativity
open CC20YoshidaNearZeros
open CCM25Concrete.CompactLogConvolution
open scoped BigOperators

noncomputable section

def signedProfileTerm (g : CompactLogTest) (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : ℝ)) *
    (bilateralProfile g.convolutionSquare (Real.log n)).re

def signedProfileCredit (g : CompactLogTest) (S : Finset ℕ) : ℝ :=
  ∑ n ∈ S, max 0 (signedProfileTerm g n)

def signedProfileDeficit (g : CompactLogTest) (S : Finset ℕ) : ℝ :=
  ∑ n ∈ S, max 0 (-signedProfileTerm g n)

def orbitVisiblePrimeRange {rho : sourceNontrivialZeroSet}
    {g : CompactLogTest} (geometry : OrbitG8Geometry rho g) : Finset ℕ :=
  Finset.range
    (Nat.ceil (Real.exp
      (2 * ((geometry.orbitIndex + 2 : Nat) : Real))) + 1)

theorem sum_signedProfileTerm_eq_credit_sub_deficit
    (g : CompactLogTest) (S : Finset ℕ) :
    (∑ n ∈ S, signedProfileTerm g n) =
      signedProfileCredit g S - signedProfileDeficit g S := by
  unfold signedProfileCredit signedProfileDeficit
  calc
    (∑ n ∈ S, signedProfileTerm g n) =
      ∑ n ∈ S,
          (max 0 (signedProfileTerm g n) -
            max 0 (-signedProfileTerm g n)) := by
      apply Finset.sum_congr rfl
      intro n hn
      by_cases h : 0 ≤ signedProfileTerm g n
      · rw [max_eq_right h, max_eq_left (neg_nonpos.mpr h)]
        ring
      · have hn : signedProfileTerm g n ≤ 0 := le_of_not_ge h
        rw [max_eq_left hn, max_eq_right (neg_nonneg.mpr hn)]
        ring
    _ = (∑ n ∈ S, max 0 (signedProfileTerm g n)) -
        ∑ n ∈ S, max 0 (-signedProfileTerm g n) := by
      rw [Finset.sum_sub_distrib]

theorem orbitWindowSemiLocalGate_iff_signedBudget
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) :
    orbitWindowSemiLocalGate g ↔
      archimedeanTerm g.convolutionSquare +
          signedProfileCredit g
            (Finset.range
              (Nat.ceil (Real.exp (2 * ((geometry.orbitIndex + 2 : Nat) : Real))) + 1)) ≤
        signedProfileDeficit g
          (Finset.range
            (Nat.ceil (Real.exp (2 * ((geometry.orbitIndex + 2 : Nat) : Real))) + 1)) := by
  rw [orbitWindowSemiLocalGate_iff_finiteRangeBilateralProfile geometry]
  have hsum := sum_signedProfileTerm_eq_credit_sub_deficit g
    (Finset.range
      (Nat.ceil (Real.exp (2 * ((geometry.orbitIndex + 2 : Nat) : Real))) + 1))
  have hterm :
      (∑ n ∈ Finset.range
          (Nat.ceil (Real.exp (2 * ((geometry.orbitIndex + 2 : Nat) : Real))) + 1),
          ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : ℝ)) *
            (bilateralProfile g.convolutionSquare (Real.log n)).re) =
        ∑ n ∈ Finset.range
          (Nat.ceil (Real.exp (2 * ((geometry.orbitIndex + 2 : Nat) : Real))) + 1),
          signedProfileTerm g n := by
    rfl
  constructor <;> intro h <;> linarith [hsum, hterm]

/- The exact remaining B5 producer contract now feeds the existing SourceRH
   consumer.  All data stay on the same selected orbit owner; no universal
   positivity or normalized carrier is introduced. -/
theorem sourceRH_of_right_orbitGeometry_signedBudget
    (hproducer : ∀ rho : sourceNontrivialZeroSet,
      (1 / 2 : Real) < rho.1.re →
        ∃ g : CompactLogTest,
          ∃ geometry : OrbitG8Geometry rho g,
            HealthyYoshidaDetectorData rho.1 g ∧
            archimedeanTerm g.convolutionSquare +
                signedProfileCredit g (orbitVisiblePrimeRange geometry) ≤
              signedProfileDeficit g (orbitVisiblePrimeRange geometry)) :
    RHDefinitionBridge.standard.SourceRH := by
  apply healthy_sourceRH_of_right_detector_specific_qw_nonneg
  intro rho hright
  obtain ⟨g, geometry, hdata, hbudget⟩ := hproducer rho hright
  have hgate : orbitWindowSemiLocalGate g := by
    apply (orbitWindowSemiLocalGate_iff_signedBudget geometry).mpr
    simpa [orbitVisiblePrimeRange] using hbudget
  have haggregate : P2BilateralProfileAggregateWitness g :=
    P2BilateralProfileAggregateWitness.of_orbitWindowSemiLocalGate g hgate
  exact ⟨g, hdata,
    qw_nonneg_of_archimedean_plus_bilateralProfile_weighted_sum_nonpos
      g hdata.vanishesOnF haggregate.hbalance⟩

end
end C1P2SignedBudget
end Source
end ConnesWeilRH
