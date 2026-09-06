import ConnesWeilRH.Dev.C1P2BilateralProfile
import ConnesWeilRH.Dev.C1HealthyYoshidaSpectralNegativity
import ConnesWeilRH.Dev.C1PositiveTraceLimitBridge

/-!
# P2 bilateral-profile same-detector exit

This leaf packages the direct profile-sign consumer with the healthy B5
contradiction.  The producer still has to construct the fields for the pinned
orbit detector; this file only fixes the owner and quantifier of that
obligation.
-/

namespace ConnesWeilRH
namespace Source
namespace C1P2BilateralProfileExit

open C1HealthyYoshidaDetector
open C1HealthyYoshidaSpectralNegativity
open C1LocalConfigurationDomination
open C1P2BilateralProfile
open C1PositiveTraceLimitBridge
open C1SameOwnerWeil
open CC20YoshidaNearZeros
open CCM25Concrete.CompactLogConvolution

noncomputable section

structure P2BilateralProfileSignWitness (g : CompactLogTest) where
  harch : archimedeanTerm g.convolutionSquare ≤ 0
  hprofile : ∀ n ∈ globalPrimeIndexSet g.convolutionSquare,
    (bilateralProfile g.convolutionSquare (Real.log n)).re ≤ 0

/-- Aggregate profile witness: the pointwise prime signs are compressed into
the exact finite weighted sum seen by `qw`. -/
structure P2BilateralProfileAggregateWitness (g : CompactLogTest) where
  hbalance :
    archimedeanTerm g.convolutionSquare +
      ∑ n ∈ globalPrimeIndexSet g.convolutionSquare,
        ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : ℝ)) *
            (bilateralProfile g.convolutionSquare (Real.log n)).re ≤ 0

/-- The earlier pointwise witness is a special case of the aggregate target. -/
theorem P2BilateralProfileSignWitness.toAggregate
    (g : CompactLogTest) (p : P2BilateralProfileSignWitness g) :
    P2BilateralProfileAggregateWitness g where
  hbalance := by
    have hprime := finitePrimeSum_nonpos_of_bilateralProfile_re_nonpos
      g.convolutionSquare p.hprofile
    have hread := finitePrimeSum_eq_bilateralProfile_weighted_sum
      g.convolutionSquare
    rw [← hread]
    exact add_nonpos p.harch hprime

/-- The orbit-window gate and the aggregate profile witness are the same
inequality, with the finite-prime sum expressed in its exact profile form. -/
theorem P2BilateralProfileAggregateWitness.of_orbitWindowSemiLocalGate
    (g : CompactLogTest)
    (hgate : C1OrbitWindowSemiLocalGate.orbitWindowSemiLocalGate g) :
    P2BilateralProfileAggregateWitness g where
  hbalance := by
    have hgate' := (orbitWindowSemiLocalGate_iff g).mp hgate
    unfold ICgate at hgate'
    rw [finitePrimeSum_eq_bilateralProfile_weighted_sum] at hgate'
    exact hgate'

/-- A producer may use the real Hermitian evaluations directly instead of
mentioning `bilateralProfile`; this is definitionally the same aggregate
socket after the convolution-square identity. -/
theorem P2BilateralProfileAggregateWitness.of_twoRealWeightedSum
    (g : CompactLogTest)
    (hbalance :
      archimedeanTerm g.convolutionSquare +
        ∑ n ∈ globalPrimeIndexSet g.convolutionSquare,
          ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : ℝ)) *
            (2 * (g.convolutionSquare.test (Real.log n)).re) ≤ 0) :
    P2BilateralProfileAggregateWitness g where
  hbalance := by
    have hprofile :
        (∑ n ∈ globalPrimeIndexSet g.convolutionSquare,
          ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : ℝ)) *
            (bilateralProfile g.convolutionSquare (Real.log n)).re) =
          ∑ n ∈ globalPrimeIndexSet g.convolutionSquare,
            ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : ℝ)) *
              (2 * (g.convolutionSquare.test (Real.log n)).re) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [bilateralProfile_convolutionSquare_re_eq_two_re]
    rw [hprofile]
    exact hbalance

/-- A genuine positive-trace limit family on the same owner is another
producer route: its order-theoretic readback gives `qw ≥ 0`, which the exact
aggregate equivalence then re-expresses as the P2 witness. -/
theorem P2BilateralProfileAggregateWitness.of_positiveTracePairLimitFamily
    {ι H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {basis : HilbertBasis ι ℂ H} (g : CompactLogTest)
    (hvanishes : CC20VanishesOn C1.healthyCC20TestSpace
      cc20TripleFiniteVanishingSet g)
    (data : PositiveTracePairLimitFamily (G := G) basis g) :
    P2BilateralProfileAggregateWitness g where
  hbalance :=
    (qw_nonneg_iff_archimedean_plus_bilateralProfile_weighted_sum_nonpos
      g hvanishes).mp (qw_nonnegative_of_positiveTracePairLimitFamily data)

theorem qw_nonneg_of_p2BilateralProfileSignWitness
    (g : CompactLogTest)
    (hvanishes : CC20VanishesOn C1.healthyCC20TestSpace
      cc20TripleFiniteVanishingSet g)
    (p : P2BilateralProfileSignWitness g) :
    0 ≤ qw g := by
  exact qw_nonneg_of_archimedean_nonpos_and_visible_bilateralProfile_nonpos
    g hvanishes p.harch p.hprofile

theorem qw_nonneg_of_p2BilateralProfileAggregateWitness
    (g : CompactLogTest)
    (hvanishes : CC20VanishesOn C1.healthyCC20TestSpace
      cc20TripleFiniteVanishingSet g)
    (p : P2BilateralProfileAggregateWitness g) :
    0 ≤ qw g := by
  exact qw_nonneg_of_archimedean_plus_bilateralProfile_weighted_sum_nonpos
    g hvanishes p.hbalance

theorem sourceRH_of_healthyDetector_p2BilateralProfileSignWitness
    (hproducer : ∀ rho : sourceNontrivialZeroSet,
      (1 / 2 : Real) < rho.1.re →
        ∃ g : CompactLogTest,
          HealthyYoshidaDetectorData rho.1 g ∧
            Nonempty (P2BilateralProfileSignWitness g)) :
    RHDefinitionBridge.standard.SourceRH := by
  apply healthy_sourceRH_of_right_detector_specific_qw_nonneg
  intro rho hright
  obtain ⟨g, hdata, ⟨hp2⟩⟩ := hproducer rho hright
  exact ⟨g, hdata,
      qw_nonneg_of_p2BilateralProfileSignWitness g hdata.vanishesOnF hp2⟩

/-- Same-owner B5 exit for the aggregate profile target. -/
theorem sourceRH_of_healthyDetector_p2BilateralProfileAggregateWitness
    (hproducer : ∀ rho : sourceNontrivialZeroSet,
      (1 / 2 : Real) < rho.1.re →
        ∃ g : CompactLogTest,
          HealthyYoshidaDetectorData rho.1 g ∧
            Nonempty (P2BilateralProfileAggregateWitness g)) :
    RHDefinitionBridge.standard.SourceRH := by
  apply healthy_sourceRH_of_right_detector_specific_qw_nonneg
  intro rho hright
  obtain ⟨g, hdata, ⟨hp2⟩⟩ := hproducer rho hright
  exact ⟨g, hdata,
    qw_nonneg_of_p2BilateralProfileAggregateWitness g hdata.vanishesOnF hp2⟩

end
end C1P2BilateralProfileExit
end Source
end ConnesWeilRH
