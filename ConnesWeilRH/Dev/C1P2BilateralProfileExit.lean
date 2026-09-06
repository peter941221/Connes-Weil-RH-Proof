import ConnesWeilRH.Dev.C1P2BilateralProfile
import ConnesWeilRH.Dev.C1BombieriP2Bridge
import ConnesWeilRH.Dev.C1HealthyYoshidaSpectralNegativity
import ConnesWeilRH.Dev.C1PositiveTraceLimitBridge
import ConnesWeilRH.Dev.C1Stage3ProjectionOperatorFamily

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
open C1BombieriP2Bridge
open C1LocalConfigurationDomination
open C1P2BilateralProfile
open C1PositiveTraceLimitBridge
open Dev.C1Stage3ProjectionOperatorFamily
open C1SameOwnerWeil
open CC20Concrete
open CC20Concrete.PositiveTrace
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

/-- Range form of the P2 producer contract.  The cutoff is supplied
separately by the detector's support certificate. -/
structure P2BilateralProfileRangeWitness (g : CompactLogTest) (B : ℝ) where
  hbalance :
    archimedeanTerm g.convolutionSquare +
      ∑ n ∈ Finset.range (Nat.ceil (Real.exp B) + 1),
        ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : ℝ)) *
          (2 * (g.convolutionSquare.test (Real.log n)).re) ≤ 0

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

/-- Exact socket equivalence: the aggregate witness is precisely the existing
orbit-window gate, with only the finite-prime expression changed by readback. -/
theorem p2AggregateWitness_iff_orbitWindowSemiLocalGate
    (g : CompactLogTest) :
    P2BilateralProfileAggregateWitness g ↔
      C1OrbitWindowSemiLocalGate.orbitWindowSemiLocalGate g := by
  constructor
  · intro p
    unfold C1OrbitWindowSemiLocalGate.orbitWindowSemiLocalGate
    rw [finitePrimeSum_eq_bilateralProfile_weighted_sum]
    exact p.hbalance
  · exact P2BilateralProfileAggregateWitness.of_orbitWindowSemiLocalGate g

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

/-- A support certificate turns the explicit range producer into the exact
aggregate owner without changing the finite visible-prime set. -/
theorem P2BilateralProfileRangeWitness.toAggregate
    (g : CompactLogTest) {B : ℝ}
    (hsupport : Function.support g.convolutionSquare.test ⊆
      Set.Ioo (-B) B) (p : P2BilateralProfileRangeWitness g B) :
    P2BilateralProfileAggregateWitness g where
  hbalance := by
    have hread := finitePrimeSum_eq_bilateralProfile_weighted_sum
      g.convolutionSquare
    have hrange :=
      finitePrimeSum_convolutionSquare_eq_two_re_weighted_sum_range_of_support
        g hsupport
    have hprofile :
        (∑ n ∈ globalPrimeIndexSet g.convolutionSquare,
          ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : ℝ)) *
            (bilateralProfile g.convolutionSquare (Real.log n)).re) =
          ∑ n ∈ Finset.range (Nat.ceil (Real.exp B) + 1),
            ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : ℝ)) *
              (2 * (g.convolutionSquare.test (Real.log n)).re) := by
      rw [← hread, hrange]
    rw [hprofile]
    exact p.hbalance

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

/-- The finite Bombieri Line-B chain is another producer socket once its
same-owner `qw_eq_mass` bridge is supplied. -/
theorem P2BilateralProfileAggregateWitness.of_bombieriP2BridgeData
    (g : CompactLogTest)
    (hvanishes : CC20VanishesOn C1.healthyCC20TestSpace
      cc20TripleFiniteVanishingSet g)
    (p : BombieriP2BridgeData g) :
    P2BilateralProfileAggregateWitness g where
  hbalance :=
    (qw_nonneg_iff_archimedean_plus_bilateralProfile_weighted_sum_nonpos
      g hvanishes).mp (qw_nonneg_of_bombieriP2BridgeData p)

/-- The direct finite Hermitian-form producer is another spelling of the same
aggregate owner: its explicit `qw` readback supplies the aggregate inequality.
-/
theorem P2BilateralProfileAggregateWitness.of_bombieriQuadraticP2BridgeData
    (g : CompactLogTest)
    (hvanishes : CC20VanishesOn C1.healthyCC20TestSpace
      cc20TripleFiniteVanishingSet g)
    (p : BombieriQuadraticP2BridgeData g) :
    P2BilateralProfileAggregateWitness g where
  hbalance :=
    (qw_nonneg_iff_archimedean_plus_bilateralProfile_weighted_sum_nonpos
      g hvanishes).mp (qw_nonneg_of_bombieriQuadraticP2BridgeData p)

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

/-- Direct healthy-B5 exit for a Bombieri finite-chain producer. -/
theorem sourceRH_of_healthyDetector_p2BombieriP2BridgeData
    (hproducer : ∀ rho : sourceNontrivialZeroSet,
      (1 / 2 : Real) < rho.1.re →
        ∃ g : CompactLogTest,
          HealthyYoshidaDetectorData rho.1 g ∧
            Nonempty (BombieriP2BridgeData g)) :
    RHDefinitionBridge.standard.SourceRH := by
  apply healthy_sourceRH_of_right_detector_specific_qw_nonneg
  intro rho hright
  obtain ⟨g, hdata, ⟨hbridge⟩⟩ := hproducer rho hright
  have haggregate : P2BilateralProfileAggregateWitness g :=
    P2BilateralProfileAggregateWitness.of_bombieriP2BridgeData
      g hdata.vanishesOnF hbridge
  exact ⟨g, hdata,
    qw_nonneg_of_p2BilateralProfileAggregateWitness g hdata.vanishesOnF
      haggregate⟩

/-- Direct healthy-B5 exit for the finite Hermitian-form producer contract. -/
theorem sourceRH_of_healthyDetector_p2BombieriQuadraticP2BridgeData
    (hproducer : ∀ rho : sourceNontrivialZeroSet,
      (1 / 2 : Real) < rho.1.re →
        ∃ g : CompactLogTest,
          HealthyYoshidaDetectorData rho.1 g ∧
            Nonempty (BombieriQuadraticP2BridgeData g)) :
    RHDefinitionBridge.standard.SourceRH := by
  apply healthy_sourceRH_of_right_detector_specific_qw_nonneg
  intro rho hright
  obtain ⟨g, hdata, ⟨hp2⟩⟩ := hproducer rho hright
  have haggregate : P2BilateralProfileAggregateWitness g :=
    P2BilateralProfileAggregateWitness.of_bombieriQuadraticP2BridgeData
      g hdata.vanishesOnF hp2
  exact ⟨g, hdata,
    qw_nonneg_of_p2BilateralProfileAggregateWitness g hdata.vanishesOnF
      haggregate⟩

/-- Direct healthy-B5 exit for a fixed-basis self-pair trace producer. -/
theorem sourceRH_of_healthyDetector_p2PositiveTracePairLimitFamily
    {ι H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (basis : HilbertBasis ι ℂ H)
    (hproducer : ∀ rho : sourceNontrivialZeroSet,
      (1 / 2 : Real) < rho.1.re →
        ∃ g : CompactLogTest,
          HealthyYoshidaDetectorData rho.1 g ∧
            Nonempty (PositiveTracePairLimitFamily (G := G) basis g)) :
    RHDefinitionBridge.standard.SourceRH := by
  apply healthy_sourceRH_of_right_detector_specific_qw_nonneg
  intro rho hright
  obtain ⟨g, hdata, ⟨htrace⟩⟩ := hproducer rho hright
  have haggregate : P2BilateralProfileAggregateWitness g :=
    P2BilateralProfileAggregateWitness.of_positiveTracePairLimitFamily
      g hdata.vanishesOnF htrace
  exact ⟨g, hdata,
    (qw_nonneg_iff_archimedean_plus_bilateralProfile_weighted_sum_nonpos
      g hdata.vanishesOnF).mpr haggregate.hbalance⟩

/-- Pinned B5 exit for the explicit-range producer contract.  The detector's
exported source support supplies the square support needed by the adapter. -/
theorem sourceRH_of_pinnedOrbitDetector_p2BilateralProfileRangeWitness
    (hproducer : ∀ rho : sourceNontrivialZeroSet,
      (1 / 2 : Real) < rho.1.re →
        ∃ g : CompactLogTest, ∃ n : Nat,
          HealthyYoshidaDetectorData rho.1 g ∧
          Function.support g.test ⊆
            Set.Ioo (-((n + 2 : Nat) : Real)) (((n + 2 : Nat) : Real)) ∧
          Nonempty
            (P2BilateralProfileRangeWitness g
              (2 * ((n + 2 : Nat) : Real)))) :
    RHDefinitionBridge.standard.SourceRH := by
  apply healthy_sourceRH_of_right_detector_specific_qw_nonneg
  intro rho hright
  obtain ⟨g, n, hdata, hsupport, ⟨hp2⟩⟩ := hproducer rho hright
  have hsquare : Function.support g.convolutionSquare.test ⊆
      Set.Ioo (-(2 * ((n + 2 : Nat) : Real)))
        (2 * ((n + 2 : Nat) : Real)) := by
    exact CompactLogTest.convolutionSquare_support_subset_two_mul_Ioo g
      (hsupport.trans Set.Ioo_subset_Icc_self)
  have haggregate : P2BilateralProfileAggregateWitness g :=
    P2BilateralProfileRangeWitness.toAggregate g hsquare hp2
  exact ⟨g, hdata,
    qw_nonneg_of_p2BilateralProfileAggregateWitness g hdata.vanishesOnF
      haggregate⟩

/-- A positive trace-class operator family on the same owner is an alternate
producer route: its order-theoretic readback gives `qw ≥ 0`, which the exact
aggregate equivalence re-expresses as the P2 witness. -/
theorem P2BilateralProfileAggregateWitness.of_positiveTraceOperatorLimitFamily
    {ι H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {basis : HilbertBasis ι ℂ H} (g : CompactLogTest)
    (hvanishes : CC20VanishesOn C1.healthyCC20TestSpace
      cc20TripleFiniteVanishingSet g)
    (data : PositiveTraceOperatorLimitFamily basis g) :
    P2BilateralProfileAggregateWitness g where
  hbalance :=
    (qw_nonneg_iff_archimedean_plus_bilateralProfile_weighted_sum_nonpos
      g hvanishes).mp (qw_nonnegative_of_positiveTraceOperatorLimitFamily data)

/-- The viable windowed projection-cutoff route supplies the same P2 socket;
its remainder convergence and owner readback stay explicit in `contracts`. -/
theorem P2BilateralProfileAggregateWitness.of_projectionCutoffLimitContracts
    {ν : Type*}
    (g : CompactLogTest) (lambda : CCM24SoninScale)
    (S : List CCM24VisiblePrime)
    (globalBasis : HilbertBasis ν ℂ projectionCarrier)
    (hvanishes : CC20VanishesOn C1.healthyCC20TestSpace
      cc20TripleFiniteVanishingSet g)
    (contracts : ProjectionCutoffLimitContracts g lambda S globalBasis) :
    P2BilateralProfileAggregateWitness g where
  hbalance :=
    (qw_nonneg_iff_archimedean_plus_bilateralProfile_weighted_sum_nonpos
      g hvanishes).mp
      (qw_nonnegative_of_projectionCutoffLimitContracts
        g lambda S globalBasis contracts)

/-- Direct healthy-B5 exit for a fixed-basis positive-operator producer. -/
theorem sourceRH_of_healthyDetector_p2PositiveTraceOperatorLimitFamily
    {ι H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (basis : HilbertBasis ι ℂ H)
    (hproducer : ∀ rho : sourceNontrivialZeroSet,
      (1 / 2 : Real) < rho.1.re →
        ∃ g : CompactLogTest,
          HealthyYoshidaDetectorData rho.1 g ∧
            Nonempty (PositiveTraceOperatorLimitFamily basis g)) :
    RHDefinitionBridge.standard.SourceRH := by
  apply healthy_sourceRH_of_right_detector_specific_qw_nonneg
  intro rho hright
  obtain ⟨g, hdata, ⟨htrace⟩⟩ := hproducer rho hright
  have haggregate : P2BilateralProfileAggregateWitness g :=
    P2BilateralProfileAggregateWitness.of_positiveTraceOperatorLimitFamily
      g hdata.vanishesOnF htrace
  exact ⟨g, hdata,
    qw_nonneg_of_p2BilateralProfileAggregateWitness g hdata.vanishesOnF
      haggregate⟩

/-- Direct healthy-B5 exit for the concrete windowed projection owner. -/
theorem sourceRH_of_healthyDetector_p2ProjectionCutoffLimitContracts
    {ν : Type*}
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime)
    (globalBasis : HilbertBasis ν ℂ projectionCarrier)
    (hproducer : ∀ rho : sourceNontrivialZeroSet,
      (1 / 2 : Real) < rho.1.re →
        ∃ g : CompactLogTest,
          HealthyYoshidaDetectorData rho.1 g ∧
            Nonempty (ProjectionCutoffLimitContracts g lambda S globalBasis)) :
    RHDefinitionBridge.standard.SourceRH := by
  apply healthy_sourceRH_of_right_detector_specific_qw_nonneg
  intro rho hright
  obtain ⟨g, hdata, ⟨hcontracts⟩⟩ := hproducer rho hright
  have haggregate : P2BilateralProfileAggregateWitness g :=
    P2BilateralProfileAggregateWitness.of_projectionCutoffLimitContracts
      g lambda S globalBasis hdata.vanishesOnF hcontracts
  exact ⟨g, hdata,
    qw_nonneg_of_p2BilateralProfileAggregateWitness g hdata.vanishesOnF
      haggregate⟩

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
