import ConnesWeilRH.Dev.C1CenterTwoCriterionBridge
import ConnesWeilRH.Source.CC20Concrete.PositiveTrace

/-!
# C1PositiveTraceLimitBridge - remainder-aware positivity consumer

This module isolates the order-theoretic consumer of a genuine positive trace
construction.  The trace is the ordinary trace of `A* A` from
`BasisHilbertSchmidtData`; it is not identified definitionally with the Weil
functional.  A cutoff-dependent real remainder is kept explicit, and the
consumer only uses its convergence to zero together with a same-owner readback
to `C1SameOwnerWeil.qw`.

The analytic construction of the operators, the readback, and the remainder
estimate remain inputs.  In particular, this module does not assert that the
remainder vanishes by definition and does not prove the RH-level sign.
-/

namespace ConnesWeilRH
namespace Source
namespace C1PositiveTraceLimitBridge

open CC20Concrete.PositiveTrace
open CCM25Concrete.CompactLogConvolution
open C1SameOwnerWeil
open C1SpectralWeil
open Filter
open scoped InnerProduct InnerProductSpace Topology

noncomputable section

/- A family is tied to one Hilbert basis, one Hilbert space, and one C1 test.
The remainder is separate from the trace so a future analytic producer cannot
silently change the owner or erase the source correction. -/
structure PositiveTraceLimitFamily
    {ι H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (basis : HilbertBasis ι ℂ H) (g : CompactLogTest) where
  traceData : Nat → BasisHilbertSchmidtData basis
  remainder : Nat → Real
  remainder_tendsto_zero :
    Tendsto remainder atTop (𝓝 (0 : Real))
  readback_tendsto_qw :
    Tendsto
      (fun n =>
        (ordinaryTraceAlong basis
            (traceData n).positiveComposition).re - remainder n)
      atTop (𝓝 (C1SameOwnerWeil.qw g))

/- A generalized version for a Hilbert--Schmidt map `H -> G`.  The existing
   `PositiveTraceLimitFamily` stores an `H -> H` map; the compact boundary
   construction naturally stores `F : H -> G` and its positive product
   `F†F`.  Keeping this adapter separate avoids pretending that the two
   Hilbert spaces are definitionally the same. -/
structure PositiveTracePairLimitFamily
    {ι H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (basis : HilbertBasis ι ℂ H) (g : CompactLogTest) where
  traceData : Nat →
    BasisHilbertSchmidtPairData (G := G) basis
  self_pair : ∀ n, (traceData n).left = (traceData n).right
  remainder : Nat → Real
  remainder_tendsto_zero :
    Tendsto remainder atTop (𝓝 (0 : Real))
  readback_tendsto_qw :
    Tendsto
      (fun n =>
        (ordinaryTraceAlong basis
            (traceData n).traceProduct).re - remainder n)
      atTop (𝓝 (C1SameOwnerWeil.qw g))

theorem positiveTrace_sub_remainder_lower_bound
    {ι H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {basis : HilbertBasis ι ℂ H} {g : CompactLogTest}
    (data : PositiveTraceLimitFamily basis g) (n : Nat) :
    -data.remainder n ≤
      (ordinaryTraceAlong basis
          (data.traceData n).positiveComposition).re - data.remainder n := by
  have htrace :
      0 ≤
        (ordinaryTraceAlong basis
            (data.traceData n).positiveComposition).re :=
    BasisHilbertSchmidtData.ordinaryTrace_positiveComposition_re_nonnegative
      (data.traceData n)
  linarith

theorem positiveTracePair_re_nonnegative_of_self
    {ι H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {basis : HilbertBasis ι ℂ H}
    (data : BasisHilbertSchmidtPairData (G := G) basis)
    (hself : data.left = data.right) :
    0 ≤ (ordinaryTraceAlong basis data.traceProduct).re := by
  rw [ordinaryTraceAlong]
  rw [Complex.re_tsum data.summable_traceProduct_diagonal]
  apply tsum_nonneg
  intro i
  have hdiag :
      (⟪basis i, data.traceProduct (basis i)⟫_ℂ).re =
        ‖data.right (basis i)‖ ^ 2 := by
    rw [data.traceProduct_diagonal i, hself]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) (data.right (basis i))
  rw [hdiag]
  exact sq_nonneg _

theorem positiveTracePair_sub_remainder_lower_bound
    {ι H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {basis : HilbertBasis ι ℂ H} {g : CompactLogTest}
    (data : PositiveTracePairLimitFamily (G := G) basis g) (n : Nat) :
    -data.remainder n ≤
      (ordinaryTraceAlong basis
          (data.traceData n).traceProduct).re - data.remainder n := by
  have htrace :
      0 ≤ (ordinaryTraceAlong basis
          (data.traceData n).traceProduct).re :=
    positiveTracePair_re_nonnegative_of_self
      (data.traceData n) (data.self_pair n)
  linarith

/-- A self-pair `F†F` family has the same order-theoretic consequence as the
original `H -> H` family.  The target space `G` is kept explicit. -/
theorem qw_nonnegative_of_positiveTracePairLimitFamily
    {ι H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {basis : HilbertBasis ι ℂ H} {g : CompactLogTest}
    (data : PositiveTracePairLimitFamily (G := G) basis g) :
    0 ≤ C1SameOwnerWeil.qw g := by
  have hlower :
      Tendsto (fun n => -data.remainder n) atTop (𝓝 (0 : Real)) := by
    simpa using data.remainder_tendsto_zero.neg
  exact le_of_tendsto_of_tendsto' hlower data.readback_tendsto_qw
    (positiveTracePair_sub_remainder_lower_bound data)

theorem spectral_nonnegative_of_positiveTracePairLimitFamily
    {ι H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {basis : HilbertBasis ι ℂ H} {g : CompactLogTest}
    (data : PositiveTracePairLimitFamily (G := G) basis g) :
    0 ≤ C1SpectralWeil.spectralWeilValue g.convolutionSquare := by
  rw [← C1CenterTwoCriterionBridge.qw_eq_spectralWeilValue_centerTwo g]
  exact qw_nonnegative_of_positiveTracePairLimitFamily data

theorem healthyCriterionState_of_positiveTracePairLimitFamily
    {ι H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (basis : HilbertBasis ι ℂ H) (F : Finset CriticalVanishingPoint)
    (hfamily :
      ∀ g : CompactLogTest,
        CC20VanishesOn C1.healthyCC20TestSpace F g →
          PositiveTracePairLimitFamily (G := G) basis g) :
    C1.healthyCriterionState F := by
  apply
    (C1CenterTwoCriterionBridge.healthyCriterionState_iff_all_vanishing_spectral_nonnegative
      F).mpr
  intro g hvanishing
  exact spectral_nonnegative_of_positiveTracePairLimitFamily
    (hfamily g hvanishing)

/-- The positive `A† A` trace and a vanishing cutoff remainder force the
same-owner Weil square to be nonnegative. -/
theorem qw_nonnegative_of_positiveTraceLimitFamily
    {ι H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {basis : HilbertBasis ι ℂ H} {g : CompactLogTest}
    (data : PositiveTraceLimitFamily basis g) :
    0 ≤ C1SameOwnerWeil.qw g := by
  have hlower :
      Tendsto (fun n => -data.remainder n) atTop (𝓝 (0 : Real)) := by
    simpa using data.remainder_tendsto_zero.neg
  exact le_of_tendsto_of_tendsto' hlower data.readback_tendsto_qw
    (positiveTrace_sub_remainder_lower_bound data)

/-- Gate 2 transports the same-owner positive-trace conclusion to the exact
zero-spectral value used by the healthy C1 criterion. -/
theorem spectral_nonnegative_of_positiveTraceLimitFamily
    {ι H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {basis : HilbertBasis ι ℂ H} {g : CompactLogTest}
    (data : PositiveTraceLimitFamily basis g) :
    0 ≤ C1SpectralWeil.spectralWeilValue g.convolutionSquare := by
  rw [← C1CenterTwoCriterionBridge.qw_eq_spectralWeilValue_centerTwo g]
  exact qw_nonnegative_of_positiveTraceLimitFamily data

/-- A family of same-owner trace limits is sufficient for the finite-vanishing
criterion, while the family itself remains the analytic producer obligation. -/
theorem healthyCriterionState_of_positiveTraceLimitFamily
    {ι H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (basis : HilbertBasis ι ℂ H) (F : Finset CriticalVanishingPoint)
    (hfamily :
      ∀ g : CompactLogTest,
        CC20VanishesOn C1.healthyCC20TestSpace F g →
          PositiveTraceLimitFamily basis g) :
    C1.healthyCriterionState F := by
  apply
    (C1CenterTwoCriterionBridge.healthyCriterionState_iff_all_vanishing_spectral_nonnegative
      F).mpr
  intro g hvanishing
  exact spectral_nonnegative_of_positiveTraceLimitFamily
    (hfamily g hvanishing)

end
end C1PositiveTraceLimitBridge
end Source
end ConnesWeilRH
