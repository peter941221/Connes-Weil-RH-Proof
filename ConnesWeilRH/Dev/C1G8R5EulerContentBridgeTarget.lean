/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R5AggregateExpansion
import ConnesWeilRH.Dev.C1G8P1CanonicalFamily
import ConnesWeilRH.Dev.C1CrossingEulerLogReadback
import ConnesWeilRH.Dev.C1SameOwnerWeil

/-!
# The rho5 Euler-content bridge as one pinned theorem

This leaf implements the pre-registered item 6 of record 1503 section 6:
the rho5 identification is stated ONCE as a named proposition, its left side
is pinned to the four compiled channels of the G8 endpoint aggregate, its
right side is pinned to the committed three-component split of `psi` on the
half-density square, and the arithmetic row is transported at the canonical
exact-support family so that it literally reads the prime component of `qw`
on the same owner and the same visible prime-power set.

Everything here is statement pinning and definition transport.  No tail
estimate, positivity, sign input, or RH conclusion is present or implied.
The gate opened by this leaf is exactly the object-level bridge of record
1507: the aggregate equality remains unproved.
-/

namespace ConnesWeilRH
namespace Dev

open Source.CC20Concrete
open Source.CC20Concrete.PositiveTrace
open Source.CCM25Concrete
open Source.CCM25Concrete.SelectedWeilSquare
open Source.CCM25Concrete.CCM24FiniteSProjectionTrace
open Source.CCM25Concrete.CCM24FiniteSProjectionTrace.FinitePrimePowerFamily
open Source.CCM25Concrete.CCM24FiniteSGramResponse
open Source.CCM25Concrete.CCM24FiniteSCoframeResponse
open Source.CCM25Concrete.CCM24FiniteSBandTrace
open Source.CCM25Concrete.CCM24FiniteSParameterizedEulerProduct
open Source.CCM25Concrete.CCM24FiniteSGatePhysicalObliqueShearReduction
open Source.CCM25Concrete.SelectedCrossingOperatorBridge
open Source.C1G8AdjointShearGram
open Source.C1CrossingEulerLogReadback
open Source.C1G8P1CanonicalFamily
open scoped BigOperators InnerProduct InnerProductSpace Topology

noncomputable section

noncomputable local instance g8R5TargetSourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- **The rho5 gate as one named proposition.**  The compiled G8 endpoint
aggregate, traced along the named source basis and read through the real
part, equals the quadratic Weil value of the same owner.  Naming the target
here is an obligation marker; it stores no equality proof. -/
def g8R5EulerContentBridge
    (owner : SelectedWeilSquareOwner) (lambda : CCM24SoninScale)
    (family : FinitePrimePowerFamily)
    {ρ : Type*}
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) : Prop :=
  (ordinaryTraceAlong sourceBasis
      (g8EndpointSourceCutoffLimitOperator owner lambda family)).re
    = Source.C1SameOwnerWeil.qw owner.sourceTest

/-- Right-hand pinning: the committed expansion `qw g = psi g.square` and
`psi F = poleTerm F - archimedeanTerm F - finitePrimeSum F` are the only
content of this equivalence.  The signs are transcribed from the committed
`psi_eq_components`; no sign premise enters anywhere. -/
theorem g8R5EulerContentBridge_iff_psiComponents
    (owner : SelectedWeilSquareOwner) (lambda : CCM24SoninScale)
    (family : FinitePrimePowerFamily)
    {ρ : Type*}
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) :
    g8R5EulerContentBridge owner lambda family sourceBasis ↔
      (ordinaryTraceAlong sourceBasis
          (g8EndpointSourceCutoffLimitOperator owner lambda family)).re =
        Source.C1SameOwnerWeil.poleTerm owner.sourceTest.convolutionSquare -
          Source.C1SameOwnerWeil.archimedeanTerm
            owner.sourceTest.convolutionSquare -
          Source.C1SameOwnerWeil.finitePrimeSum
            owner.sourceTest.convolutionSquare := by
  rw [g8R5EulerContentBridge, Source.C1SameOwnerWeil.qw_eq_psi_square,
    Source.C1SameOwnerWeil.psi_eq_components]

/-- Left-hand pinning: the aggregate operator is the base detector channel,
the two adjoint shear cross channels, and the leakage square, exactly as the
four-term expansion of record 1511/1563 compiles it.  The rho5 gate is hence
stated on the channels whose limits `rho2`-`rho4` already supply. -/
theorem g8R5EulerContentBridge_iff_fourChannels
    (owner : SelectedWeilSquareOwner) (lambda : CCM24SoninScale)
    (family : FinitePrimePowerFamily)
    {ρ : Type*}
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) :
    g8R5EulerContentBridge owner lambda family sourceBasis ↔
      (ordinaryTraceAlong sourceBasis
          ((sourceInclusion lambda)† ∘L (rootConvolution owner)† ∘L
              detectorOperator owner ∘L rootConvolution owner ∘L
                sourceInclusion lambda +
            (sourceInclusion lambda)† ∘L (rootConvolution owner)† ∘L
              finiteEulerPulledObliqueShear lambda family ∘L
                detectorOperator owner ∘L rootConvolution owner ∘L
                  sourceInclusion lambda +
            (sourceInclusion lambda)† ∘L (rootConvolution owner)† ∘L
              detectorOperator owner ∘L
                (finiteEulerPulledObliqueShear lambda family)† ∘L
                  rootConvolution owner ∘L sourceInclusion lambda +
            (sourceInclusion lambda)† ∘L (rootConvolution owner)† ∘L
              finiteEulerPulledObliqueShear lambda family ∘L
                detectorOperator owner ∘L
                  (finiteEulerPulledObliqueShear lambda family)† ∘L
                    rootConvolution owner ∘L sourceInclusion lambda)).re =
        Source.C1SameOwnerWeil.qw owner.sourceTest := by
  rw [g8R5EulerContentBridge, g8EndpointSourceCutoffLimitOperator_eq_fourTerms]

/-- **Same detector, same prime set.**  At the canonical exact-support family
the finite arithmetic row of the G8 ledger reads exactly the prime component
of the owner's own Weil functional on the half-density square.  The proof is
pure transport through committed definitions: the family terms identify with
the canonical prime-power terms, those telescope to the computed index set of
the owner, and `finitePrimeSum` on the square unfolds to the same index set
and the same summands via `finitePrimeSum_square_eq_selected`.  No estimate
and no trace-convergence statement is used. -/
theorem g8R5CanonicalArithmeticRow_eq_finitePrimeSum
    (owner : SelectedWeilSquareOwner) :
    (∑ pm ∈ (g8CanonicalFamily owner).terms,
        owner.finitePrimeTerm (pm.1 ^ pm.2)).re =
      Source.C1SameOwnerWeil.finitePrimeSum owner.sourceTest.convolutionSquare := by
  have hterms : (g8CanonicalFamily owner).terms = canonicalPrimePowerTerms owner := by
    ext pm
    simp [g8CanonicalFamily, FinitePrimePowerFamily.ofSelectedOwner,
      FinitePrimePowerFamily.ofSelectedExactSupport, canonicalTerm,
      canonicalPrimePowerTerms, canonicalPrimePowerTerm]
  rw [hterms, canonicalPrimePowerTerms_sum_eq_selectedFinitePrimeTerm_sum]
  rw [Source.C1SameOwnerWeil.finitePrimeSum_square_eq_selected owner.sourceTest]
  have hsource : (SelectedWeilSquareOwner.ofCompactLogTest
      owner.sourceTest).sourceTest = owner.sourceTest := by
    rfl
  have hterm (n : ℕ) : owner.finitePrimeTerm n =
      (SelectedWeilSquareOwner.ofCompactLogTest owner.sourceTest).finitePrimeTerm n := by
    simp [SelectedWeilSquareOwner.finitePrimeTerm,
      SelectedWeilSquareOwner.primePowerValue, hsource]
  have hset :
      (SelectedFinitePrimeSupportData.ofOwner owner).globalPrimeIndexSet =
        (SelectedFinitePrimeSupportData.ofOwner
          (SelectedWeilSquareOwner.ofCompactLogTest
            owner.sourceTest)).globalPrimeIndexSet := by
    apply Finset.ext
    intro n
    rw [(SelectedFinitePrimeSupportData.ofOwner owner).globalExact n,
      (SelectedFinitePrimeSupportData.ofOwner
        (SelectedWeilSquareOwner.ofCompactLogTest
          owner.sourceTest)).globalExact n]
    rw [hterm n]
  have hsum :
      ∑ n ∈ (SelectedFinitePrimeSupportData.ofOwner owner).globalPrimeIndexSet,
          owner.finitePrimeTerm n =
        ∑ n ∈ (SelectedFinitePrimeSupportData.ofOwner
            (SelectedWeilSquareOwner.ofCompactLogTest
              owner.sourceTest)).globalPrimeIndexSet,
          (SelectedWeilSquareOwner.ofCompactLogTest
            owner.sourceTest).finitePrimeTerm n := by
    rw [hset]
    exact Finset.sum_congr rfl fun n _ => hterm n
  rw [hsum]
  simp [SelectedWeilSquareOwner.finitePrimeTermReal]

/-- The transported arithmetic supplier row: under exactly the hypotheses of
record 1564's supplier, the ordinary trace of the canonical-family arithmetic
operator re-reads the prime component of `qw` on the half-density square.
Combined with the prefix ledger of record 1563 this is the finite-level
Euler-content row of the rho5 bridge, with both sides pinned. -/
theorem ordinaryTraceAlong_g8CanonicalArithmeticOperator_eq_finitePrimeSum
    (owner : SelectedWeilSquareOwner)
    (a c : ℝ)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (basisData : ∀ pm : {pm // pm ∈ (g8CanonicalFamily owner).terms},
      GlobalPrimePowerTraceBasisData a c pm.1.1 pm.1.2) :
    (ordinaryTraceAlong globalBasis
        (arithmeticOperator owner (g8CanonicalFamily owner))).re =
      Source.C1SameOwnerWeil.finitePrimeSum owner.sourceTest.convolutionSquare := by
  have h := ordinaryTraceAlong_g8ArithmeticOperator_eq_finitePrimeTerm_sum
    owner (g8CanonicalFamily owner) a c hsupp globalBasis basisData
  exact (congrArg Complex.re h).trans
    (g8R5CanonicalArithmeticRow_eq_finitePrimeSum owner)

end
end Dev
end ConnesWeilRH
