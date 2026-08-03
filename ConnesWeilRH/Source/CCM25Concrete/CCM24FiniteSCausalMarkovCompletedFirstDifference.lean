/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCausalMarkovTwoSidedFirstDifference
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSActualBandCompletedNumerator

/-!
# Completed one-prime ledger for the actual finite-S band response

The normalized Markov first jet has a linear one-prime coboundary.  The
actual source endpoint is not that first jet alone: it is the difference
between the pulled-back first jet and the completed nonlinear remainder.

This module puts those three objects on one literal source-carrier ledger.
For a prepended visible prime, the endpoint increment is exactly the
Hermitian Markov coboundary minus the matching completed-remainder increment.
Consequently a quadratic Gate 3U gain can only arise in that same completed
subtraction.  It cannot come from a cancellation internal to the Markov
two-sided first jet.

No norm, trace, positivity, or Gate 3U estimate is asserted here.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCausalMarkovCompletedFirstDifference

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSProjectionTrace
open CCM24FiniteSGramResponse
open CCM24FiniteSBandTrace
open CCM24FiniteSActualBandFirstJetTrace
open CCM24FiniteSActualBandSourceRemainder
open CCM24FiniteSActualBandQuadraticCycle
open CCM24FiniteSActualBandCompletedNumerator
open CCM24FiniteSCausalMarkovTwoSidedFirstDifference

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

local notation "AmbientOp" => finiteSCarrier →L[ℂ] finiteSCarrier
local notation "SourceOp" lambda =>
  sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda

/-- The literal-list first jet pulled back to the actual source Sonin
carrier. -/
noncomputable def normalizedListActualBandSoninResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) : SourceOp lambda :=
  (sourceInclusion lambda).adjoint ∘L
    normalizedListActualBandPairedResponse owner lambda S ∘L
      sourceInclusion lambda

/-- The literal-list Markov coboundary on the actual source Sonin carrier.
The full detector, band, and source-Sonin factors remain inside the ambient
middle operator before this pullback. -/
noncomputable def normalizedListActualBandSoninCoboundary
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) : SourceOp lambda :=
  (sourceInclusion lambda).adjoint ∘L
    normalizedListActualBandTwoSidedCoboundary owner lambda p S ∘L
      sourceInclusion lambda

/-- Pulling back preserves the exact one-prime difference of the actual
two-sided Markov first jet. -/
theorem normalizedListActualBandSoninResponse_cons_sub_eq_coboundary
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    normalizedListActualBandSoninResponse owner lambda (p :: S) -
        normalizedListActualBandSoninResponse owner lambda S =
      normalizedListActualBandSoninCoboundary owner lambda p S := by
  apply ContinuousLinearMap.ext
  intro u
  have h := congrArg
    (fun operator : AmbientOp =>
      (sourceInclusion lambda).adjoint
        (operator (sourceInclusion lambda u)))
    (normalizedListActualBandPairedResponse_cons_sub_eq_twoSidedCoboundary
      owner lambda p S)
  simpa only [normalizedListActualBandSoninResponse,
    normalizedListActualBandSoninCoboundary, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.comp_apply, map_sub] using h

/-- The packaged source first jet is the literal-list source response. -/
theorem sourceActualBandFiniteEulerSoninResponse_eq_normalizedList
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceActualBandFiniteEulerSoninResponse owner lambda family =
      normalizedListActualBandSoninResponse owner lambda family.visiblePrimes := by
  unfold sourceActualBandFiniteEulerSoninResponse
    normalizedListActualBandSoninResponse
  rw [sourceActualBandFiniteEulerPairedResponse_eq_normalizedList]

/-- The packaged actual source first jet has the literal Markov coboundary
whenever its two visible-prime lists differ by one prepended prime. -/
theorem sourceActualBandFiniteEulerSoninResponse_sub_eq_coboundary_of_visiblePrimeLists
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (newFamily oldFamily : FinitePrimePowerFamily)
    (hnew : newFamily.visiblePrimes = p :: S)
    (hold : oldFamily.visiblePrimes = S) :
    sourceActualBandFiniteEulerSoninResponse owner lambda newFamily -
        sourceActualBandFiniteEulerSoninResponse owner lambda oldFamily =
      normalizedListActualBandSoninCoboundary owner lambda p S := by
  rw [sourceActualBandFiniteEulerSoninResponse_eq_normalizedList,
    sourceActualBandFiniteEulerSoninResponse_eq_normalizedList, hnew, hold]
  exact normalizedListActualBandSoninResponse_cons_sub_eq_coboundary
    owner lambda p S

/-- The source endpoint increment which reads the actual Gate trace after
the legal fixed-family trace conversion. -/
noncomputable def sourceBandGramIncrement
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    (newFamily oldFamily : FinitePrimePowerFamily) : SourceOp lambda :=
  sourceBandGramResponse owner lambda newFamily -
    sourceBandGramResponse owner lambda oldFamily

/-- The completed nonlinear remainder increment on the same source carrier.
This is kept as one difference and is not split into physical branches. -/
noncomputable def sourceActualBandFiniteEulerRemainderIncrement
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    (newFamily oldFamily : FinitePrimePowerFamily) : SourceOp lambda :=
  sourceActualBandFiniteEulerRemainderResponse owner lambda newFamily -
    sourceActualBandFiniteEulerRemainderResponse owner lambda oldFamily

/-- Exact completed ledger: the nonlinear-remainder increment is the
two-sided Markov first-jet increment minus the matching source endpoint
increment. -/
theorem sourceActualBandFiniteEulerRemainderIncrement_eq_coboundary_sub_endpoint
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (newFamily oldFamily : FinitePrimePowerFamily)
    (hnew : newFamily.visiblePrimes = p :: S)
    (hold : oldFamily.visiblePrimes = S) :
    sourceActualBandFiniteEulerRemainderIncrement owner lambda newFamily oldFamily =
      normalizedListActualBandSoninCoboundary owner lambda p S -
        sourceBandGramIncrement owner lambda newFamily oldFamily := by
  unfold sourceActualBandFiniteEulerRemainderIncrement sourceBandGramIncrement
    sourceActualBandFiniteEulerRemainderResponse
  calc
    _ = (sourceActualBandFiniteEulerSoninResponse owner lambda newFamily -
          sourceActualBandFiniteEulerSoninResponse owner lambda oldFamily) -
        (sourceBandGramResponse owner lambda newFamily -
          sourceBandGramResponse owner lambda oldFamily) := by
      abel
    _ = _ := by
      rw [sourceActualBandFiniteEulerSoninResponse_sub_eq_coboundary_of_visiblePrimeLists
        owner lambda p S newFamily oldFamily hnew hold]

/-- Equivalent endpoint form of the completed ledger.  The linear Markov
increment can disappear from the Gate only by cancellation with the complete
remainder increment displayed here. -/
theorem sourceBandGramIncrement_eq_coboundary_sub_remainder
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (newFamily oldFamily : FinitePrimePowerFamily)
    (hnew : newFamily.visiblePrimes = p :: S)
    (hold : oldFamily.visiblePrimes = S) :
    sourceBandGramIncrement owner lambda newFamily oldFamily =
      normalizedListActualBandSoninCoboundary owner lambda p S -
        sourceActualBandFiniteEulerRemainderIncrement owner lambda newFamily oldFamily := by
  rw [sourceActualBandFiniteEulerRemainderIncrement_eq_coboundary_sub_endpoint
    owner lambda p S newFamily oldFamily hnew hold]
  abel

/-- The same completed increment is the actual quadratic-cycle increment.
This identifies the matching cancellation channel with the source owner's
nonlinear endpoint, rather than an auxiliary literal-list model. -/
theorem actualBandQuadraticCycledResponse_sub_eq_coboundary_sub_endpoint
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (newFamily oldFamily : FinitePrimePowerFamily)
    (hnew : newFamily.visiblePrimes = p :: S)
    (hold : oldFamily.visiblePrimes = S) :
    actualBandQuadraticCycledResponse owner lambda newFamily -
        actualBandQuadraticCycledResponse owner lambda oldFamily =
      normalizedListActualBandSoninCoboundary owner lambda p S -
        sourceBandGramIncrement owner lambda newFamily oldFamily := by
  rw [<- sourceActualBandFiniteEulerRemainderResponse_eq_quadraticCycle,
    <- sourceActualBandFiniteEulerRemainderResponse_eq_quadraticCycle]
  exact sourceActualBandFiniteEulerRemainderIncrement_eq_coboundary_sub_endpoint
    owner lambda p S newFamily oldFamily hnew hold

/-- The actual completed relative response carries exactly the same
one-prime cancellation ledger as the quadratic-cycle owner. -/
theorem actualBandCompletedRelativeResponse_sub_eq_coboundary_sub_endpoint
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (newFamily oldFamily : FinitePrimePowerFamily)
    (hnew : newFamily.visiblePrimes = p :: S)
    (hold : oldFamily.visiblePrimes = S) :
    actualBandCompletedRelativeResponse owner lambda newFamily -
        actualBandCompletedRelativeResponse owner lambda oldFamily =
      normalizedListActualBandSoninCoboundary owner lambda p S -
        sourceBandGramIncrement owner lambda newFamily oldFamily := by
  rw [<- sourceActualBandFiniteEulerRemainderResponse_eq_completedRelativeResponse,
    <- sourceActualBandFiniteEulerRemainderResponse_eq_completedRelativeResponse]
  exact sourceActualBandFiniteEulerRemainderIncrement_eq_coboundary_sub_endpoint
    owner lambda p S newFamily oldFamily hnew hold

end CCM24FiniteSCausalMarkovCompletedFirstDifference
end CCM25Concrete
end Source
end ConnesWeilRH
