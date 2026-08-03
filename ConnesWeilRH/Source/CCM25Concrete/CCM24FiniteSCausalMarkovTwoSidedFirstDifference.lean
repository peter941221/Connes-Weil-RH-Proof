/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCausalMarkovFirstDifference
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSActualBandFirstJetTrace

/-!
# Two-sided one-prime difference of the normalized actual-band first jet

The normalized causal inverse enters the actual-band first jet on both
adjoint-related sides.  Prepended-prime variation therefore has an exact
Hermitian two-sided form.  This records the complete old Markov prefix and
keeps the detector, quotient band, and source Sonin projection inside one
operator until the two sides have been recombined.

This is not the completed Hardy--prolate endpoint remainder.  In particular,
the result shows that the two-sided normalized first jet itself does not
algebraically delete the linear prime coboundary: it is a sum of one arm and
its adjoint.  Any Gate 3U half-power gain must consequently use the matching
endpoint/remainder contribution in the literal completed physical pairing.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCausalMarkovTwoSidedFirstDifference

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSProjectionTrace
open CCM24FiniteSGramResponse
open CCM24FiniteSBandTrace
open CCM24FiniteSFixedQuotientCarrier
open CCM24FiniteSActualBandFirstJetTrace
open CCM24FiniteSCausalMarkov
open CCM24FiniteSCausalMarkovFirstDifference
open CCM24FiniteSRootCompletedFirstJet

local notation "Op" => finiteSCarrier →L[ℂ] finiteSCarrier

private theorem adjoint_sub_endomorphism (A B : Op) :
    ContinuousLinearMap.adjoint (A - B) =
      ContinuousLinearMap.adjoint A - ContinuousLinearMap.adjoint B := by
  apply ContinuousLinearMap.ext
  intro u
  exact ext_inner_right ℂ fun v => by
    simp only [ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearMap.sub_apply, inner_sub_left, inner_sub_right]

private theorem detectorOperator_adjoint_eq_self
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) :
    ContinuousLinearMap.adjoint (detectorOperator owner) = detectorOperator owner := by
  rw [detectorOperator_eq_rootConvolution_adjoint_comp_rootConvolution,
    ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint]

private theorem actualBandDetectorPairedResponse_sub_of_add
    {A : Type*} [Ring A]
    (band inner detector newTransport oldTransport increment
      newAdjoint oldAdjoint incrementAdjoint : A)
    (htransport : newTransport = increment + oldTransport)
    (hadjoint : newAdjoint = incrementAdjoint + oldAdjoint) :
    actualBandDetectorPairedResponse band inner detector newTransport newAdjoint -
        actualBandDetectorPairedResponse band inner detector oldTransport oldAdjoint =
      actualBandDetectorPairedResponse band inner detector increment incrementAdjoint := by
  rw [htransport, hadjoint]
  unfold actualBandDetectorPairedResponse
  noncomm_ring

/-- The actual two-sided first-jet response, written for a literal ordered
visible-prime list rather than a packaged arithmetic family. -/
noncomputable def normalizedListActualBandPairedResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) : Op :=
  actualBandDetectorPairedResponse (sourceBandProjection lambda)
    (sourceSoninProjection lambda) (detectorOperator owner)
    (normalizedFiniteEulerInverseList S)
    (ContinuousLinearMap.adjoint (normalizedFiniteEulerInverseList S))

/-- The forward arm of the genuine one-prime Markov coboundary after the
actual detector and source band have been inserted. -/
noncomputable def normalizedListActualBandCoboundaryLeft
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) : Op :=
  sourceSoninProjection lambda * detectorOperator owner *
    sourceBandProjection lambda *
      (normalizedFiniteEulerInverseList S ∘L
        normalizedPrimeEulerInverseTranslationCoboundary p) *
          sourceSoninProjection lambda

/-- The reverse arm paired with the same old Markov prefix and one-prime
coboundary.  It is kept beside the left arm before any scalar operation. -/
noncomputable def normalizedListActualBandCoboundaryRight
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) : Op :=
  sourceSoninProjection lambda *
    ContinuousLinearMap.adjoint
      (normalizedFiniteEulerInverseList S ∘L
        normalizedPrimeEulerInverseTranslationCoboundary p) *
      sourceBandProjection lambda * detectorOperator owner *
        sourceSoninProjection lambda

/-- The complete two-sided first-order increment.  Its two arms are retained
in one actual-band response rather than estimated separately. -/
noncomputable def normalizedListActualBandTwoSidedCoboundary
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) : Op :=
  actualBandDetectorPairedResponse (sourceBandProjection lambda)
    (sourceSoninProjection lambda) (detectorOperator owner)
    (normalizedFiniteEulerInverseList S ∘L
      normalizedPrimeEulerInverseTranslationCoboundary p)
    (ContinuousLinearMap.adjoint
      (normalizedFiniteEulerInverseList S ∘L
        normalizedPrimeEulerInverseTranslationCoboundary p))

/-- The reverse arm is literally the adjoint of the forward arm. -/
theorem normalizedListActualBandCoboundaryRight_eq_left_adjoint
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    normalizedListActualBandCoboundaryRight owner lambda p S =
      ContinuousLinearMap.adjoint
        (normalizedListActualBandCoboundaryLeft owner lambda p S) := by
  let delta : Op :=
    normalizedFiniteEulerInverseList S ∘L
      normalizedPrimeEulerInverseTranslationCoboundary p
  let forward : Op :=
    sourceSoninProjection lambda ∘L detectorOperator owner ∘L
      sourceBandProjection lambda ∘L delta ∘L sourceSoninProjection lambda
  have hAdjoint :
      ContinuousLinearMap.adjoint forward =
        sourceSoninProjection lambda ∘L ContinuousLinearMap.adjoint delta ∘L
          sourceBandProjection lambda ∘L detectorOperator owner ∘L
            sourceSoninProjection lambda := by
    dsimp only [forward]
    rw [ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_comp,
      (sourceSoninProjection_isStarProjection lambda).isSelfAdjoint.adjoint_eq,
      (sourceBandProjection_isStarProjection lambda).isSelfAdjoint.adjoint_eq,
      detectorOperator_adjoint_eq_self]
    apply ContinuousLinearMap.ext
    intro u
    rfl
  simpa only [normalizedListActualBandCoboundaryRight,
    normalizedListActualBandCoboundaryLeft, ContinuousLinearMap.mul_def,
    delta, forward] using hAdjoint.symm

/-- The normalized actual-band first jet has the exact prefixed one-prime
difference.  The complete old Markov prefix remains on both physical sides. -/
theorem normalizedListActualBandPairedResponse_cons_sub_eq_twoSidedCoboundary
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    normalizedListActualBandPairedResponse owner lambda (p :: S) -
        normalizedListActualBandPairedResponse owner lambda S =
      normalizedListActualBandTwoSidedCoboundary owner lambda p S := by
  let Mnew : Op := normalizedFiniteEulerInverseList (p :: S)
  let Mold : Op := normalizedFiniteEulerInverseList S
  let delta : Op := Mold ∘L normalizedPrimeEulerInverseTranslationCoboundary p
  have hdiff : Mnew - Mold = delta := by
    exact normalizedFiniteEulerInverseList_cons_sub_eq_prefixedTranslationCoboundary p S
  have hM : Mnew = delta + Mold := by
    calc
      Mnew = Mnew - Mold + Mold := (sub_add_cancel Mnew Mold).symm
      _ = delta + Mold := by rw [hdiff]
  have hAdjDiff : ContinuousLinearMap.adjoint Mnew -
      ContinuousLinearMap.adjoint Mold = ContinuousLinearMap.adjoint delta := by
    calc
      ContinuousLinearMap.adjoint Mnew - ContinuousLinearMap.adjoint Mold =
          ContinuousLinearMap.adjoint (Mnew - Mold) :=
        (adjoint_sub_endomorphism Mnew Mold).symm
      _ = ContinuousLinearMap.adjoint delta :=
        congrArg ContinuousLinearMap.adjoint hdiff
  have hMAdj : ContinuousLinearMap.adjoint Mnew =
      ContinuousLinearMap.adjoint delta + ContinuousLinearMap.adjoint Mold := by
    calc
      ContinuousLinearMap.adjoint Mnew =
          ContinuousLinearMap.adjoint Mnew - ContinuousLinearMap.adjoint Mold +
            ContinuousLinearMap.adjoint Mold :=
        (sub_add_cancel (ContinuousLinearMap.adjoint Mnew)
          (ContinuousLinearMap.adjoint Mold)).symm
      _ = ContinuousLinearMap.adjoint delta + ContinuousLinearMap.adjoint Mold := by
        rw [hAdjDiff]
  change actualBandDetectorPairedResponse (sourceBandProjection lambda)
      (sourceSoninProjection lambda) (detectorOperator owner) Mnew
        (ContinuousLinearMap.adjoint Mnew) -
        actualBandDetectorPairedResponse (sourceBandProjection lambda)
          (sourceSoninProjection lambda) (detectorOperator owner) Mold
            (ContinuousLinearMap.adjoint Mold) =
      actualBandDetectorPairedResponse (sourceBandProjection lambda)
        (sourceSoninProjection lambda) (detectorOperator owner) delta
          (ContinuousLinearMap.adjoint delta)
  exact actualBandDetectorPairedResponse_sub_of_add
    (sourceBandProjection lambda) (sourceSoninProjection lambda)
    (detectorOperator owner) Mnew Mold delta
    (ContinuousLinearMap.adjoint Mnew) (ContinuousLinearMap.adjoint Mold)
    (ContinuousLinearMap.adjoint delta) hM hMAdj

/-- The two-sided increment is the sum of its two directed arms, not an
internal subtraction.  Thus the one-prime coboundary alone supplies no
algebraic linear-term cancellation. -/
theorem normalizedListActualBandTwoSidedCoboundary_eq_left_add_right
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    normalizedListActualBandTwoSidedCoboundary owner lambda p S =
      normalizedListActualBandCoboundaryLeft owner lambda p S +
        normalizedListActualBandCoboundaryRight owner lambda p S := by
  unfold normalizedListActualBandTwoSidedCoboundary
    normalizedListActualBandCoboundaryLeft
    normalizedListActualBandCoboundaryRight actualBandDetectorPairedResponse
  rfl

/-- The exact two-sided increment is an adjoint pair with a plus sign.  It
does not vanish algebraically before the matching endpoint/remainder channel
is inserted. -/
theorem normalizedListActualBandTwoSidedCoboundary_eq_left_add_adjoint
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    normalizedListActualBandTwoSidedCoboundary owner lambda p S =
      normalizedListActualBandCoboundaryLeft owner lambda p S +
        ContinuousLinearMap.adjoint
          (normalizedListActualBandCoboundaryLeft owner lambda p S) := by
  rw [normalizedListActualBandTwoSidedCoboundary_eq_left_add_right,
    normalizedListActualBandCoboundaryRight_eq_left_adjoint]

/-- The packaged actual first jet reads back to the literal-list owner. -/
theorem sourceActualBandFiniteEulerPairedResponse_eq_normalizedList
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceActualBandFiniteEulerPairedResponse owner lambda family =
      normalizedListActualBandPairedResponse owner lambda family.visiblePrimes := by
  rw [sourceActualBandFiniteEulerPairedResponse_eq_rawDetector,
    normalizedFiniteEulerInverse_eq_causalAverage,
    finiteEulerCausalAverage_eq_normalizedInverse]
  rfl

end CCM24FiniteSCausalMarkovTwoSidedFirstDifference
end CCM25Concrete
end Source
end ConnesWeilRH
