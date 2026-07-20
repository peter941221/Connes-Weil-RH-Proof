/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSFixedQuotientContractionBound

/-!
# Root-completed fixed-quotient first jet

Proof 433 bounds the literal fixed-quotient first jet by a physical pair whose
prolate coordinate is not homogeneous under scaling of the selected root.  This
module returns to Proof 405's two-branch scalar owner and splits the positive
detector `C† C` before any Hilbert--Schmidt energy is taken.

The resulting three terms contain the left root and the right root exactly once:
one prolate-range term and the two Leibniz orientations of the second-support
commutator.  This is an exact same-object identity.  No Schatten estimate,
support--Sobolev bound, endpoint telescope, Gate 3U, or RH premise is stored.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSRootCompletedFirstJet

open CCM24FiniteSProjectionTrace
open CCM24FiniteSBandTrace
open CCM24FiniteSGramResponse
open CCM24FiniteSInverseMetric
open CCM24FiniteSTwoSidedRootRecombination
open CCM24FiniteSFixedQuotientFirstJet
open CCM24FiniteSCommonBoundaryPair

variable {A : Type*} [Ring A]

/-- The additive commutator obeys the Leibniz rule in an arbitrary
noncommutative ring. -/
theorem commutator_mul_eq_root_split
    (leftRoot rightRoot operator : A) :
    commutator (leftRoot * rightRoot) operator =
      leftRoot * commutator rightRoot operator +
        commutator leftRoot operator * rightRoot := by
  unfold commutator
  noncomm_ring

/-- Proof 405's two surviving branches after the detector product has been
split at root level.  Every summand contains both roots exactly once. -/
def rootCompletedSecondSupportCorner
    (band inner secondSupport leftRoot rightRoot transport : A) : A :=
  band * secondSupport * leftRoot * rightRoot * inner * transport * band +
    band * (1 - secondSupport) * leftRoot *
      commutator rightRoot secondSupport * inner * transport * band +
    band * (1 - secondSupport) * commutator leftRoot secondSupport *
      rightRoot * inner * transport * band

/-- The fixed-quotient detector corner is exactly the root-completed
three-branch expression. -/
theorem detector_innerCorner_transport_eq_rootCompleted
    (band inner secondSupport leftRoot rightRoot transport : A)
    (hInner : IsIdempotentElem inner)
    (hBandInner : band * inner = 0)
    (hSecond : IsIdempotentElem secondSupport)
    (hSecondInner : secondSupport * inner = inner) :
    band * commutator (leftRoot * rightRoot) inner * inner * transport * band =
      rootCompletedSecondSupportCorner band inner secondSupport leftRoot
        rightRoot transport := by
  rw [detector_innerCorner_transport_eq_secondSupport_twoBranch band inner
    secondSupport (leftRoot * rightRoot) transport hInner hBandInner hSecond
    hSecondInner]
  rw [commutator_mul_eq_root_split]
  unfold rootCompletedSecondSupportCorner
  noncomm_ring

local notation "Op" => finiteSCarrier →L[ℂ] finiteSCarrier

/-- The left root of the support-compressed positive detector. -/
noncomputable def sourceCompressedDetectorLeftRoot
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) : Op :=
  radialSupportProjection lambda ∘L (rootConvolution owner)†

/-- The right root of the support-compressed positive detector. -/
noncomputable def sourceCompressedDetectorRightRoot
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) : Op :=
  rootConvolution owner ∘L radialSupportProjection lambda

/-- The actual compressed detector is the ordered product of the two named
roots. -/
theorem compressedDetector_eq_sourceCompressedDetectorRoots
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    compressedDetector (radialSupportProjection lambda)
        (detectorOperator owner) =
      sourceCompressedDetectorLeftRoot owner lambda ∘L
        sourceCompressedDetectorRightRoot owner lambda := by
  unfold compressedDetector detectorOperator
    sourceCompressedDetectorLeftRoot sourceCompressedDetectorRightRoot
    rootConvolution CC20Concrete.cc20GlobalConvolutionPositive
  apply ContinuousLinearMap.ext
  intro u
  rfl

/-- The genuine source first-jet corner with both convolution roots exposed
before any square-energy estimate. -/
noncomputable def sourceRootCompletedFixedQuotientCorner
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (transport : Op) : Op :=
  rootCompletedSecondSupportCorner
    (sourceBandProjection lambda)
    (sourceSoninProjection lambda)
    (sourceFourierSupportProjection lambda)
    (sourceCompressedDetectorLeftRoot owner lambda)
    (sourceCompressedDetectorRightRoot owner lambda)
    transport

/-- Proof 405's actual fixed-quotient corner equals the root-completed owner.
This removes Proof 433's nonhomogeneous prolate energy from the next analytic
contract without changing the represented operator. -/
theorem sourceFixedQuotientCorner_eq_rootCompleted
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (transport : Op) :
    sourceBandProjection lambda ∘L
        commutator (compressedDetector (radialSupportProjection lambda)
          (detectorOperator owner)) (sourceSoninProjection lambda) ∘L
        sourceSoninProjection lambda ∘L transport ∘L
        sourceBandProjection lambda =
      sourceRootCompletedFixedQuotientCorner owner lambda transport := by
  rw [sourceFixedQuotientCorner_eq_secondSupport_twoBranch owner lambda
    transport]
  rw [compressedDetector_eq_sourceCompressedDetectorRoots]
  unfold sourceRootCompletedFixedQuotientCorner
    rootCompletedSecondSupportCorner
  rw [commutator_mul_eq_root_split]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply]
  abel

/-- The normalized finite-Euler transport is the concrete family-uniform
instance of the root-completed first-jet identity. -/
theorem sourceFiniteEulerFixedQuotientCorner_eq_rootCompleted
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceBandProjection lambda ∘L
        commutator (compressedDetector (radialSupportProjection lambda)
          (detectorOperator owner)) (sourceSoninProjection lambda) ∘L
        sourceSoninProjection lambda ∘L
        (radialSupportProjection lambda ∘L
          normalizedFiniteEulerInverse family ∘L
          radialSupportProjection lambda) ∘L
        sourceBandProjection lambda =
      sourceRootCompletedFixedQuotientCorner owner lambda
        (radialSupportProjection lambda ∘L
          normalizedFiniteEulerInverse family ∘L
          radialSupportProjection lambda) := by
  exact sourceFixedQuotientCorner_eq_rootCompleted owner lambda
    (radialSupportProjection lambda ∘L normalizedFiniteEulerInverse family ∘L
      radialSupportProjection lambda)

end CCM24FiniteSRootCompletedFirstJet
end CCM25Concrete
end Source
end ConnesWeilRH
