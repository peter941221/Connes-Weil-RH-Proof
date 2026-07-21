/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSRootCompletedCommutator
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSMultiRenewal

/-!
# Completed projection-commutator renewal expansion

The normalized Euler inverse is an operator-norm probability series of causal
translations.  This module pushes that series through the complete linear
owner `C_g P [.] B`.  Every renewal atom is completed by the root, Sonin
projection, and quotient-band projection before summation.  No atomwise trace
or total-variation estimate is asserted.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSRootCompletedCommutatorRenewal

open CC20Concrete
open CCM24FiniteSProjectionTrace
open CCM24FiniteSBandTrace
open CCM24FiniteSInverseMetric
open CCM24FiniteSMultiRenewal
open CCM24FiniteSRootCompletedCommutator
open CCM24FiniteSTwoSidedRootRecombination

noncomputable local instance finiteSCarrierCompleteSpace :
    CompleteSpace finiteSCarrier := inferInstance

/-- Continuous linear dependence of the completed common right leg on its
transport input. -/
noncomputable def rootCompletedBandCommutatorTransform
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    (finiteSCarrier →L[ℂ] finiteSCarrier) →L[ℂ]
      (finiteSCarrier →L[ℂ] finiteSCarrier) := by
  let B := sourceBandProjection lambda
  let rightComposeB :=
    (ContinuousLinearMap.compL ℂ finiteSCarrier finiteSCarrier finiteSCarrier).flip B
  let leftComposeB := ContinuousLinearMap.compL ℂ
    finiteSCarrier finiteSCarrier finiteSCarrier B
  let commutatorMap := rightComposeB - leftComposeB
  let projectInput :=
    (ContinuousLinearMap.compL ℂ finiteSCarrier finiteSCarrier finiteSCarrier).flip B
  let projectSonin := ContinuousLinearMap.compL ℂ
    finiteSCarrier finiteSCarrier finiteSCarrier
      (sourceSoninProjection lambda)
  let applyRoot := ContinuousLinearMap.compL ℂ
    finiteSCarrier finiteSCarrier finiteSCarrier (rootConvolution owner)
  exact applyRoot ∘L projectSonin ∘L projectInput ∘L commutatorMap

theorem rootCompletedBandCommutatorTransform_apply
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    (transport : finiteSCarrier →L[ℂ] finiteSCarrier) :
    rootCompletedBandCommutatorTransform owner lambda transport =
      rootConvolution owner ∘L sourceSoninProjection lambda ∘L
        commutator transport (sourceBandProjection lambda) ∘L
        sourceBandProjection lambda := by
  rfl

/-- One causal renewal atom after the complete root/Sonin/band owner has been
formed. -/
noncomputable def finiteEulerRootCompletedCommutatorAtom
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime)
    (index : FiniteEulerRenewalIndex S) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  rootCompletedBandCommutatorTransform owner lambda
    (finiteEulerRenewalOperatorTerm S index)

/-- The completed causal atoms are summable in operator norm for every finite
visible-prime list. -/
theorem summable_finiteEulerRootCompletedCommutatorAtom
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    Summable (finiteEulerRootCompletedCommutatorAtom owner lambda S) := by
  exact (rootCompletedBandCommutatorTransform owner lambda).summable
    (summable_finiteEulerRenewalOperatorTerm S)

/-- The Proof 464 common right leg is exactly the operator-norm sum of the
completed causal commutator atoms. -/
theorem sourceRootCompletedFiniteEulerCommonRightLeg_eq_commutatorRenewal
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    CCM24FiniteSRootCompletedFirstJet.sourceRootCompletedCommonRightLeg
        owner lambda
        (radialSupportProjection lambda ∘L
          normalizedFiniteEulerInverse family ∘L
          radialSupportProjection lambda) =
      ∑' index : FiniteEulerRenewalIndex family.visiblePrimes,
        finiteEulerRootCompletedCommutatorAtom owner lambda
          family.visiblePrimes index := by
  rw [sourceRootCompletedFiniteEulerCommonRightLeg_eq_projectionCommutator]
  rw [← rootCompletedBandCommutatorTransform_apply]
  rw [normalizedFiniteEulerInverse_eq_multiRenewalOperator]
  exact (rootCompletedBandCommutatorTransform owner lambda).map_tsum
    (summable_finiteEulerRenewalOperatorTerm family.visiblePrimes)

/-- One renewal atom of the complete root-homogeneous first-jet pairing. -/
noncomputable def finiteEulerRootCompletedPairAtom
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime)
    (index : FiniteEulerRenewalIndex S) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  (rootConvolution owner ∘L sourceBandProjection lambda).adjoint ∘L
    finiteEulerRootCompletedCommutatorAtom owner lambda S index

/-- The unweighted completed response at one causal displacement. -/
noncomputable def rootCompletedTranslationCommutatorPair
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (displacement : ℝ) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  (rootConvolution owner ∘L sourceBandProjection lambda).adjoint ∘L
    rootCompletedBandCommutatorTransform owner lambda
      (cc20GlobalLogTranslation (-displacement)).toContinuousLinearMap

/-- A completed renewal atom is its probability weight times the response at
the corresponding total causal displacement. -/
theorem finiteEulerRootCompletedPairAtom_eq_weight_smul_translation
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime)
    (index : FiniteEulerRenewalIndex S) :
    finiteEulerRootCompletedPairAtom owner lambda S index =
      (finiteEulerRenewalWeight S index : ℂ) •
        rootCompletedTranslationCommutatorPair owner lambda
          (finiteEulerRenewalDisplacement S index) := by
  unfold finiteEulerRootCompletedPairAtom
    finiteEulerRootCompletedCommutatorAtom
    rootCompletedTranslationCommutatorPair
    finiteEulerRenewalOperatorTerm
  rw [map_smul]
  let leftCompose := ContinuousLinearMap.compL ℂ
    finiteSCarrier finiteSCarrier finiteSCarrier
      ((rootConvolution owner ∘L sourceBandProjection lambda).adjoint)
  change leftCompose
      ((finiteEulerRenewalWeight S index : ℂ) •
        rootCompletedBandCommutatorTransform owner lambda
          (cc20GlobalLogTranslation
            (-finiteEulerRenewalDisplacement S index)).toContinuousLinearMap) =
    (finiteEulerRenewalWeight S index : ℂ) •
      leftCompose
        (rootCompletedBandCommutatorTransform owner lambda
          (cc20GlobalLogTranslation
            (-finiteEulerRenewalDisplacement S index)).toContinuousLinearMap)
  rw [map_smul]

/-- The complete root-pair atoms remain operator-norm summable. -/
theorem summable_finiteEulerRootCompletedPairAtom
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    Summable (finiteEulerRootCompletedPairAtom owner lambda S) := by
  let leftCompose := ContinuousLinearMap.compL ℂ
    finiteSCarrier finiteSCarrier finiteSCarrier
      ((rootConvolution owner ∘L sourceBandProjection lambda).adjoint)
  exact leftCompose.summable
    (summable_finiteEulerRootCompletedCommutatorAtom owner lambda S)

/-- The complete root-homogeneous finite-Euler corner is the operator-norm
sum of completed root-pair renewal atoms. -/
theorem sourceRootCompletedFiniteEulerCorner_eq_commutatorRenewal
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    CCM24FiniteSRootCompletedFirstJet.sourceRootCompletedFixedQuotientCorner
        owner lambda
        (radialSupportProjection lambda ∘L
          normalizedFiniteEulerInverse family ∘L
          radialSupportProjection lambda) =
      ∑' index : FiniteEulerRenewalIndex family.visiblePrimes,
        finiteEulerRootCompletedPairAtom owner lambda
          family.visiblePrimes index := by
  rw [CCM24FiniteSRootCompletedFirstJet.sourceRootCompletedFixedQuotientCorner_eq_unsplitRootPair,
    sourceRootCompletedFiniteEulerCommonRightLeg_eq_commutatorRenewal]
  let leftCompose := ContinuousLinearMap.compL ℂ
    finiteSCarrier finiteSCarrier finiteSCarrier
      ((rootConvolution owner ∘L sourceBandProjection lambda).adjoint)
  change leftCompose
      (∑' index : FiniteEulerRenewalIndex family.visiblePrimes,
        finiteEulerRootCompletedCommutatorAtom owner lambda
          family.visiblePrimes index) = _
  rw [leftCompose.map_tsum
    (summable_finiteEulerRootCompletedCommutatorAtom owner lambda
      family.visiblePrimes)]
  apply tsum_congr
  intro index
  rfl

/-- Final displacement-law form of the complete root-homogeneous corner. -/
theorem sourceRootCompletedFiniteEulerCorner_eq_weightedTranslationLaw
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    CCM24FiniteSRootCompletedFirstJet.sourceRootCompletedFixedQuotientCorner
        owner lambda
        (radialSupportProjection lambda ∘L
          normalizedFiniteEulerInverse family ∘L
          radialSupportProjection lambda) =
      ∑' index : FiniteEulerRenewalIndex family.visiblePrimes,
        (finiteEulerRenewalWeight family.visiblePrimes index : ℂ) •
          rootCompletedTranslationCommutatorPair owner lambda
            (finiteEulerRenewalDisplacement family.visiblePrimes index) := by
  rw [sourceRootCompletedFiniteEulerCorner_eq_commutatorRenewal]
  apply tsum_congr
  intro index
  exact finiteEulerRootCompletedPairAtom_eq_weight_smul_translation
    owner lambda family.visiblePrimes index

end CCM24FiniteSRootCompletedCommutatorRenewal
end CCM25Concrete
end Source
end ConnesWeilRH
