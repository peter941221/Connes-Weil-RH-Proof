/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSSchurMarkovPairing
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSGramOrderingBridge

/-!
# Polar trace bridge for the Schur--Markov numerator

The complete Schur--Markov relative numerator is the positive scalar
`rho_S` times a bounded similarity of the left-Gram-order endpoint.  The
similarity is formed by the terminal inverse-Gram square root and has an
explicit two-sided inverse.  Cycling that similarity is legal only through
the existing four-branch Hilbert--Schmidt pair.

Consequently the absolute ordinary trace of the polar numerator is exactly
`rho_S` times the absolute ordinary trace of the route's right-Gram-order
endpoint.  This retains the ordering anomaly: the two endpoint operators are
adjoints, not equal, and no trace of a non-trace-class similarity is cycled.

No uniform estimate, sign theorem, Gate 3U conclusion, or RH premise is
introduced here.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSSchurMarkovPolarTraceBridge

open MeasureTheory
open scoped InnerProduct InnerProductSpace

open CC20Concrete
open _root_.ConnesWeilRH.CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open CC20Concrete.PositiveTrace
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSBandTrace
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSFixedSourcePolar
open CCM24FiniteSGramInverseCalculus
open CCM24FiniteSGramOrderingBridge
open CCM24FiniteSGramResponse
open CCM24FiniteSParameterizedEulerProduct
open CCM24FiniteSProjectionTrace
open CCM24FiniteSSchurMarkovPairing
open CCM24FiniteSSchurPolarTelescoping
open CCM24FiniteSTransportBounds
open CCM24SourceProlateTrace

local notation "SourceOp" lambda =>
  CCM24FiniteSFrameGramCalculus.sourceSoninCarrier lambda →L[ℂ]
    CCM24FiniteSFrameGramCalculus.sourceSoninCarrier lambda

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace
      (CCM24FiniteSFrameGramCalculus.sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- The terminal positive inverse-Gram square root `Z_S=Gamma_S^(-1/2)`.
It is the right factor in the polar similarity. -/
noncomputable def suffixEulerPolarRightSimilarity
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    SourceOp lambda :=
  parameterizedSoninGramInvSqrt lambda 1 family.visiblePrimes (by norm_num)

/-- The left factor `Z_S Gamma_S` in the polar similarity. -/
noncomputable def suffixEulerPolarLeftSimilarity
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    SourceOp lambda :=
  suffixEulerPolarRightSimilarity lambda family ∘L
    finiteEulerGram lambda family

/-- The two polar similarity factors multiply to the identity in the order
used by Hilbert--Schmidt trace cyclicity. -/
theorem suffixEulerPolarRight_comp_left
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    suffixEulerPolarRightSimilarity lambda family ∘L
        suffixEulerPolarLeftSimilarity lambda family =
      ContinuousLinearMap.id ℂ (sourceSoninCarrier lambda) := by
  rw [suffixEulerPolarLeftSimilarity]
  apply ContinuousLinearMap.ext
  intro x
  have hsquare := parameterizedSoninGramInvSqrt_mul_self
    lambda 1 family.visiblePrimes (by norm_num)
  have hsquarePoint := congrArg
    (fun operator : SourceOp lambda => operator
      (finiteEulerGram lambda family x)) hsquare
  rw [parameterizedSoninGramInv_one_eq_finiteEulerGramInv] at hsquarePoint
  have hinverse := congrArg
    (fun operator : SourceOp lambda => operator x)
    (finiteEulerGramInv_comp_gram lambda family)
  simpa only [suffixEulerPolarRightSimilarity,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using
      hsquarePoint.trans hinverse

/-- The same factors multiply to the identity in the opposite order. -/
theorem suffixEulerPolarLeft_comp_right
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    suffixEulerPolarLeftSimilarity lambda family ∘L
        suffixEulerPolarRightSimilarity lambda family =
      ContinuousLinearMap.id ℂ (sourceSoninCarrier lambda) := by
  apply ContinuousLinearMap.ext
  intro x
  have h := congrArg
    (fun operator : SourceOp lambda => operator x)
    (parameterizedSoninGramInvSqrt_gram_mul
      lambda 1 family.visiblePrimes (by norm_num))
  rw [show CCM24FiniteSFrameGramCalculus.parameterizedSoninGram
      lambda 1 family.visiblePrimes = finiteEulerGram lambda family by
    rw [CCM24FiniteSFrameGramCalculus.parameterizedSoninGram,
      parameterizedSoninFrame_one_eq_finiteEulerFrame, finiteEulerGram]] at h
  simpa only [suffixEulerPolarLeftSimilarity,
    suffixEulerPolarRightSimilarity,
    parameterizedSoninFrame_one_eq_finiteEulerFrame,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using h

/-- The untransported restricted frame is the literal source inclusion. -/
theorem parameterizedSoninFrame_one_nil_eq_sourceInclusion
    (lambda : CCM24SoninScale) :
    CCM24FiniteSFrameGramCalculus.parameterizedSoninFrame lambda 1 [] =
      sourceInclusion lambda := by
  apply ContinuousLinearMap.ext
  intro x
  rfl

/-- The empty restricted Gram is the identity. -/
theorem parameterizedSoninGram_one_nil_eq_id
    (lambda : CCM24SoninScale) :
    CCM24FiniteSFrameGramCalculus.parameterizedSoninGram lambda 1 [] =
      ContinuousLinearMap.id ℂ (sourceSoninCarrier lambda) := by
  rw [CCM24FiniteSFrameGramCalculus.parameterizedSoninGram,
    parameterizedSoninFrame_one_nil_eq_sourceInclusion]
  exact sourceInclusion_adjoint_comp_self lambda

/-- The constructed inverse Gram is also the identity at the empty suffix. -/
theorem parameterizedSoninGramInv_one_nil_eq_id
    (lambda : CCM24SoninScale) :
    parameterizedSoninGramInv lambda 1 [] (by norm_num) =
      ContinuousLinearMap.id ℂ (sourceSoninCarrier lambda) := by
  have h := parameterizedSoninGramInv_mul_gram
    lambda 1 [] (by norm_num)
  rw [parameterizedSoninGram_one_nil_eq_id] at h
  simpa only [ContinuousLinearMap.mul_def,
    ContinuousLinearMap.comp_id] using h

/-- The fixed polar coordinate at the empty suffix.  Its square is the
identity, which is all the complete numerator needs. -/
noncomputable def suffixEulerEmptyPolarSimilarity
    (lambda : CCM24SoninScale) : SourceOp lambda :=
  parameterizedSoninGramInvSqrt lambda 1 [] (by norm_num)

theorem suffixEulerEmptyPolarSimilarity_comp_self
    (lambda : CCM24SoninScale) :
    suffixEulerEmptyPolarSimilarity lambda ∘L
        suffixEulerEmptyPolarSimilarity lambda =
      ContinuousLinearMap.id ℂ (sourceSoninCarrier lambda) := by
  rw [suffixEulerEmptyPolarSimilarity,
    parameterizedSoninGramInvSqrt_mul_self,
    parameterizedSoninGramInv_one_nil_eq_id]

theorem suffixEulerEmptyPolarSimilarity_isSelfAdjoint
    (lambda : CCM24SoninScale) :
    IsSelfAdjoint (suffixEulerEmptyPolarSimilarity lambda) := by
  exact parameterizedSoninGramInvSqrt_isSelfAdjoint
    lambda 1 [] (by norm_num)

/-- The empty polar frame is the source inclusion followed by its fixed
positive polar coordinate. -/
theorem newSuffixFrame_nil_eq_sourceInclusion_comp_emptySimilarity
    (lambda : CCM24SoninScale) :
    newSuffixFrame lambda [] =
      sourceInclusion lambda ∘L suffixEulerEmptyPolarSimilarity lambda := by
  rw [newSuffixFrame, parameterizedSoninPolarFrame,
    parameterizedSoninFrame_one_nil_eq_sourceInclusion]
  rfl

/-- The terminal polar frame is the finite Euler frame followed by `Z_S`. -/
theorem newSuffixFrame_visiblePrimes_eq_frame_comp_rightSimilarity
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    newSuffixFrame lambda family.visiblePrimes =
      finiteEulerFrame lambda family ∘L
        suffixEulerPolarRightSimilarity lambda family := by
  rw [newSuffixFrame, parameterizedSoninPolarFrame,
    parameterizedSoninFrame_one_eq_finiteEulerFrame]
  rfl

/-- At synchronized time one, the parameterized restricted Gram is the
finite-Euler Gram on the same visible-prime family. -/
theorem parameterizedSoninGram_one_eq_finiteEulerGram
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    CCM24FiniteSFrameGramCalculus.parameterizedSoninGram lambda 1
        family.visiblePrimes =
      finiteEulerGram lambda family := by
  rw [CCM24FiniteSFrameGramCalculus.parameterizedSoninGram,
    parameterizedSoninFrame_one_eq_finiteEulerFrame, finiteEulerGram]

/-- The complete forward polar similarity includes the fixed empty polar
coordinate on its right. -/
noncomputable def suffixEulerPolarForwardSimilarity
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    SourceOp lambda :=
  suffixEulerPolarLeftSimilarity lambda family ∘L
    suffixEulerEmptyPolarSimilarity lambda

/-- The reverse polar similarity carries the same empty coordinate on its
left. -/
noncomputable def suffixEulerPolarReverseSimilarity
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    SourceOp lambda :=
  suffixEulerEmptyPolarSimilarity lambda ∘L
    suffixEulerPolarRightSimilarity lambda family

theorem suffixEulerPolarReverse_comp_forward
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    suffixEulerPolarReverseSimilarity lambda family ∘L
        suffixEulerPolarForwardSimilarity lambda family =
      ContinuousLinearMap.id ℂ (sourceSoninCarrier lambda) := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [suffixEulerPolarReverseSimilarity,
    suffixEulerPolarForwardSimilarity, ContinuousLinearMap.comp_apply]
  rw [show suffixEulerPolarRightSimilarity lambda family
      (suffixEulerPolarLeftSimilarity lambda family
        (suffixEulerEmptyPolarSimilarity lambda x)) =
      suffixEulerEmptyPolarSimilarity lambda x by
    exact congrFun (congrArg DFunLike.coe
      (suffixEulerPolarRight_comp_left lambda family)) _]
  exact congrFun (congrArg DFunLike.coe
    (suffixEulerEmptyPolarSimilarity_comp_self lambda)) x

theorem suffixEulerPolarForward_comp_reverse
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    suffixEulerPolarForwardSimilarity lambda family ∘L
        suffixEulerPolarReverseSimilarity lambda family =
      ContinuousLinearMap.id ℂ (sourceSoninCarrier lambda) := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [suffixEulerPolarReverseSimilarity,
    suffixEulerPolarForwardSimilarity, ContinuousLinearMap.comp_apply]
  rw [show suffixEulerEmptyPolarSimilarity lambda
      (suffixEulerEmptyPolarSimilarity lambda
        (suffixEulerPolarRightSimilarity lambda family x)) =
      suffixEulerPolarRightSimilarity lambda family x by
    exact congrFun (congrArg DFunLike.coe
      (suffixEulerEmptyPolarSimilarity_comp_self lambda)) _]
  exact congrFun (congrArg DFunLike.coe
    (suffixEulerPolarLeft_comp_right lambda family)) x

/-- The empty polar detector compression is the literal source detector
compression `W_0`. -/
theorem suffixPolarDetectorCompression_nil_eq_sourceDetector
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    suffixPolarDetectorCompression owner lambda [] =
      suffixEulerEmptyPolarSimilarity lambda ∘L
        ((sourceInclusion lambda)† ∘L detectorOperator owner ∘L
          sourceInclusion lambda) ∘L
        suffixEulerEmptyPolarSimilarity lambda := by
  have hZ : (suffixEulerEmptyPolarSimilarity lambda)† =
      suffixEulerEmptyPolarSimilarity lambda :=
    (suffixEulerEmptyPolarSimilarity_isSelfAdjoint lambda).adjoint_eq
  rw [suffixPolarDetectorCompression,
    newSuffixFrame_nil_eq_sourceInclusion_comp_emptySimilarity,
    ContinuousLinearMap.adjoint_comp, hZ]
  apply ContinuousLinearMap.ext
  intro x
  rfl

/-- The terminal polar compression is `Z_S K_S^dagger W K_S Z_S`. -/
theorem suffixPolarDetectorCompression_visiblePrimes_eq
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    suffixPolarDetectorCompression owner lambda family.visiblePrimes =
      suffixEulerPolarRightSimilarity lambda family ∘L
        ((finiteEulerFrame lambda family)† ∘L detectorOperator owner ∘L
          finiteEulerFrame lambda family) ∘L
        suffixEulerPolarRightSimilarity lambda family := by
  have hZ : (suffixEulerPolarRightSimilarity lambda family)† =
      suffixEulerPolarRightSimilarity lambda family := by
    exact (parameterizedSoninGramInvSqrt_isSelfAdjoint
      lambda 1 family.visiblePrimes (by norm_num)).adjoint_eq
  rw [suffixPolarDetectorCompression,
    newSuffixFrame_visiblePrimes_eq_frame_comp_rightSimilarity,
    ContinuousLinearMap.adjoint_comp, hZ]
  apply ContinuousLinearMap.ext
  intro x
  rfl

/-- The two empty polar coordinates cancel inside the complete forward/base/
reverse detector product. -/
theorem polarForward_comp_emptyCompression_comp_reverse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    suffixEulerPolarForwardSimilarity lambda family ∘L
        suffixPolarDetectorCompression owner lambda [] ∘L
          suffixEulerPolarReverseSimilarity lambda family =
      suffixEulerPolarLeftSimilarity lambda family ∘L
        ((sourceInclusion lambda)† ∘L detectorOperator owner ∘L
          sourceInclusion lambda) ∘L
        suffixEulerPolarRightSimilarity lambda family := by
  rw [suffixPolarDetectorCompression_nil_eq_sourceDetector]
  apply ContinuousLinearMap.ext
  intro x
  have hempty (y : sourceSoninCarrier lambda) :
      suffixEulerEmptyPolarSimilarity lambda
          (suffixEulerEmptyPolarSimilarity lambda y) = y := by
    exact congrFun (congrArg DFunLike.coe
      (suffixEulerEmptyPolarSimilarity_comp_self lambda)) y
  simp only [suffixEulerPolarForwardSimilarity,
    suffixEulerPolarReverseSimilarity, ContinuousLinearMap.comp_apply]
  rw [hempty, hempty]

/-- The upper-normalized complete Schur transition is the left polar
similarity divided by the exact upper Euler factor. -/
theorem suffixEulerTransitionProduct_eq_invUpper_smul_forwardSimilarity
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    suffixEulerTransitionProduct lambda family.visiblePrimes =
      ((finiteEulerUpperFactor family.visiblePrimes : ℂ)⁻¹) •
        suffixEulerPolarForwardSimilarity lambda family := by
  let S := family.visiblePrimes
  let upper : ℂ := finiteEulerUpperFactor S
  let transition := suffixEulerTransitionProduct lambda S
  let ambient := suffixEulerAmbientProduct S
  let polar := newSuffixFrame lambda S
  let empty := newSuffixFrame lambda []
  let frame := finiteEulerFrame lambda family
  let Z := suffixEulerPolarRightSimilarity lambda family
  have hupperNe : upper ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr
      (ne_of_gt (finiteEulerUpperFactor_pos S))
  have hintertwine := suffixEulerAmbientProduct_comp_emptyPolarFrame lambda S
  have hupper := upperFactor_smul_suffixEulerAmbientProduct S
  have hisometry := parameterizedSoninPolarFrame_adjoint_comp_self
    lambda 1 S (by norm_num)
  apply ContinuousLinearMap.ext
  intro x
  change transition x =
    (upper⁻¹ • suffixEulerPolarForwardSimilarity lambda family) x
  have hintertwinePoint := congrArg
    (fun operator : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier =>
      operator x) hintertwine
  have hupperPoint := congrArg
    (fun operator : finiteSCarrier →L[ℂ] finiteSCarrier =>
      operator (empty x)) hupper
  have hisometryPoint := congrArg
    (fun operator : SourceOp lambda => operator (transition x)) hisometry
  have hscaled : upper • transition x =
      suffixEulerPolarForwardSimilarity lambda family x := by
    calc
      upper • transition x =
          upper • (ContinuousLinearMap.adjoint polar
            (polar (transition x))) := by
        simpa only [ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.id_apply, transition, polar] using
            congrArg (fun y => upper • y) hisometryPoint.symm
      _ = ContinuousLinearMap.adjoint polar
          (upper • polar (transition x)) := by rw [map_smul]
      _ = ContinuousLinearMap.adjoint polar
          (upper • ambient (empty x)) := by
        simpa only [ContinuousLinearMap.comp_apply, empty, polar, ambient,
          transition] using
            congrArg (fun y => ContinuousLinearMap.adjoint polar (upper • y))
              hintertwinePoint.symm
      _ = ContinuousLinearMap.adjoint polar
          (ccm24FiniteEulerTransportEquiv S (empty x)) := by
        simpa only [upper, empty, ContinuousLinearMap.smul_apply] using
          congrArg (ContinuousLinearMap.adjoint polar) hupperPoint
      _ = suffixEulerPolarForwardSimilarity lambda family x := by
        dsimp only [polar, Z, S, empty, frame]
        rw [newSuffixFrame_visiblePrimes_eq_frame_comp_rightSimilarity]
        rw [newSuffixFrame_nil_eq_sourceInclusion_comp_emptySimilarity]
        have hZ : (suffixEulerPolarRightSimilarity lambda family)† =
            suffixEulerPolarRightSimilarity lambda family := by
          exact (parameterizedSoninGramInvSqrt_isSelfAdjoint
            lambda 1 family.visiblePrimes (by norm_num)).adjoint_eq
        simp only [ContinuousLinearMap.adjoint_comp,
          ContinuousLinearMap.comp_apply]
        rw [hZ]
        rfl
  calc
    transition x = upper⁻¹ • (upper • transition x) := by
      rw [smul_smul, inv_mul_cancel₀ hupperNe, one_smul]
    _ = upper⁻¹ • suffixEulerPolarForwardSimilarity lambda family x := by
      rw [hscaled]
    _ = (((finiteEulerUpperFactor family.visiblePrimes : ℂ)⁻¹) •
        suffixEulerPolarForwardSimilarity lambda family) x := by
      rfl

/-- The reverse probability-normalized product is the lower Euler factor
times the right polar similarity. -/
theorem suffixEulerReverseTransitionProduct_eq_lower_smul_reverseSimilarity
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    suffixEulerReverseTransitionProduct lambda family.visiblePrimes =
      (CCM24FiniteSGramResponse.finiteEulerLowerFactor
          family.visiblePrimes : ℂ) •
        suffixEulerPolarReverseSimilarity lambda family := by
  let S := family.visiblePrimes
  let upper : ℂ := finiteEulerUpperFactor S
  let lower : ℂ :=
    CCM24FiniteSGramResponse.finiteEulerLowerFactor S
  let rho : ℂ := suffixEulerSchurMarkovScalar S
  let transition := suffixEulerTransitionProduct lambda S
  let reverse := suffixEulerReverseTransitionProduct lambda S
  let forward := suffixEulerPolarForwardSimilarity lambda family
  let reverseSimilarity := suffixEulerPolarReverseSimilarity lambda family
  have htransition :=
    suffixEulerTransitionProduct_eq_invUpper_smul_forwardSimilarity
      lambda family
  have hpair := suffixEulerTransitionProduct_comp_reverse lambda S
  have hleftInverse := suffixEulerPolarReverse_comp_forward lambda family
  have hscalarReal : finiteEulerUpperFactor S *
      suffixEulerSchurMarkovScalar S =
        CCM24FiniteSGramResponse.finiteEulerLowerFactor S := by
    rw [suffixEulerSchurMarkovScalar_eq_lower_div_upper]
    field_simp [ne_of_gt (finiteEulerUpperFactor_pos S)]
  have hscalar : upper * rho = lower := by
    dsimp only [upper, rho, lower]
    exact_mod_cast hscalarReal
  apply ContinuousLinearMap.ext
  intro x
  change reverse x = (lower • reverseSimilarity) x
  have hpairPoint := congrArg
    (fun operator : SourceOp lambda => operator x) hpair
  have hleftInversePoint := congrArg
    (fun operator : SourceOp lambda => operator (reverse x)) hleftInverse
  have htransitionPoint := congrArg
    (fun operator : SourceOp lambda => operator (reverse x)) htransition
  have hleftReverse : forward (reverse x) = lower • x := by
    have hpairEval : transition (reverse x) = rho • x := by
      simpa only [ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply] using
          hpairPoint
    have htransitionEval : transition (reverse x) =
        upper⁻¹ • forward (reverse x) := by
      simpa only [ContinuousLinearMap.smul_apply] using htransitionPoint
    rw [htransitionEval] at hpairEval
    have hupperNe : upper ≠ 0 := by
      exact Complex.ofReal_ne_zero.mpr
        (ne_of_gt (finiteEulerUpperFactor_pos S))
    have hscaledPair := congrArg (fun y => upper • y) hpairEval
    simpa only [smul_smul, mul_inv_cancel₀ hupperNe, one_smul,
      hscalar] using hscaledPair
  calc
    reverse x = reverseSimilarity (forward (reverse x)) := by
      simpa only [ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.id_apply, reverseSimilarity, forward] using
          hleftInversePoint.symm
    _ = reverseSimilarity (lower • x) := by rw [hleftReverse]
    _ = lower • reverseSimilarity x :=
      map_smul reverseSimilarity lower x
    _ = (lower • reverseSimilarity) x := by
      rfl

/-- The left Gram order is the fixed detector compression minus the inverse
Gram followed by the transported detector compression. -/
theorem leftOrderedSourceBandGramResponse_eq_detector_sub
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    leftOrderedSourceBandGramResponse owner lambda family =
      ((sourceInclusion lambda)† ∘L detectorOperator owner ∘L
          sourceInclusion lambda) -
        finiteEulerGramInv lambda family ∘L
          ((finiteEulerFrame lambda family)† ∘L detectorOperator owner ∘L
            finiteEulerFrame lambda family) := by
  rw [leftOrderedSourceBandGramResponse,
    leftOrderedSourceGramResponse]
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply]
  abel

/-- Conjugating the left Gram order by the polar inverse pair gives the
difference of the two polar detector compressions. -/
theorem polarSimilarity_comp_leftOrdered_eq_compressionDifference
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    suffixEulerPolarLeftSimilarity lambda family ∘L
        leftOrderedSourceBandGramResponse owner lambda family ∘L
          suffixEulerPolarRightSimilarity lambda family =
      suffixEulerPolarLeftSimilarity lambda family ∘L
          ((sourceInclusion lambda)† ∘L detectorOperator owner ∘L
            sourceInclusion lambda) ∘L
          suffixEulerPolarRightSimilarity lambda family -
        suffixPolarDetectorCompression owner lambda family.visiblePrimes := by
  rw [leftOrderedSourceBandGramResponse_eq_detector_sub,
    suffixPolarDetectorCompression_visiblePrimes_eq]
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, map_sub]
  rw [show suffixEulerPolarLeftSimilarity lambda family
      (finiteEulerGramInv lambda family
        (((finiteEulerFrame lambda family)†)
          (detectorOperator owner
            (finiteEulerFrame lambda family
              (suffixEulerPolarRightSimilarity lambda family x))))) =
      suffixEulerPolarRightSimilarity lambda family
        (((finiteEulerFrame lambda family)†)
          (detectorOperator owner
            (finiteEulerFrame lambda family
              (suffixEulerPolarRightSimilarity lambda family x)))) by
    simp only [suffixEulerPolarLeftSimilarity,
      ContinuousLinearMap.comp_apply]
    rw [show finiteEulerGram lambda family
        (finiteEulerGramInv lambda family
          (((finiteEulerFrame lambda family)†)
            (detectorOperator owner
              (finiteEulerFrame lambda family
                (suffixEulerPolarRightSimilarity lambda family x))))) =
      ((finiteEulerFrame lambda family)†)
        (detectorOperator owner
          (finiteEulerFrame lambda family
            (suffixEulerPolarRightSimilarity lambda family x))) by
      exact congrFun (congrArg DFunLike.coe
        (finiteEulerGram_comp_inv lambda family)) _]]

/-- Exact polar similarity readback of the complete relative numerator. -/
theorem suffixEulerDetectorRelativeNumeratorProduct_eq_scaled_leftSimilarity
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    suffixEulerDetectorRelativeNumeratorProduct owner lambda
        family.visiblePrimes =
      (suffixEulerSchurMarkovScalar family.visiblePrimes : ℂ) •
        (suffixEulerPolarLeftSimilarity lambda family ∘L
          leftOrderedSourceBandGramResponse owner lambda family ∘L
            suffixEulerPolarRightSimilarity lambda family) := by
  rw [suffixEulerDetectorRelativeNumeratorProduct_eq_ordered,
    suffixEulerTransitionProduct_eq_invUpper_smul_forwardSimilarity,
    suffixEulerReverseTransitionProduct_eq_lower_smul_reverseSimilarity,
    polarSimilarity_comp_leftOrdered_eq_compressionDifference]
  apply ContinuousLinearMap.ext
  intro x
  have hcancelPoint := congrArg
    (fun operator : SourceOp lambda => operator x)
    (polarForward_comp_emptyCompression_comp_reverse owner lambda family)
  simp only [ContinuousLinearMap.comp_apply] at hcancelPoint
  simp only [suffixEulerSchurMarkovScaleOperator,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, map_smul,
    smul_smul]
  rw [hcancelPoint]
  have hscalarReal := suffixEulerSchurMarkovScalar_eq_lower_div_upper
    family.visiblePrimes
  have hscalar :
      (CCM24FiniteSGramResponse.finiteEulerLowerFactor
          family.visiblePrimes : ℂ) *
        (finiteEulerUpperFactor family.visiblePrimes : ℂ)⁻¹ =
      (suffixEulerSchurMarkovScalar family.visiblePrimes : ℂ) := by
    rw [hscalarReal]
    push_cast
    rfl
  rw [hscalar]
  rw [smul_sub]

/-- The four-branch pair makes the polar similarity trace cycle legal. -/
theorem ordinaryTraceAlong_polarLeftSimilarity_eq_leftOrdered
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {iota kappa tau iotaR kappaR tauR nu mu rho : Type*}
    (negativeBasis : HilbertBasis iota ℂ
      (Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure
        (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis kappa ℂ
      (Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure
        (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis tau ℂ
      (Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure
        (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis iotaR ℂ
      (Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure
        (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis kappaR ℂ
      (Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure
        (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis tauR ℂ
      (Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure
        (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis mu ℂ (commonBoundaryCarrier a c))
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    ordinaryTraceAlong sourceBasis
        (suffixEulerPolarLeftSimilarity lambda family ∘L
          leftOrderedSourceBandGramResponse owner lambda family ∘L
            suffixEulerPolarRightSimilarity lambda family) =
      ordinaryTraceAlong sourceBasis
        (leftOrderedSourceBandGramResponse owner lambda family) := by
  let base := sourceThreeBranchSourcePairData owner lambda family a c hac
    hsupp negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
    sourceBasis hfactor
  let leftPair := base.swap
  let similarPair := leftPair.boundedSandwich boundaryBasis
    (suffixEulerPolarLeftSimilarity lambda family)
    (suffixEulerPolarRightSimilarity lambda family)
  have hbase : base.traceProduct =
      sourceBandGramResponse owner lambda family := by
    exact sourceThreeBranchSourcePairData_traceProduct_eq owner lambda family
      a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis sourceBasis hfactor
  have hleft : leftPair.traceProduct =
      leftOrderedSourceBandGramResponse owner lambda family := by
    dsimp only [leftPair]
    rw [BasisHilbertSchmidtPairData.swap_traceProduct_eq_adjoint, hbase]
    exact (leftOrderedSourceBandGramResponse_eq_adjoint
      owner lambda family).symm
  have hsimilar : similarPair.traceProduct =
      suffixEulerPolarLeftSimilarity lambda family ∘L
        leftOrderedSourceBandGramResponse owner lambda family ∘L
          suffixEulerPolarRightSimilarity lambda family := by
    dsimp only [similarPair]
    rw [BasisHilbertSchmidtPairData.boundedSandwich_traceProduct_eq, hleft]
  calc
    ordinaryTraceAlong sourceBasis
        (suffixEulerPolarLeftSimilarity lambda family ∘L
          leftOrderedSourceBandGramResponse owner lambda family ∘L
            suffixEulerPolarRightSimilarity lambda family) =
      ordinaryTraceAlong sourceBasis similarPair.traceProduct := by
        rw [hsimilar]
    _ = ordinaryTraceAlong boundaryBasis
        (similarPair.right ∘L
          ContinuousLinearMap.adjoint similarPair.left) :=
      similarPair.ordinaryTraceAlong_traceProduct_eq_cyclic boundaryBasis
    _ = ordinaryTraceAlong boundaryBasis
        (leftPair.right ∘L ContinuousLinearMap.adjoint leftPair.left) := by
      apply congrArg (ordinaryTraceAlong boundaryBasis)
      apply ContinuousLinearMap.ext
      intro x
      simp only [similarPair, BasisHilbertSchmidtPairData.boundedSandwich,
        ContinuousLinearMap.adjoint_comp,
        ContinuousLinearMap.adjoint_adjoint,
        ContinuousLinearMap.comp_apply]
      rw [show suffixEulerPolarRightSimilarity lambda family
          (suffixEulerPolarLeftSimilarity lambda family
            (ContinuousLinearMap.adjoint leftPair.left x)) =
          ContinuousLinearMap.adjoint leftPair.left x by
        exact congrFun (congrArg DFunLike.coe
          (suffixEulerPolarRight_comp_left lambda family)) _]
    _ = ordinaryTraceAlong sourceBasis leftPair.traceProduct :=
      (leftPair.ordinaryTraceAlong_traceProduct_eq_cyclic boundaryBasis).symm
    _ = ordinaryTraceAlong sourceBasis
        (leftOrderedSourceBandGramResponse owner lambda family) := by
      rw [hleft]

/-- The polar numerator trace is the Schur--Markov scalar times the complex
conjugate of the route endpoint trace.  The conjugation is the retained
left/right Gram-order anomaly. -/
theorem ordinaryTraceAlong_relativeNumerator_eq_scaled_star_endpoint
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {iota kappa tau iotaR kappaR tauR nu mu rho : Type*}
    (negativeBasis : HilbertBasis iota ℂ
      (Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure
        (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis kappa ℂ
      (Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure
        (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis tau ℂ
      (Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure
        (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis iotaR ℂ
      (Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure
        (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis kappaR ℂ
      (Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure
        (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis tauR ℂ
      (Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure
        (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis mu ℂ (commonBoundaryCarrier a c))
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    ordinaryTraceAlong sourceBasis
        (suffixEulerDetectorRelativeNumeratorProduct owner lambda
          family.visiblePrimes) =
      (suffixEulerSchurMarkovScalar family.visiblePrimes : ℂ) *
        star (ordinaryTraceAlong sourceBasis
          (sourceBandGramResponse owner lambda family)) := by
  let base := sourceThreeBranchSourcePairData owner lambda family a c hac
    hsupp negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
    sourceBasis hfactor
  let leftPair := base.swap
  have hleft : leftPair.traceProduct =
      leftOrderedSourceBandGramResponse owner lambda family := by
    dsimp only [leftPair]
    rw [BasisHilbertSchmidtPairData.swap_traceProduct_eq_adjoint,
      sourceThreeBranchSourcePairData_traceProduct_eq owner lambda family
        a c hac hsupp negativeBasis positiveBasis outputBasis
        reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
        globalBasis boundaryBasis sourceBasis hfactor]
    exact (leftOrderedSourceBandGramResponse_eq_adjoint
      owner lambda family).symm
  have hsimilarClass : IsTraceClassAlong sourceBasis
      (suffixEulerPolarLeftSimilarity lambda family ∘L
        leftOrderedSourceBandGramResponse owner lambda family ∘L
          suffixEulerPolarRightSimilarity lambda family) := by
    rw [← hleft]
    exact leftPair.boundedSandwich_isTraceClassAlong boundaryBasis
      (suffixEulerPolarLeftSimilarity lambda family)
      (suffixEulerPolarRightSimilarity lambda family)
  rw [suffixEulerDetectorRelativeNumeratorProduct_eq_scaled_leftSimilarity,
    ordinaryTraceAlong_smul sourceBasis _ _ hsimilarClass,
    ordinaryTraceAlong_polarLeftSimilarity_eq_leftOrdered owner lambda family
      a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis sourceBasis hfactor,
    ordinaryTraceAlong_leftOrderedSourceBandGramResponse_eq_star]

/-- Exact scaled absolute-trace readback.  A uniform Gate 3U bound for the
route endpoint is now equivalent to the same bound for the complete polar
signed cocycle after division by the explicit positive scalar `rho_S`. -/
theorem norm_ordinaryTraceAlong_relativeNumerator_eq_scaled_endpoint
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {iota kappa tau iotaR kappaR tauR nu mu rho : Type*}
    (negativeBasis : HilbertBasis iota ℂ
      (Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure
        (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis kappa ℂ
      (Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure
        (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis tau ℂ
      (Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure
        (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis iotaR ℂ
      (Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure
        (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis kappaR ℂ
      (Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure
        (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis tauR ℂ
      (Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure
        (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis mu ℂ (commonBoundaryCarrier a c))
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    ‖ordinaryTraceAlong sourceBasis
        (suffixEulerDetectorRelativeNumeratorProduct owner lambda
          family.visiblePrimes)‖ =
      suffixEulerSchurMarkovScalar family.visiblePrimes *
        ‖ordinaryTraceAlong sourceBasis
          (sourceBandGramResponse owner lambda family)‖ := by
  rw [ordinaryTraceAlong_relativeNumerator_eq_scaled_star_endpoint owner
    lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis sourceBasis hfactor]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (suffixEulerSchurMarkovScalar_pos family.visiblePrimes),
    Complex.star_def, Complex.norm_conj]

end CCM24FiniteSSchurMarkovPolarTraceBridge
end CCM25Concrete
end Source
end ConnesWeilRH
