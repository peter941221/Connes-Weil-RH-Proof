/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSGramFlowCollapse
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSGramResponse

/-!
# Pullback of the actual moving Sonin crossing

The Gram-corrected moving projection is kept literal. Its oriented crossing
is pulled back to the fixed source Sonin carrier through the Euler frame and
the restricted Gram inverse. This exact identity does not assert trace-class
legality or a uniform Gate 3U estimate.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSMovingCrossingPullback

open CC20Concrete
open CCM24FiniteSProjectionTrace
open CCM24FiniteSParameterizedEulerGenerator
open CCM24FiniteSParameterizedEulerProduct
open CCM24FiniteSParameterizedEulerCommutation
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSGramInverseCalculus
open CCM24FiniteSGramProjectionCalculus
open CCM24FiniteSOrthogonalProjectionFlow
open CCM24FiniteSGramResponse
open _root_.ConnesWeilRH.CC20Concrete

local notation "Op" => finiteSCarrier →L[ℂ] finiteSCarrier

noncomputable local instance sourceSoninCompleteSpace
    (lambda : CCM24SoninScale) :
    CompleteSpace
      (CCM24FiniteSFrameGramCalculus.sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- The fixed-source rectangular crossing hit by the synchronized Euler
generator. -/
noncomputable def sourceSoninGeneratorCrossing
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) :
    CCM24FiniteSFrameGramCalculus.sourceSoninCarrier lambda →L[ℂ]
      finiteSCarrier :=
  (1 - sourceSoninProjection lambda) ∘L
    parameterizedFiniteEulerGenerator alpha S ∘L sourceInclusion lambda

/- The ambient signed three-branch owner of the fixed-source generator
crossing.  The sign is kept explicit: `cc20ThreeBranchCommutator` owns
`[R,X]`, whereas the left crossing is `(I-R) X R`. -/
noncomputable def sourceSoninGeneratorThreeBranchLedger
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) : Op :=
  cc20ThreeBranchCommutator
    (radialSupportProjection lambda)
    (sourceFourierSupportProjection lambda)
    (sourceProlateRemainder lambda)
    (parameterizedFiniteEulerGenerator alpha S)

theorem projectionLeftCrossing_eq_neg_commutator_sandwich
    (P X : Op) (hP : IsStarProjection P) :
    projectionLeftCrossing P X =
      (1 - P) ∘L (-cc20Commutator P X) ∘L P := by
  unfold projectionLeftCrossing cc20Commutator
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
    ContinuousLinearMap.neg_apply, map_sub, map_neg]
  have hidem := congrArg
    (fun map : Op => map u) hP.isIdempotentElem
  simp only [ContinuousLinearMap.mul_apply] at hidem
  have hXP := congrArg
    (fun map : Op => map (X (P u))) hP.isIdempotentElem
  simp only [ContinuousLinearMap.mul_apply] at hXP
  rw [hidem]
  change X (P u) - P (X (P u)) =
    -(P (X (P u)) - P (P (X (P u))) -
      (X (P u) - P (X (P u))))
  rw [hXP]
  abel

theorem sourceSoninGeneratorCrossing_eq_threeBranch_comp_inclusion
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) :
    sourceSoninGeneratorCrossing lambda alpha S =
      ((1 - sourceSoninProjection lambda) ∘L
        (-sourceSoninGeneratorThreeBranchLedger lambda alpha S) ∘L
          sourceSoninProjection lambda) ∘L sourceInclusion lambda := by
  let P := sourceSoninProjection lambda
  let X := parameterizedFiniteEulerGenerator alpha S
  let ledger := sourceSoninGeneratorThreeBranchLedger lambda alpha S
  have hledger : cc20Commutator P X = ledger := by
    dsimp only [P, X, ledger, sourceSoninGeneratorThreeBranchLedger]
    exact cc20Commutator_eq_threeBranch_of_eq _ _ _ _ _
      (sourceSoninProjection_eq_compression_sub_prolate lambda)
  calc
    sourceSoninGeneratorCrossing lambda alpha S =
        projectionLeftCrossing P X ∘L sourceInclusion lambda := by
      dsimp only [P, X]
      unfold sourceSoninGeneratorCrossing projectionLeftCrossing
      apply ContinuousLinearMap.ext
      intro u
      have hfix := congrArg (fun map => map u)
        (sourceInclusion_adjoint_comp_self lambda)
      simp only [ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.id_apply] at hfix
      have hprojection : sourceSoninProjection lambda
          (sourceInclusion lambda u) = sourceInclusion lambda u := by
        rw [← sourceInclusion_comp_adjoint lambda]
        simp only [ContinuousLinearMap.comp_apply]
        rw [hfix]
      simp only [ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
        ContinuousLinearMap.mul_apply]
      rw [hprojection]
    _ = ((1 - P) ∘L (-ledger) ∘L P) ∘L
          sourceInclusion lambda := by
      rw [projectionLeftCrossing_eq_neg_commutator_sandwich P X
        (sourceSoninProjection_isStarProjection lambda)]
      rw [hledger]
    _ = _ := by rfl

/-- The boundedly dressed pullback of the fixed-source rectangular crossing. -/
noncomputable def movingSoninCrossingPullback
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) : Op :=
  (1 - parameterizedCanonicalGramProjection lambda alpha S) ∘L
    parameterizedFiniteEulerFactor alpha S ∘L
    sourceSoninGeneratorCrossing lambda alpha S ∘L
    parameterizedSoninGramInv lambda alpha S halpha ∘L
    ContinuousLinearMap.adjoint (parameterizedSoninFrame lambda alpha S)

/-- The pullback keeps the complete fixed-source outer/second-support/prolate
ledger inside one bounded moving sandwich. -/
theorem movingSoninCrossingPullback_eq_threeBranch
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    movingSoninCrossingPullback lambda alpha S halpha =
      (1 - parameterizedCanonicalGramProjection lambda alpha S) ∘L
        parameterizedFiniteEulerFactor alpha S ∘L
        ((1 - sourceSoninProjection lambda) ∘L
          (-sourceSoninGeneratorThreeBranchLedger lambda alpha S) ∘L
            sourceSoninProjection lambda) ∘L
        sourceInclusion lambda ∘L
        parameterizedSoninGramInv lambda alpha S halpha ∘L
        ContinuousLinearMap.adjoint
          (parameterizedSoninFrame lambda alpha S) := by
  unfold movingSoninCrossingPullback
  rw [sourceSoninGeneratorCrossing_eq_threeBranch_comp_inclusion]
  apply ContinuousLinearMap.ext
  intro u
  rfl

/-- The canonical Gram projection fixes every vector in its moving frame. -/
theorem parameterizedCanonicalGramProjection_comp_frame_eq_frame
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    parameterizedCanonicalGramProjection lambda alpha S ∘L
        parameterizedSoninFrame lambda alpha S =
      parameterizedSoninFrame lambda alpha S := by
  unfold parameterizedCanonicalGramProjection gramCorrectedProjection
  rw [ringInverse_parameterizedSoninGram lambda alpha S halpha]
  apply ContinuousLinearMap.ext
  intro u
  have hu := congrArg
    (fun operator :
        CCM24FiniteSFrameGramCalculus.sourceSoninCarrier lambda →L[ℂ]
          CCM24FiniteSFrameGramCalculus.sourceSoninCarrier lambda => operator u)
    (parameterizedSoninGramInv_mul_gram lambda alpha S halpha)
  apply congrArg (parameterizedSoninFrame lambda alpha S)
  simpa only [parameterizedSoninGram, ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.one_apply] using hu

/-- The ambient moving projection is the Euler product followed by its
source-carrier coframe. -/
theorem parameterizedCanonicalGramProjection_eq_factor_coframe
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    parameterizedCanonicalGramProjection lambda alpha S =
      parameterizedFiniteEulerFactor alpha S ∘L
        sourceInclusion lambda ∘L
        parameterizedSoninGramInv lambda alpha S halpha ∘L
        ContinuousLinearMap.adjoint (parameterizedSoninFrame lambda alpha S) := by
  unfold parameterizedCanonicalGramProjection gramCorrectedProjection
    parameterizedSoninFrame sourceInclusion
  rw [ringInverse_parameterizedSoninGram lambda alpha S halpha]
  apply ContinuousLinearMap.ext
  intro u
  rfl

/-- The complementary moving projection kills the transported source Sonin
projection before any trace or norm is taken. -/
theorem movingComplement_factor_sourceProjection_eq_zero
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    (1 - parameterizedCanonicalGramProjection lambda alpha S) ∘L
        parameterizedFiniteEulerFactor alpha S ∘L
        sourceSoninProjection lambda = 0 := by
  rw [← sourceInclusion_comp_adjoint lambda]
  rw [← ContinuousLinearMap.comp_assoc]
  change (1 - parameterizedCanonicalGramProjection lambda alpha S) ∘L
      parameterizedSoninFrame lambda alpha S ∘L
      ContinuousLinearMap.adjoint (sourceInclusion lambda) = 0
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply]
  have hfix := congrArg
    (fun operator :
        CCM24FiniteSFrameGramCalculus.sourceSoninCarrier lambda →L[ℂ]
          finiteSCarrier => operator
      (ContinuousLinearMap.adjoint (sourceInclusion lambda) u))
    (parameterizedCanonicalGramProjection_comp_frame_eq_frame
      lambda alpha S halpha)
  simp only [ContinuousLinearMap.comp_apply] at hfix
  rw [hfix]
  simp

/-- Exact Proof 261 pullback formula for the actual Gram-corrected moving
Sonin projection. All metric dependence remains in bounded outer factors. -/
theorem actualMovingSoninCrossing_eq_pullback
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    projectionLeftCrossing
        (parameterizedCanonicalGramProjection lambda alpha S)
        (parameterizedFiniteEulerGenerator alpha S) =
      movingSoninCrossingPullback lambda alpha S halpha := by
  let R := parameterizedCanonicalGramProjection lambda alpha S
  let T := parameterizedFiniteEulerFactor alpha S
  let X := parameterizedFiniteEulerGenerator alpha S
  let P := sourceSoninProjection lambda
  let A : Op := sourceInclusion lambda ∘L
    parameterizedSoninGramInv lambda alpha S halpha ∘L
      ContinuousLinearMap.adjoint (parameterizedSoninFrame lambda alpha S)
  have hR : R = T ∘L A := by
    dsimp only [R, T, A]
    exact parameterizedCanonicalGramProjection_eq_factor_coframe
      lambda alpha S halpha
  have hXT : X ∘L T = T ∘L X := by
    exact (parameterizedFiniteEulerFactor_commute_finiteGenerator
      alpha alpha S S).symm.eq
  have hzero : (1 - R) ∘L T ∘L P = 0 := by
    dsimp only [R, T, P]
    exact movingComplement_factor_sourceProjection_eq_zero
      lambda alpha S halpha
  unfold projectionLeftCrossing movingSoninCrossingPullback
    sourceSoninGeneratorCrossing
  dsimp only [R, T, X, P, A] at hR hXT hzero ⊢
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
    ContinuousLinearMap.mul_apply]
  have hr := congrArg (fun operator : Op => operator u) hR
  simp only [ContinuousLinearMap.comp_apply] at hr
  rw [hr]
  have hcomm := congrArg (fun operator : Op =>
    operator (sourceInclusion lambda
      (parameterizedSoninGramInv lambda alpha S halpha
        (ContinuousLinearMap.adjoint
          (parameterizedSoninFrame lambda alpha S) u)))) hXT
  simp only [ContinuousLinearMap.comp_apply] at hcomm
  rw [hcomm]
  let x : finiteSCarrier := parameterizedFiniteEulerGenerator alpha S
    (sourceInclusion lambda
      (parameterizedSoninGramInv lambda alpha S halpha
        (ContinuousLinearMap.adjoint
          (parameterizedSoninFrame lambda alpha S) u)))
  change (1 - parameterizedCanonicalGramProjection lambda alpha S)
      (parameterizedFiniteEulerFactor alpha S x) =
    (1 - parameterizedCanonicalGramProjection lambda alpha S)
      (parameterizedFiniteEulerFactor alpha S
        ((1 - sourceSoninProjection lambda) x))
  have hz := congrArg (fun operator : Op => operator x) hzero
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.zero_apply] at hz
  have hdecomp :
      (1 - parameterizedCanonicalGramProjection lambda alpha S)
          (parameterizedFiniteEulerFactor alpha S x) =
        (1 - parameterizedCanonicalGramProjection lambda alpha S)
            (parameterizedFiniteEulerFactor alpha S
              ((1 - sourceSoninProjection lambda) x)) +
          (1 - parameterizedCanonicalGramProjection lambda alpha S)
            (parameterizedFiniteEulerFactor alpha S
              (sourceSoninProjection lambda x)) := by
    simp only [ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.one_apply]
    rw [map_sub]
    rw [map_sub]
    abel
  rw [hz, add_zero] at hdecomp
  exact hdecomp

/-- Final exact readback: the actual Gram-corrected moving crossing is a
bounded dressing of the complete fixed-source three-branch generator ledger.
This theorem is algebraic and does not assert trace-class legality. -/
theorem actualMovingSoninCrossing_eq_threeBranchPullback
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    projectionLeftCrossing
        (parameterizedCanonicalGramProjection lambda alpha S)
        (parameterizedFiniteEulerGenerator alpha S) =
      (1 - parameterizedCanonicalGramProjection lambda alpha S) ∘L
        parameterizedFiniteEulerFactor alpha S ∘L
        ((1 - sourceSoninProjection lambda) ∘L
          (-sourceSoninGeneratorThreeBranchLedger lambda alpha S) ∘L
            sourceSoninProjection lambda) ∘L
        sourceInclusion lambda ∘L
        parameterizedSoninGramInv lambda alpha S halpha ∘L
        ContinuousLinearMap.adjoint
          (parameterizedSoninFrame lambda alpha S) := by
  rw [actualMovingSoninCrossing_eq_pullback lambda alpha S halpha]
  exact movingSoninCrossingPullback_eq_threeBranch lambda alpha S halpha

end CCM24FiniteSMovingCrossingPullback
end CCM25Concrete
end Source
end ConnesWeilRH
