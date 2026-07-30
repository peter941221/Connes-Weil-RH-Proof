/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorOnePrimeScaledTargetSize
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierBlockReduction

/-!
# The suffix-independent adjacent projection gap

The complete suffix Schur--Markov scalar can collapse along long lists, so it
cannot be removed from Proof 645's normalized row estimate.  The actual
adjacent Sonin subspaces do not have this loss.  The forward and reverse
one-prime Euler maps both differ from the identity by at most `2 q_p`, and
they map the two adjacent polar-frame ranges into one another.  Therefore

```text
||P_(p::S) - P_S|| <= 4 q_p
```

for every literal suffix `S`.  Consequently, for every bounded detector `W`,

```text
||[P_(p::S),W] - [P_S,W]|| <= 8 q_p ||W||.
```

This closes the suffix-independent orthogonal-geometry part of the scaled
target-size gate.  It does not yet identify the complete raw coframe response
with this projection commutator.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorAdjacentProjectionGap

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open _root_.ConnesWeilRH.CC20Concrete
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCausalMarkov
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierBlockReduction
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierFixedSourceKernelGuard
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierMomentDecay
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSProjectionTrace
open CCM24FiniteSSchurMarkovPairing

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! ## Generic two-sided range perturbation -/

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace Complex H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace Complex K] [CompleteSpace K]

/-- If a transport maps one isometric frame into another, the old-frame
complement annihilates the transported new-frame projection. -/
theorem frameComplement_comp_transport_comp_frameProjection_eq_zero
    (oldFrame newFrame : H →L[Complex] K)
    (transport : K →L[Complex] K) (transition : H →L[Complex] H)
    (hold : oldFrame† ∘L oldFrame = ContinuousLinearMap.id Complex H)
    (htransport : transport ∘L newFrame = oldFrame ∘L transition) :
    (ContinuousLinearMap.id Complex K - oldFrame ∘L oldFrame†) ∘L
        transport ∘L (newFrame ∘L newFrame†) = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  have htransportPoint :
      transport (newFrame ((newFrame†) x)) =
        oldFrame (transition ((newFrame†) x)) := by
    simpa only [ContinuousLinearMap.comp_apply] using
      DFunLike.congr_fun htransport ((newFrame†) x)
  have holdPoint :
      (oldFrame†) (oldFrame (transition ((newFrame†) x))) =
        transition ((newFrame†) x) := by
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] using
      DFunLike.congr_fun hold (transition ((newFrame†) x))
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]
  rw [htransportPoint, holdPoint]
  simp

/-- Two near-identity transports in opposite directions control the gap
between their two isometric-frame range projections. -/
theorem norm_frameProjection_sub_frameProjection_le_nearIdentity_add
    (oldFrame newFrame : H →L[Complex] K)
    (forward reverse : K →L[Complex] K)
    (transition reverseTransition : H →L[Complex] H)
    (forwardBound reverseBound : Real)
    (hold : oldFrame† ∘L oldFrame = ContinuousLinearMap.id Complex H)
    (hnew : newFrame† ∘L newFrame = ContinuousLinearMap.id Complex H)
    (hforward : forward ∘L newFrame = oldFrame ∘L transition)
    (hreverse : reverse ∘L oldFrame = newFrame ∘L reverseTransition)
    (hforwardNear :
      ‖forward - ContinuousLinearMap.id Complex K‖ ≤ forwardBound)
    (hreverseNear :
      ‖reverse - ContinuousLinearMap.id Complex K‖ ≤ reverseBound) :
    ‖oldFrame ∘L oldFrame† - newFrame ∘L newFrame†‖ ≤
      forwardBound + reverseBound := by
  let oldProjection := oldFrame ∘L oldFrame†
  let newProjection := newFrame ∘L newFrame†
  have holdProjection : IsStarProjection oldProjection := by
    simpa only [oldProjection] using
      frame_comp_adjoint_isStarProjection oldFrame hold
  have hnewProjection : IsStarProjection newProjection := by
    simpa only [newProjection] using
      frame_comp_adjoint_isStarProjection newFrame hnew
  have hforwardZero :
      (ContinuousLinearMap.id Complex K - oldProjection) ∘L forward ∘L
          newProjection = 0 := by
    simpa only [oldProjection, newProjection] using
      frameComplement_comp_transport_comp_frameProjection_eq_zero
        oldFrame newFrame forward transition hold hforward
  have hreverseZero :
      (ContinuousLinearMap.id Complex K - newProjection) ∘L reverse ∘L
          oldProjection = 0 := by
    simpa only [oldProjection, newProjection] using
      frameComplement_comp_transport_comp_frameProjection_eq_zero
        newFrame oldFrame reverse reverseTransition hnew hreverse
  have hforwardGap :
      (ContinuousLinearMap.id Complex K - oldProjection) ∘L newProjection =
        (ContinuousLinearMap.id Complex K - oldProjection) ∘L
          (ContinuousLinearMap.id Complex K - forward) ∘L
            newProjection := by
    apply ContinuousLinearMap.ext
    intro x
    have hzero := DFunLike.congr_fun hforwardZero x
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.zero_apply, map_sub] at hzero ⊢
    rw [hzero, sub_zero]
  have hreverseGap :
      (ContinuousLinearMap.id Complex K - newProjection) ∘L oldProjection =
        (ContinuousLinearMap.id Complex K - newProjection) ∘L
          (ContinuousLinearMap.id Complex K - reverse) ∘L
            oldProjection := by
    apply ContinuousLinearMap.ext
    intro x
    have hzero := DFunLike.congr_fun hreverseZero x
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.zero_apply, map_sub] at hzero ⊢
    rw [hzero, sub_zero]
  have hforwardNear' :
      ‖ContinuousLinearMap.id Complex K - forward‖ ≤ forwardBound := by
    rw [show ContinuousLinearMap.id Complex K - forward =
        -(forward - ContinuousLinearMap.id Complex K) by abel, norm_neg]
    exact hforwardNear
  have hreverseNear' :
      ‖ContinuousLinearMap.id Complex K - reverse‖ ≤ reverseBound := by
    rw [show ContinuousLinearMap.id Complex K - reverse =
        -(reverse - ContinuousLinearMap.id Complex K) by abel, norm_neg]
    exact hreverseNear
  have hforwardBoundNonneg : 0 ≤ forwardBound :=
    (norm_nonneg _).trans hforwardNear
  have hreverseBoundNonneg : 0 ≤ reverseBound :=
    (norm_nonneg _).trans hreverseNear
  have hforwardGapNorm :
      ‖(ContinuousLinearMap.id Complex K - oldProjection) ∘L
          newProjection‖ ≤ forwardBound := by
    rw [hforwardGap]
    calc
      ‖(ContinuousLinearMap.id Complex K - oldProjection) ∘L
          (ContinuousLinearMap.id Complex K - forward) ∘L
            newProjection‖ ≤
          ‖ContinuousLinearMap.id Complex K - oldProjection‖ *
            ‖(ContinuousLinearMap.id Complex K - forward) ∘L
              newProjection‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 *
          (‖ContinuousLinearMap.id Complex K - forward‖ *
            ‖newProjection‖) := by
        exact mul_le_mul
          (IsStarProjection.norm_le _ holdProjection.one_sub)
          (ContinuousLinearMap.opNorm_comp_le _ _)
          (norm_nonneg _) zero_le_one
      _ ≤ 1 * (forwardBound * 1) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul hforwardNear'
            (IsStarProjection.norm_le _ hnewProjection)
            (norm_nonneg _) hforwardBoundNonneg)
          zero_le_one
      _ = forwardBound := by ring
  have hreverseGapNorm :
      ‖(ContinuousLinearMap.id Complex K - newProjection) ∘L
          oldProjection‖ ≤ reverseBound := by
    rw [hreverseGap]
    calc
      ‖(ContinuousLinearMap.id Complex K - newProjection) ∘L
          (ContinuousLinearMap.id Complex K - reverse) ∘L
            oldProjection‖ ≤
          ‖ContinuousLinearMap.id Complex K - newProjection‖ *
            ‖(ContinuousLinearMap.id Complex K - reverse) ∘L
              oldProjection‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 *
          (‖ContinuousLinearMap.id Complex K - reverse‖ *
            ‖oldProjection‖) := by
        exact mul_le_mul
          (IsStarProjection.norm_le _ hnewProjection.one_sub)
          (ContinuousLinearMap.opNorm_comp_le _ _)
          (norm_nonneg _) zero_le_one
      _ ≤ 1 * (reverseBound * 1) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul hreverseNear'
            (IsStarProjection.norm_le _ holdProjection)
            (norm_nonneg _) hreverseBoundNonneg)
          zero_le_one
      _ = reverseBound := by ring
  have hreverseAdjointNorm :
      ‖oldProjection ∘L
          (ContinuousLinearMap.id Complex K - newProjection)‖ =
        ‖(ContinuousLinearMap.id Complex K - newProjection) ∘L
          oldProjection‖ := by
    have hnewComplementSelf :
        IsSelfAdjoint
          (ContinuousLinearMap.id Complex K - newProjection) := by
      change IsSelfAdjoint (1 - newProjection)
      exact hnewProjection.one_sub.isSelfAdjoint
    calc
      ‖oldProjection ∘L
          (ContinuousLinearMap.id Complex K - newProjection)‖ =
          ‖(oldProjection ∘L
            (ContinuousLinearMap.id Complex K - newProjection))†‖ := by
        symm
        exact ContinuousLinearMap.adjoint.norm_map _
      _ = ‖(ContinuousLinearMap.id Complex K - newProjection) ∘L
          oldProjection‖ := by
        rw [ContinuousLinearMap.adjoint_comp,
          holdProjection.isSelfAdjoint.adjoint_eq,
          hnewComplementSelf.adjoint_eq]
  have hprojectionDifference :
      oldProjection - newProjection =
        oldProjection ∘L
            (ContinuousLinearMap.id Complex K - newProjection) -
          (ContinuousLinearMap.id Complex K - oldProjection) ∘L
            newProjection := by
    apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, map_sub]
    abel
  change ‖oldProjection - newProjection‖ ≤
    forwardBound + reverseBound
  rw [hprojectionDifference]
  calc
    ‖oldProjection ∘L
          (ContinuousLinearMap.id Complex K - newProjection) -
        (ContinuousLinearMap.id Complex K - oldProjection) ∘L
          newProjection‖ ≤
      ‖oldProjection ∘L
          (ContinuousLinearMap.id Complex K - newProjection)‖ +
        ‖(ContinuousLinearMap.id Complex K - oldProjection) ∘L
          newProjection‖ := norm_sub_le _ _
    _ ≤ reverseBound + forwardBound := by
      rw [hreverseAdjointNorm]
      exact add_le_add hreverseGapNorm hforwardGapNorm
    _ = forwardBound + reverseBound := by ring

/-! ## The actual adjacent Sonin projections -/

noncomputable def oldSuffixRangeProjection
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    finiteSCarrier →L[Complex] finiteSCarrier :=
  oldSuffixFrame lambda p S ∘L (oldSuffixFrame lambda p S)†

noncomputable def newSuffixRangeProjection
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    finiteSCarrier →L[Complex] finiteSCarrier :=
  newSuffixFrame lambda S ∘L (newSuffixFrame lambda S)†

/-- The normalized forward one-prime transport itself, not only its adjoint,
is within `2 q_p` of the identity. -/
theorem normalizedPrimeEulerFrameTransport_sub_id_norm_le_two_coefficient
    (p : CCM24VisiblePrime) :
    ‖normalizedPrimeEulerFrameTransport p -
        ContinuousLinearMap.id Complex finiteSCarrier‖ ≤
      2 * ccm24PrimeEulerCoefficient p := by
  have hsub (A B : finiteSCarrier →L[Complex] finiteSCarrier) :
      (A - B)† = A† - B† := by
    apply ContinuousLinearMap.ext
    intro x
    exact ext_inner_right Complex fun y => by
      simp only [ContinuousLinearMap.adjoint_inner_left,
        ContinuousLinearMap.sub_apply, inner_sub_left, inner_sub_right]
  calc
    ‖normalizedPrimeEulerFrameTransport p -
        ContinuousLinearMap.id Complex finiteSCarrier‖ =
      ‖(normalizedPrimeEulerFrameTransport p -
        ContinuousLinearMap.id Complex finiteSCarrier)†‖ := by
          symm
          exact ContinuousLinearMap.adjoint.norm_map _
    _ = ‖(normalizedPrimeEulerFrameTransport p)† -
        ContinuousLinearMap.id Complex finiteSCarrier‖ := by
      rw [hsub, ContinuousLinearMap.adjoint_id]
    _ ≤ 2 * ccm24PrimeEulerCoefficient p :=
      normalizedPrimeEulerFrameTransport_adjoint_sub_id_norm_le_two_coefficient p

/-- The probability-normalized reverse one-prime transport is also within
`2 q_p` of the identity. -/
theorem normalizedPrimeEulerInverse_sub_id_norm_le_two_coefficient
    (p : CCM24VisiblePrime) :
    ‖normalizedPrimeEulerInverse p -
        ContinuousLinearMap.id Complex finiteSCarrier‖ ≤
      2 * ccm24PrimeEulerCoefficient p := by
  simpa only [normalizedPrimeEulerInverse] using
    norm_lowerPrimeEulerInverse_sub_id_le_two_mul_coefficient p

/-- Every adjacent pair of actual finite-S Sonin range projections differs
by `O(q_p)`, with no suffix Schur--Markov scalar. -/
theorem norm_oldSuffixRangeProjection_sub_newSuffixRangeProjection_le
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    ‖oldSuffixRangeProjection lambda p S -
        newSuffixRangeProjection lambda S‖ ≤
      4 * ccm24PrimeEulerCoefficient p := by
  have hold : (oldSuffixFrame lambda p S)† ∘L
      oldSuffixFrame lambda p S =
        ContinuousLinearMap.id Complex (sourceSoninCarrier lambda) := by
    exact (suffixEulerFrameSchurStep lambda p S).oldFrame_isometry
  have hnew : (newSuffixFrame lambda S)† ∘L
      newSuffixFrame lambda S =
        ContinuousLinearMap.id Complex (sourceSoninCarrier lambda) := by
    exact (suffixEulerFrameSchurStep lambda p S).newFrame_isometry
  have hforward : normalizedPrimeEulerFrameTransport p ∘L
      newSuffixFrame lambda S =
        oldSuffixFrame lambda p S ∘L
          suffixEulerFrameTransition lambda p S := by
    exact (suffixEulerFrameSchurStep lambda p S).transport_intertwining
  have hreverse : normalizedPrimeEulerInverse p ∘L
      oldSuffixFrame lambda p S =
        newSuffixFrame lambda S ∘L
          suffixEulerFrameReverseTransition lambda p S :=
    normalizedPrimeEulerInverse_comp_oldFrame lambda p S
  simpa only [oldSuffixRangeProjection, newSuffixRangeProjection,
    show 2 * ccm24PrimeEulerCoefficient p +
        2 * ccm24PrimeEulerCoefficient p =
      4 * ccm24PrimeEulerCoefficient p by ring] using
    norm_frameProjection_sub_frameProjection_le_nearIdentity_add
      (oldSuffixFrame lambda p S) (newSuffixFrame lambda S)
      (normalizedPrimeEulerFrameTransport p)
      (normalizedPrimeEulerInverse p)
      (suffixEulerFrameTransition lambda p S)
      (suffixEulerFrameReverseTransition lambda p S)
      (2 * ccm24PrimeEulerCoefficient p)
      (2 * ccm24PrimeEulerCoefficient p)
      hold hnew hforward hreverse
      (normalizedPrimeEulerFrameTransport_sub_id_norm_le_two_coefficient p)
      (normalizedPrimeEulerInverse_sub_id_norm_le_two_coefficient p)

/-! ## Detector commutator consequence -/

/-- The commutator is linear in its projection slot. -/
theorem cc20Commutator_sub_cc20Commutator_eq
    (P Q W : finiteSCarrier →L[Complex] finiteSCarrier) :
    cc20Commutator P W - cc20Commutator Q W =
      cc20Commutator (P - Q) W := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [cc20Commutator, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, map_sub]
  abel

/-- A commutator costs at most twice the product of the two operator norms. -/
theorem norm_cc20Commutator_le_two_mul
    (P W : finiteSCarrier →L[Complex] finiteSCarrier) :
    ‖cc20Commutator P W‖ ≤ 2 * ‖P‖ * ‖W‖ := by
  unfold cc20Commutator
  calc
    ‖P ∘L W - W ∘L P‖ ≤ ‖P ∘L W‖ + ‖W ∘L P‖ :=
      norm_sub_le _ _
    _ ≤ ‖P‖ * ‖W‖ + ‖W‖ * ‖P‖ :=
      add_le_add (ContinuousLinearMap.opNorm_comp_le _ _)
        (ContinuousLinearMap.opNorm_comp_le _ _)
    _ = 2 * ‖P‖ * ‖W‖ := by ring

/-- Every detector commutator sees only the current one-prime projection
variation, uniformly over the suffix. -/
theorem norm_adjacentSuffixProjectionCommutatorDifference_le
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime)
    (W : finiteSCarrier →L[Complex] finiteSCarrier) :
    ‖cc20Commutator (oldSuffixRangeProjection lambda p S) W -
        cc20Commutator (newSuffixRangeProjection lambda S) W‖ ≤
      8 * ccm24PrimeEulerCoefficient p * ‖W‖ := by
  rw [cc20Commutator_sub_cc20Commutator_eq]
  calc
    ‖cc20Commutator
        (oldSuffixRangeProjection lambda p S -
          newSuffixRangeProjection lambda S) W‖ ≤
      2 * ‖oldSuffixRangeProjection lambda p S -
        newSuffixRangeProjection lambda S‖ * ‖W‖ :=
          norm_cc20Commutator_le_two_mul _ _
    _ ≤ 2 * (4 * ccm24PrimeEulerCoefficient p) * ‖W‖ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (norm_oldSuffixRangeProjection_sub_newSuffixRangeProjection_le
            lambda p S) (by norm_num))
        (norm_nonneg W)
    _ = 8 * ccm24PrimeEulerCoefficient p * ‖W‖ := by ring

end
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorAdjacentProjectionGap
end CCM25Concrete
end Source
end ConnesWeilRH
