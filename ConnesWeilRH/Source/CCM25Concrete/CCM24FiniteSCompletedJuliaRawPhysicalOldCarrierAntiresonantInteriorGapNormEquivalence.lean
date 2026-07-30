/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorGapNormalForm

/-!
# Two-sided recovery and norm equivalence for the interior gap

The exact normal form is compiled in the imported module before it is used
here.  This module reconstructs the synchronized gap through the forward
transition and proves the resulting uniform two-sided operator-norm bounds.

No term of the signed gap is estimated separately.  Bone 1, Gate 3U, the
finite-S sign, Burnol's identity, and RH remain open.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorGap

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCompletedJuliaJointProducer
open CCM24FiniteSCompletedJuliaRawCoframeBoundaryTelescope
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantGeometricBoundaryResolvent
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantRadialSplit
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantScalarInterior
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeJointPullback
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeOrientationLedger
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeRangeAnnihilationGuard
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeScalarRightInverse
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierSignedTelescope
open CCM24FiniteSCausalMarkov
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSProjectionTrace
open CCM24FiniteSRawLocalTraceFactorization
open CCM24FiniteSSchurMarkovPairing

noncomputable local instance sourceSoninCarrierCompleteSpaceForNormEquivalence
    (lambda : CCM24SoninScale) : CompleteSpace
      (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

local notation "SourceOp" lambda =>
  sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda

theorem signedCompressedInteriorOwner_comp_transitionAdjoint_eq_scalar_gap
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    signedCompressedInteriorOwner owner lambda p S ∘L
        (suffixEulerFrameTransition lambda p S)† =
      (primeSchurMarkovScalar p : ℂ) •
        coframeBoundaryMomentGap owner lambda p S := by
  exact comp_eq_smul_of_eq_comp_and_comp_eq_smul_id
    (signedCompressedInteriorOwner owner lambda p S)
    (coframeBoundaryMomentGap owner lambda p S)
    ((suffixEulerFrameReverseTransition lambda p S)†)
    ((suffixEulerFrameTransition lambda p S)†)
    (primeSchurMarkovScalar p : ℂ)
    (signedCompressedInteriorOwner_eq_gap_comp_reverseAdjoint
      owner lambda p S)
    (suffixEulerFrameReverseTransitionAdjoint_comp_transitionAdjoint_eq_scalar
      lambda p S)

theorem norm_signedCompressedInteriorOwner_le_gap
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    ‖signedCompressedInteriorOwner owner lambda p S‖ ≤
      ‖coframeBoundaryMomentGap owner lambda p S‖ := by
  rw [signedCompressedInteriorOwner_eq_gap_comp_reverseAdjoint]
  calc
    ‖coframeBoundaryMomentGap owner lambda p S ∘L
        (suffixEulerFrameReverseTransition lambda p S)†‖ ≤
      ‖coframeBoundaryMomentGap owner lambda p S‖ *
        ‖(suffixEulerFrameReverseTransition lambda p S)†‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ = ‖coframeBoundaryMomentGap owner lambda p S‖ *
        ‖suffixEulerFrameReverseTransition lambda p S‖ := by
      exact congrArg
        (fun value : ℝ =>
          ‖coframeBoundaryMomentGap owner lambda p S‖ * value)
        (ContinuousLinearMap.adjoint.norm_map
          (suffixEulerFrameReverseTransition lambda p S))
    _ ≤ ‖coframeBoundaryMomentGap owner lambda p S‖ * 1 := by
      exact mul_le_mul_of_nonneg_left
        (suffixEulerFrameReverseTransition_norm_le_one lambda p S)
        (norm_nonneg _)
    _ = ‖coframeBoundaryMomentGap owner lambda p S‖ := by
      rw [mul_one]

theorem one_eighth_mul_norm_gap_le_signedCompressedInteriorOwner
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    (1 / 8 : ℝ) * ‖coframeBoundaryMomentGap owner lambda p S‖ ≤
      ‖signedCompressedInteriorOwner owner lambda p S‖ := by
  have hreconstruct :=
    signedCompressedInteriorOwner_comp_transitionAdjoint_eq_scalar_gap
      owner lambda p S
  calc
    (1 / 8 : ℝ) * ‖coframeBoundaryMomentGap owner lambda p S‖ ≤
        primeSchurMarkovScalar p *
          ‖coframeBoundaryMomentGap owner lambda p S‖ :=
      mul_le_mul_of_nonneg_right
        (primeSchurMarkovScalar_ge_one_eighth p) (norm_nonneg _)
    _ = ‖(primeSchurMarkovScalar p : ℂ) •
          coframeBoundaryMomentGap owner lambda p S‖ := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (primeSchurMarkovScalar_pos p)]
    _ = ‖signedCompressedInteriorOwner owner lambda p S ∘L
          (suffixEulerFrameTransition lambda p S)†‖ := by
      rw [hreconstruct]
    _ ≤ ‖signedCompressedInteriorOwner owner lambda p S‖ *
        ‖(suffixEulerFrameTransition lambda p S)†‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ = ‖signedCompressedInteriorOwner owner lambda p S‖ *
        ‖suffixEulerFrameTransition lambda p S‖ := by
      exact congrArg
        (fun value : ℝ =>
          ‖signedCompressedInteriorOwner owner lambda p S‖ * value)
        (ContinuousLinearMap.adjoint.norm_map
          (suffixEulerFrameTransition lambda p S))
    _ ≤ ‖signedCompressedInteriorOwner owner lambda p S‖ * 1 := by
      exact mul_le_mul_of_nonneg_left
        (suffixEulerFrameTransition_norm_le_one lambda p S)
        (norm_nonneg _)
    _ = ‖signedCompressedInteriorOwner owner lambda p S‖ := by
      rw [mul_one]

theorem norm_gap_le_eight_mul_signedCompressedInteriorOwner
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    ‖coframeBoundaryMomentGap owner lambda p S‖ ≤
      8 * ‖signedCompressedInteriorOwner owner lambda p S‖ := by
  have hlower :=
    one_eighth_mul_norm_gap_le_signedCompressedInteriorOwner
      owner lambda p S
  nlinarith [norm_nonneg
    (coframeBoundaryMomentGap owner lambda p S),
    norm_nonneg (signedCompressedInteriorOwner owner lambda p S)]

end CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorGap
end CCM25Concrete
end Source
end ConnesWeilRH
