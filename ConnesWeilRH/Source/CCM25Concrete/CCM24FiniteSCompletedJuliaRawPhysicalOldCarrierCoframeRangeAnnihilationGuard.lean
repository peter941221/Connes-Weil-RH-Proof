/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeJointPullback
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeJointGapResponse

/-!
# Range-annihilation guard for the complete old-carrier telescope

The generic range factorization in Proof 602 is a boundary-channel tool.  If
its annihilation premise is applied to the complete signed telescope, the
exact pullback ledger reduces that premise to the vanishing of the
synchronized boundary-moment gap.  The reverse transition is not a lossy
contraction: it has a two-sided scalar inverse, so its adjoint can be cancelled
as well.

This file records that boundary precisely.  It does not claim that the gap
vanishes, and it does not turn a bounded row into a readout.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeRangeAnnihilationGuard

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCompletedJuliaRawPhysicalFactorization
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeScalarRightInverse
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeJointGapResponse
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeJointPullback
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierSignedTelescope
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSSchurMarkovPairing

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace
      (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

local notation "SourceOp" lambda =>
  sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda

/-! ## The adjoint scalar inverse -/

theorem suffixEulerFrameReverseTransitionAdjoint_comp_transitionAdjoint_eq_scalar
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    (suffixEulerFrameReverseTransition lambda p S)† ∘L
        (suffixEulerFrameTransition lambda p S)† =
      (primeSchurMarkovScalar p : ℂ) •
        ContinuousLinearMap.id ℂ (sourceSoninCarrier lambda) := by
  have hscalarAdjoint :
      ContinuousLinearMap.adjoint
          ((primeSchurMarkovScalar p : ℂ) •
            ContinuousLinearMap.id ℂ (sourceSoninCarrier lambda)) =
        (primeSchurMarkovScalar p : ℂ) •
          ContinuousLinearMap.id ℂ (sourceSoninCarrier lambda) := by
    have hstar : star (primeSchurMarkovScalar p : ℂ) =
        (primeSchurMarkovScalar p : ℂ) := by
      rw [RCLike.star_def, Complex.conj_ofReal]
    simpa only [map_smulₛₗ, hstar, starRingEnd_apply,
      ContinuousLinearMap.adjoint_id] using
      (ContinuousLinearMap.adjoint.map_smulₛₗ
        (primeSchurMarkovScalar p : ℂ)
        (ContinuousLinearMap.id ℂ (sourceSoninCarrier lambda)))
  have h := congrArg ContinuousLinearMap.adjoint
    (suffixEulerFrameTransition_comp_reverse lambda p S)
  simpa only [ContinuousLinearMap.adjoint_comp, hscalarAdjoint] using h

/-! ## The exact annihilation boundary -/

theorem comp_eq_zero_iff_eq_zero_of_comp_eq_smul_id
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (X B A : H →L[ℂ] H) (rho : ℂ) (hrho : rho ≠ 0)
    (hBA : B ∘L A = rho • ContinuousLinearMap.id ℂ H) :
    X ∘L B = 0 ↔ X = 0 := by
  constructor
  · intro hzero
    have hcomp := congrArg
      (fun operator : H →L[ℂ] H => operator ∘L A) hzero
    have hcomp' : X ∘L (B ∘L A) = 0 := by
      calc
        X ∘L (B ∘L A) = (X ∘L B) ∘L A := by
          simp only [ContinuousLinearMap.comp_assoc]
        _ = 0 ∘L A := hcomp
        _ = 0 := by simp
    rw [hBA] at hcomp'
    apply ContinuousLinearMap.ext
    intro x
    have hx := DFunLike.congr_fun hcomp' x
    have hscalar : rho • X x = 0 := by
      simpa only [ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
        map_smul, ContinuousLinearMap.zero_apply] using hx
    exact (smul_eq_zero.mp hscalar).resolve_left hrho
  · intro hzero
    rw [hzero]
    simp

/-- The complete telescope kills the scalar-normalized new-frame range
exactly when the synchronized boundary-moment gap vanishes.  The proof uses
the already established pullback identity and cancels the adjoint reverse
transition with the adjoint forward transition. -/
theorem suffixActualBandRawPhysicalOldCarrierSignedTelescope_comp_scalarNormalizedInverseAdjoint_comp_newFrame_eq_zero_iff_gap_eq_zero
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    (suffixActualBandRawPhysicalOldCarrierSignedTelescope owner lambda p S) ∘L
        (scalarNormalizedPrimeEulerInverse p)† ∘L
          (suffixEulerFrameSchurStep lambda p S).newFrame = 0 ↔
      coframeBoundaryMomentGap owner lambda p S = 0 := by
  have hrho : (primeSchurMarkovScalar p : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (primeSchurMarkovScalar_pos p))
  have hrhoInv : (primeSchurMarkovScalar p : ℂ)⁻¹ ≠ 0 :=
    inv_ne_zero hrho
  have hreverse :
      coframeBoundaryMomentGap owner lambda p S ∘L
          (suffixEulerFrameReverseTransition lambda p S)† = 0 ↔
        coframeBoundaryMomentGap owner lambda p S = 0 :=
    comp_eq_zero_iff_eq_zero_of_comp_eq_smul_id
      (coframeBoundaryMomentGap owner lambda p S)
      ((suffixEulerFrameReverseTransition lambda p S)†)
      ((suffixEulerFrameTransition lambda p S)†)
      (primeSchurMarkovScalar p : ℂ) hrho
      (suffixEulerFrameReverseTransitionAdjoint_comp_transitionAdjoint_eq_scalar
        lambda p S)
  constructor
  · intro hzero
    have hscaled :
        (primeSchurMarkovScalar p : ℂ)⁻¹ •
            (coframeBoundaryMomentGap owner lambda p S ∘L
              (suffixEulerFrameReverseTransition lambda p S)†) = 0 := by
      rw [← suffixActualBandRawPhysicalOldCarrierSignedTelescope_comp_scalarNormalizedInverseAdjoint_comp_newFrame_eq
        owner lambda p S]
      exact hzero
    apply hreverse.mp
    exact (smul_eq_zero.mp hscaled).resolve_left hrhoInv
  · intro hgap
    rw [suffixActualBandRawPhysicalOldCarrierSignedTelescope_comp_scalarNormalizedInverseAdjoint_comp_newFrame_eq,
      hgap]
    simp

/-- The same guard in the named physical row coordinates. -/
theorem suffixActualBandRawPhysicalOldCarrierSignedTelescope_comp_scalarNormalizedInverseAdjoint_comp_newFrame_eq_zero_iff_rawPhysicalFourTermRow_eq_zero
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    (suffixActualBandRawPhysicalOldCarrierSignedTelescope owner lambda p S) ∘L
        (scalarNormalizedPrimeEulerInverse p)† ∘L
          (suffixEulerFrameSchurStep lambda p S).newFrame = 0 ↔
      suffixActualBandRawPhysicalFourTermRow owner lambda p S = 0 := by
  rw [suffixActualBandRawPhysicalOldCarrierSignedTelescope_comp_scalarNormalizedInverseAdjoint_comp_newFrame_eq_zero_iff_gap_eq_zero,
    coframeBoundaryMomentGap_eq_rawPhysicalFourTermRow]

end CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeRangeAnnihilationGuard
end CCM25Concrete
end Source
end ConnesWeilRH
