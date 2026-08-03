/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSGatePhysicalCausalCompletedBracket
import ConnesWeilRH.Source.CCM25Concrete.CCM24RadialBoundaryPairTransport
import ConnesWeilRH.Source.CCM25Concrete.CCM24SourceProlateTrace
import Mathlib.Tactic.NoncommRing

/-!
# Hardy--prolate Gram completion of the causal finite-S bracket

The completed source band `E - R_0` has two coupled pieces.  The first is the
actual Hardy--Titchmarsh Fourier leakage and the second is the actual prolate
factor.  This module packages them as one Gram identity:

`E - R_0 = (F H E)^* (F H E) + (Q(E - R_0))^* Q(E - R_0)`.

Here `E` is the radial support projection, `F = I - E`, and `Q = H E H` is
the genuine source Fourier-support projection.  This is an exact source
normal form only.  It does not license separate Hilbert--Schmidt or trace-norm
estimates of the two summands.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSGatePhysicalHardyProlateGram

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSCausalSupport
open CCM24FiniteSBandTrace
open CCM24FiniteSGatePhysicalCausalCompletedBracket
open CCM24FiniteSGatePhysicalCausalDualFrameCorner
open CCM24FiniteSGatePhysicalMetricDetectorCorner
open CCM24FiniteSGatePhysicalNormalizedDoubleBoundaryReduction
open CCM24FiniteSGramOrderingBridge
open CCM24FiniteSGramResponse
open CCM24FiniteSProjectionTrace
open CCM24FiniteSRootCompletedFirstJet
open CCM24RadialBoundaryPairTransport
open CCM24SourceProlateTrace

local notation "Op" => finiteSCarrier →L[ℂ] finiteSCarrier

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- The actual Fourier leakage from the radial half-line after the
Hardy--Titchmarsh involution. -/
noncomputable def sourceHardyFourierLeakageFactor (lambda : CCM24SoninScale) : Op :=
  radialComplementProjection lambda ∘L
    archimedeanHardyTitchmarshOperator ∘L radialSupportProjection lambda

/-- Keep the Fourier leakage and the prolate square root in one completed
Gram object.  Downstream estimates must retain this sum before taking an
absolute value. -/
noncomputable def sourceHardyProlateCompletedGram (lambda : CCM24SoninScale) : Op :=
  (sourceHardyFourierLeakageFactor lambda).adjoint ∘L
      sourceHardyFourierLeakageFactor lambda +
    (sourceProlateHilbertSchmidtFactor lambda).adjoint ∘L
      sourceProlateHilbertSchmidtFactor lambda

private theorem radialComplementProjection_adjoint_eq_self
    (lambda : CCM24SoninScale) :
    (radialComplementProjection lambda).adjoint = radialComplementProjection lambda := by
  unfold radialComplementProjection
  rw [map_sub, ContinuousLinearMap.adjoint_id,
    (radialSupportProjection_isStarProjection lambda).isSelfAdjoint.adjoint_eq]

private theorem radialComplementProjection_comp_self
    (lambda : CCM24SoninScale) :
    radialComplementProjection lambda ∘L radialComplementProjection lambda =
      radialComplementProjection lambda := by
  have hE : radialSupportProjection lambda * radialSupportProjection lambda =
      radialSupportProjection lambda := by
    simpa only [ContinuousLinearMap.mul_def] using
      (radialSupportProjection_isStarProjection lambda).isIdempotentElem
  unfold radialComplementProjection
  simpa only [ContinuousLinearMap.mul_def] using show
    (1 - radialSupportProjection lambda) *
        (1 - radialSupportProjection lambda) =
      1 - radialSupportProjection lambda by
    calc
      (1 - radialSupportProjection lambda) *
          (1 - radialSupportProjection lambda) =
        1 - radialSupportProjection lambda - radialSupportProjection lambda +
          radialSupportProjection lambda * radialSupportProjection lambda := by
          noncomm_ring
      _ = 1 - radialSupportProjection lambda := by
        rw [hE]
        abel

/-- The actual Fourier complement is the Hardy--Titchmarsh conjugate of the
opposite radial half-line. -/
private theorem hardyTitchmarsh_comp_radialComplement_comp_hardy_eq_fourierComplement
    (lambda : CCM24SoninScale) :
    archimedeanHardyTitchmarshOperator ∘L radialComplementProjection lambda ∘L
        archimedeanHardyTitchmarshOperator =
      1 - sourceFourierSupportProjection lambda := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply, radialComplementProjection,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.one_apply, map_sub]
  rw [archimedeanHardyTitchmarshOperator_involutive]
  rw [sourceFourierSupportProjection_eq_hardyTitchmarsh_conjugation]
  rfl

/-- The first completed Gram summand is the actual radial/Fourier complement
corner. -/
theorem sourceHardyFourierLeakageFactor_adjoint_comp_self_eq_fourierComplement
    (lambda : CCM24SoninScale) :
    (sourceHardyFourierLeakageFactor lambda).adjoint ∘L
        sourceHardyFourierLeakageFactor lambda =
      radialSupportProjection lambda ∘L
        (1 - sourceFourierSupportProjection lambda) ∘L
          radialSupportProjection lambda := by
  rw [sourceHardyFourierLeakageFactor, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_comp,
    (radialSupportProjection_isStarProjection lambda).isSelfAdjoint.adjoint_eq,
    archimedeanHardyTitchmarshOperator_isSelfAdjoint.adjoint_eq,
    radialComplementProjection_adjoint_eq_self]
  apply ContinuousLinearMap.ext
  intro u
  have hFF := DFunLike.congr_fun (radialComplementProjection_comp_self lambda)
    (archimedeanHardyTitchmarshOperator (radialSupportProjection lambda u))
  simp only [ContinuousLinearMap.comp_apply] at hFF
  have hconj := DFunLike.congr_fun
    (hardyTitchmarsh_comp_radialComplement_comp_hardy_eq_fourierComplement lambda)
    (radialSupportProjection lambda u)
  simp only [ContinuousLinearMap.comp_apply] at hconj
  simp only [ContinuousLinearMap.comp_apply]
  rw [hFF]
  exact congrArg (radialSupportProjection lambda) hconj

/-- The literal source quotient band is one Hardy/Fourier-plus-prolate Gram.
This uses the genuine real-line Hardy--Titchmarsh involution; it is not a
generic pair-of-projections replacement. -/
theorem sourceHardyProlateCompletedGram_eq_sourceBandProjection
    (lambda : CCM24SoninScale) :
    sourceHardyProlateCompletedGram lambda = sourceBandProjection lambda := by
  rw [sourceHardyProlateCompletedGram,
    sourceHardyFourierLeakageFactor_adjoint_comp_self_eq_fourierComplement,
    sourceProlateHilbertSchmidtFactor_adjoint_comp_self,
    radial_fourierComplement_radial_eq_band_sub_prolate]
  abel

/-- The causal source complement with its actual Hardy/Fourier and prolate
components retained in a single Gram object. -/
noncomputable def finiteEulerCausalHardyProlateCompletedSoninComplement
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) : Op :=
  radialSupportProjection lambda ∘L finiteEulerTransportOperator family ∘L
      radialComplementProjection lambda +
    finiteEulerTransportOperator family ∘L sourceHardyProlateCompletedGram lambda

/-- The new Hardy--prolate form is exactly Proof 777's causal completed
bracket. -/
theorem finiteEulerCausalHardyProlateCompletedSoninComplement_eq_causalCompleted
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteEulerCausalHardyProlateCompletedSoninComplement lambda family =
      finiteEulerCausalCompletedSoninComplement lambda family := by
  rw [finiteEulerCausalHardyProlateCompletedSoninComplement,
    finiteEulerCausalCompletedSoninComplement,
    sourceHardyProlateCompletedGram_eq_sourceBandProjection,
    sourceCausalCompletedBand_eq_sourceBandProjection]

/-- The literal target is a causal outer crossing plus one actual
Hardy--prolate Gram completion before the compact root acts. -/
theorem finiteEulerTargetCommutatorResponse_eq_causalHardyProlateRootCorner
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteEulerTargetCommutatorResponse owner lambda family =
      (finiteEulerDualFrame lambda family).adjoint ∘L
        finiteEulerCausalHardyProlateCompletedSoninComplement lambda family ∘L
          (rootConvolution owner).adjoint ∘L rootConvolution owner ∘L
            sourceInclusion lambda := by
  rw [finiteEulerTargetCommutatorResponse_eq_causalCompletedProlateRootCorner,
    finiteEulerCausalHardyProlateCompletedSoninComplement_eq_causalCompleted]

end CCM24FiniteSGatePhysicalHardyProlateGram
end CCM25Concrete
end Source
end ConnesWeilRH
