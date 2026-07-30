/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Analysis.InnerProductSpace.Adjoint
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeJointGapResponse

/-!
# Response-facing readout for the complete old-carrier gap

The complete response is the useful source-facing object

```text
L_(p,S) = rho_p * R_(p::S) - T_(p,S) * R_S * reverseT_(p,S).
```

The existing gap readout is equivalent to the adjoint response factor

```text
oldFrame * L_(p,S) * transition
  = -rho_p * oldCarrierAnalysis^dagger * K_(p,S),
```

where `K_(p,S)` has the same source-to-ambient norm bound as the gap readout.
This is an exact change of producer coordinates.  It keeps the complete
response and the transition orientation together; it does not assume that the
gap vanishes and it does not produce the missing source factor.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeJointGapResponseReadout

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCompletedJuliaAmbientDefectFactorization
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierReduction
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeJointGapReadout
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeJointGapResponse
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeJointPullback
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeOrientationLedger
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSSchurMarkovPairing

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace
      (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

local notation "SourceOp" lambda =>
  sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda

/-! ## Response-facing producer contract -/

/-- A source factor for the complete response, written in the coordinates that
are adjoint to the old-carrier gap readout. -/
structure SuffixRawOldCarrierCoframeJointGapResponseReadoutData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (bound : ℝ) where
  bound_nonneg : 0 ≤ bound
  factor : sourceSoninCarrier lambda →L[ℂ]
    suffixEulerFrameAmbientBoundaryCarrier
  factor_norm_le : ‖factor‖ ≤ bound
  response_factorization :
    (suffixEulerFrameSchurStep lambda p S).oldFrame ∘L
        suffixActualBandRawPhysicalOldCarrierCoframeJointGapResponse
          owner lambda p S ∘L
          suffixEulerFrameTransition lambda p S =
      -((primeSchurMarkovScalar p : ℂ) •
        ((suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S)† ∘L
          factor))

/-! ## Scalar cancellation used by both directions -/

theorem eq_of_neg_smul_eq_neg_smul
    {H K : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup K] [NormedSpace ℂ K]
    {X Y : H →L[ℂ] K} {rho : ℂ} (hrho : rho ≠ 0)
    (h : -(rho • X) = -(rho • Y)) : X = Y := by
  apply ContinuousLinearMap.ext
  intro x
  have hx := DFunLike.congr_fun h x
  have hneg : rho • X x = rho • Y x := by
    exact neg_injective hx
  have hzero : rho • (X x - Y x) = 0 := by
    rw [smul_sub, hneg]
    simp
  exact sub_eq_zero.mp ((smul_eq_zero.mp hzero).resolve_left hrho)

/-! ## Response factor -> gap readout -/

/-- The response factor produces the original gap-facing readout by adjointing
the source-to-ambient factor. -/
noncomputable def
    SuffixRawOldCarrierCoframeJointGapResponseReadoutData.toJointGapReadoutData
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {bound : ℝ}
    (data : SuffixRawOldCarrierCoframeJointGapResponseReadoutData owner
      lambda p S bound) :
    SuffixRawOldCarrierCoframeJointGapReadoutData owner lambda p S bound := by
  have hrho : (primeSchurMarkovScalar p : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (primeSchurMarkovScalar_pos p))
  have hresponse :=
    suffixActualBandRawPhysicalOldCarrierCoframeJointGapResponse_comp_transition_eq_neg_scalar_gap_adjoint
      owner lambda p S
  have hscaled :
      -((primeSchurMarkovScalar p : ℂ) •
          (((suffixEulerFrameSchurStep lambda p S).oldFrame ∘L
            (coframeBoundaryMomentGap owner lambda p S)†))) =
        -((primeSchurMarkovScalar p : ℂ) •
          ((suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S)† ∘L
            data.factor)) := by
    apply ContinuousLinearMap.ext
    intro x
    have hresponse' := congrArg
      (fun T : SourceOp lambda =>
        (suffixEulerFrameSchurStep lambda p S).oldFrame ∘L T)
      hresponse
    have hresponsePoint := DFunLike.congr_fun hresponse' x
    have hdataPoint := DFunLike.congr_fun data.response_factorization x
    have hsame :
        ((suffixEulerFrameSchurStep lambda p S).oldFrame ∘L
          (-(primeSchurMarkovScalar p : ℂ) •
            (coframeBoundaryMomentGap owner lambda p S)†)) x =
          (-((primeSchurMarkovScalar p : ℂ) •
            ((suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S)† ∘L
              data.factor))) x := by
      calc
        ((suffixEulerFrameSchurStep lambda p S).oldFrame ∘L
            (-(primeSchurMarkovScalar p : ℂ) •
              (coframeBoundaryMomentGap owner lambda p S)†)) x =
            ((suffixEulerFrameSchurStep lambda p S).oldFrame ∘L
              (suffixActualBandRawPhysicalOldCarrierCoframeJointGapResponse
                owner lambda p S ∘L suffixEulerFrameTransition lambda p S)) x := by
          simpa only [ContinuousLinearMap.comp_apply,
            ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply,
            map_smul, map_neg, neg_smul] using hresponsePoint.symm
        _ = (-((primeSchurMarkovScalar p : ℂ) •
            ((suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S)† ∘L
              data.factor))) x := by
          simpa only [ContinuousLinearMap.comp_apply] using hdataPoint
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply,
      map_smul, map_neg, neg_smul] using hsame
  have hcancel :
      (suffixEulerFrameSchurStep lambda p S).oldFrame ∘L
          (coframeBoundaryMomentGap owner lambda p S)† =
        (suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S)† ∘L
          data.factor :=
    eq_of_neg_smul_eq_neg_smul hrho hscaled
  have hadjoint := congrArg ContinuousLinearMap.adjoint hcancel
  refine
    { bound_nonneg := data.bound_nonneg
      readout := data.factor†
      readout_norm_le := ?_
      factorization := ?_ }
  · calc
      ‖data.factor†‖ = ‖data.factor‖ :=
        ContinuousLinearMap.adjoint.norm_map data.factor
      _ ≤ bound := data.factor_norm_le
  · simpa only [ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint] using hadjoint.symm

/-! ## Gap readout -> response factor -/

/-- The existing gap readout can be adjointed to recover the response-facing
factorization. -/
noncomputable def
    SuffixRawOldCarrierCoframeJointGapReadoutData.toResponseReadoutData
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {bound : ℝ}
    (data : SuffixRawOldCarrierCoframeJointGapReadoutData owner lambda p S
      bound) :
    SuffixRawOldCarrierCoframeJointGapResponseReadoutData owner lambda p S
      bound := by
  have hfactorAdj := congrArg ContinuousLinearMap.adjoint data.factorization
  have hfactorAdj' :
      (suffixEulerFrameSchurStep lambda p S).oldFrame ∘L
          (coframeBoundaryMomentGap owner lambda p S)† =
        (suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S)† ∘L
          data.readout† := by
    simpa only [ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint, frameOldFrameAdjoint] using
      hfactorAdj.symm
  refine
    { bound_nonneg := data.bound_nonneg
      factor := data.readout†
      factor_norm_le := ?_
      response_factorization := ?_ }
  · calc
      ‖data.readout†‖ = ‖data.readout‖ :=
        ContinuousLinearMap.adjoint.norm_map data.readout
      _ ≤ bound := data.readout_norm_le
  · have hresponse :=
      suffixActualBandRawPhysicalOldCarrierCoframeJointGapResponse_comp_transition_eq_neg_scalar_gap_adjoint
        owner lambda p S
    calc
      (suffixEulerFrameSchurStep lambda p S).oldFrame ∘L
          suffixActualBandRawPhysicalOldCarrierCoframeJointGapResponse
            owner lambda p S ∘L suffixEulerFrameTransition lambda p S =
        (suffixEulerFrameSchurStep lambda p S).oldFrame ∘L
          (-((primeSchurMarkovScalar p : ℂ) •
            (coframeBoundaryMomentGap owner lambda p S)†)) := by
          rw [hresponse]
      _ = -((primeSchurMarkovScalar p : ℂ) •
          ((suffixEulerFrameSchurStep lambda p S).oldFrame ∘L
            (coframeBoundaryMomentGap owner lambda p S)†)) := by
          apply ContinuousLinearMap.ext
          intro x
          simp only [ContinuousLinearMap.comp_apply,
            ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply,
            map_smul, map_neg]
      _ = -((primeSchurMarkovScalar p : ℂ) •
          ((suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S)† ∘L
            data.readout†)) := by
          rw [hfactorAdj']

/-! ## Exact one-suffix and family-uniform equivalences -/

theorem exists_jointGapResponseReadout_iff_exists_jointGapReadout
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (bound : ℝ) :
    Nonempty
        (SuffixRawOldCarrierCoframeJointGapResponseReadoutData owner lambda
          p S bound) ↔
      Nonempty
        (SuffixRawOldCarrierCoframeJointGapReadoutData owner lambda p S
          bound) := by
  constructor
  · rintro ⟨data⟩
    exact ⟨SuffixRawOldCarrierCoframeJointGapResponseReadoutData.toJointGapReadoutData
      data⟩
  · rintro ⟨data⟩
    exact ⟨SuffixRawOldCarrierCoframeJointGapReadoutData.toResponseReadoutData
      data⟩

structure SuffixRawOldCarrierCoframeUniformJointGapResponseReadoutData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (bound : ℝ) where
  bound_nonneg : 0 ≤ bound
  factor : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
    SuffixRawOldCarrierCoframeJointGapResponseReadoutData owner lambda p S
      bound

noncomputable def
    SuffixRawOldCarrierCoframeUniformJointGapResponseReadoutData.toUniformGapReadoutData
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {bound : ℝ}
    (data : SuffixRawOldCarrierCoframeUniformJointGapResponseReadoutData
      owner lambda bound) :
    SuffixRawOldCarrierCoframeUniformJointGapReadoutData owner lambda bound :=
  { bound_nonneg := data.bound_nonneg
    readout := fun p S =>
      SuffixRawOldCarrierCoframeJointGapResponseReadoutData.toJointGapReadoutData
        (data.factor p S) }

noncomputable def
    SuffixRawOldCarrierCoframeUniformJointGapReadoutData.toUniformResponseReadoutData
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {bound : ℝ}
    (data : SuffixRawOldCarrierCoframeUniformJointGapReadoutData owner lambda
      bound) :
    SuffixRawOldCarrierCoframeUniformJointGapResponseReadoutData owner lambda
      bound :=
  { bound_nonneg := data.bound_nonneg
    factor := fun p S =>
      SuffixRawOldCarrierCoframeJointGapReadoutData.toResponseReadoutData
        (data.readout p S) }

theorem exists_uniform_jointGapResponseReadout_iff_exists_uniform_jointGapReadout
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (bound : ℝ) :
    Nonempty
        (SuffixRawOldCarrierCoframeUniformJointGapResponseReadoutData owner
          lambda bound) ↔
      Nonempty
        (SuffixRawOldCarrierCoframeUniformJointGapReadoutData owner lambda
          bound) := by
  constructor
  · rintro ⟨data⟩
    exact ⟨SuffixRawOldCarrierCoframeUniformJointGapResponseReadoutData.toUniformGapReadoutData data⟩
  · rintro ⟨data⟩
    exact ⟨SuffixRawOldCarrierCoframeUniformJointGapReadoutData.toUniformResponseReadoutData data⟩

end CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeJointGapResponseReadout
end CCM25Concrete
end Source
end ConnesWeilRH
