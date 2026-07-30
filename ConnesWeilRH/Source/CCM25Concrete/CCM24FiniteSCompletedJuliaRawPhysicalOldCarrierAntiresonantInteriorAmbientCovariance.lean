/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorSingleChannelRouteDomination

/-!
# Ambient covariance normal form for the antiresonant interior

Let `U_S` be the actual suffix polar frame and let `Q_S` be the complete raw
quadratic response.  Its canonical ambient lift is

```text
Z_S = U_S Q_S U_S^dagger.
```

For the normalized forward transport `F_p`, inverse `N_p`, source transition
`T_(p,S)`, and reverse transition `R_(p,S)`, this module proves

```text
(F_p Z_S - Z_(p::S) F_p) U_S
  = U_(p::S) rawIntertwiningDefect_(p,S),

K_(p,S)^dagger T_(p,S)
  = U_S^dagger N_p (F_p Z_S - Z_(p::S) F_p) U_S.
```

The complete first-jet, endpoint Gram correction, three boundary branches,
and prolate term remain inside `Q_S`; no summand is estimated separately.
Consequently a route-uniform factorization

```text
(F_p Z_S - Z_(p::S) F_p) U_S = L_p H_(p,S)
```

with uniformly bounded `H_(p,S)` is a sufficient producer for the exact
Proof 627 single-channel Bone 1 factor.  This module identifies that source
obligation but does not construct the uniformly bounded factors.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorAmbientCovariance

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCausalMarkov
open CCM24FiniteSCompletedJuliaAmbientDefectFactorization
open CCM24FiniteSCompletedJuliaMismatchFactorization
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorGap
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorLocalCofactor
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorReverseIntertwining
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorRouteValidFactorization
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorSingleChannelFactorization
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSParameterizedSoninSubspace
open CCM24FiniteSProjectionTrace
open CCM24FiniteSRawCompletedSchurCocycle
open CCM24FiniteSSchurMarkovPairing

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

local notation "SourceOp" lambda =>
  sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda

local notation "SourceToFinite" lambda =>
  sourceSoninCarrier lambda →L[ℂ] finiteSCarrier

/-! ## Generic frame covariance -/

/-- A covariance column survives an isometric change of frame without any
commutation assumption on the two responses. -/
theorem frameLiftedCovarianceColumn_eq
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (newFrame oldFrame : H →L[ℂ] K) (transport : K →L[ℂ] K)
    (transition oldResponse newResponse : H →L[ℂ] H)
    (hnew : newFrame† ∘L newFrame = ContinuousLinearMap.id ℂ H)
    (hold : oldFrame† ∘L oldFrame = ContinuousLinearMap.id ℂ H)
    (htransport : transport ∘L newFrame = oldFrame ∘L transition) :
    (transport ∘L
          (newFrame ∘L oldResponse ∘L newFrame†) -
        (oldFrame ∘L newResponse ∘L oldFrame†) ∘L transport) ∘L
        newFrame =
      oldFrame ∘L
        (transition ∘L oldResponse - newResponse ∘L transition) := by
  apply ContinuousLinearMap.ext
  intro x
  change
    transport (newFrame (oldResponse ((newFrame†) (newFrame x)))) -
        oldFrame (newResponse ((oldFrame†) (transport (newFrame x)))) =
      oldFrame
        (transition (oldResponse x) - newResponse (transition x))
  have hnewPoint : (newFrame†) (newFrame x) = x := by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
      using DFunLike.congr_fun hnew x
  have holdPoint : (oldFrame†) (oldFrame (transition x)) = transition x := by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
      using DFunLike.congr_fun hold (transition x)
  have htransportPoint : transport (newFrame x) =
      oldFrame (transition x) := by
    simpa only [ContinuousLinearMap.comp_apply] using
      DFunLike.congr_fun htransport x
  have htransportOldPoint : transport (newFrame (oldResponse x)) =
      oldFrame (transition (oldResponse x)) := by
    simpa only [ContinuousLinearMap.comp_apply] using
      DFunLike.congr_fun htransport (oldResponse x)
  rw [hnewPoint, htransportOldPoint, htransportPoint, holdPoint, map_sub]

/-! ## Actual polar lift and covariance column -/

/-- The canonical ambient lift of the complete source response through its
actual suffix polar frame.  This is a frame lift, not a new independent
physical response. -/
noncomputable def suffixActualBandPolarLiftedRawQuadraticResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  newSuffixFrame lambda S ∘L
    suffixActualBandRawQuadraticCycledResponse owner lambda S ∘L
      (newSuffixFrame lambda S)†

/-- The complete forward covariance column on the actual new suffix frame. -/
noncomputable def suffixActualBandAmbientRawCovarianceColumn
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) : SourceToFinite lambda :=
  (normalizedPrimeEulerFrameTransport p ∘L
        suffixActualBandPolarLiftedRawQuadraticResponse owner lambda S -
      suffixActualBandPolarLiftedRawQuadraticResponse owner lambda (p :: S) ∘L
        normalizedPrimeEulerFrameTransport p) ∘L
    newSuffixFrame lambda S

/-- The ambient covariance column is exactly the complete raw
intertwining defect in the adjacent old polar frame. -/
theorem suffixActualBandAmbientRawCovarianceColumn_eq_oldFrame_comp_rawDefect
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandAmbientRawCovarianceColumn owner lambda p S =
      oldSuffixFrame lambda p S ∘L
        suffixActualBandRawQuadraticIntertwiningDefect owner lambda p S := by
  have hnew : (newSuffixFrame lambda S)† ∘L newSuffixFrame lambda S =
      ContinuousLinearMap.id ℂ (sourceSoninCarrier lambda) := by
    exact (suffixEulerFrameSchurStep lambda p S).newFrame_isometry
  have hold : (oldSuffixFrame lambda p S)† ∘L
        oldSuffixFrame lambda p S =
      ContinuousLinearMap.id ℂ (sourceSoninCarrier lambda) := by
    exact (suffixEulerFrameSchurStep lambda p S).oldFrame_isometry
  have htransport : normalizedPrimeEulerFrameTransport p ∘L
        newSuffixFrame lambda S =
      oldSuffixFrame lambda p S ∘L
        suffixEulerFrameTransition lambda p S := by
    simpa only [suffixEulerFrameSchurStep] using
      (suffixEulerFrameSchurStep lambda p S).transport_intertwining
  simpa only [suffixActualBandAmbientRawCovarianceColumn,
    suffixActualBandPolarLiftedRawQuadraticResponse,
    suffixActualBandRawQuadraticIntertwiningDefect] using
    (frameLiftedCovarianceColumn_eq
      (newSuffixFrame lambda S) (oldSuffixFrame lambda p S)
      (normalizedPrimeEulerFrameTransport p)
      (suffixEulerFrameTransition lambda p S)
      (suffixActualBandRawQuadraticCycledResponse owner lambda S)
      (suffixActualBandRawQuadraticCycledResponse owner lambda (p :: S))
      hnew hold htransport)

/-! ## Reverse-intertwining pullback -/

/-- The complete reverse-intertwining cofactor is the normalized-inverse
pullback of one intact ambient covariance column. -/
theorem
    completeBoundaryReverseIntertwiningDefect_adjoint_comp_transition_eq_ambientCovariancePullback
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    (suffixActualBandCompleteBoundaryReverseIntertwiningDefect
        owner lambda p S)† ∘L suffixEulerFrameTransition lambda p S =
      (newSuffixFrame lambda S)† ∘L normalizedPrimeEulerInverse p ∘L
        suffixActualBandAmbientRawCovarianceColumn owner lambda p S := by
  have hinterior :=
    signedCompressedInteriorOwner_eq_transitionAdjoint_comp_completeBoundaryReverseIntertwiningDefect
      owner lambda p S
  have hinteriorAdjoint := congrArg ContinuousLinearMap.adjoint hinterior
  have hcofactor :
      (suffixActualBandCompleteBoundaryReverseIntertwiningDefect
          owner lambda p S)† ∘L suffixEulerFrameTransition lambda p S =
        (signedCompressedInteriorOwner owner lambda p S)† := by
    simpa only [ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint] using hinteriorAdjoint.symm
  calc
    (suffixActualBandCompleteBoundaryReverseIntertwiningDefect
          owner lambda p S)† ∘L suffixEulerFrameTransition lambda p S =
        (signedCompressedInteriorOwner owner lambda p S)† := hcofactor
    _ = suffixEulerFrameReverseTransition lambda p S ∘L
          suffixActualBandRawQuadraticIntertwiningDefect owner lambda p S :=
      signedCompressedInteriorOwner_adjoint_eq_reverse_comp_rawIntertwiningDefect
        owner lambda p S
    _ = (newSuffixFrame lambda S)† ∘L
          normalizedPrimeEulerInverse p ∘L
            (oldSuffixFrame lambda p S ∘L
              suffixActualBandRawQuadraticIntertwiningDefect
                owner lambda p S) := by
      simp only [suffixEulerFrameReverseTransition,
        ContinuousLinearMap.comp_assoc]
    _ = (newSuffixFrame lambda S)† ∘L
          normalizedPrimeEulerInverse p ∘L
            suffixActualBandAmbientRawCovarianceColumn owner lambda p S := by
      rw [suffixActualBandAmbientRawCovarianceColumn_eq_oldFrame_comp_rawDefect]

/-- Equivalent interior-adjoint form of the covariance pullback. -/
theorem signedCompressedInteriorOwner_adjoint_eq_ambientCovariancePullback
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    (signedCompressedInteriorOwner owner lambda p S)† =
      (newSuffixFrame lambda S)† ∘L normalizedPrimeEulerInverse p ∘L
        suffixActualBandAmbientRawCovarianceColumn owner lambda p S := by
  calc
    (signedCompressedInteriorOwner owner lambda p S)† =
        (suffixActualBandCompleteBoundaryReverseIntertwiningDefect
            owner lambda p S)† ∘L
          suffixEulerFrameTransition lambda p S := by
      simpa only [ContinuousLinearMap.adjoint_comp,
        ContinuousLinearMap.adjoint_adjoint] using
        congrArg ContinuousLinearMap.adjoint
          (signedCompressedInteriorOwner_eq_transitionAdjoint_comp_completeBoundaryReverseIntertwiningDefect
            owner lambda p S)
    _ = (newSuffixFrame lambda S)† ∘L
          normalizedPrimeEulerInverse p ∘L
            suffixActualBandAmbientRawCovarianceColumn owner lambda p S :=
      completeBoundaryReverseIntertwiningDefect_adjoint_comp_transition_eq_ambientCovariancePullback
        owner lambda p S

/-! ## The single remaining sufficient factor -/

/-- A bounded left factorization of the intact ambient covariance column
through the genuine antiresonant loss factor. -/
structure SuffixRawOldCarrierAntiresonantInteriorAmbientCovarianceFactorData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (bound : ℝ) where
  bound_nonneg : 0 ≤ bound
  factor : SourceToFinite lambda
  factor_norm_le : ‖factor‖ ≤ bound
  factorization :
    suffixActualBandAmbientRawCovarianceColumn owner lambda p S =
      primeEulerAmbientLossFactor p ∘L factor

/-- Ambient covariance divisibility feeds the exact Proof 627 channel with
no loss in the factor norm. -/
noncomputable def
    SuffixRawOldCarrierAntiresonantInteriorAmbientCovarianceFactorData.toSingleChannelFactorData
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {bound : ℝ}
    (data :
      SuffixRawOldCarrierAntiresonantInteriorAmbientCovarianceFactorData
        owner lambda p S bound) :
    SuffixRawOldCarrierAntiresonantInteriorSingleChannelFactorData
      owner lambda p S bound := by
  refine
    { bound_nonneg := data.bound_nonneg
      factor := data.factor
      factor_norm_le := data.factor_norm_le
      factorization := ?_ }
  calc
    (suffixActualBandCompleteBoundaryReverseIntertwiningDefect
          owner lambda p S)† ∘L suffixEulerFrameTransition lambda p S =
        (newSuffixFrame lambda S)† ∘L normalizedPrimeEulerInverse p ∘L
          suffixActualBandAmbientRawCovarianceColumn owner lambda p S :=
      completeBoundaryReverseIntertwiningDefect_adjoint_comp_transition_eq_ambientCovariancePullback
        owner lambda p S
    _ = (newSuffixFrame lambda S)† ∘L normalizedPrimeEulerInverse p ∘L
          (primeEulerAmbientLossFactor p ∘L data.factor) := by
      rw [data.factorization]
    _ = (newSuffixFrame lambda S)† ∘L normalizedPrimeEulerInverse p ∘L
          primeEulerAmbientLossFactor p ∘L data.factor := by
      simp only [ContinuousLinearMap.comp_assoc]

/-- One common covariance factor bound on every route-valid adjacent step. -/
structure
    SuffixRawOldCarrierAntiresonantInteriorRouteUniformAmbientCovarianceFactorData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (bound : ℝ) where
  bound_nonneg : 0 ≤ bound
  factor : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
    SuffixRouteValidStep p S →
      SuffixRawOldCarrierAntiresonantInteriorAmbientCovarianceFactorData
        owner lambda p S bound

/-- The route-uniform covariance producer maps directly to the existing
route-uniform single-channel Bone 1 producer. -/
noncomputable def
    SuffixRawOldCarrierAntiresonantInteriorRouteUniformAmbientCovarianceFactorData.toRouteUniformSingleChannelFactorData
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {bound : ℝ}
    (data :
      SuffixRawOldCarrierAntiresonantInteriorRouteUniformAmbientCovarianceFactorData
        owner lambda bound) :
    SuffixRawOldCarrierAntiresonantInteriorRouteUniformSingleChannelFactorData
      owner lambda bound :=
  { bound_nonneg := data.bound_nonneg
    factor := fun p S hvalid =>
      (data.factor p S hvalid).toSingleChannelFactorData }

/-- A route-uniform ambient covariance factor proves the exact renewed
relative-energy form of Bone 1 with the same bound. -/
theorem routeUniformRenewedAmbientDomination_of_ambientCovarianceFactorData
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {bound : ℝ}
    (data :
      SuffixRawOldCarrierAntiresonantInteriorRouteUniformAmbientCovarianceFactorData
        owner lambda bound) :
    SuffixRawOldCarrierAntiresonantInteriorRouteUniformRenewedAmbientDomination
      owner lambda bound :=
  routeUniformRenewedAmbientDomination_of_singleChannelFactorData
    data.toRouteUniformSingleChannelFactorData

end CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorAmbientCovariance
end CCM25Concrete
end Source
end ConnesWeilRH
