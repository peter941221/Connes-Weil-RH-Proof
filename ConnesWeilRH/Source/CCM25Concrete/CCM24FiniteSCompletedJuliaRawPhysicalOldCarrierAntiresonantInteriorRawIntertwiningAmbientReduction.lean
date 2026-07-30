/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorAmbientCovariance
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorNonpolarCofactorCollapse

/-!
# Ambient reduction of the raw intertwinement

Proof 660 reduces the complete Bone 1A target to the recombined raw
intertwining defect

```text
I_(p,S) = T_(p,S) M_S - M_(p::S) T_(p,S).
```

The existing ambient covariance identity is

```text
AmbientCovariance_(p,S) = oldFrame_(p,S) I_(p,S).
```

The old frame is isometric.  This module records the resulting exact norm
identity, including the genuine ambient-loss scaling and the route-uniform
bound.  Thus Bone 1A is equivalent, with no change of constant, to uniformly
bounding the intact ambient covariance column.

This is a carrier reduction, not the missing estimate.  In particular, it
does not identify the raw response with the adjacent projection commutator
and does not bound any metric or first-jet residual separately.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorRawIntertwiningAmbientReduction

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSActualJuliaRangeSineAmbientScaleGuard
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCompletedJuliaAmbientDefectFactorization
open CCM24FiniteSCompletedJuliaJointProducer
open CCM24FiniteSCompletedJuliaMismatchFactorization
open CCM24FiniteSCompletedJuliaNonpolarMismatchNormalForm
open CCM24FiniteSCompletedJuliaPolarRawReadout
open CCM24FiniteSCompletedJuliaSynthesis
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorAdjacentBoundaryResponse
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorAmbientCovariance
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFiniteHorizonCoboundary
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorGap
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorNonpolarCofactorCollapse
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorOneStepTargetSize
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorPointwiseAlternatingPrimitive
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorPolarScaledTargetSize
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantRadialBlockRecurrence
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierBlockReduction
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierFixedSourceKernelGuard
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeRangeAnnihilationGuard
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSFixedSourcePolar
open CCM24FiniteSJuliaCoDefect
open CCM24FiniteSProjectionTrace
open CCM24FiniteSSchurMarkovPairing
open CCM24UnitScaleProlateAlignment

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! ## Generic isometric postcomposition -/

/-- Postcomposition by a norm-preserving linear map preserves the operator
norm exactly.  Surjectivity of the frame is neither needed nor true here. -/
theorem norm_isometric_postcomp_eq
    {E H K : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup K] [NormedSpace ℂ K]
    (frame : H →L[ℂ] K) (operator : E →L[ℂ] H)
    (hframe : ∀ y : H, ‖frame y‖ = ‖y‖) :
    ‖frame ∘L operator‖ = ‖operator‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg operator)
    intro x
    rw [ContinuousLinearMap.comp_apply, hframe]
    exact operator.le_opNorm x
  · apply ContinuousLinearMap.opNorm_le_bound _
      (norm_nonneg (frame ∘L operator))
    intro x
    rw [← hframe (operator x), ← ContinuousLinearMap.comp_apply]
    exact (frame ∘L operator).le_opNorm x

/-! ## Fixed-step norm identity -/

/-- The ambient covariance column and the source raw intertwinement have
exactly the same operator norm. -/
theorem norm_suffixActualBandAmbientRawCovarianceColumn_eq_rawIntertwiningDefect
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    ‖suffixActualBandAmbientRawCovarianceColumn owner lambda p S‖ =
      ‖suffixActualBandRawQuadraticIntertwiningDefect owner lambda p S‖ := by
  rw [suffixActualBandAmbientRawCovarianceColumn_eq_oldFrame_comp_rawDefect]
  apply norm_isometric_postcomp_eq
  exact
    (ContinuousLinearMap.norm_map_iff_adjoint_comp_self
      (oldSuffixFrame lambda p S)).mpr (by
        simpa only [ContinuousLinearMap.one_def] using
          (suffixEulerFrameSchurStep lambda p S).oldFrame_isometry)

/-- The exact norm identity survives division by the genuine one-prime
ambient-loss scale. -/
theorem
    norm_ambientLossScaled_suffixActualBandAmbientRawCovarianceColumn_eq_rawIntertwiningDefect
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    ‖((primeEulerAmbientLossScale p : ℂ)⁻¹) •
        suffixActualBandAmbientRawCovarianceColumn owner lambda p S‖ =
      ‖((primeEulerAmbientLossScale p : ℂ)⁻¹) •
        suffixActualBandRawQuadraticIntertwiningDefect owner lambda p S‖ := by
  rw [norm_smul, norm_smul,
    norm_suffixActualBandAmbientRawCovarianceColumn_eq_rawIntertwiningDefect]

/-! ## Route-uniform equivalence -/

/-- The ambient covariance column divided by the genuine one-prime loss
scale at one route-valid adjacent step. -/
noncomputable def routeScaledAmbientRawCovarianceColumn
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (index : RouteFiniteHorizonIndex) :
    sourceSoninCarrier unitSoninScale →L[ℂ] finiteSCarrier :=
  ((primeEulerAmbientLossScale index.prime : ℂ)⁻¹) •
    suffixActualBandAmbientRawCovarianceColumn
      owner unitSoninScale index.prime index.suffix

/-- At every route-valid step, the scaled ambient and source columns have
the same norm. -/
theorem norm_routeScaledAmbientRawCovarianceColumn_eq_rawIntertwiningDefect
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (index : RouteFiniteHorizonIndex) :
    ‖routeScaledAmbientRawCovarianceColumn owner index‖ =
      ‖routeScaledRawQuadraticIntertwiningDefect owner index‖ := by
  exact
    norm_ambientLossScaled_suffixActualBandAmbientRawCovarianceColumn_eq_rawIntertwiningDefect
      owner unitSoninScale index.prime index.suffix

/-- One operator-norm bound for every route-valid scaled ambient covariance
column. -/
def SuffixAmbientRawRouteUniformScaledCovarianceBound
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (bound : ℝ) : Prop :=
  0 ≤ bound ∧ ∀ index : RouteFiniteHorizonIndex,
    ‖routeScaledAmbientRawCovarianceColumn owner index‖ ≤ bound

/-- The ambient and source route-uniform statements are definitionally
different but mathematically identical, with the same bound. -/
theorem routeUniformScaledAmbientCovarianceBound_iff_rawIntertwiningBound
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (bound : ℝ) :
    SuffixAmbientRawRouteUniformScaledCovarianceBound owner bound ↔
      SuffixRawRouteUniformScaledIntertwiningBound owner bound := by
  constructor
  · rintro ⟨hbound, hambient⟩
    refine ⟨hbound, ?_⟩
    intro index
    rw [← norm_routeScaledAmbientRawCovarianceColumn_eq_rawIntertwiningDefect]
    exact hambient index
  · rintro ⟨hbound, hraw⟩
    refine ⟨hbound, ?_⟩
    intro index
    rw [norm_routeScaledAmbientRawCovarianceColumn_eq_rawIntertwiningDefect]
    exact hraw index

/-- Existence of a route-uniform scaled ambient covariance bound is exactly
existence of the source raw-intertwinement bound. -/
theorem exists_routeUniformScaledAmbientCovarianceBound_iff_rawIntertwiningBound
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) :
    (∃ bound : ℝ,
      SuffixAmbientRawRouteUniformScaledCovarianceBound owner bound) ↔
      ∃ bound : ℝ,
        SuffixRawRouteUniformScaledIntertwiningBound owner bound := by
  constructor
  · rintro ⟨bound, data⟩
    exact ⟨bound,
      (routeUniformScaledAmbientCovarianceBound_iff_rawIntertwiningBound
        owner bound).mp data⟩
  · rintro ⟨bound, data⟩
    exact ⟨bound,
      (routeUniformScaledAmbientCovarianceBound_iff_rawIntertwiningBound
        owner bound).mpr data⟩

/-- Combining Proofs 660 and 661, Bone 1A is equivalent to one
route-uniform bound for the intact ambient covariance column. -/
theorem exists_routeUniformScaledCompleteTargetBound_iff_ambientCovarianceBound
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) :
    (∃ bound : ℝ,
      SuffixCompleteCoupledRouteUniformScaledTargetBound owner bound) ↔
      ∃ bound : ℝ,
        SuffixAmbientRawRouteUniformScaledCovarianceBound owner bound :=
  (exists_routeUniformScaledCompleteTargetBound_iff_rawIntertwiningBound
    owner).trans
      (exists_routeUniformScaledAmbientCovarianceBound_iff_rawIntertwiningBound
        owner).symm

end
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorRawIntertwiningAmbientReduction
end CCM25Concrete
end Source
end ConnesWeilRH
