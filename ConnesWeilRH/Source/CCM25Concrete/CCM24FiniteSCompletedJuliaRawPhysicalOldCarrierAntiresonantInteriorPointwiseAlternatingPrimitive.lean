/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorUniformAlternatingPrimitive
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorSingleChannelColumnEquivalence
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus

/-!
# Pointwise alternating primitives and Banach--Steinhaus

Proof 648 identifies uniform operator-norm control of the canonical finite-
horizon readouts as a sufficient ambient source theorem for Bone 1.  The
Banach--Steinhaus theorem reduces that uniform estimate to a fixed-input
question.

The index below keeps the route-valid prime, suffix, and horizon together.
If every ambient vector has some finite bound across this entire index set,
Banach--Steinhaus produces one operator-norm bound shared by all indices.
Proof 648 then gives the raw Bone 1 domination, and the existing raw/renewed
column equivalence gives the renewed form with cost eight.

No pointwise bound is asserted here.  Compactness and terminal decay only say
that the summands tend to zero; they do not bound their alternating partial
sums.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorPointwiseAlternatingPrimitive

open MeasureTheory Filter Function Set Topology
open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCompletedJuliaAmbientDefectFactorization
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFiniteHorizonCoboundary
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorGap
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorRouteValidFactorization
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorSingleChannelColumnEquivalence
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorSingleChannelFactorization
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorUniformAlternatingPrimitive
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantRadialSplit
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSProjectionTrace
open CCM24UnitScaleProlateAlignment

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! ## The route-valid horizon family -/

/-- One route-valid adjacent step together with one finite horizon. -/
structure RouteFiniteHorizonIndex where
  prime : CCM24VisiblePrime
  suffix : List CCM24VisiblePrime
  valid : SuffixRouteValidStep prime suffix
  horizon : Nat

/-- The canonical Proof 646 readout at one route-valid index. -/
noncomputable def routeFiniteHorizonReadout
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (index : RouteFiniteHorizonIndex) :
    finiteSCarrier →L[Complex] sourceSoninCarrier unitSoninScale :=
  suffixActualBandFiniteHorizonCoboundaryReadout
    owner unitSoninScale index.prime index.suffix index.horizon

/-- Pointwise boundedness of the entire route-valid finite-horizon family.
The bound may initially depend on the fixed ambient input. -/
def SuffixCompleteCoupledRoutePointwiseFiniteHorizonReadoutBound
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) : Prop :=
  ∀ u : finiteSCarrier, ∃ inputBound : Real,
    ∀ index : RouteFiniteHorizonIndex,
      ‖routeFiniteHorizonReadout owner index u‖ ≤ inputBound

/-- One operator-norm bound shared by every route-valid finite horizon. -/
def SuffixCompleteCoupledRouteUniformFiniteHorizonReadoutBound
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (bound : Real) : Prop :=
  0 ≤ bound ∧ ∀ index : RouteFiniteHorizonIndex,
    ‖routeFiniteHorizonReadout owner index‖ ≤ bound

/-! ## Banach--Steinhaus equivalence -/

/-- Pointwise boundedness automatically supplies one shared operator-norm
bound for every route-valid step and horizon. -/
theorem exists_routeUniformFiniteHorizonReadoutBound_of_pointwise
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    (hpointwise :
      SuffixCompleteCoupledRoutePointwiseFiniteHorizonReadoutBound owner) :
    ∃ bound : Real,
      SuffixCompleteCoupledRouteUniformFiniteHorizonReadoutBound
        owner bound := by
  obtain ⟨rawBound, hrawBound⟩ :=
    banach_steinhaus
      (g := fun index : RouteFiniteHorizonIndex =>
        routeFiniteHorizonReadout owner index) hpointwise
  refine ⟨max rawBound 0, le_max_right _ _, ?_⟩
  intro index
  exact (hrawBound index).trans (le_max_left _ _)

/-- A shared operator-norm bound gives the corresponding fixed-input bound. -/
theorem routePointwiseFiniteHorizonReadoutBound_of_uniform
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner} {bound : Real}
    (huniform :
      SuffixCompleteCoupledRouteUniformFiniteHorizonReadoutBound
        owner bound) :
    SuffixCompleteCoupledRoutePointwiseFiniteHorizonReadoutBound owner := by
  intro u
  refine ⟨bound * ‖u‖, ?_⟩
  intro index
  calc
    ‖routeFiniteHorizonReadout owner index u‖ ≤
        ‖routeFiniteHorizonReadout owner index‖ * ‖u‖ :=
      (routeFiniteHorizonReadout owner index).le_opNorm u
    _ ≤ bound * ‖u‖ :=
      mul_le_mul_of_nonneg_right (huniform.2 index) (norm_nonneg u)

/-- Existence of a route-uniform canonical-horizon bound is exactly
pointwise boundedness of the same family. -/
theorem routePointwise_iff_exists_routeUniformFiniteHorizonReadoutBound
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) :
    SuffixCompleteCoupledRoutePointwiseFiniteHorizonReadoutBound owner ↔
      ∃ bound : Real,
        SuffixCompleteCoupledRouteUniformFiniteHorizonReadoutBound
          owner bound := by
  constructor
  · exact exists_routeUniformFiniteHorizonReadoutBound_of_pointwise
  · rintro ⟨bound, huniform⟩
    exact routePointwiseFiniteHorizonReadoutBound_of_uniform huniform

/-! ## Handoff to Bone 1 -/

/-- The route-uniform canonical-horizon estimate gives the active raw-column
same-vector domination with no additional constant. -/
theorem routeUniformRawAmbientDomination_of_uniformFiniteHorizonReadoutBound
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner} {bound : Real}
    (huniform :
      SuffixCompleteCoupledRouteUniformFiniteHorizonReadoutBound
        owner bound) :
    SuffixRawOldCarrierAntiresonantInteriorRouteUniformRawAmbientDomination
      owner unitSoninScale bound := by
  refine ⟨huniform.1, ?_⟩
  intro p S hvalid x
  have hstep : SuffixCompleteCoupledUniformFiniteHorizonReadoutBound
      owner p S bound := by
    refine ⟨huniform.1, ?_⟩
    intro N
    exact huniform.2
      { prime := p
        suffix := S
        valid := hvalid
        horizon := N }
  have hambient :=
    norm_completeCoupledAmbientTarget_le_of_uniformFiniteHorizonReadout
      hstep (newSuffixFrame unitSoninScale S x)
  have htarget :
      suffixActualBandCompleteCoupledAmbientTarget
          owner unitSoninScale p S
          (newSuffixFrame unitSoninScale S x) =
        signedCompressedInteriorOwner owner unitSoninScale p S x := by
    simpa only [ContinuousLinearMap.comp_apply] using
      DFunLike.congr_fun
        (suffixActualBandCompleteCoupledAmbientTarget_comp_newFrame
          owner unitSoninScale p S) x
  rw [htarget] at hambient
  have hnorm :
      ‖signedCompressedInteriorOwner owner unitSoninScale p S x‖ ≤
        bound * ‖newFrameAntiresonantColumn unitSoninScale p S x‖ := by
    simpa only [ContinuousLinearMap.comp_apply,
      newFrameAntiresonantColumn] using hambient
  simpa only [mul_pow] using
    (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg huniform.1 (norm_nonneg _))).2 hnorm

/-- Fixed-input boundedness of the complete alternating primitives is a
sufficient source theorem for a route-uniform raw Bone 1 constant. -/
theorem exists_routeUniformRawAmbientDomination_of_pointwise
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    (hpointwise :
      SuffixCompleteCoupledRoutePointwiseFiniteHorizonReadoutBound owner) :
    ∃ bound : Real,
      SuffixRawOldCarrierAntiresonantInteriorRouteUniformRawAmbientDomination
        owner unitSoninScale bound := by
  obtain ⟨bound, huniform⟩ :=
    exists_routeUniformFiniteHorizonReadoutBound_of_pointwise hpointwise
  exact ⟨bound,
    routeUniformRawAmbientDomination_of_uniformFiniteHorizonReadoutBound
      huniform⟩

/-- The same fixed-input premise reaches the active renewed Bone 1 form with
the existing universal column-recovery cost eight. -/
theorem exists_routeUniformRenewedAmbientDomination_of_pointwise
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    (hpointwise :
      SuffixCompleteCoupledRoutePointwiseFiniteHorizonReadoutBound owner) :
    ∃ bound : Real,
      SuffixRawOldCarrierAntiresonantInteriorRouteUniformRenewedAmbientDomination
        owner unitSoninScale bound := by
  obtain ⟨bound, hraw⟩ :=
    exists_routeUniformRawAmbientDomination_of_pointwise hpointwise
  exact ⟨8 * bound,
    renewedAmbientDomination_of_routeUniformRawAmbientDomination hraw⟩

end
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorPointwiseAlternatingPrimitive
end CCM25Concrete
end Source
end ConnesWeilRH
