/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorPointwiseAlternatingPrimitive

/-!
# Weak matrix coefficients for the alternating primitive

Proof 649 reduces Bone 1 to pointwise boundedness of the route-valid
finite-horizon readouts on every ambient input. This module applies
Banach--Steinhaus once more, now on the target Hilbert space. It is enough to
bound every scalar matrix coefficient of the same family.

The resulting source target is

```text
forall u v, exists M_(u,v), forall route-valid (p,S,N),
  ||inner (H_(p,S,N) u) v|| <= M_(u,v).
```

This is equivalent to Proof 649's pointwise vector bound. It exposes the
signed scalar correlation sum on which compact detector support may legally
act; no scalar bound is asserted here.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorWeakAlternatingPrimitive

open MeasureTheory Filter Function Set Topology
open scoped InnerProduct InnerProductSpace

open CC20Concrete
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorPointwiseAlternatingPrimitive
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorSingleChannelColumnEquivalence
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorSingleChannelFactorization
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSProjectionTrace
open CCM24UnitScaleProlateAlignment

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! ## Generic weak-to-strong family criterion -/

variable {Index E F : Type*}
  [NormedAddCommGroup E] [NormedSpace Complex E]
  [NormedAddCommGroup F] [InnerProductSpace Complex F] [CompleteSpace F]

/-- Every scalar matrix coefficient of a family is bounded across its index.
The bound may depend on both fixed vectors. -/
def WeakMatrixCoefficientFamilyBound
    (family : Index → E →L[Complex] F) : Prop :=
  ∀ u : E, ∀ v : F, ∃ scalarBound : Real,
    ∀ index : Index, ‖inner Complex (family index u) v‖ ≤ scalarBound

/-- Every fixed input has a vector-norm bound across the family. -/
def PointwiseVectorFamilyBound
    (family : Index → E →L[Complex] F) : Prop :=
  ∀ u : E, ∃ inputBound : Real,
    ∀ index : Index, ‖family index u‖ ≤ inputBound

/-- Banach--Steinhaus on the target Hilbert space promotes scalar matrix-
coefficient bounds to a vector-norm bound for every fixed input. -/
theorem pointwiseVectorFamilyBound_of_weakMatrixCoefficientFamilyBound
    {family : Index → E →L[Complex] F}
    (hweak : WeakMatrixCoefficientFamilyBound family) :
    PointwiseVectorFamilyBound family := by
  intro u
  obtain ⟨rawBound, hrawBound⟩ :=
    banach_steinhaus
      (g := fun index : Index => innerSL Complex (family index u))
      (by
        intro v
        obtain ⟨scalarBound, hscalarBound⟩ := hweak u v
        exact ⟨scalarBound, fun index => by
          simpa only [innerSL_apply_apply] using hscalarBound index⟩)
  refine ⟨max rawBound 0, ?_⟩
  intro index
  rw [← innerSL_apply_norm Complex (family index u)]
  exact (hrawBound index).trans (le_max_left _ _)

/-- A pointwise vector-norm bound gives all scalar coefficient bounds by
Cauchy--Schwarz. -/
theorem weakMatrixCoefficientFamilyBound_of_pointwiseVectorFamilyBound
    {family : Index → E →L[Complex] F}
    (hpointwise : PointwiseVectorFamilyBound family) :
    WeakMatrixCoefficientFamilyBound family := by
  intro u v
  obtain ⟨inputBound, hinputBound⟩ := hpointwise u
  refine ⟨inputBound * ‖v‖, ?_⟩
  intro index
  calc
    ‖inner Complex (family index u) v‖ ≤
        ‖family index u‖ * ‖v‖ := norm_inner_le_norm _ _
    _ ≤ inputBound * ‖v‖ :=
      mul_le_mul_of_nonneg_right (hinputBound index) (norm_nonneg v)

/-- Weak scalar boundedness and pointwise vector boundedness are equivalent
for a family with Hilbert target. -/
theorem weakMatrixCoefficientFamilyBound_iff_pointwiseVectorFamilyBound
    (family : Index → E →L[Complex] F) :
    WeakMatrixCoefficientFamilyBound family ↔
      PointwiseVectorFamilyBound family := by
  constructor
  · exact pointwiseVectorFamilyBound_of_weakMatrixCoefficientFamilyBound
  · exact weakMatrixCoefficientFamilyBound_of_pointwiseVectorFamilyBound

/-! ## Actual route-valid family -/

/-- Weak scalar boundedness of all actual route-valid finite-horizon
readouts. The scalar bound may depend on the fixed ambient and target
vectors, but not on the route index. -/
def SuffixCompleteCoupledRouteWeakMatrixCoefficientBound
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) : Prop :=
  WeakMatrixCoefficientFamilyBound
    (fun index : RouteFiniteHorizonIndex =>
      routeFiniteHorizonReadout owner index)

/-- Weak scalar boundedness gives Proof 649's pointwise vector bound. -/
theorem routePointwiseFiniteHorizonReadoutBound_of_weakMatrixCoefficient
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    (hweak : SuffixCompleteCoupledRouteWeakMatrixCoefficientBound owner) :
    SuffixCompleteCoupledRoutePointwiseFiniteHorizonReadoutBound owner := by
  exact pointwiseVectorFamilyBound_of_weakMatrixCoefficientFamilyBound hweak

/-- Proof 649's pointwise vector bound gives every weak scalar bound. -/
theorem routeWeakMatrixCoefficientBound_of_pointwiseFiniteHorizonReadout
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    (hpointwise :
      SuffixCompleteCoupledRoutePointwiseFiniteHorizonReadoutBound owner) :
    SuffixCompleteCoupledRouteWeakMatrixCoefficientBound owner := by
  exact weakMatrixCoefficientFamilyBound_of_pointwiseVectorFamilyBound
    hpointwise

/-- The actual weak scalar premise is exactly Proof 649's pointwise premise. -/
theorem routeWeakMatrixCoefficient_iff_pointwiseFiniteHorizonReadout
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) :
    SuffixCompleteCoupledRouteWeakMatrixCoefficientBound owner ↔
      SuffixCompleteCoupledRoutePointwiseFiniteHorizonReadoutBound owner :=
  weakMatrixCoefficientFamilyBound_iff_pointwiseVectorFamilyBound _

/-! ## Handoff to Bone 1 -/

/-- Route-uniform weak scalar bounds are sufficient for the active raw Bone 1
domination. -/
theorem exists_routeUniformRawAmbientDomination_of_weakMatrixCoefficient
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    (hweak : SuffixCompleteCoupledRouteWeakMatrixCoefficientBound owner) :
    ∃ bound : Real,
      SuffixRawOldCarrierAntiresonantInteriorRouteUniformRawAmbientDomination
        owner unitSoninScale bound :=
  exists_routeUniformRawAmbientDomination_of_pointwise
    (routePointwiseFiniteHorizonReadoutBound_of_weakMatrixCoefficient hweak)

/-- The same weak scalar premise reaches the renewed Bone 1 form with the
existing universal recovery cost eight. -/
theorem exists_routeUniformRenewedAmbientDomination_of_weakMatrixCoefficient
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    (hweak : SuffixCompleteCoupledRouteWeakMatrixCoefficientBound owner) :
    ∃ bound : Real,
      SuffixRawOldCarrierAntiresonantInteriorRouteUniformRenewedAmbientDomination
        owner unitSoninScale bound :=
  exists_routeUniformRenewedAmbientDomination_of_pointwise
    (routePointwiseFiniteHorizonReadoutBound_of_weakMatrixCoefficient hweak)

end
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorWeakAlternatingPrimitive
end CCM25Concrete
end Source
end ConnesWeilRH
