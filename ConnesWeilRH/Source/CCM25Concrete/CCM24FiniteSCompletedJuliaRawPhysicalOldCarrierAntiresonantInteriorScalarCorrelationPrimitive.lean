/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorWeakAlternatingPrimitive

/-!
# Scalar correlation normal form for the alternating primitive

Proof 650 reduces Bone 1 to bounded scalar matrix coefficients of the actual
route-valid finite-horizon readouts. This module expands each coefficient as
the exact finite signed translation correlation sum

```text
star(s_p^(-1)) * sum_(k<N)
  inner ((-1)^k U_(k log p) u) (C_(p,S)^dagger v).
```

The complete coupled target `C_(p,S)` remains intact inside its adjoint. The
outer, reflected, second-support, and prolate branches are not estimated
separately. No bound on the displayed sum is asserted here.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorScalarCorrelationPrimitive

open MeasureTheory Filter Function Set Topology
open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSCompletedJuliaAmbientDefectFactorization
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFiniteHorizonCoboundary
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorInfiniteHorizonTail
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorPointwiseAlternatingPrimitive
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorWeakAlternatingPrimitive
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

/-! ## Generic scalar finite-sum identity -/

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace Complex E]
  [NormedAddCommGroup F] [InnerProductSpace Complex F]

/-- A finite-horizon readout matrix coefficient is the scaled finite sum of
the target applied to the alternating orbit. -/
theorem inner_finiteHorizonAntiresonantCoboundaryReadout_eq_sum
    (scale : Complex) (U : E →L[Complex] E) (C : E →L[Complex] F)
    (N : Nat) (u : E) (v : F) :
    inner Complex
        (finiteHorizonAntiresonantCoboundaryReadout scale U C N u) v =
      (starRingEnd Complex) (scale⁻¹) *
        ∑ k ∈ Finset.range N, inner Complex (C (((-U) ^ k) u)) v := by
  simp only [finiteHorizonAntiresonantCoboundaryReadout,
    finiteAntiresonantAlternatingPolynomial,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sum_apply, map_sum, sum_inner, inner_smul_left]

/-! ## Actual prime-log correlation sum -/

/-- The exact scaled scalar correlation attached to one route-valid horizon.
All suffix dependence remains inside the adjoint complete coupled target. -/
noncomputable def routeFiniteHorizonScaledScalarCorrelation
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (index : RouteFiniteHorizonIndex) (u : finiteSCarrier)
    (v : sourceSoninCarrier unitSoninScale) : Complex :=
  (starRingEnd Complex)
      ((primeEulerAmbientLossScale index.prime : Complex)⁻¹) *
    ∑ k ∈ Finset.range index.horizon,
      inner Complex
        (((-1 : Complex) ^ k) •
          cc20GlobalLogTranslation
            ((k : Real) * Real.log index.prime) u)
        (((suffixActualBandCompleteCoupledAmbientTarget
          owner unitSoninScale index.prime index.suffix)†) v)

/-- The matrix coefficient of the actual finite-horizon readout equals the
explicit scaled prime-log correlation sum. -/
theorem inner_routeFiniteHorizonReadout_eq_scaledScalarCorrelation
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (index : RouteFiniteHorizonIndex) (u : finiteSCarrier)
    (v : sourceSoninCarrier unitSoninScale) :
    inner Complex (routeFiniteHorizonReadout owner index u) v =
      routeFiniteHorizonScaledScalarCorrelation owner index u v := by
  unfold routeFiniteHorizonReadout
  unfold suffixActualBandFiniteHorizonCoboundaryReadout
  trans
    (starRingEnd Complex)
        ((primeEulerAmbientLossScale index.prime : Complex)⁻¹) *
      ∑ k ∈ Finset.range index.horizon,
        inner Complex
          (suffixActualBandCompleteCoupledAmbientTarget
            owner unitSoninScale index.prime index.suffix
            (((-(cc20GlobalLogTranslation
              (Real.log index.prime)).toContinuousLinearMap) ^ k) u)) v
  · exact inner_finiteHorizonAntiresonantCoboundaryReadout_eq_sum
      (primeEulerAmbientLossScale index.prime : Complex)
      (cc20GlobalLogTranslation
        (Real.log index.prime)).toContinuousLinearMap
      (suffixActualBandCompleteCoupledAmbientTarget
        owner unitSoninScale index.prime index.suffix)
      index.horizon u v
  · unfold routeFiniteHorizonScaledScalarCorrelation
    congr 1
    apply Finset.sum_congr rfl
    intro k _hk
    rw [← ContinuousLinearMap.adjoint_inner_right,
      neg_cc20GlobalLogTranslation_pow_apply]

/-- Boundedness of the explicit scaled scalar correlations across the entire
route family. The bound may depend on the two fixed vectors. -/
def SuffixCompleteCoupledRouteScaledScalarCorrelationBound
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) : Prop :=
  ∀ u : finiteSCarrier, ∀ v : sourceSoninCarrier unitSoninScale,
    ∃ scalarBound : Real, ∀ index : RouteFiniteHorizonIndex,
      ‖routeFiniteHorizonScaledScalarCorrelation owner index u v‖ ≤
        scalarBound

/-- The explicit scalar-correlation bound gives Proof 650's weak matrix-
coefficient bound. -/
theorem routeWeakMatrixCoefficientBound_of_scaledScalarCorrelation
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    (hcorrelation :
      SuffixCompleteCoupledRouteScaledScalarCorrelationBound owner) :
    SuffixCompleteCoupledRouteWeakMatrixCoefficientBound owner := by
  intro u v
  obtain ⟨scalarBound, hscalarBound⟩ := hcorrelation u v
  refine ⟨scalarBound, ?_⟩
  intro index
  rw [inner_routeFiniteHorizonReadout_eq_scaledScalarCorrelation]
  exact hscalarBound index

/-- Proof 650's weak matrix-coefficient bound gives boundedness of the exact
scaled scalar correlations. -/
theorem routeScaledScalarCorrelationBound_of_weakMatrixCoefficient
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    (hweak : SuffixCompleteCoupledRouteWeakMatrixCoefficientBound owner) :
    SuffixCompleteCoupledRouteScaledScalarCorrelationBound owner := by
  intro u v
  obtain ⟨scalarBound, hscalarBound⟩ := hweak u v
  refine ⟨scalarBound, ?_⟩
  intro index
  rw [← inner_routeFiniteHorizonReadout_eq_scaledScalarCorrelation]
  exact hscalarBound index

/-- The scalar correlation target is exactly the weak target from Proof 650. -/
theorem routeScaledScalarCorrelation_iff_weakMatrixCoefficient
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) :
    SuffixCompleteCoupledRouteScaledScalarCorrelationBound owner ↔
      SuffixCompleteCoupledRouteWeakMatrixCoefficientBound owner := by
  constructor
  · exact routeWeakMatrixCoefficientBound_of_scaledScalarCorrelation
  · exact routeScaledScalarCorrelationBound_of_weakMatrixCoefficient

/-! ## Handoff to Bone 1 -/

/-- Uniform boundedness of the exact scaled scalar correlations is sufficient
for the active raw Bone 1 domination. -/
theorem exists_routeUniformRawAmbientDomination_of_scaledScalarCorrelation
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    (hcorrelation :
      SuffixCompleteCoupledRouteScaledScalarCorrelationBound owner) :
    ∃ bound : Real,
      SuffixRawOldCarrierAntiresonantInteriorRouteUniformRawAmbientDomination
        owner unitSoninScale bound :=
  exists_routeUniformRawAmbientDomination_of_weakMatrixCoefficient
    (routeWeakMatrixCoefficientBound_of_scaledScalarCorrelation hcorrelation)

/-- The same scalar premise reaches the renewed Bone 1 form with the existing
universal recovery cost eight. -/
theorem exists_routeUniformRenewedAmbientDomination_of_scaledScalarCorrelation
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    (hcorrelation :
      SuffixCompleteCoupledRouteScaledScalarCorrelationBound owner) :
    ∃ bound : Real,
      SuffixRawOldCarrierAntiresonantInteriorRouteUniformRenewedAmbientDomination
        owner unitSoninScale bound :=
  exists_routeUniformRenewedAmbientDomination_of_weakMatrixCoefficient
    (routeWeakMatrixCoefficientBound_of_scaledScalarCorrelation hcorrelation)

end
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorScalarCorrelationPrimitive
end CCM25Concrete
end Source
end ConnesWeilRH
