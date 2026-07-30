/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorPairedEnvelopeEquivalence

/-!
# Coboundary normal form for paired scalar correlations

Proof 653 makes adjacent pairing equivalent to the raw scalar Bone 1 target.
This module moves each adjacent difference onto the complete coupled adjoint
target. If `a = log p` and `C = C_(p,S)`, then

```text
<U_(2j a)u,C^dagger v> - <U_((2j+1)a)u,C^dagger v>
  = <U_(2j a)u,(I-U_(-a))C^dagger v>.
```

The coboundary target is also exactly `[C(I-U_a)]^dagger`. All physical
branches remain coupled inside `C`; the loss scale and the odd terminal term
remain present. No bound on the resulting correlations is asserted here.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorPairedCorrelationCoboundary

open MeasureTheory Filter Function Set Topology
open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSCompletedJuliaAmbientDefectFactorization
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFiniteHorizonCoboundary
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorPairedEnvelopeEquivalence
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorPairedScalarCorrelation
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorPointwiseAlternatingPrimitive
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorScalarCorrelationPrimitive
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSProjectionTrace
open CCM24UnitScaleProlateAlignment
open SelectedCrossingOperatorBridge

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! ## Translation coboundary -/

/-- Moving one translation step from the first inner-product variable to the
second produces the inverse translation. This is where conjugate linearity in
the first variable fixes the orientation. -/
theorem inner_translation_sub_translation_add_eq_inner_coboundary
    (a b : Real) (u w : finiteSCarrier) :
    inner Complex (cc20GlobalLogTranslation b u) w -
        inner Complex (cc20GlobalLogTranslation (b + a) u) w =
      inner Complex (cc20GlobalLogTranslation b u)
        ((ContinuousLinearMap.id Complex finiteSCarrier -
          (cc20GlobalLogTranslation (-a)).toContinuousLinearMap) w) := by
  have hadjoint :
      (cc20GlobalLogTranslation a).toContinuousLinearMap.adjoint =
        (cc20GlobalLogTranslation (-a)).toContinuousLinearMap := by
    simpa only [neg_neg] using
      (cc20GlobalLogTranslation_neg_adjoint (-a))
  have hshiftCLM :
      inner Complex (cc20GlobalLogTranslation b u)
          ((cc20GlobalLogTranslation
            (-a)).toContinuousLinearMap w) =
        inner Complex (cc20GlobalLogTranslation (b + a) u) w := by
    calc
      inner Complex (cc20GlobalLogTranslation b u)
          ((cc20GlobalLogTranslation
            (-a)).toContinuousLinearMap w) =
          inner Complex (cc20GlobalLogTranslation b u)
            ((cc20GlobalLogTranslation
              a).toContinuousLinearMap.adjoint w) := by
                rw [hadjoint]
      _ = inner Complex
          (cc20GlobalLogTranslation a
            (cc20GlobalLogTranslation b u)) w :=
        by
          simpa only [LinearIsometry.coe_toContinuousLinearMap] using
            (ContinuousLinearMap.adjoint_inner_right
              (cc20GlobalLogTranslation a).toContinuousLinearMap
              (cc20GlobalLogTranslation b u) w)
      _ = inner Complex (cc20GlobalLogTranslation (a + b) u) w := by
        rw [cc20GlobalLogTranslation_add_apply]
      _ = inner Complex (cc20GlobalLogTranslation (b + a) u) w := by
        rw [add_comm]
  have hshift :
      inner Complex (cc20GlobalLogTranslation b u)
          (cc20GlobalLogTranslation (-a) w) =
        inner Complex (cc20GlobalLogTranslation (b + a) u) w := by
    simpa only [LinearIsometry.coe_toContinuousLinearMap] using hshiftCLM
  simp only [ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply, inner_sub_right,
    LinearIsometry.coe_toContinuousLinearMap, hshift]

/-! ## Complete coupled adjoint target -/

/-- The one-step adjoint coboundary of the complete coupled ambient target.
No physical branch is split in this definition. -/
noncomputable def routePrimeLogAdjointCoboundaryTarget
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (index : RouteFiniteHorizonIndex) :
    sourceSoninCarrier unitSoninScale →L[Complex] finiteSCarrier :=
  (ContinuousLinearMap.id Complex finiteSCarrier -
      (cc20GlobalLogTranslation
        (-Real.log index.prime)).toContinuousLinearMap) ∘L
    (suffixActualBandCompleteCoupledAmbientTarget
      owner unitSoninScale index.prime index.suffix)†

/-- The adjoint coboundary is the adjoint of the complete target followed by
the positive one-step coboundary. -/
theorem routePrimeLogAdjointCoboundaryTarget_eq_adjoint
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (index : RouteFiniteHorizonIndex) :
    routePrimeLogAdjointCoboundaryTarget owner index =
      (suffixActualBandCompleteCoupledAmbientTarget
          owner unitSoninScale index.prime index.suffix ∘L
        (ContinuousLinearMap.id Complex finiteSCarrier -
          (cc20GlobalLogTranslation
            (Real.log index.prime)).toContinuousLinearMap))† := by
  unfold routePrimeLogAdjointCoboundaryTarget
  rw [ContinuousLinearMap.adjoint_comp]
  simp only [map_sub, ContinuousLinearMap.adjoint_id]
  have hadjoint :
      (cc20GlobalLogTranslation
          (Real.log index.prime)).toContinuousLinearMap.adjoint =
        (cc20GlobalLogTranslation
          (-Real.log index.prime)).toContinuousLinearMap := by
    simpa only [neg_neg] using
      (cc20GlobalLogTranslation_neg_adjoint
        (-Real.log index.prime))
  rw [hadjoint]

/-- Each actual adjacent correlation pair is one correlation against the
complete adjoint coboundary target. -/
theorem routePrimeLogPairedScalarCorrelation_eq_adjointCoboundary
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (index : RouteFiniteHorizonIndex) (j : Nat) (u : finiteSCarrier)
    (v : sourceSoninCarrier unitSoninScale) :
    routePrimeLogPairedScalarCorrelation owner index j u v =
      inner Complex
        (cc20GlobalLogTranslation
          ((2 * j : Nat) * Real.log index.prime) u)
        (routePrimeLogAdjointCoboundaryTarget owner index v) := by
  rw [routePrimeLogPairedScalarCorrelation_eq_difference]
  have hstep :
      ((2 * j + 1 : Nat) : Real) * Real.log index.prime =
        ((2 * j : Nat) : Real) * Real.log index.prime +
          Real.log index.prime := by
    push_cast
    ring
  rw [hstep]
  unfold routePrimeLogAdjointCoboundaryTarget
  simp only [ContinuousLinearMap.comp_apply]
  exact inner_translation_sub_translation_add_eq_inner_coboundary
    (Real.log index.prime)
    (((2 * j : Nat) : Real) * Real.log index.prime) u
    (((suffixActualBandCompleteCoupledAmbientTarget
      owner unitSoninScale index.prime index.suffix)†) v)

/-- A paired prefix is exactly a prime-square-step translation correlation
against one fixed complete adjoint coboundary target. -/
theorem sum_routePrimeLogPairedScalarCorrelation_eq_adjointCoboundary
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (index : RouteFiniteHorizonIndex) (N : Nat) (u : finiteSCarrier)
    (v : sourceSoninCarrier unitSoninScale) :
    ∑ j ∈ Finset.range N,
        routePrimeLogPairedScalarCorrelation owner index j u v =
      ∑ j ∈ Finset.range N,
        inner Complex
          (cc20GlobalLogTranslation
            ((2 * j : Nat) * Real.log index.prime) u)
          (routePrimeLogAdjointCoboundaryTarget owner index v) := by
  apply Finset.sum_congr rfl
  intro j _hj
  exact routePrimeLogPairedScalarCorrelation_eq_adjointCoboundary
    owner index j u v

/-- The even terminal term has positive sign. -/
theorem routePrimeLogScalarCorrelationTerm_two_mul_eq
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (index : RouteFiniteHorizonIndex) (N : Nat) (u : finiteSCarrier)
    (v : sourceSoninCarrier unitSoninScale) :
    routePrimeLogScalarCorrelationTerm owner index (2 * N) u v =
      inner Complex
        (cc20GlobalLogTranslation
          ((2 * N : Nat) * Real.log index.prime) u)
        (((suffixActualBandCompleteCoupledAmbientTarget
          owner unitSoninScale index.prime index.suffix)†) v) := by
  have heven : (-1 : Complex) ^ (2 * N) = 1 := by
    rw [pow_mul]
    norm_num
  simp only [routePrimeLogScalarCorrelationTerm, heven, one_smul]

/-! ## Equivalent coboundary envelope -/

/-- The paired envelope written entirely as a correlation against the fixed
adjoint coboundary target plus the genuine odd-horizon terminal term. -/
noncomputable def routePairedAdjointCoboundaryEnvelope
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (index : RouteFiniteHorizonIndex) (N : Nat) (u : finiteSCarrier)
    (v : sourceSoninCarrier unitSoninScale) : Real :=
  ‖(starRingEnd Complex)
        ((primeEulerAmbientLossScale index.prime : Complex)⁻¹) *
      ∑ j ∈ Finset.range N,
        inner Complex
          (cc20GlobalLogTranslation
            ((2 * j : Nat) * Real.log index.prime) u)
          (routePrimeLogAdjointCoboundaryTarget owner index v)‖ +
    ‖(starRingEnd Complex)
        ((primeEulerAmbientLossScale index.prime : Complex)⁻¹) *
      inner Complex
        (cc20GlobalLogTranslation
          ((2 * N : Nat) * Real.log index.prime) u)
        (((suffixActualBandCompleteCoupledAmbientTarget
          owner unitSoninScale index.prime index.suffix)†) v)‖

/-- The original paired envelope and its adjoint-coboundary normal form are
identical pointwise. -/
theorem routePairedScalarCorrelationEnvelope_eq_adjointCoboundaryEnvelope
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (index : RouteFiniteHorizonIndex) (N : Nat) (u : finiteSCarrier)
    (v : sourceSoninCarrier unitSoninScale) :
    routePairedScalarCorrelationEnvelope owner index N u v =
      routePairedAdjointCoboundaryEnvelope owner index N u v := by
  unfold routePairedScalarCorrelationEnvelope
    routePairedAdjointCoboundaryEnvelope
  rw [sum_routePrimeLogPairedScalarCorrelation_eq_adjointCoboundary,
    routePrimeLogScalarCorrelationTerm_two_mul_eq]

/-- Pointwise route-uniform boundedness of the exact adjoint-coboundary
envelope. -/
def SuffixCompleteCoupledRoutePairedAdjointCoboundaryEnvelopeBound
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) : Prop :=
  ∀ u : finiteSCarrier, ∀ v : sourceSoninCarrier unitSoninScale,
    ∃ scalarBound : Real, ∀ index : RouteFiniteHorizonIndex, ∀ N : Nat,
      routePairedAdjointCoboundaryEnvelope owner index N u v ≤ scalarBound

/-- The coboundary-envelope target is exactly the paired target from Proof
653, hence also exactly the scalar Bone 1 target. -/
theorem routePairedAdjointCoboundaryEnvelope_iff_pairedEnvelope
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) :
    SuffixCompleteCoupledRoutePairedAdjointCoboundaryEnvelopeBound owner ↔
      SuffixCompleteCoupledRoutePairedScalarCorrelationEnvelopeBound owner := by
  constructor
  · intro hbound u v
    obtain ⟨scalarBound, hscalarBound⟩ := hbound u v
    refine ⟨scalarBound, ?_⟩
    intro index N
    rw [routePairedScalarCorrelationEnvelope_eq_adjointCoboundaryEnvelope]
    exact hscalarBound index N
  · intro hbound u v
    obtain ⟨scalarBound, hscalarBound⟩ := hbound u v
    refine ⟨scalarBound, ?_⟩
    intro index N
    rw [← routePairedScalarCorrelationEnvelope_eq_adjointCoboundaryEnvelope]
    exact hscalarBound index N

/-- The final coboundary envelope is equivalent to Proof 649's pointwise
finite-horizon target. -/
theorem routePairedAdjointCoboundaryEnvelope_iff_pointwiseFiniteHorizonReadout
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) :
    SuffixCompleteCoupledRoutePairedAdjointCoboundaryEnvelopeBound owner ↔
      SuffixCompleteCoupledRoutePointwiseFiniteHorizonReadoutBound owner := by
  rw [routePairedAdjointCoboundaryEnvelope_iff_pairedEnvelope,
    routePairedEnvelope_iff_pointwiseFiniteHorizonReadout]

end
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorPairedCorrelationCoboundary
end CCM25Concrete
end Source
end ConnesWeilRH
