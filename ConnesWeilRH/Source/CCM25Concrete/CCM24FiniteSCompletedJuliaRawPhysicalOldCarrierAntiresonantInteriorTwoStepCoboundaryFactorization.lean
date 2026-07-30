/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorOneStepTargetSize

/-!
# Two-step coboundary factorization of paired prefixes

Proof 655 isolates the necessary horizon-one size gate. This module isolates
the remaining paired-prefix channel. After scaling by `s_p^(-1)`, require the
complete adjoint coboundary to factor as

```text
s_p^(-1) (I-U_(-a)) C_(p,S)^dagger
  = (I-U_(-2a)) R_(p,S),
  a = log p.
```

The prime-square-step sum then telescopes exactly, with bound
`2 ||R_(p,S)||`. A route-uniform size gate plus a route-uniform bound on these
factors is sufficient for Proof 649 and hence for the existing raw and renewed
Bone 1 consumers. Neither source bound is proved here.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorTwoStepCoboundaryFactorization

open MeasureTheory Filter Function Set Topology
open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSCompletedJuliaAmbientDefectFactorization
open CCM24FiniteSCausalMarkov
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorOneStepTargetSize
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorPairedCorrelationCoboundary
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorPairedScalarCorrelation
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

/-! ## Generic two-step telescope -/

variable {A : Type*} [AddCommGroup A]

/-- Consecutive differences telescope over a finite range. -/
theorem sum_range_sub_succ_eq_sub
    (term : Nat → A) (N : Nat) :
    ∑ j ∈ Finset.range N, (term j - term (j + 1)) =
      term 0 - term N := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      abel

/-- A correlation sum against a literal two-step coboundary telescopes to
its two endpoints. -/
theorem sum_inner_translation_twoStepCoboundary_eq_endpoints
    (a : Real) (N : Nat) (u w : finiteSCarrier) :
    ∑ j ∈ Finset.range N,
        inner Complex
          (cc20GlobalLogTranslation ((2 * j : Nat) * a) u)
          ((ContinuousLinearMap.id Complex finiteSCarrier -
            (cc20GlobalLogTranslation (-2 * a)).toContinuousLinearMap) w) =
      inner Complex u w -
        inner Complex
          (cc20GlobalLogTranslation ((2 * N : Nat) * a) u) w := by
  let term : Nat → Complex := fun j =>
    inner Complex
      (cc20GlobalLogTranslation ((2 * j : Nat) * a) u) w
  calc
    ∑ j ∈ Finset.range N,
          inner Complex
            (cc20GlobalLogTranslation ((2 * j : Nat) * a) u)
            ((ContinuousLinearMap.id Complex finiteSCarrier -
              (cc20GlobalLogTranslation (-2 * a)).toContinuousLinearMap) w) =
        ∑ j ∈ Finset.range N, (term j - term (j + 1)) := by
      apply Finset.sum_congr rfl
      intro j _hj
      calc
        inner Complex
            (cc20GlobalLogTranslation ((2 * j : Nat) * a) u)
            ((ContinuousLinearMap.id Complex finiteSCarrier -
              (cc20GlobalLogTranslation (-2 * a)).toContinuousLinearMap) w) =
            inner Complex
                (cc20GlobalLogTranslation ((2 * j : Nat) * a) u) w -
              inner Complex
                (cc20GlobalLogTranslation
                  (((2 * j : Nat) : Real) * a + 2 * a) u) w := by
          simpa only [neg_mul] using
            (inner_translation_sub_translation_add_eq_inner_coboundary
              (2 * a) (((2 * j : Nat) : Real) * a) u w).symm
        _ = term j - term (j + 1) := by
          congr 2
          push_cast
          ring
    _ = term 0 - term N := sum_range_sub_succ_eq_sub term N
    _ = inner Complex u w -
          inner Complex
            (cc20GlobalLogTranslation ((2 * N : Nat) * a) u) w := by
      unfold term
      rw [show ((2 * 0 : Nat) : Real) * a = 0 by norm_num,
        cc20GlobalLogTranslation_zero_apply]

/-! ## The actual scaled two-step source target -/

/-- The exact adjoint coboundary with the scalar used by the correlation
readout already applied. -/
noncomputable def routeScaledPrimeLogAdjointCoboundaryTarget
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (index : RouteFiniteHorizonIndex) :
    sourceSoninCarrier unitSoninScale →L[Complex] finiteSCarrier :=
  (starRingEnd Complex)
      ((primeEulerAmbientLossScale index.prime : Complex)⁻¹) •
    routePrimeLogAdjointCoboundaryTarget owner index

/-- Scaling the paired prefix is the same as pairing against the scaled
adjoint coboundary target. -/
theorem scaled_sum_routePrimeLogPairedScalarCorrelation_eq_scaledTarget
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (index : RouteFiniteHorizonIndex) (N : Nat) (u : finiteSCarrier)
    (v : sourceSoninCarrier unitSoninScale) :
    (starRingEnd Complex)
          ((primeEulerAmbientLossScale index.prime : Complex)⁻¹) *
        ∑ j ∈ Finset.range N,
          routePrimeLogPairedScalarCorrelation owner index j u v =
      ∑ j ∈ Finset.range N,
        inner Complex
          (cc20GlobalLogTranslation
            ((2 * j : Nat) * Real.log index.prime) u)
          (routeScaledPrimeLogAdjointCoboundaryTarget owner index v) := by
  rw [sum_routePrimeLogPairedScalarCorrelation_eq_adjointCoboundary]
  simp only [routeScaledPrimeLogAdjointCoboundaryTarget,
    ContinuousLinearMap.smul_apply, inner_smul_right, Finset.mul_sum]

/-- A bounded factor of the scaled complete coboundary through the literal
two-step translation coboundary. -/
structure RouteScaledTwoStepCoboundaryFactorData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (index : RouteFiniteHorizonIndex) (bound : Real) where
  factor : sourceSoninCarrier unitSoninScale →L[Complex] finiteSCarrier
  factor_norm_le : ‖factor‖ ≤ bound
  factorization :
    routeScaledPrimeLogAdjointCoboundaryTarget owner index =
      (ContinuousLinearMap.id Complex finiteSCarrier -
          (cc20GlobalLogTranslation
            (-2 * Real.log index.prime)).toContinuousLinearMap) ∘L
        factor

/-- One factor bound shared by every route-valid prime and suffix. -/
def SuffixCompleteCoupledRouteUniformScaledTwoStepCoboundaryFactor
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (bound : Real) : Prop :=
  0 ≤ bound ∧ ∀ index : RouteFiniteHorizonIndex,
    Nonempty (RouteScaledTwoStepCoboundaryFactorData owner index bound)

/-- One two-step factor bounds the corresponding complete paired prefix. -/
theorem norm_scaled_paired_prefix_le_of_twoStepFactor
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {index : RouteFiniteHorizonIndex} {bound : Real}
    (data : RouteScaledTwoStepCoboundaryFactorData owner index bound)
    (N : Nat) (u : finiteSCarrier)
    (v : sourceSoninCarrier unitSoninScale) :
    ‖(starRingEnd Complex)
          ((primeEulerAmbientLossScale index.prime : Complex)⁻¹) *
        ∑ j ∈ Finset.range N,
          routePrimeLogPairedScalarCorrelation owner index j u v‖ ≤
      2 * bound * ‖u‖ * ‖v‖ := by
  rw [scaled_sum_routePrimeLogPairedScalarCorrelation_eq_scaledTarget]
  have hfactor := DFunLike.congr_fun data.factorization v
  simp only [ContinuousLinearMap.comp_apply] at hfactor
  rw [hfactor,
    sum_inner_translation_twoStepCoboundary_eq_endpoints]
  have hfactorPoint : ‖data.factor v‖ ≤ bound * ‖v‖ := by
    calc
      ‖data.factor v‖ ≤ ‖data.factor‖ * ‖v‖ := data.factor.le_opNorm v
      _ ≤ bound * ‖v‖ :=
        mul_le_mul_of_nonneg_right data.factor_norm_le (norm_nonneg _)
  calc
    ‖inner Complex u (data.factor v) -
        inner Complex
          (cc20GlobalLogTranslation
            ((2 * N : Nat) * Real.log index.prime) u)
          (data.factor v)‖ ≤
        ‖inner Complex u (data.factor v)‖ +
          ‖inner Complex
            (cc20GlobalLogTranslation
              ((2 * N : Nat) * Real.log index.prime) u)
            (data.factor v)‖ := norm_sub_le _ _
    _ ≤ ‖u‖ * ‖data.factor v‖ +
          ‖cc20GlobalLogTranslation
            ((2 * N : Nat) * Real.log index.prime) u‖ *
              ‖data.factor v‖ :=
      add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
    _ = 2 * ‖u‖ * ‖data.factor v‖ := by
      rw [norm_cc20GlobalLogTranslation]
      ring
    _ ≤ 2 * ‖u‖ * (bound * ‖v‖) :=
      mul_le_mul_of_nonneg_left hfactorPoint
        (mul_nonneg (by norm_num) (norm_nonneg _))
    _ = 2 * bound * ‖u‖ * ‖v‖ := by ring

/-! ## Divide-and-conquer handoff to Bone 1 -/

/-- The horizon-one size gate and the two-step factor gate together bound the
entire paired envelope. -/
theorem pairedAdjointCoboundaryEnvelopeBound_of_size_and_twoStepFactor
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {targetBound pairBound : Real}
    (htarget :
      SuffixCompleteCoupledRouteUniformScaledTargetBound owner targetBound)
    (hpair :
      SuffixCompleteCoupledRouteUniformScaledTwoStepCoboundaryFactor
        owner pairBound) :
    SuffixCompleteCoupledRoutePairedAdjointCoboundaryEnvelopeBound owner := by
  intro u v
  refine ⟨(2 * pairBound + targetBound) * ‖u‖ * ‖v‖, ?_⟩
  intro index N
  obtain ⟨data⟩ := hpair.2 index
  rw [← routePairedScalarCorrelationEnvelope_eq_adjointCoboundaryEnvelope]
  unfold routePairedScalarCorrelationEnvelope
  calc
    ‖(starRingEnd Complex)
            ((primeEulerAmbientLossScale index.prime : Complex)⁻¹) *
          ∑ j ∈ Finset.range N,
            routePrimeLogPairedScalarCorrelation owner index j u v‖ +
        ‖(starRingEnd Complex)
            ((primeEulerAmbientLossScale index.prime : Complex)⁻¹) *
          routePrimeLogScalarCorrelationTerm owner index (2 * N) u v‖ ≤
        (2 * pairBound * ‖u‖ * ‖v‖) +
          (targetBound * ‖u‖ * ‖v‖) := by
      apply add_le_add
      · exact norm_scaled_paired_prefix_le_of_twoStepFactor
          data N u v
      · rw [routePrimeLogScalarCorrelationTerm_two_mul_eq]
        exact norm_scaled_even_terminal_le_of_scaledTargetBound
          htarget index N u v
    _ = (2 * pairBound + targetBound) * ‖u‖ * ‖v‖ := by ring

/-- The two independent source gates imply Proof 649's pointwise route
target. -/
theorem routePointwiseFiniteHorizonReadoutBound_of_size_and_twoStepFactor
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {targetBound pairBound : Real}
    (htarget :
      SuffixCompleteCoupledRouteUniformScaledTargetBound owner targetBound)
    (hpair :
      SuffixCompleteCoupledRouteUniformScaledTwoStepCoboundaryFactor
        owner pairBound) :
    SuffixCompleteCoupledRoutePointwiseFiniteHorizonReadoutBound owner :=
  (routePairedAdjointCoboundaryEnvelope_iff_pointwiseFiniteHorizonReadout
    owner).mp
      (pairedAdjointCoboundaryEnvelopeBound_of_size_and_twoStepFactor
        htarget hpair)

/-- The same two source gates reach the active raw Bone 1 consumer. -/
theorem exists_routeUniformRawAmbientDomination_of_size_and_twoStepFactor
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {targetBound pairBound : Real}
    (htarget :
      SuffixCompleteCoupledRouteUniformScaledTargetBound owner targetBound)
    (hpair :
      SuffixCompleteCoupledRouteUniformScaledTwoStepCoboundaryFactor
        owner pairBound) :
    ∃ bound : Real,
      SuffixRawOldCarrierAntiresonantInteriorRouteUniformRawAmbientDomination
        owner unitSoninScale bound :=
  exists_routeUniformRawAmbientDomination_of_pointwise
    (routePointwiseFiniteHorizonReadoutBound_of_size_and_twoStepFactor
      htarget hpair)

/-- The same two source gates reach the renewed Bone 1 consumer with the
existing universal recovery cost. -/
theorem exists_routeUniformRenewedAmbientDomination_of_size_and_twoStepFactor
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {targetBound pairBound : Real}
    (htarget :
      SuffixCompleteCoupledRouteUniformScaledTargetBound owner targetBound)
    (hpair :
      SuffixCompleteCoupledRouteUniformScaledTwoStepCoboundaryFactor
        owner pairBound) :
    ∃ bound : Real,
      SuffixRawOldCarrierAntiresonantInteriorRouteUniformRenewedAmbientDomination
        owner unitSoninScale bound :=
  exists_routeUniformRenewedAmbientDomination_of_pointwise
    (routePointwiseFiniteHorizonReadoutBound_of_size_and_twoStepFactor
      htarget hpair)

end
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorTwoStepCoboundaryFactorization
end CCM25Concrete
end Source
end ConnesWeilRH
