/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorScalarCorrelationPrimitive

/-!
# Paired scalar correlations for the alternating primitive

Proof 651 exposes the exact signed prime-log correlation sum. This module
pairs adjacent horizons before taking any absolute value. Even horizons are
the sum of consecutive correlation differences; odd horizons add one terminal
correlation.

A route-uniform bound on the paired sum plus that single terminal term is a
sufficient source theorem for Bone 1. No such bound is asserted here.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorPairedScalarCorrelation

open MeasureTheory Filter Function Set Topology
open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSCompletedJuliaAmbientDefectFactorization
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFiniteHorizonCoboundary
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorPointwiseAlternatingPrimitive
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorWeakAlternatingPrimitive
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorScalarCorrelationPrimitive
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

/-! ## Generic adjacent pairing -/

variable {A : Type*} [AddCommMonoid A]

/-- A sum over an even range is the sum of its consecutive pairs. -/
theorem sum_range_two_mul_eq_sum_pairs
    (term : Nat → A) (N : Nat) :
    ∑ k ∈ Finset.range (2 * N), term k =
      ∑ j ∈ Finset.range N, (term (2 * j) + term (2 * j + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
      calc
        ∑ k ∈ Finset.range (2 * (N + 1)), term k =
            (∑ k ∈ Finset.range (2 * N), term k) +
              term (2 * N) + term (2 * N + 1) := by
                rw [show 2 * (N + 1) = (2 * N + 1) + 1 by omega,
                  Finset.sum_range_succ, Finset.sum_range_succ]
        _ = (∑ j ∈ Finset.range N,
              (term (2 * j) + term (2 * j + 1))) +
            (term (2 * N) + term (2 * N + 1)) := by
              rw [ih, add_assoc]
        _ = ∑ j ∈ Finset.range (N + 1),
              (term (2 * j) + term (2 * j + 1)) := by
                rw [Finset.sum_range_succ]

/-- An odd range is its paired even prefix plus one terminal term. -/
theorem sum_range_two_mul_add_one_eq_sum_pairs_add_terminal
    (term : Nat → A) (N : Nat) :
    ∑ k ∈ Finset.range (2 * N + 1), term k =
      (∑ j ∈ Finset.range N, (term (2 * j) + term (2 * j + 1))) +
        term (2 * N) := by
  rw [Finset.sum_range_succ, sum_range_two_mul_eq_sum_pairs]

/-! ## Actual paired prime-log correlations -/

/-- One unscaled signed prime-log correlation term. -/
noncomputable def routePrimeLogScalarCorrelationTerm
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (index : RouteFiniteHorizonIndex) (k : Nat) (u : finiteSCarrier)
    (v : sourceSoninCarrier unitSoninScale) : Complex :=
  inner Complex
    (((-1 : Complex) ^ k) •
      cc20GlobalLogTranslation
        ((k : Real) * Real.log index.prime) u)
    (((suffixActualBandCompleteCoupledAmbientTarget
      owner unitSoninScale index.prime index.suffix)†) v)

/-- The sum of two adjacent signed correlations. -/
noncomputable def routePrimeLogPairedScalarCorrelation
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (index : RouteFiniteHorizonIndex) (j : Nat) (u : finiteSCarrier)
    (v : sourceSoninCarrier unitSoninScale) : Complex :=
  routePrimeLogScalarCorrelationTerm owner index (2 * j) u v +
    routePrimeLogScalarCorrelationTerm owner index (2 * j + 1) u v

/-- Adjacent signed correlations are exactly the difference of the two
unsigned prime-log correlations. -/
theorem routePrimeLogPairedScalarCorrelation_eq_difference
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (index : RouteFiniteHorizonIndex) (j : Nat) (u : finiteSCarrier)
    (v : sourceSoninCarrier unitSoninScale) :
    routePrimeLogPairedScalarCorrelation owner index j u v =
      inner Complex
          (cc20GlobalLogTranslation
            ((2 * j : Nat) * Real.log index.prime) u)
          (((suffixActualBandCompleteCoupledAmbientTarget
            owner unitSoninScale index.prime index.suffix)†) v) -
        inner Complex
          (cc20GlobalLogTranslation
            (((2 * j + 1 : Nat)) * Real.log index.prime) u)
          (((suffixActualBandCompleteCoupledAmbientTarget
            owner unitSoninScale index.prime index.suffix)†) v) := by
  have heven : (-1 : Complex) ^ (2 * j) = 1 := by
    rw [pow_mul]
    norm_num
  have hodd : (-1 : Complex) ^ (2 * j + 1) = -1 := by
    rw [pow_succ, heven]
    norm_num
  simp only [routePrimeLogPairedScalarCorrelation,
    routePrimeLogScalarCorrelationTerm, heven, hodd, one_smul,
    neg_one_smul, inner_neg_left, sub_eq_add_neg]

/-- Even horizons are exactly the scaled sum of adjacent correlation pairs. -/
theorem routeFiniteHorizonScaledScalarCorrelation_eq_paired_of_even
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (index : RouteFiniteHorizonIndex) (N : Nat)
    (horizon_eq : index.horizon = 2 * N) (u : finiteSCarrier)
    (v : sourceSoninCarrier unitSoninScale) :
    routeFiniteHorizonScaledScalarCorrelation owner index u v =
      (starRingEnd Complex)
          ((primeEulerAmbientLossScale index.prime : Complex)⁻¹) *
        ∑ j ∈ Finset.range N,
          routePrimeLogPairedScalarCorrelation owner index j u v := by
  unfold routeFiniteHorizonScaledScalarCorrelation
  unfold routePrimeLogPairedScalarCorrelation
  unfold routePrimeLogScalarCorrelationTerm
  rw [horizon_eq, sum_range_two_mul_eq_sum_pairs]

/-- Odd horizons are the paired even prefix plus one scaled terminal
correlation. -/
theorem routeFiniteHorizonScaledScalarCorrelation_eq_paired_of_odd
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (index : RouteFiniteHorizonIndex) (N : Nat)
    (horizon_eq : index.horizon = 2 * N + 1) (u : finiteSCarrier)
    (v : sourceSoninCarrier unitSoninScale) :
    routeFiniteHorizonScaledScalarCorrelation owner index u v =
      (starRingEnd Complex)
          ((primeEulerAmbientLossScale index.prime : Complex)⁻¹) *
        ((∑ j ∈ Finset.range N,
            routePrimeLogPairedScalarCorrelation owner index j u v) +
          routePrimeLogScalarCorrelationTerm owner index (2 * N) u v) := by
  unfold routeFiniteHorizonScaledScalarCorrelation
  unfold routePrimeLogPairedScalarCorrelation
  unfold routePrimeLogScalarCorrelationTerm
  rw [horizon_eq, sum_range_two_mul_add_one_eq_sum_pairs_add_terminal]

/-- The paired-prefix norm plus the only possible odd terminal norm. -/
noncomputable def routePairedScalarCorrelationEnvelope
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (index : RouteFiniteHorizonIndex) (N : Nat) (u : finiteSCarrier)
    (v : sourceSoninCarrier unitSoninScale) : Real :=
  ‖(starRingEnd Complex)
        ((primeEulerAmbientLossScale index.prime : Complex)⁻¹) *
      ∑ j ∈ Finset.range N,
        routePrimeLogPairedScalarCorrelation owner index j u v‖ +
    ‖(starRingEnd Complex)
        ((primeEulerAmbientLossScale index.prime : Complex)⁻¹) *
      routePrimeLogScalarCorrelationTerm owner index (2 * N) u v‖

/-- A pointwise route-uniform envelope for the paired prefixes and the single
odd terminal term. -/
def SuffixCompleteCoupledRoutePairedScalarCorrelationEnvelopeBound
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) : Prop :=
  ∀ u : finiteSCarrier, ∀ v : sourceSoninCarrier unitSoninScale,
    ∃ scalarBound : Real, ∀ index : RouteFiniteHorizonIndex, ∀ N : Nat,
      routePairedScalarCorrelationEnvelope owner index N u v ≤ scalarBound

/-- The paired envelope bounds every exact scaled scalar correlation. -/
theorem routeScaledScalarCorrelationBound_of_pairedEnvelope
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    (henvelope :
      SuffixCompleteCoupledRoutePairedScalarCorrelationEnvelopeBound owner) :
    SuffixCompleteCoupledRouteScaledScalarCorrelationBound owner := by
  intro u v
  obtain ⟨scalarBound, hscalarBound⟩ := henvelope u v
  refine ⟨scalarBound, ?_⟩
  intro index
  rcases Nat.even_or_odd' index.horizon with ⟨N, heven | hodd⟩
  · rw [routeFiniteHorizonScaledScalarCorrelation_eq_paired_of_even
      owner index N heven u v]
    calc
      ‖(starRingEnd Complex)
            ((primeEulerAmbientLossScale index.prime : Complex)⁻¹) *
          ∑ j ∈ Finset.range N,
            routePrimeLogPairedScalarCorrelation owner index j u v‖ ≤
          routePairedScalarCorrelationEnvelope owner index N u v := by
            exact le_add_of_nonneg_right (norm_nonneg _)
      _ ≤ scalarBound := hscalarBound index N
  · rw [routeFiniteHorizonScaledScalarCorrelation_eq_paired_of_odd
      owner index N hodd u v, mul_add]
    calc
      ‖(starRingEnd Complex)
              ((primeEulerAmbientLossScale index.prime : Complex)⁻¹) *
            ∑ j ∈ Finset.range N,
              routePrimeLogPairedScalarCorrelation owner index j u v +
          (starRingEnd Complex)
              ((primeEulerAmbientLossScale index.prime : Complex)⁻¹) *
            routePrimeLogScalarCorrelationTerm owner index (2 * N) u v‖ ≤
          routePairedScalarCorrelationEnvelope owner index N u v := by
            exact norm_add_le _ _
      _ ≤ scalarBound := hscalarBound index N

/-! ## Handoff to Bone 1 -/

/-- A route-uniform paired scalar envelope is sufficient for raw Bone 1. -/
theorem exists_routeUniformRawAmbientDomination_of_pairedEnvelope
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    (henvelope :
      SuffixCompleteCoupledRoutePairedScalarCorrelationEnvelopeBound owner) :
    ∃ bound : Real,
      SuffixRawOldCarrierAntiresonantInteriorRouteUniformRawAmbientDomination
        owner unitSoninScale bound :=
  exists_routeUniformRawAmbientDomination_of_scaledScalarCorrelation
    (routeScaledScalarCorrelationBound_of_pairedEnvelope henvelope)

/-- The same paired scalar envelope reaches the renewed Bone 1 form with the
existing universal recovery cost eight. -/
theorem exists_routeUniformRenewedAmbientDomination_of_pairedEnvelope
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    (henvelope :
      SuffixCompleteCoupledRoutePairedScalarCorrelationEnvelopeBound owner) :
    ∃ bound : Real,
      SuffixRawOldCarrierAntiresonantInteriorRouteUniformRenewedAmbientDomination
        owner unitSoninScale bound :=
  exists_routeUniformRenewedAmbientDomination_of_scaledScalarCorrelation
    (routeScaledScalarCorrelationBound_of_pairedEnvelope henvelope)

end
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorPairedScalarCorrelation
end CCM25Concrete
end Source
end ConnesWeilRH
