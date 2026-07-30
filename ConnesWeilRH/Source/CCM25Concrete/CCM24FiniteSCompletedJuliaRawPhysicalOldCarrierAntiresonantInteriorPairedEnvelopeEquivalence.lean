/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorPairedScalarCorrelation

/-!
# Equivalence of paired and raw scalar correlation bounds

Proof 652 shows that a route-uniform paired envelope bounds every raw
alternating prefix. This module proves the converse with a universal factor
three. For a fixed prime and suffix, the paired prefix is the raw prefix at
the even horizon `2N`, while the terminal term is the difference between the
raw prefixes at horizons `2N + 1` and `2N`.

Thus pairing is an equivalent reformulation of the scalar Bone 1 target, not
an additional analytic assumption. No bound on either formulation is proved
here.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorPairedEnvelopeEquivalence

open MeasureTheory Filter Function Set Topology
open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSCompletedJuliaAmbientDefectFactorization
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorPairedScalarCorrelation
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorPointwiseAlternatingPrimitive
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorScalarCorrelationPrimitive
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorSingleChannelColumnEquivalence
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorSingleChannelFactorization
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorWeakAlternatingPrimitive
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSProjectionTrace
open CCM24UnitScaleProlateAlignment

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! ## Generic factor-three reverse estimate -/

/-- If every scaled raw prefix is bounded by `bound`, then the norm of the
scaled paired prefix plus the scaled terminal term is bounded by
`3 * bound`. The three copies are the even prefix and the two prefixes whose
difference is the terminal term. -/
theorem scaled_paired_envelope_le_three_mul_of_prefix_bound
    (scale : Complex) (term : Nat → Complex) (bound : Real)
    (hbound : ∀ horizon : Nat,
      ‖scale * ∑ k ∈ Finset.range horizon, term k‖ ≤ bound)
    (N : Nat) :
    ‖scale * ∑ j ∈ Finset.range N,
        (term (2 * j) + term (2 * j + 1))‖ +
      ‖scale * term (2 * N)‖ ≤ 3 * bound := by
  have heven :
      ‖scale * ∑ j ∈ Finset.range N,
          (term (2 * j) + term (2 * j + 1))‖ ≤ bound := by
    rw [← sum_range_two_mul_eq_sum_pairs]
    exact hbound (2 * N)
  have hterminal_eq :
      scale * term (2 * N) =
        scale * (∑ k ∈ Finset.range (2 * N + 1), term k) -
          scale * (∑ k ∈ Finset.range (2 * N), term k) := by
    rw [Finset.sum_range_succ]
    ring
  have hterminal : ‖scale * term (2 * N)‖ ≤ bound + bound := by
    rw [hterminal_eq]
    calc
      ‖scale * (∑ k ∈ Finset.range (2 * N + 1), term k) -
          scale * (∑ k ∈ Finset.range (2 * N), term k)‖ ≤
          ‖scale * ∑ k ∈ Finset.range (2 * N + 1), term k‖ +
            ‖scale * ∑ k ∈ Finset.range (2 * N), term k‖ :=
        norm_sub_le _ _
      _ ≤ bound + bound :=
        add_le_add (hbound (2 * N + 1)) (hbound (2 * N))
  calc
    ‖scale * ∑ j ∈ Finset.range N,
          (term (2 * j) + term (2 * j + 1))‖ +
        ‖scale * term (2 * N)‖ ≤
        bound + (bound + bound) := add_le_add heven hterminal
    _ = 3 * bound := by ring

/-! ## Actual route-family equivalence -/

set_option maxRecDepth 4096 in
/-- Replacing only the horizon leaves every scalar term unchanged and changes
only the range of the prefix sum. -/
theorem routeFiniteHorizonScaledScalarCorrelation_withHorizon
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (index : RouteFiniteHorizonIndex) (horizon : Nat)
    (u : finiteSCarrier)
    (v : sourceSoninCarrier unitSoninScale) :
    routeFiniteHorizonScaledScalarCorrelation owner
        { index with horizon := horizon } u v =
      (starRingEnd Complex)
          ((primeEulerAmbientLossScale index.prime : Complex)⁻¹) *
        ∑ k ∈ Finset.range horizon,
          routePrimeLogScalarCorrelationTerm owner index k u v := by
  rfl

/-- A route-uniform raw scalar-correlation bound controls the paired envelope
with at most a universal factor three. The horizon changes, but the prime,
suffix, and route-validity witness remain fixed. -/
theorem pairedEnvelopeBound_of_routeScaledScalarCorrelation
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    (hcorrelation :
      SuffixCompleteCoupledRouteScaledScalarCorrelationBound owner) :
    SuffixCompleteCoupledRoutePairedScalarCorrelationEnvelopeBound owner := by
  intro u v
  obtain ⟨scalarBound, hscalarBound⟩ := hcorrelation u v
  refine ⟨3 * scalarBound, ?_⟩
  intro index N
  have hprefix : ∀ horizon : Nat,
      ‖(starRingEnd Complex)
            ((primeEulerAmbientLossScale index.prime : Complex)⁻¹) *
          ∑ k ∈ Finset.range horizon,
            routePrimeLogScalarCorrelationTerm owner index k u v‖ ≤
        scalarBound := by
    intro horizon
    have h := hscalarBound { index with horizon := horizon }
    rw [routeFiniteHorizonScaledScalarCorrelation_withHorizon] at h
    exact h
  unfold routePairedScalarCorrelationEnvelope
  simpa only [routePrimeLogPairedScalarCorrelation] using
    scaled_paired_envelope_le_three_mul_of_prefix_bound
      ((starRingEnd Complex)
        ((primeEulerAmbientLossScale index.prime : Complex)⁻¹))
      (fun k => routePrimeLogScalarCorrelationTerm owner index k u v)
      scalarBound hprefix N

/-- The paired envelope and the raw scaled scalar correlations are equivalent
route-family targets. -/
theorem routePairedEnvelope_iff_scaledScalarCorrelation
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) :
    SuffixCompleteCoupledRoutePairedScalarCorrelationEnvelopeBound owner ↔
      SuffixCompleteCoupledRouteScaledScalarCorrelationBound owner := by
  constructor
  · exact routeScaledScalarCorrelationBound_of_pairedEnvelope
  · exact pairedEnvelopeBound_of_routeScaledScalarCorrelation

/-- Equivalently, the paired envelope is exactly the weak matrix-coefficient
target of Proof 650. -/
theorem routePairedEnvelope_iff_weakMatrixCoefficient
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) :
    SuffixCompleteCoupledRoutePairedScalarCorrelationEnvelopeBound owner ↔
      SuffixCompleteCoupledRouteWeakMatrixCoefficientBound owner := by
  rw [routePairedEnvelope_iff_scaledScalarCorrelation,
    routeScaledScalarCorrelation_iff_weakMatrixCoefficient]

/-- Equivalently, the paired envelope is exactly Proof 649's pointwise vector
boundedness target. -/
theorem routePairedEnvelope_iff_pointwiseFiniteHorizonReadout
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) :
    SuffixCompleteCoupledRoutePairedScalarCorrelationEnvelopeBound owner ↔
      SuffixCompleteCoupledRoutePointwiseFiniteHorizonReadoutBound owner := by
  rw [routePairedEnvelope_iff_weakMatrixCoefficient,
    routeWeakMatrixCoefficient_iff_pointwiseFiniteHorizonReadout]

end
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorPairedEnvelopeEquivalence
end CCM25Concrete
end Source
end ConnesWeilRH
