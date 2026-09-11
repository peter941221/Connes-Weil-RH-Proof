/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8P1RadialCrossingEnergyTransport
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFrameLossCommutatorReduction
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorAdjacentProjectionGap

/-!
# G8 P1 radial commutator channel ledger

The exact signed split of the frame-loss commutator,

```text
[U_p, P_S] = [E U_p E, P_S] + (I - E) U_p P_S,
```

is packaged here with closed per-channel constants: the compressed interior
channel costs at most `2` in operator norm (translation is an isometry and
both radial projections are contractions), and the radial boundary channel
costs at most `32 ‖q_p⁻¹‖` times the pulled-back antiresonant column norm
pointwise.  Together this is the radial-side channel ledger dual to the
metric-side projection-defect ledger of P1: one bounded interior channel and
one column-controlled boundary channel.

No channel is discarded and no vanishing is asserted; a summability or
smallness estimate for the antiresonant-column energy remains the open
analytic input on this side.
-/

namespace ConnesWeilRH
namespace Source
namespace C1G8P1RadialCommutatorChannelLedger

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.PositiveTrace
open CCM25Concrete.AntiresonantFrameLossRadialBoundaryColumnBridge
open CCM25Concrete.AntiresonantFrameLossRadialBoundaryColumnFullCarrierExtension
open CCM25Concrete.AntiresonantFrameLossRadialBoundaryCauchyPairProducer
open CCM25Concrete.AntiresonantFrameLossRadialBoundaryCauchyDefect
open CCM25Concrete.AntiresonantFrameLossRadialBoundarySplit
open CCM25Concrete.AntiresonantFrameLossCommutator
open CCM25Concrete.CCM24FiniteSActualSchurCascade
open CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorAdjacentProjectionGap
open CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantRadialBlockRecurrence
open CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantRadialSplit
open CCM25Concrete.CCM24FiniteSFrameGramCalculus
open CCM25Concrete.CCM24FiniteSProjectionTrace
open CCM25Concrete.CCM24UnitScaleProlateAlignment

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! ## The interior channel -/

/-- The compressed positive translation is a contraction: both radial support
projections are contractions and the prime-log translation is an isometry. -/
theorem norm_radialCompressedPositiveTranslation_le_one
    (p : CCM24VisiblePrime) :
    ‖radialCompressedPositiveTranslation p‖ ≤ 1 := by
  have hrsp := norm_radialSupportProjection_le_one (unitSoninScale)
  have hrsp0 : (0:ℝ) ≤ ‖radialSupportProjection unitSoninScale‖ := norm_nonneg _
  have htr := norm_primeEulerPositiveTranslation_le_one p
  have h2 : ‖((cc20GlobalLogTranslation
      (Real.log p)).toContinuousLinearMap ∘L
    radialSupportProjection unitSoninScale)‖ ≤
      ‖(cc20GlobalLogTranslation
        (Real.log p)).toContinuousLinearMap‖ *
        ‖radialSupportProjection unitSoninScale‖ :=
    ContinuousLinearMap.opNorm_comp_le _ _
  have hmid : ‖((cc20GlobalLogTranslation
      (Real.log p)).toContinuousLinearMap ∘L
    radialSupportProjection unitSoninScale)‖ ≤ 1 := by nlinarith
  calc ‖radialCompressedPositiveTranslation p‖
      ≤ ‖radialSupportProjection unitSoninScale‖ *
          ‖((cc20GlobalLogTranslation
              (Real.log p)).toContinuousLinearMap ∘L
            radialSupportProjection unitSoninScale)‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 := by nlinarith

/-- The interior channel `[E U_p E, P_S]` costs at most `2`: a commutator
costs twice the product of the two norms, and both slots are contractions. -/
theorem norm_radialInteriorSoninCommutator_le_two
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime) :
    ‖radialInteriorSoninCommutator p S‖ ≤ 2 := by
  have hproj : ‖newSuffixRangeProjection unitSoninScale S‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
    intro u
    simpa using norm_newSuffixRangeProjection_apply_le unitSoninScale S u
  have hproj0 : (0:ℝ) ≤ ‖newSuffixRangeProjection unitSoninScale S‖ :=
    norm_nonneg _
  have hcore0 : (0:ℝ) ≤ ‖radialCompressedPositiveTranslation p‖ :=
    norm_nonneg _
  have hcore := norm_radialCompressedPositiveTranslation_le_one p
  have hcomm := norm_cc20Commutator_le_two_mul
    (radialCompressedPositiveTranslation p)
    (newSuffixRangeProjection unitSoninScale S)
  calc ‖radialInteriorSoninCommutator p S‖
      = ‖cc20Commutator (radialCompressedPositiveTranslation p)
          (newSuffixRangeProjection unitSoninScale S)‖ := rfl
    _ ≤ 2 * ‖radialCompressedPositiveTranslation p‖ *
          ‖newSuffixRangeProjection unitSoninScale S‖ := hcomm
    _ ≤ 2 := by
        nlinarith [hcore, hproj, hproj0, hcore0]

/-! ## The boundary channel -/

/-- The radial boundary channel costs at most `32 ‖q_p⁻¹‖` times the
pulled-back antiresonant column norm, pointwise on the full finite-S
carrier.  The inverse Euler coefficient stays visible. -/
theorem norm_radialSoninBoundaryCrossing_apply_le_canonical_antiresonantColumn
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime) (u : finiteSCarrier) :
    ‖radialSoninBoundaryCrossing p S u‖ ≤
      (32 * ‖(ccm24PrimeEulerCoefficient p : ℂ)⁻¹‖) *
        ‖newFrameAntiresonantColumn unitSoninScale p S
          (ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S) u)‖ := by
  have hnorm := norm_fullCarrierBoundaryChannelReadout_apply_le
    (canonicalRadialBoundarySourceColumnFactorizationData p S) u
  rwa [fullCarrierBoundaryChannelReadout_eq_radialSoninBoundaryCrossing
    (canonicalRadialBoundarySourceColumnFactorizationData p S)] at hnorm

/-! ## The two-channel ledger -/

set_option maxHeartbeats 800000 in

/-- The exact split becomes a two-channel pointwise ledger: the frame-loss
commutator costs at most `2‖u‖` from the interior channel plus the visible
boundary-column term. -/
theorem norm_suffixPrimeTranslationProjectionCommutator_apply_le_twoChannel
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime) (u : finiteSCarrier) :
    ‖suffixPrimeTranslationProjectionCommutator p S u‖ ≤
      2 * ‖u‖ + (32 * ‖(ccm24PrimeEulerCoefficient p : ℂ)⁻¹‖) *
        ‖newFrameAntiresonantColumn unitSoninScale p S
          (ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S) u)‖ := by
  have htri : ‖suffixPrimeTranslationProjectionCommutator p S u‖ ≤
      ‖radialInteriorSoninCommutator p S u‖ +
        ‖radialSoninBoundaryCrossing p S u‖ := by
    have hpoint : ‖(radialInteriorSoninCommutator p S +
        radialSoninBoundaryCrossing p S) u‖ =
        ‖suffixPrimeTranslationProjectionCommutator p S u‖ := by
      rw [suffixPrimeTranslationProjectionCommutator_eq_radialInterior_add_boundary]
    rw [← hpoint, ContinuousLinearMap.add_apply]
    exact norm_add_le _ _
  have hint : ‖radialInteriorSoninCommutator p S u‖ ≤ 2 * ‖u‖ := by
    calc ‖radialInteriorSoninCommutator p S u‖
        ≤ ‖radialInteriorSoninCommutator p S‖ * ‖u‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ 2 * ‖u‖ := by
          exact mul_le_mul_of_nonneg_right
            (norm_radialInteriorSoninCommutator_le_two p S) (norm_nonneg _)
  calc ‖suffixPrimeTranslationProjectionCommutator p S u‖
      ≤ ‖radialInteriorSoninCommutator p S u‖ +
          ‖radialSoninBoundaryCrossing p S u‖ := htri
    _ ≤ 2 * ‖u‖ + ‖radialSoninBoundaryCrossing p S u‖ :=
        add_le_add hint le_rfl
    _ ≤ 2 * ‖u‖ + (32 * ‖(ccm24PrimeEulerCoefficient p : ℂ)⁻¹‖) *
        ‖newFrameAntiresonantColumn unitSoninScale p S
          (ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S) u)‖ :=
        add_le_add le_rfl
          (norm_radialSoninBoundaryCrossing_apply_le_canonical_antiresonantColumn
            p S u)

set_option maxHeartbeats 800000 in

/-- Operator-norm corollary: the whole frame-loss commutator is bounded by
`2` plus the visible boundary-column cost, with the pulled-back column
composite carrying the boundary constant. -/
theorem norm_suffixPrimeTranslationProjectionCommutator_le_twoChannel
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime) :
    ‖suffixPrimeTranslationProjectionCommutator p S‖ ≤
      2 + (32 * ‖(ccm24PrimeEulerCoefficient p : ℂ)⁻¹‖) *
        ‖newFrameAntiresonantColumn unitSoninScale p S ∘L
          ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S)‖ := by
  have hnonneg : (0:ℝ) ≤ 2 + (32 * ‖(ccm24PrimeEulerCoefficient p : ℂ)⁻¹‖) *
      ‖newFrameAntiresonantColumn unitSoninScale p S ∘L
        ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S)‖ :=
    add_nonneg (by norm_num)
      (mul_nonneg (mul_nonneg (by norm_num) (norm_nonneg _)) (norm_nonneg _))
  refine ContinuousLinearMap.opNorm_le_bound _ hnonneg ?_
  intro u
  have hledger :=
    norm_suffixPrimeTranslationProjectionCommutator_apply_le_twoChannel p S u
  have hcol : ‖newFrameAntiresonantColumn unitSoninScale p S
      (ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S) u)‖ ≤
      ‖(newFrameAntiresonantColumn unitSoninScale p S ∘L
        ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S))‖ *
        ‖u‖ :=
    ContinuousLinearMap.le_opNorm
      (newFrameAntiresonantColumn unitSoninScale p S ∘L
        ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S)) u
  have hnonnegU : (0:ℝ) ≤ ‖u‖ := norm_nonneg u
  have hnonnegC : (0:ℝ) ≤ 32 * ‖(ccm24PrimeEulerCoefficient p : ℂ)⁻¹‖ :=
    mul_nonneg (by norm_num) (norm_nonneg _)
  calc ‖suffixPrimeTranslationProjectionCommutator p S u‖
      ≤ 2 * ‖u‖ + (32 * ‖(ccm24PrimeEulerCoefficient p : ℂ)⁻¹‖) *
          ‖newFrameAntiresonantColumn unitSoninScale p S
            (ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S)
              u)‖ := hledger
    _ ≤ 2 * ‖u‖ + (32 * ‖(ccm24PrimeEulerCoefficient p : ℂ)⁻¹‖) *
          (‖(newFrameAntiresonantColumn unitSoninScale p S ∘L
              ContinuousLinearMap.adjoint
                (newSuffixFrame unitSoninScale S))‖ * ‖u‖) :=
        add_le_add le_rfl
          (mul_le_mul_of_nonneg_left hcol hnonnegC)
    _ = (2 + (32 * ‖(ccm24PrimeEulerCoefficient p : ℂ)⁻¹‖) *
            ‖(newFrameAntiresonantColumn unitSoninScale p S ∘L
              ContinuousLinearMap.adjoint
                (newSuffixFrame unitSoninScale S))‖) * ‖u‖ := by ring

end C1G8P1RadialCommutatorChannelLedger
end Source
end ConnesWeilRH
