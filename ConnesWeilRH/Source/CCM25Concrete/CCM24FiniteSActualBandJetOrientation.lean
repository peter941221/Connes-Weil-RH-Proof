/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSPairedFirstJetRemainder

/-!
# Actual finite-S band jet orientation

The actual target Sonin projection is first written as one ambient Gram
projection.  Proof 437's paired endpoint identity then applies on the literal
common-log carrier.  Replacing the transport pair by the normalized inverse
reveals the correct band orientation and an exact two-factor gauge remainder.

No trace cycle, trace estimate, Gate 3U premise, or RH premise is used here.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSActualBandJetOrientation

open CC20Concrete
open CCM24FiniteSProjectionTrace
open CCM24FiniteSGramResponse
open CCM24FiniteSCausalSupport
open CCM24FiniteSInverseMetric
open CCM24FiniteSFixedQuotientCarrier
open CCM24FiniteSRootCompletedFirstJet
open CCM24FiniteSPairedFirstJetRemainder

/-! ## Generic inverse-pair algebra -/

variable {A : Type*} [Ring A]

/-- The transport-oriented pair belonging to a band endpoint. -/
def transportBandPair
    (band inner transport transportAdjoint : A) : A :=
  band * transport * inner + inner * transportAdjoint * band

/-- The correctly oriented normalized-inverse pair for the same band. -/
def normalizedInverseBandPair
    (band inner normalizedInverse normalizedInverseAdjoint : A) : A :=
  band * normalizedInverse * inner +
    inner * normalizedInverseAdjoint * band

/-- The gauge correction has two factors which vanish at the identity. -/
def normalizedInverseBandGaugeCorrection
    (band inner transport transportAdjoint normalizedInverse
      normalizedInverseAdjoint : A) : A :=
  band * (1 - normalizedInverse) * (transport - 1) * inner +
    inner * (transportAdjoint - 1) *
      (1 - normalizedInverseAdjoint) * band

/-- The skew part of the normalized inverse after compression to the common
support.  On a Hilbert carrier the second term is the adjoint of the first. -/
def compressedNormalizedInverseSkew
    (support normalizedInverse normalizedInverseAdjoint : A) : A :=
  support * normalizedInverse * support -
    support * normalizedInverseAdjoint * support

/-- Proof 436's paired orientation differs from the actual band orientation
by one commutator with the skew compressed normalized inverse. -/
theorem quotientPairedFirstJet_sub_normalizedInverseBandPair_eq_commutator
    (support band inner normalizedInverse normalizedInverseAdjoint : A)
    (hSupport : support = band + inner)
    (hInner : IsIdempotentElem inner)
    (hBandInner : band * inner = 0)
    (hInnerBand : inner * band = 0) :
    quotientPairedFirstJet band inner normalizedInverse
          normalizedInverseAdjoint -
        normalizedInverseBandPair band inner normalizedInverse
          normalizedInverseAdjoint =
      CCM24FiniteSTwoSidedRootRecombination.commutator inner
        (compressedNormalizedInverseSkew support normalizedInverse
          normalizedInverseAdjoint) := by
  have hInnerSq : inner * inner = inner := hInner
  have hInnerSupport : inner * (band + inner) = inner := by
    rw [mul_add, hInnerBand, hInnerSq, zero_add]
  have hSupportInner : (band + inner) * inner = inner := by
    rw [add_mul, hBandInner, hInnerSq, zero_add]
  rw [hSupport]
  unfold quotientPairedFirstJet quotientForwardFirstJet
    quotientReverseFirstJet normalizedInverseBandPair
    compressedNormalizedInverseSkew
    CCM24FiniteSTwoSidedRootRecombination.commutator
  symm
  calc
    inner *
          ((band + inner) * normalizedInverse * (band + inner) -
            (band + inner) * normalizedInverseAdjoint * (band + inner)) -
        ((band + inner) * normalizedInverse * (band + inner) -
            (band + inner) * normalizedInverseAdjoint * (band + inner)) *
          inner =
        (inner * (band + inner)) * normalizedInverse * (band + inner) -
          (inner * (band + inner)) * normalizedInverseAdjoint *
            (band + inner) -
          (band + inner) * normalizedInverse * ((band + inner) * inner) +
          (band + inner) * normalizedInverseAdjoint *
            ((band + inner) * inner) := by
      noncomm_ring
    _ = inner * normalizedInverse * (band + inner) -
          inner * normalizedInverseAdjoint * (band + inner) -
          (band + inner) * normalizedInverse * inner +
          (band + inner) * normalizedInverseAdjoint * inner := by
      rw [hInnerSupport, hSupportInner]
    _ = inner * normalizedInverse * band +
          band * normalizedInverseAdjoint * inner -
          (band * normalizedInverse * inner +
            inner * normalizedInverseAdjoint * band) := by
      noncomm_ring

/-- Multiplying an orientation commutator by a detector leaves a fixed
detector commutator plus a residual commutator.  Removing the latter requires
a separate trace-cycle theorem in infinite dimension. -/
theorem detector_mul_commutator_eq_fixed_add_residual
    (detector inner skew : A) :
    detector * CCM24FiniteSTwoSidedRootRecombination.commutator inner skew =
      CCM24FiniteSTwoSidedRootRecombination.commutator detector inner * skew +
        CCM24FiniteSTwoSidedRootRecombination.commutator inner
          (detector * skew) := by
  unfold CCM24FiniteSTwoSidedRootRecombination.commutator
  noncomm_ring

/-- If the normalized inverse times the transport is scalar on the two
off-diagonal corners, the negative transport pair is the normalized inverse
pair minus an exact two-factor correction. -/
theorem neg_transportBandPair_eq_normalizedInversePair_sub_gaugeCorrection
    (band inner transport transportAdjoint normalizedInverse
      normalizedInverseAdjoint : A)
    (hBandInner : band * inner = 0)
    (hInnerBand : inner * band = 0)
    (hNormalizedTransport :
      band * (normalizedInverse * transport) * inner = 0)
    (hAdjointNormalized :
      inner * (transportAdjoint * normalizedInverseAdjoint) * band = 0) :
    -transportBandPair band inner transport transportAdjoint =
      normalizedInverseBandPair band inner normalizedInverse
          normalizedInverseAdjoint -
        normalizedInverseBandGaugeCorrection band inner transport
          transportAdjoint normalizedInverse normalizedInverseAdjoint := by
  have hForward :
      -band * transport * inner =
        band * normalizedInverse * inner -
          band * (1 - normalizedInverse) * (transport - 1) * inner := by
    symm
    calc
      band * normalizedInverse * inner -
            band * (1 - normalizedInverse) * (transport - 1) * inner =
          -band * transport * inner + band * inner +
            band * (normalizedInverse * transport) * inner := by
              noncomm_ring
      _ = -band * transport * inner := by
        rw [hBandInner, hNormalizedTransport]
        simp
  have hReverse :
      -inner * transportAdjoint * band =
        inner * normalizedInverseAdjoint * band -
          inner * (transportAdjoint - 1) *
            (1 - normalizedInverseAdjoint) * band := by
    symm
    calc
      inner * normalizedInverseAdjoint * band -
            inner * (transportAdjoint - 1) *
              (1 - normalizedInverseAdjoint) * band =
          -inner * transportAdjoint * band + inner * band +
            inner * (transportAdjoint * normalizedInverseAdjoint) * band := by
              noncomm_ring
      _ = -inner * transportAdjoint * band := by
        rw [hInnerBand, hAdjointNormalized]
        simp
  have hReverseFull :
      -(inner * transportAdjoint * band) =
        inner * normalizedInverseAdjoint * band -
          inner * (transportAdjoint - 1) *
            (1 - normalizedInverseAdjoint) * band := by
    calc
      -(inner * transportAdjoint * band) =
          -inner * transportAdjoint * band := by noncomm_ring
      _ = _ := hReverse
  unfold transportBandPair normalizedInverseBandPair
    normalizedInverseBandGaugeCorrection
  calc
    -(band * transport * inner + inner * transportAdjoint * band) =
        -band * transport * inner - inner * transportAdjoint * band := by
          noncomm_ring
    _ = (band * normalizedInverse * inner -
          band * (1 - normalizedInverse) * (transport - 1) * inner) +
        (-(inner * transportAdjoint * band)) := by
      rw [hForward, sub_eq_add_neg]
    _ = (band * normalizedInverse * inner -
          band * (1 - normalizedInverse) * (transport - 1) * inner) +
        (inner * normalizedInverseAdjoint * band -
          inner * (transportAdjoint - 1) *
            (1 - normalizedInverseAdjoint) * band) := by
      rw [hReverseFull]
    _ = _ := by noncomm_ring

/-! ## The actual ambient Gram producer -/

local notation "Op" => finiteSCarrier →L[ℂ] finiteSCarrier

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- The restricted source Gram inverse lifted to the ambient carrier. -/
noncomputable def finiteEulerSourceGramInvAmbient
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) : Op :=
  sourceInclusion lambda ∘L finiteEulerGramInv lambda family ∘L
    ContinuousLinearMap.adjoint (sourceInclusion lambda)

theorem sourceSoninProjection_comp_sourceGramInvAmbient
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninProjection lambda ∘L
        finiteEulerSourceGramInvAmbient lambda family =
      finiteEulerSourceGramInvAmbient lambda family := by
  rw [← sourceInclusion_comp_adjoint lambda]
  apply ContinuousLinearMap.ext
  intro u
  simp only [finiteEulerSourceGramInvAmbient,
    ContinuousLinearMap.comp_apply]
  have hJ := congrFun (congrArg DFunLike.coe
    (sourceInclusion_adjoint_comp_self lambda))
      (finiteEulerGramInv lambda family
        (ContinuousLinearMap.adjoint (sourceInclusion lambda) u))
  simpa only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply] using congrArg (sourceInclusion lambda) hJ

theorem sourceGramInvAmbient_comp_sourceSoninProjection
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteEulerSourceGramInvAmbient lambda family ∘L
        sourceSoninProjection lambda =
      finiteEulerSourceGramInvAmbient lambda family := by
  rw [← sourceInclusion_comp_adjoint lambda]
  apply ContinuousLinearMap.ext
  intro u
  simp only [finiteEulerSourceGramInvAmbient,
    ContinuousLinearMap.comp_apply]
  have hJ := congrFun (congrArg DFunLike.coe
    (sourceInclusion_adjoint_comp_self lambda))
      (ContinuousLinearMap.adjoint (sourceInclusion lambda) u)
  simpa only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply] using
      congrArg (fun v => sourceInclusion lambda
        (finiteEulerGramInv lambda family v)) hJ

/-- The actual finite-S Sonin projection in one ambient Gram formula. -/
theorem targetSoninProjection_eq_ambientGramProjection
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    targetSoninProjection lambda family =
      finiteEulerTransportOperator family ∘L
        finiteEulerSourceGramInvAmbient lambda family ∘L
          ContinuousLinearMap.adjoint
            (finiteEulerTransportOperator family) := by
  rw [targetSoninProjection_eq_dualFrame_comp_frameAdjoint,
    finiteEulerDualFrame, finiteEulerFrame_eq_transport_comp_inclusion,
    ContinuousLinearMap.adjoint_comp]
  apply ContinuousLinearMap.ext
  intro u
  rfl

/-- The same formula with the source projection blocks exposed for Proof 437. -/
theorem targetSoninProjection_eq_blockedAmbientGramProjection
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    targetSoninProjection lambda family =
      finiteEulerTransportOperator family ∘L
        sourceSoninProjection lambda ∘L
          finiteEulerSourceGramInvAmbient lambda family ∘L
            sourceSoninProjection lambda ∘L
              ContinuousLinearMap.adjoint
                (finiteEulerTransportOperator family) := by
  rw [targetSoninProjection_eq_ambientGramProjection]
  have hLeft := sourceSoninProjection_comp_sourceGramInvAmbient lambda family
  have hRight := sourceGramInvAmbient_comp_sourceSoninProjection lambda family
  apply ContinuousLinearMap.ext
  intro u
  have hLeftAt := congrFun (congrArg DFunLike.coe hLeft)
    (ContinuousLinearMap.adjoint (finiteEulerTransportOperator family) u)
  have hRightAt := congrFun (congrArg DFunLike.coe hRight)
    (ContinuousLinearMap.adjoint (finiteEulerTransportOperator family) u)
  simp only [ContinuousLinearMap.comp_apply] at hLeftAt hRightAt ⊢
  rw [hRightAt, hLeftAt]

/-! ## Actual endpoint decomposition -/

/-- The paired transport jet of the actual target Sonin projection. -/
noncomputable def sourceSoninTransportPairedJet
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) : Op :=
  quotientPairedFirstJet (sourceSoninProjection lambda)
    (sourceBandProjection lambda) (finiteEulerTransportOperator family)
    (ContinuousLinearMap.adjoint (finiteEulerTransportOperator family))

/-- Proof 437's complete Gram remainder for the actual target Sonin
projection, before changing from `R_S-R_0` to `B_S-B_0`. -/
noncomputable def sourceSoninGramQuadraticRemainder
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) : Op :=
  gramProjectionQuadraticRemainder (radialSupportProjection lambda)
    (sourceSoninProjection lambda) (sourceBandProjection lambda)
    (targetSoninProjection lambda family) (finiteEulerTransportOperator family)
    (ContinuousLinearMap.adjoint (finiteEulerTransportOperator family))
    (finiteEulerSourceGramInvAmbient lambda family)

/-- Actual-carrier instantiation of Proof 437 for `R_S-R_0`. -/
theorem soninProjectionDifference_eq_transportPairedJet_add_gramRemainder
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    bandDifference lambda family =
      sourceSoninTransportPairedJet lambda family +
        sourceSoninGramQuadraticRemainder lambda family := by
  have hSupport : radialSupportProjection lambda =
      sourceSoninProjection lambda + sourceBandProjection lambda := by
    unfold sourceBandProjection
    abel
  have hInnerBand : sourceBandProjection lambda *
      sourceSoninProjection lambda = 0 := by
    simpa only [ContinuousLinearMap.mul_def] using
      sourceBandProjection_comp_sourceSoninProjection_eq_zero lambda
  have hBandInner : sourceSoninProjection lambda *
      sourceBandProjection lambda = 0 := by
    simpa only [ContinuousLinearMap.mul_def] using
      sourceSoninProjection_comp_sourceBandProjection_eq_zero lambda
  have hSupportTarget : radialSupportProjection lambda *
      targetSoninProjection lambda family = targetSoninProjection lambda family := by
    simpa only [ContinuousLinearMap.mul_def] using
      radialSupportProjection_comp_targetSoninProjection lambda family
  have hTargetSupport : targetSoninProjection lambda family *
      radialSupportProjection lambda = targetSoninProjection lambda family := by
    simpa only [ContinuousLinearMap.mul_def] using
      targetSoninProjection_comp_radialSupportProjection lambda family
  simpa only [bandDifference, sourceSoninTransportPairedJet,
      sourceSoninGramQuadraticRemainder, ContinuousLinearMap.mul_def] using
    (gramProjectionDifference_eq_pairedFirstJet_add_quadraticRemainder
      (radialSupportProjection lambda) (sourceSoninProjection lambda)
      (sourceBandProjection lambda) (targetSoninProjection lambda family)
      (finiteEulerTransportOperator family)
      (ContinuousLinearMap.adjoint (finiteEulerTransportOperator family))
      (finiteEulerSourceGramInvAmbient lambda family) hSupport
      (sourceSoninProjection_isStarProjection lambda).isIdempotentElem
      (sourceBandProjection_isStarProjection lambda).isIdempotentElem
      hBandInner hInnerBand
      (targetSoninProjection_isStarProjection lambda family).isIdempotentElem
      hSupportTarget hTargetSupport
      (targetSoninProjection_eq_blockedAmbientGramProjection lambda family))

/-! ## Gauge-normalized inverse orientation -/

/-- The correctly oriented normalized-inverse pair for the actual band. -/
noncomputable def sourceActualBandNormalizedInversePairedJet
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) : Op :=
  normalizedInverseBandPair (sourceBandProjection lambda)
    (sourceSoninProjection lambda) (normalizedFiniteEulerInverse family)
    (ContinuousLinearMap.adjoint (normalizedFiniteEulerInverse family))

/-- The exact two-factor correction introduced when the transport pair is
replaced by the gauge-normalized inverse pair. -/
noncomputable def sourceActualBandGaugeQuadraticCorrection
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) : Op :=
  normalizedInverseBandGaugeCorrection (sourceBandProjection lambda)
    (sourceSoninProjection lambda) (finiteEulerTransportOperator family)
    (ContinuousLinearMap.adjoint (finiteEulerTransportOperator family))
    (normalizedFiniteEulerInverse family)
    (ContinuousLinearMap.adjoint (normalizedFiniteEulerInverse family))

theorem normalizedInverse_comp_transport_eq_lowerFactor_smul_id
    (family : FinitePrimePowerFamily) :
    normalizedFiniteEulerInverse family ∘L
        finiteEulerTransportOperator family =
      (finiteEulerLowerFactor family.visiblePrimes : ℂ) •
        ContinuousLinearMap.id ℂ finiteSCarrier := by
  apply ContinuousLinearMap.ext
  intro u
  have hInverse := congrFun (congrArg DFunLike.coe
    (inverse_comp_transport family)) u
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smul_apply] at hInverse ⊢
  rw [normalizedFiniteEulerInverse, ContinuousLinearMap.smul_apply, hInverse]

theorem sourceBand_normalizedInverse_transport_sourceSonin_eq_zero
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceBandProjection lambda ∘L
        (normalizedFiniteEulerInverse family ∘L
          finiteEulerTransportOperator family) ∘L
      sourceSoninProjection lambda = 0 := by
  rw [normalizedInverse_comp_transport_eq_lowerFactor_smul_id]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, map_smul]
  have hzero := congrFun (congrArg DFunLike.coe
    (sourceBandProjection_comp_sourceSoninProjection_eq_zero lambda)) u
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.zero_apply] at hzero
  rw [hzero, smul_zero]
  simp only [ContinuousLinearMap.zero_apply]

theorem sourceSonin_transportAdjoint_normalizedAdjoint_band_eq_zero
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninProjection lambda ∘L
        (ContinuousLinearMap.adjoint (finiteEulerTransportOperator family) ∘L
          ContinuousLinearMap.adjoint
            (normalizedFiniteEulerInverse family)) ∘L
      sourceBandProjection lambda = 0 := by
  have h := congrArg ContinuousLinearMap.adjoint
    (sourceBand_normalizedInverse_transport_sourceSonin_eq_zero lambda family)
  simpa only [ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint,
    map_zero,
    (sourceBandProjection_isStarProjection lambda).isSelfAdjoint.adjoint_eq,
    (sourceSoninProjection_isStarProjection lambda).isSelfAdjoint.adjoint_eq]
    using h

theorem neg_sourceSoninTransportPairedJet_eq_actualNormalizedPair_sub_correction
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    -sourceSoninTransportPairedJet lambda family =
      sourceActualBandNormalizedInversePairedJet lambda family -
        sourceActualBandGaugeQuadraticCorrection lambda family := by
  have hBandInner : sourceBandProjection lambda *
      sourceSoninProjection lambda = 0 := by
    simpa only [ContinuousLinearMap.mul_def] using
      sourceBandProjection_comp_sourceSoninProjection_eq_zero lambda
  have hInnerBand : sourceSoninProjection lambda *
      sourceBandProjection lambda = 0 := by
    simpa only [ContinuousLinearMap.mul_def] using
      sourceSoninProjection_comp_sourceBandProjection_eq_zero lambda
  have hNormalized : sourceBandProjection lambda *
      (normalizedFiniteEulerInverse family *
        finiteEulerTransportOperator family) *
      sourceSoninProjection lambda = 0 := by
    simpa only [ContinuousLinearMap.mul_def] using
      sourceBand_normalizedInverse_transport_sourceSonin_eq_zero lambda family
  have hAdjoint : sourceSoninProjection lambda *
      (ContinuousLinearMap.adjoint (finiteEulerTransportOperator family) *
        ContinuousLinearMap.adjoint
          (normalizedFiniteEulerInverse family)) *
      sourceBandProjection lambda = 0 := by
    simpa only [ContinuousLinearMap.mul_def] using
      sourceSonin_transportAdjoint_normalizedAdjoint_band_eq_zero lambda family
  simpa only [sourceSoninTransportPairedJet,
      quotientPairedFirstJet, quotientForwardFirstJet,
      quotientReverseFirstJet, sourceActualBandNormalizedInversePairedJet,
      sourceActualBandGaugeQuadraticCorrection,
      ContinuousLinearMap.mul_def] using
    (neg_transportBandPair_eq_normalizedInversePair_sub_gaugeCorrection
      (sourceBandProjection lambda) (sourceSoninProjection lambda)
      (finiteEulerTransportOperator family)
      (ContinuousLinearMap.adjoint (finiteEulerTransportOperator family))
      (normalizedFiniteEulerInverse family)
      (ContinuousLinearMap.adjoint (normalizedFiniteEulerInverse family))
      hBandInner hInnerBand
      hNormalized hAdjoint)

/-- The complete actual endpoint remainder after extracting the correctly
oriented normalized-inverse pair. -/
noncomputable def sourceActualBandQuadraticRemainder
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) : Op :=
  sourceActualBandGaugeQuadraticCorrection lambda family +
    sourceSoninGramQuadraticRemainder lambda family

/-! ## Proof 436 versus the actual band orientation -/

/-- The skew part of the normalized inverse compressed to the literal common
support carrier. -/
noncomputable def sourceFiniteEulerCompressedSkew
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) : Op :=
  radialSupportProjection lambda ∘L normalizedFiniteEulerInverse family ∘L
      radialSupportProjection lambda -
    radialSupportProjection lambda ∘L
      ContinuousLinearMap.adjoint (normalizedFiniteEulerInverse family) ∘L
        radialSupportProjection lambda

/-- The displayed skew compression is genuinely an operator minus its
Hilbert adjoint. -/
theorem sourceFiniteEulerCompressedSkew_eq_compression_sub_adjoint
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceFiniteEulerCompressedSkew lambda family =
      (radialSupportProjection lambda ∘L
          normalizedFiniteEulerInverse family ∘L
            radialSupportProjection lambda) -
        ContinuousLinearMap.adjoint
          (radialSupportProjection lambda ∘L
            normalizedFiniteEulerInverse family ∘L
              radialSupportProjection lambda) := by
  rw [sourceFiniteEulerCompressedSkew,
    ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    (radialSupportProjection_isStarProjection lambda)
      |>.isSelfAdjoint.adjoint_eq]
  apply ContinuousLinearMap.ext
  intro u
  rfl

/-- The exact first-order owner missed when Proof 436's Sonin-to-band pair is
used for the actual band-to-Sonin endpoint orientation. -/
noncomputable def sourceFiniteEulerPairedJetOrientationCommutator
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) : Op :=
  CCM24FiniteSTwoSidedRootRecombination.commutator
    (sourceSoninProjection lambda)
    (sourceFiniteEulerCompressedSkew lambda family)

/-- Exact actual-carrier direction audit: the Proof 436 pair minus the actual
band pair is the compressed-skew commutator. -/
theorem sourceFiniteEulerPairedFirstJet_sub_actualBandPair_eq_orientation
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceFiniteEulerPairedFirstJet lambda family -
        sourceActualBandNormalizedInversePairedJet lambda family =
      sourceFiniteEulerPairedJetOrientationCommutator lambda family := by
  have hSupport : radialSupportProjection lambda =
      sourceBandProjection lambda + sourceSoninProjection lambda := by
    unfold sourceBandProjection
    abel
  have hBandInner : sourceBandProjection lambda *
      sourceSoninProjection lambda = 0 := by
    simpa only [ContinuousLinearMap.mul_def] using
      sourceBandProjection_comp_sourceSoninProjection_eq_zero lambda
  have hInnerBand : sourceSoninProjection lambda *
      sourceBandProjection lambda = 0 := by
    simpa only [ContinuousLinearMap.mul_def] using
      sourceSoninProjection_comp_sourceBandProjection_eq_zero lambda
  simpa only [sourceFiniteEulerPairedFirstJet,
      CCM24FiniteSFixedQuotientFirstJet.quotientBandVariation,
      sourceActualBandNormalizedInversePairedJet,
      sourceFiniteEulerPairedJetOrientationCommutator,
      sourceFiniteEulerCompressedSkew, compressedNormalizedInverseSkew,
      ContinuousLinearMap.mul_def] using
    (quotientPairedFirstJet_sub_normalizedInverseBandPair_eq_commutator
      (radialSupportProjection lambda) (sourceBandProjection lambda)
      (sourceSoninProjection lambda) (normalizedFiniteEulerInverse family)
      (ContinuousLinearMap.adjoint (normalizedFiniteEulerInverse family))
      hSupport
      (sourceSoninProjection_isStarProjection lambda).isIdempotentElem
      hBandInner hInnerBand)

/-- The detector ledger exposes both the fixed source commutator and the
residual commutator whose trace cannot be discarded without legality. -/
theorem detector_comp_orientationCommutator_eq_fixed_add_residual
    (detector : Op) (lambda : CCM24SoninScale)
    (family : FinitePrimePowerFamily) :
    detector ∘L sourceFiniteEulerPairedJetOrientationCommutator lambda family =
      CCM24FiniteSTwoSidedRootRecombination.commutator detector
          (sourceSoninProjection lambda) ∘L
            sourceFiniteEulerCompressedSkew lambda family +
        CCM24FiniteSTwoSidedRootRecombination.commutator
          (sourceSoninProjection lambda)
          (detector ∘L sourceFiniteEulerCompressedSkew lambda family) := by
  simpa only [sourceFiniteEulerPairedJetOrientationCommutator,
      ContinuousLinearMap.mul_def] using
    (detector_mul_commutator_eq_fixed_add_residual detector
      (sourceSoninProjection lambda)
      (sourceFiniteEulerCompressedSkew lambda family))

/-- Exact actual-carrier endpoint decomposition with the normalized inverse
pair in the correct band orientation. -/
theorem soninBandDifference_eq_actualNormalizedPair_sub_quadraticRemainder
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    soninBandDifference lambda family =
      sourceActualBandNormalizedInversePairedJet lambda family -
        sourceActualBandQuadraticRemainder lambda family := by
  rw [soninBandDifference_eq_neg_soninProjectionDifference,
    soninProjectionDifference_eq_transportPairedJet_add_gramRemainder]
  calc
    -(sourceSoninTransportPairedJet lambda family +
          sourceSoninGramQuadraticRemainder lambda family) =
        -sourceSoninTransportPairedJet lambda family -
          sourceSoninGramQuadraticRemainder lambda family := by
            noncomm_ring
    _ = (sourceActualBandNormalizedInversePairedJet lambda family -
          sourceActualBandGaugeQuadraticCorrection lambda family) -
        sourceSoninGramQuadraticRemainder lambda family := by
      rw [neg_sourceSoninTransportPairedJet_eq_actualNormalizedPair_sub_correction]
    _ = _ := by
      unfold sourceActualBandQuadraticRemainder
      noncomm_ring

/-- The complete endpoint ledger relative to Proof 436.  The orientation
commutator is first order; only the final remainder is quadratic. -/
theorem soninBandDifference_eq_proof436Pair_sub_orientation_sub_quadratic
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    soninBandDifference lambda family =
      sourceFiniteEulerPairedFirstJet lambda family -
        sourceFiniteEulerPairedJetOrientationCommutator lambda family -
          sourceActualBandQuadraticRemainder lambda family := by
  rw [soninBandDifference_eq_actualNormalizedPair_sub_quadraticRemainder]
  have hOrientation :=
    sourceFiniteEulerPairedFirstJet_sub_actualBandPair_eq_orientation
      lambda family
  have hActual :
      sourceActualBandNormalizedInversePairedJet lambda family =
        sourceFiniteEulerPairedFirstJet lambda family -
          sourceFiniteEulerPairedJetOrientationCommutator lambda family := by
    calc
      sourceActualBandNormalizedInversePairedJet lambda family =
          sourceFiniteEulerPairedFirstJet lambda family -
            (sourceFiniteEulerPairedFirstJet lambda family -
              sourceActualBandNormalizedInversePairedJet lambda family) := by
                noncomm_ring
      _ = _ := by rw [hOrientation]
  rw [hActual]

end CCM24FiniteSActualBandJetOrientation
end CCM25Concrete
end Source
end ConnesWeilRH
