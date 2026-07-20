/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSRootCompletedFirstJet

/-!
# Paired fixed-quotient first jet and exact endpoint remainder

The first variation of an orthogonal Gram projection has two orientations.
This module keeps the forward transport corner and its adjoint together, then
decomposes the finite projection endpoint into that Hermitian pair and terms
which contain two boundary or coframe defects.

The physical reflected-outer branch remains inside the fixed detector
commutator.  It is not used as a substitute for the adjoint transport jet.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSPairedFirstJetRemainder

open CC20Concrete
open CCM24FiniteSProjectionTrace
open CCM24FiniteSGramResponse
open CCM24FiniteSBandTrace
open CCM24FiniteSCausalSupport
open CCM24FiniteSInverseMetric
open CCM24FiniteSFixedQuotientFirstJet
open CCM24FiniteSFixedQuotientCarrier
open CCM24FiniteSRootCompletedFirstJet
open scoped InnerProduct

/-! ## Generic noncommutative endpoint algebra -/

variable {A : Type*} [Ring A]

/-- The two off-diagonal blocks of a target projection relative to the source
band/inner splitting. -/
def endpointOffDiagonalPair (band inner target : A) : A :=
  inner * target * band + band * target * inner

/-- The two diagonal endpoint defects.  The second term is kept as a product
of the two missed-range crossings. -/
def endpointSquareRemainder
    (support band inner target : A) : A :=
  inner * target * inner -
    (band * (support - target)) * ((support - target) * band)

/-- The forward fixed-quotient transport corner. -/
def quotientForwardFirstJet (band inner transport : A) : A :=
  inner * transport * band

/-- The reverse fixed-quotient transport corner. -/
def quotientReverseFirstJet (band inner transportAdjoint : A) : A :=
  band * transportAdjoint * inner

/-- The complete Hermitian first jet. -/
def quotientPairedFirstJet
    (band inner transport transportAdjoint : A) : A :=
  quotientForwardFirstJet band inner transport +
    quotientReverseFirstJet band inner transportAdjoint

/-- The band-side coframe defect following the forward crossing. -/
def quotientBandCoframeDefect
    (band transportAdjoint gramInverse : A) : A :=
  gramInverse * band * transportAdjoint * band - band

/-- The reverse band-side coframe defect. -/
def quotientBandReverseCoframeDefect
    (band transport gramInverse : A) : A :=
  band * transport * band * gramInverse - band

/-- Every summand contains two quantities which vanish at the identity
endpoint: crossing/coframe, crossing/crossing, or missed/missed. -/
def gramProjectionQuadraticRemainder
    (support band inner target transport transportAdjoint gramInverse : A) : A :=
  quotientForwardFirstJet band inner transport *
      quotientBandCoframeDefect band transportAdjoint gramInverse +
    quotientBandReverseCoframeDefect band transport gramInverse *
      quotientReverseFirstJet band inner transportAdjoint +
    quotientForwardFirstJet band inner transport * gramInverse *
      quotientReverseFirstJet band inner transportAdjoint -
    (band * (support - target)) * ((support - target) * band)

theorem quotientBandVariation_eq_pairedFirstJet
    (band inner transport transportAdjoint : A) :
    quotientBandVariation band inner transport transportAdjoint =
      quotientPairedFirstJet band inner transport transportAdjoint := by
  rfl

/-- Exact block decomposition of two nested orthogonal projections.  No
trace, positivity, or analytic estimate is used. -/
theorem endpointProjectionDifference_eq_offDiagonal_add_squareRemainder
    (support band inner target : A)
    (hSupport : support = band + inner)
    (hBand : IsIdempotentElem band)
    (hInner : IsIdempotentElem inner)
    (hBandInner : band * inner = 0)
    (hInnerBand : inner * band = 0)
    (hTarget : IsIdempotentElem target)
    (hSupportTarget : support * target = target)
    (hTargetSupport : target * support = target) :
    target - band =
      endpointOffDiagonalPair band inner target +
        endpointSquareRemainder support band inner target := by
  have hBandSq : band * band = band := hBand
  have hInnerSq : inner * inner = inner := hInner
  have hTargetSq : target * target = target := hTarget
  have hSupportSq : support * support = support := by
    rw [hSupport]
    calc
      (band + inner) * (band + inner) =
          band * band + band * inner + inner * band + inner * inner := by
            noncomm_ring
      _ = band + inner := by
        rw [hBandSq, hInnerSq, hBandInner, hInnerBand]
        simp
  have hComplementSq :
      (support - target) * (support - target) = support - target := by
    calc
      (support - target) * (support - target) =
          support * support - support * target - target * support +
            target * target := by
              noncomm_ring
      _ = support - target := by
        rw [hSupportSq, hSupportTarget, hTargetSupport, hTargetSq]
        noncomm_ring
  have hBandSupportBand : band * support * band = band := by
    rw [hSupport]
    calc
      band * (band + inner) * band =
          (band * band) * band + (band * inner) * band := by
            noncomm_ring
      _ = band := by
        rw [hBandSq, hBandInner, zero_mul, add_zero, hBandSq]
  have hTargetCorner : target = support * target * support := by
    calc
      target = support * target := hSupportTarget.symm
      _ = support * (target * support) := by rw [hTargetSupport]
      _ = support * target * support := by rw [mul_assoc]
  have hMissedSquare :
      (band * (support - target)) * ((support - target) * band) =
        band - band * target * band := by
    calc
      (band * (support - target)) * ((support - target) * band) =
          band * ((support - target) * (support - target)) * band := by
            noncomm_ring
      _ = band * (support - target) * band := by rw [hComplementSq]
      _ = band * support * band - band * target * band := by
        noncomm_ring
      _ = band - band * target * band := by rw [hBandSupportBand]
  have hTargetBlocks :
      target = band * target * band + band * target * inner +
        inner * target * band + inner * target * inner := by
    calc
      target = support * target * support := hTargetCorner
      _ = (band + inner) * target * (band + inner) := by rw [hSupport]
      _ = band * target * band + band * target * inner +
          inner * target * band + inner * target * inner := by
            noncomm_ring
  unfold endpointOffDiagonalPair endpointSquareRemainder
  rw [hMissedSquare]
  calc
    target - band =
        (band * target * band + band * target * inner +
          inner * target * band + inner * target * inner) - band := by
            exact congrArg (fun value => value - band) hTargetBlocks
    _ = inner * target * band + band * target * inner +
        (inner * target * inner - (band - band * target * band)) := by
          noncomm_ring

/-- The forward off-diagonal block is the raw forward jet followed by its
band coframe correction. -/
theorem inner_gramProjection_band_eq_forward_add_correction
    (band inner target transport transportAdjoint gramInverse : A)
    (hBand : IsIdempotentElem band)
    (hTarget : target =
      transport * band * gramInverse * band * transportAdjoint) :
    inner * target * band =
      quotientForwardFirstJet band inner transport +
        quotientForwardFirstJet band inner transport *
          quotientBandCoframeDefect band transportAdjoint gramInverse := by
  have hBandSq : band * band = band := hBand
  have hForwardBand :
      inner * transport * band * band = inner * transport * band := by
    calc
      inner * transport * band * band =
          inner * transport * (band * band) := by noncomm_ring
      _ = inner * transport * band := by rw [hBandSq]
  rw [hTarget]
  unfold quotientForwardFirstJet quotientBandCoframeDefect
  calc
    inner * (transport * band * gramInverse * band * transportAdjoint) * band =
        (inner * transport * band) *
          (gramInverse * band * transportAdjoint * band) := by
            noncomm_ring
    _ = inner * transport * band +
          inner * transport * band *
            (gramInverse * band * transportAdjoint * band - band) := by
      rw [mul_sub, hForwardBand]
      noncomm_ring

/-- The reverse off-diagonal block is the reverse coframe correction followed
by the raw reverse jet. -/
theorem band_gramProjection_inner_eq_reverse_add_correction
    (band inner target transport transportAdjoint gramInverse : A)
    (hBand : IsIdempotentElem band)
    (hTarget : target =
      transport * band * gramInverse * band * transportAdjoint) :
    band * target * inner =
      quotientReverseFirstJet band inner transportAdjoint +
        quotientBandReverseCoframeDefect band transport gramInverse *
          quotientReverseFirstJet band inner transportAdjoint := by
  have hBandSq : band * band = band := hBand
  have hBandReverse :
      band * (band * transportAdjoint * inner) =
        band * transportAdjoint * inner := by
    calc
      band * (band * transportAdjoint * inner) =
          (band * band) * transportAdjoint * inner := by noncomm_ring
      _ = band * transportAdjoint * inner := by rw [hBandSq]
  rw [hTarget]
  unfold quotientReverseFirstJet quotientBandReverseCoframeDefect
  calc
    band * (transport * band * gramInverse * band * transportAdjoint) * inner =
        (band * transport * band * gramInverse) *
          (band * transportAdjoint * inner) := by
            noncomm_ring
    _ = band * transportAdjoint * inner +
          (band * transport * band * gramInverse - band) *
            (band * transportAdjoint * inner) := by
      rw [sub_mul, hBandReverse]
      noncomm_ring

/-- The target block landing in the old inner space contains both oriented
transport crossings. -/
theorem inner_gramProjection_inner_eq_two_crossings
    (band inner target transport transportAdjoint gramInverse : A)
    (hTarget : target =
      transport * band * gramInverse * band * transportAdjoint) :
    inner * target * inner =
      quotientForwardFirstJet band inner transport * gramInverse *
        quotientReverseFirstJet band inner transportAdjoint := by
  rw [hTarget]
  unfold quotientForwardFirstJet quotientReverseFirstJet
  noncomm_ring

/-- Exact Gram endpoint decomposition.  Subtracting only the forward jet
leaves the reverse jet at first order; subtracting the pair leaves the four
displayed quadratic products. -/
theorem gramProjectionDifference_eq_pairedFirstJet_add_quadraticRemainder
    (support band inner target transport transportAdjoint gramInverse : A)
    (hSupport : support = band + inner)
    (hBand : IsIdempotentElem band)
    (hInner : IsIdempotentElem inner)
    (hBandInner : band * inner = 0)
    (hInnerBand : inner * band = 0)
    (hTargetIdempotent : IsIdempotentElem target)
    (hSupportTarget : support * target = target)
    (hTargetSupport : target * support = target)
    (hTarget : target =
      transport * band * gramInverse * band * transportAdjoint) :
    target - band =
      quotientPairedFirstJet band inner transport transportAdjoint +
        gramProjectionQuadraticRemainder support band inner target transport
          transportAdjoint gramInverse := by
  rw [endpointProjectionDifference_eq_offDiagonal_add_squareRemainder
    support band inner target hSupport hBand hInner hBandInner hInnerBand
    hTargetIdempotent hSupportTarget hTargetSupport]
  unfold endpointOffDiagonalPair endpointSquareRemainder
  rw [inner_gramProjection_band_eq_forward_add_correction band inner target
      transport transportAdjoint gramInverse hBand hTarget,
    band_gramProjection_inner_eq_reverse_add_correction band inner target
      transport transportAdjoint gramInverse hBand hTarget,
    inner_gramProjection_inner_eq_two_crossings band inner target transport
      transportAdjoint gramInverse hTarget]
  unfold quotientPairedFirstJet gramProjectionQuadraticRemainder
  noncomm_ring

/-! ## Actual finite-S band endpoint -/

local notation "Op" => finiteSCarrier →L[ℂ] finiteSCarrier

noncomputable local instance targetSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    CompleteSpace
      (ccm24SemilocalSoninClosedSubspace lambda family.visiblePrimes).toSubmodule :=
  (ccm24SemilocalSoninClosedSubspace lambda family.visiblePrimes)
    |>.isClosed.completeSpace_coe

noncomputable local instance targetSoninIntersectionCompleteSpace
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    CompleteSpace
      (↥(((ccm24LogRadialSupportClosedSubspace lambda).toSubmodule) ⊓
        ((ccm24SemilocalFourierSupportClosedSubspace lambda
          family.visiblePrimes).toSubmodule))) :=
  (ccm24SemilocalSoninClosedSubspace lambda family.visiblePrimes)
    |>.isClosed.completeSpace_coe

/-- The actual finite-S Sonin projection is absorbed by the common radial
support projection on the left. -/
theorem radialSupportProjection_comp_targetSoninProjection
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    radialSupportProjection lambda ∘L targetSoninProjection lambda family =
      targetSoninProjection lambda family := by
  simpa [radialSupportProjection, targetSoninProjection,
    ccm24SemilocalSoninClosedSubspace] using
    (_root_.ConnesWeilRH.CC20Concrete.left_starProjection_absorbs_intersection
      (ccm24LogRadialSupportClosedSubspace lambda).toSubmodule
      (ccm24SemilocalFourierSupportClosedSubspace lambda
        family.visiblePrimes).toSubmodule)

/-- The same target Sonin projection is absorbed on the right. -/
theorem targetSoninProjection_comp_radialSupportProjection
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    targetSoninProjection lambda family ∘L radialSupportProjection lambda =
      targetSoninProjection lambda family := by
  simpa [radialSupportProjection, targetSoninProjection,
    ccm24SemilocalSoninClosedSubspace] using
    (_root_.ConnesWeilRH.CC20Concrete.intersection_absorbs_left_starProjection
      (ccm24LogRadialSupportClosedSubspace lambda).toSubmodule
      (ccm24SemilocalFourierSupportClosedSubspace lambda
        family.visiblePrimes).toSubmodule)

/-- The actual target band `E - R_S` is an orthogonal projection. -/
theorem targetBandProjection_isStarProjection
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    IsStarProjection (targetBandProjection lambda family) := by
  unfold targetBandProjection
  apply (targetSoninProjection_isStarProjection lambda family).sub_of_mul_eq_left
    (radialSupportProjection_isStarProjection lambda)
  simpa only [ContinuousLinearMap.mul_def] using
    targetSoninProjection_comp_radialSupportProjection lambda family

theorem radialSupportProjection_comp_targetBandProjection_eq_self
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    radialSupportProjection lambda ∘L targetBandProjection lambda family =
      targetBandProjection lambda family := by
  have hSupport : IsIdempotentElem (radialSupportProjection lambda) :=
    (radialSupportProjection_isStarProjection lambda).isIdempotentElem
  have hTarget :=
    radialSupportProjection_comp_targetSoninProjection lambda family
  have hTargetMul : radialSupportProjection lambda *
      targetSoninProjection lambda family = targetSoninProjection lambda family := by
    simpa only [ContinuousLinearMap.mul_def] using hTarget
  unfold targetBandProjection
  simpa only [ContinuousLinearMap.mul_def] using show
      radialSupportProjection lambda *
          (radialSupportProjection lambda - targetSoninProjection lambda family) =
        radialSupportProjection lambda - targetSoninProjection lambda family by
      rw [mul_sub, hSupport, hTargetMul]

theorem targetBandProjection_comp_radialSupportProjection_eq_self
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    targetBandProjection lambda family ∘L radialSupportProjection lambda =
      targetBandProjection lambda family := by
  have hSupport : IsIdempotentElem (radialSupportProjection lambda) :=
    (radialSupportProjection_isStarProjection lambda).isIdempotentElem
  have hTarget :=
    targetSoninProjection_comp_radialSupportProjection lambda family
  have hTargetMul : targetSoninProjection lambda family *
      radialSupportProjection lambda = targetSoninProjection lambda family := by
    simpa only [ContinuousLinearMap.mul_def] using hTarget
  unfold targetBandProjection
  simpa only [ContinuousLinearMap.mul_def] using show
    (radialSupportProjection lambda - targetSoninProjection lambda family) *
          radialSupportProjection lambda =
        radialSupportProjection lambda - targetSoninProjection lambda family by
      rw [sub_mul, hSupport, hTargetMul]

/-- The true endpoint off-diagonal pair.  It is distinct from the physical
reflected-outer coordinate inside the detector commutator. -/
noncomputable def sourceTargetBandOffDiagonalPair
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) : Op :=
  endpointOffDiagonalPair (sourceBandProjection lambda)
    (sourceSoninProjection lambda) (targetBandProjection lambda family)

/-- The true endpoint diagonal remainder, already written as a positive
landing block minus a missed-range square. -/
noncomputable def sourceTargetBandSquareRemainder
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) : Op :=
  endpointSquareRemainder (radialSupportProjection lambda)
    (sourceBandProjection lambda) (sourceSoninProjection lambda)
    (targetBandProjection lambda family)

/-- Actual-carrier endpoint decomposition of `B_S - B_0`. -/
theorem soninBandDifference_eq_offDiagonalPair_add_squareRemainder
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    soninBandDifference lambda family =
      sourceTargetBandOffDiagonalPair lambda family +
        sourceTargetBandSquareRemainder lambda family := by
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
  have hSupportTarget : radialSupportProjection lambda *
      targetBandProjection lambda family = targetBandProjection lambda family := by
    simpa only [ContinuousLinearMap.mul_def] using
      radialSupportProjection_comp_targetBandProjection_eq_self lambda family
  have hTargetSupport : targetBandProjection lambda family *
      radialSupportProjection lambda = targetBandProjection lambda family := by
    simpa only [ContinuousLinearMap.mul_def] using
      targetBandProjection_comp_radialSupportProjection_eq_self lambda family
  simpa only [soninBandDifference, sourceTargetBandOffDiagonalPair,
      sourceTargetBandSquareRemainder, ContinuousLinearMap.mul_def] using
    (endpointProjectionDifference_eq_offDiagonal_add_squareRemainder
      (radialSupportProjection lambda) (sourceBandProjection lambda)
      (sourceSoninProjection lambda) (targetBandProjection lambda family)
      hSupport (sourceBandProjection_isStarProjection lambda).isIdempotentElem
      (sourceSoninProjection_isStarProjection lambda).isIdempotentElem
      hBandInner hInnerBand
      (targetBandProjection_isStarProjection lambda family).isIdempotentElem
      hSupportTarget hTargetSupport)

/-- The reverse endpoint block is the adjoint of the forward endpoint block.
This is the missing transport orientation; it is not the reflected physical
boundary coordinate. -/
theorem sourceTargetBand_reverseCrossing_eq_adjoint
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceBandProjection lambda ∘L targetBandProjection lambda family ∘L
        sourceSoninProjection lambda =
    (sourceSoninProjection lambda ∘L targetBandProjection lambda family ∘L
        sourceBandProjection lambda)† := by
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    (sourceBandProjection_isStarProjection lambda).isSelfAdjoint.adjoint_eq,
    (sourceSoninProjection_isStarProjection lambda).isSelfAdjoint.adjoint_eq,
    (targetBandProjection_isStarProjection lambda family)
      |>.isSelfAdjoint.adjoint_eq]
  apply ContinuousLinearMap.ext
  intro u
  rfl

theorem sourceTargetBandOffDiagonalPair_eq_forward_add_adjoint
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceTargetBandOffDiagonalPair lambda family =
      sourceSoninProjection lambda ∘L targetBandProjection lambda family ∘L
          sourceBandProjection lambda +
        (sourceSoninProjection lambda ∘L targetBandProjection lambda family ∘L
          sourceBandProjection lambda)† := by
  apply ContinuousLinearMap.ext
  intro u
  have hReverse := congrFun (congrArg DFunLike.coe
    (sourceTargetBand_reverseCrossing_eq_adjoint lambda family)) u
  simp only [sourceTargetBandOffDiagonalPair, endpointOffDiagonalPair,
    ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.add_apply] at hReverse ⊢
  rw [hReverse]

/-- The positive diagonal term is the square of the target-band landing of
the old Sonin range. -/
noncomputable def sourceTargetBandLandingCrossing
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) : Op :=
  targetBandProjection lambda family ∘L sourceSoninProjection lambda

/-- The negative diagonal term is the square of the source-band component
missed by the target band. -/
noncomputable def sourceTargetBandMissedCrossing
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) : Op :=
  (radialSupportProjection lambda - targetBandProjection lambda family) ∘L
    sourceBandProjection lambda

theorem sourceTargetBandSquareRemainder_eq_landingSq_sub_missedSq
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceTargetBandSquareRemainder lambda family =
      (sourceTargetBandLandingCrossing lambda family)† ∘L
          sourceTargetBandLandingCrossing lambda family -
        (sourceTargetBandMissedCrossing lambda family)† ∘L
          sourceTargetBandMissedCrossing lambda family := by
  have hAdjointSub :
      (radialSupportProjection lambda - targetBandProjection lambda family)† =
        (radialSupportProjection lambda)† -
          (targetBandProjection lambda family)† := by
    apply ContinuousLinearMap.ext
    intro u
    exact ext_inner_right ℂ fun v => by
      simp only [ContinuousLinearMap.adjoint_inner_left,
        ContinuousLinearMap.sub_apply, inner_sub_left, inner_sub_right]
  have hTargetSq : targetBandProjection lambda family *
      targetBandProjection lambda family = targetBandProjection lambda family :=
    (targetBandProjection_isStarProjection lambda family).isIdempotentElem
  have hLandingSq :
      sourceSoninProjection lambda * targetBandProjection lambda family *
          targetBandProjection lambda family * sourceSoninProjection lambda =
        sourceSoninProjection lambda * targetBandProjection lambda family *
          sourceSoninProjection lambda := by
    calc
      sourceSoninProjection lambda * targetBandProjection lambda family *
          targetBandProjection lambda family * sourceSoninProjection lambda =
        sourceSoninProjection lambda *
          (targetBandProjection lambda family *
            targetBandProjection lambda family) *
          sourceSoninProjection lambda := by noncomm_ring
      _ = sourceSoninProjection lambda * targetBandProjection lambda family *
          sourceSoninProjection lambda := by rw [hTargetSq]
  rw [sourceTargetBandSquareRemainder, endpointSquareRemainder,
    sourceTargetBandLandingCrossing, sourceTargetBandMissedCrossing,
    ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    hAdjointSub,
    (sourceBandProjection_isStarProjection lambda).isSelfAdjoint.adjoint_eq,
    (sourceSoninProjection_isStarProjection lambda).isSelfAdjoint.adjoint_eq,
    (radialSupportProjection_isStarProjection lambda).isSelfAdjoint.adjoint_eq,
    (targetBandProjection_isStarProjection lambda family)
      |>.isSelfAdjoint.adjoint_eq]
  simpa only [ContinuousLinearMap.mul_def] using show
    sourceSoninProjection lambda * targetBandProjection lambda family *
          sourceSoninProjection lambda -
        (sourceBandProjection lambda *
          (radialSupportProjection lambda - targetBandProjection lambda family)) *
          ((radialSupportProjection lambda - targetBandProjection lambda family) *
            sourceBandProjection lambda) =
      sourceSoninProjection lambda * targetBandProjection lambda family *
          targetBandProjection lambda family * sourceSoninProjection lambda -
        sourceBandProjection lambda *
          (radialSupportProjection lambda - targetBandProjection lambda family) *
          (radialSupportProjection lambda - targetBandProjection lambda family) *
          sourceBandProjection lambda by
    rw [hLandingSq]
    noncomm_ring

/-! ## The Proof 436 first jet with its mandatory adjoint -/

/-- The actual normalized finite-Euler quotient-band tangent before inserting
the detector. -/
noncomputable def sourceFiniteEulerPairedFirstJet
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) : Op :=
  quotientBandVariation (sourceBandProjection lambda)
    (sourceSoninProjection lambda) (normalizedFiniteEulerInverse family)
    ((normalizedFiniteEulerInverse family)†)

theorem sourceFiniteEulerPairedFirstJet_eq_forward_add_adjoint
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceFiniteEulerPairedFirstJet lambda family =
      sourceSoninProjection lambda ∘L normalizedFiniteEulerInverse family ∘L
          sourceBandProjection lambda +
        (sourceSoninProjection lambda ∘L normalizedFiniteEulerInverse family ∘L
          sourceBandProjection lambda)† := by
  let forward := sourceSoninProjection lambda ∘L
    normalizedFiniteEulerInverse family ∘L sourceBandProjection lambda
  have hAdjoint : forward† =
      sourceBandProjection lambda ∘L
        (normalizedFiniteEulerInverse family)† ∘L
          sourceSoninProjection lambda := by
    dsimp only [forward]
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
      (sourceBandProjection_isStarProjection lambda).isSelfAdjoint.adjoint_eq,
      (sourceSoninProjection_isStarProjection lambda).isSelfAdjoint.adjoint_eq]
    apply ContinuousLinearMap.ext
    intro u
    rfl
  rw [sourceFiniteEulerPairedFirstJet, quotientBandVariation]
  change forward + sourceBandProjection lambda ∘L
      (normalizedFiniteEulerInverse family)† ∘L sourceSoninProjection lambda =
    forward + forward†
  rw [hAdjoint]

/-- Detector-level Hermitian completion of the one-sided corner bounded in
Proof 436. -/
noncomputable def sourceRootCompletedPairedFiniteEulerCorner
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) : Op :=
  sourceRootCompletedFixedQuotientCorner owner lambda
      (radialSupportProjection lambda ∘L
        normalizedFiniteEulerInverse family ∘L
        radialSupportProjection lambda) +
    (sourceRootCompletedFixedQuotientCorner owner lambda
      (radialSupportProjection lambda ∘L
        normalizedFiniteEulerInverse family ∘L
        radialSupportProjection lambda))†

theorem sourceRootCompletedPairedFiniteEulerCorner_eq_fixedCommutator_add_adjoint
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceRootCompletedPairedFiniteEulerCorner owner lambda family =
      (sourceBandProjection lambda ∘L
        CCM24FiniteSTwoSidedRootRecombination.commutator
          (detectorOperator owner) (sourceSoninProjection lambda) ∘L
        sourceSoninProjection lambda ∘L normalizedFiniteEulerInverse family ∘L
        sourceBandProjection lambda) +
      (sourceBandProjection lambda ∘L
        CCM24FiniteSTwoSidedRootRecombination.commutator
          (detectorOperator owner) (sourceSoninProjection lambda) ∘L
        sourceSoninProjection lambda ∘L normalizedFiniteEulerInverse family ∘L
        sourceBandProjection lambda)† := by
  rw [sourceRootCompletedPairedFiniteEulerCorner,
    sourceRootCompletedFiniteEulerCorner_eq_fixedCommutatorSandwich]

end CCM24FiniteSPairedFirstJetRemainder
end CCM25Concrete
end Source
end ConnesWeilRH
