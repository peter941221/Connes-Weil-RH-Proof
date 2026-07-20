/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSWeightedBoundaryResolvent

/-!
# Isometric target-crossing collapse

This module absorbs the base Burnol weight into an isometric source frame and
rewrites Proof 427's moving-complement resolvent through the orthogonal target
Gram projection.  The normalized boundary difference becomes one inverse-
transport-sandwiched target detector commutator.

No star semantics, orthogonality, trace, trace-class assertion, Schatten
estimate, Markov bound, uniform estimate, Gate 3U premise, finite-S sign,
Burnol identity, or RH premise is stored here.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSIsometricTargetCrossing

open CCM24FiniteSWeightedBoundaryResolvent

variable {A : Type*} [Ring A]

/-- The Gram-corrected projection onto the transported frame range. -/
def transportedGramProjection
    (frame frameDagger transport transportDagger gramInverse : A) : A :=
  transport * frame * gramInverse * frameDagger * transportDagger

/-- The detector commutator with the target projection, in the orientation
used by the completed boundary response. -/
def targetDetectorCommutator (detector targetProjection : A) : A :=
  detector * targetProjection - targetProjection * detector

/-- A left Gram inverse makes the target Gram projection fix the transported
frame. -/
theorem transportedGramProjection_mul_transportedFrame
    (frame frameDagger transport transportDagger gramInverse : A)
    (hGramLeft :
      gramInverse *
        weightedGram frameDagger (transportDagger * transport) frame = 1) :
    transportedGramProjection frame frameDagger transport transportDagger
          gramInverse * transport * frame =
      transport * frame := by
  unfold transportedGramProjection weightedGram at *
  calc
    transport * frame * gramInverse * frameDagger * transportDagger *
          transport * frame =
        transport * frame *
          (gramInverse *
            (frameDagger * (transportDagger * transport) * frame)) := by
              noncomm_ring
    _ = transport * frame := by rw [hGramLeft]; noncomm_ring

/-- A right Gram inverse makes the transported frame adjoint fixed by the
target Gram projection on the right. -/
theorem transportedFrameDagger_mul_transportedGramProjection
    (frame frameDagger transport transportDagger gramInverse : A)
    (hGramRight :
      weightedGram frameDagger (transportDagger * transport) frame *
        gramInverse = 1) :
    frameDagger * transportDagger *
        transportedGramProjection frame frameDagger transport
          transportDagger gramInverse =
      frameDagger * transportDagger := by
  unfold transportedGramProjection weightedGram at *
  calc
    frameDagger * transportDagger *
          (transport * frame * gramInverse * frameDagger * transportDagger) =
        (frameDagger * (transportDagger * transport) * frame * gramInverse) *
          frameDagger * transportDagger := by
            noncomm_ring
    _ = frameDagger * transportDagger := by
      rw [hGramRight]
      noncomm_ring

/-- The transported Gram projection is idempotent. -/
theorem transportedGramProjection_sq
    (frame frameDagger transport transportDagger gramInverse : A)
    (hGramLeft :
      gramInverse *
        weightedGram frameDagger (transportDagger * transport) frame = 1) :
    transportedGramProjection frame frameDagger transport transportDagger
          gramInverse *
        transportedGramProjection frame frameDagger transport transportDagger
          gramInverse =
      transportedGramProjection frame frameDagger transport transportDagger
        gramInverse := by
  unfold transportedGramProjection weightedGram at *
  calc
    (transport * frame * gramInverse * frameDagger * transportDagger) *
          (transport * frame * gramInverse * frameDagger * transportDagger) =
        transport * frame *
          (gramInverse *
            (frameDagger * (transportDagger * transport) * frame)) *
          gramInverse * frameDagger * transportDagger := by
            noncomm_ring
    _ = transport * frame * gramInverse * frameDagger * transportDagger := by
      rw [hGramLeft]
      noncomm_ring

/-- The target complement kills the transported frame. -/
theorem targetComplement_mul_transportedFrame_eq_zero
    (frame frameDagger transport transportDagger gramInverse : A)
    (hGramLeft :
      gramInverse *
        weightedGram frameDagger (transportDagger * transport) frame = 1) :
    (1 - transportedGramProjection frame frameDagger transport
        transportDagger gramInverse) * transport * frame = 0 := by
  have hRange := transportedGramProjection_mul_transportedFrame frame
    frameDagger transport transportDagger gramInverse hGramLeft
  calc
    (1 - transportedGramProjection frame frameDagger transport
          transportDagger gramInverse) * transport * frame =
        transport * frame -
          transportedGramProjection frame frameDagger transport
            transportDagger gramInverse * transport * frame := by
              noncomm_ring
    _ = 0 := by rw [hRange]; noncomm_ring

/-- The transported frame adjoint kills the target complement. -/
theorem transportedFrameDagger_mul_targetComplement_eq_zero
    (frame frameDagger transport transportDagger gramInverse : A)
    (hGramRight :
      weightedGram frameDagger (transportDagger * transport) frame *
        gramInverse = 1) :
    frameDagger * transportDagger *
        (1 - transportedGramProjection frame frameDagger transport
          transportDagger gramInverse) = 0 := by
  have hRangeDagger :=
    transportedFrameDagger_mul_transportedGramProjection frame frameDagger
      transport transportDagger gramInverse hGramRight
  calc
    frameDagger * transportDagger *
          (1 - transportedGramProjection frame frameDagger transport
            transportDagger gramInverse) =
        frameDagger * transportDagger -
          frameDagger * transportDagger *
            transportedGramProjection frame frameDagger transport
              transportDagger gramInverse := by
                noncomm_ring
    _ = 0 := by rw [hRangeDagger]; noncomm_ring

/-- Pulling the target complement back by the inverse transport gives the
moving weighted oblique complement from Proof 427. -/
theorem inverse_mul_targetComplement_mul_transport_eq_movingComplement
    (frame frameDagger transport transportDagger transportInverse
      gramInverse : A)
    (hInverseLeft : transportInverse * transport = 1) :
    transportInverse *
          (1 - transportedGramProjection frame frameDagger transport
            transportDagger gramInverse) * transport =
      1 - weightedObliqueProjection frame gramInverse frameDagger
        (transportDagger * transport) := by
  unfold transportedGramProjection weightedObliqueProjection
    weightedRetraction
  calc
    transportInverse *
          (1 - transport * frame * gramInverse * frameDagger *
            transportDagger) * transport =
        transportInverse * transport -
          (transportInverse * transport) * frame * gramInverse *
            frameDagger * transportDagger * transport := by
              noncomm_ring
    _ = 1 - frame * (gramInverse * frameDagger *
          (transportDagger * transport)) := by
      rw [hInverseLeft]
      noncomm_ring

/-- In isometric source coordinates, the moving weighted retraction
difference is an inverse-transport-sandwiched target crossing. -/
theorem isometricWeightedRetraction_sub_eq_inverseTargetCrossing
    (frame frameDagger transport transportDagger transportInverse
      gramInverse : A)
    (hFrameIsometry : frameDagger * frame = 1)
    (hInverseLeft : transportInverse * transport = 1)
    (hInverseRight : transport * transportInverse = 1)
    (hGramRight :
      weightedGram frameDagger (transportDagger * transport) frame *
        gramInverse = 1) :
    weightedRetraction gramInverse frameDagger
          (transportDagger * transport) - frameDagger =
      -frameDagger * transportInverse *
        (1 - transportedGramProjection frame frameDagger transport
          transportDagger gramInverse) * transport := by
  have hOldLeft :
      (1 : A) * weightedGram frameDagger 1 frame = 1 := by
    unfold weightedGram
    calc
      1 * (frameDagger * 1 * frame) = frameDagger * frame := by noncomm_ring
      _ = 1 := hFrameIsometry
  have hMoving := weightedRetraction_sub_eq_movingComplement frame frameDagger
    1 (transportDagger * transport) 1 gramInverse hOldLeft hGramRight
  have hComplement :=
    inverse_mul_targetComplement_mul_transport_eq_movingComplement frame
      frameDagger transport transportDagger transportInverse gramInverse
      hInverseLeft
  have hTargetDagger := transportedFrameDagger_mul_targetComplement_eq_zero
    frame frameDagger transport transportDagger gramInverse hGramRight
  calc
    weightedRetraction gramInverse frameDagger
          (transportDagger * transport) - frameDagger =
        weightedRetraction gramInverse frameDagger
            (transportDagger * transport) -
          weightedRetraction 1 frameDagger 1 := by
            unfold weightedRetraction
            noncomm_ring
    _ = frameDagger * ((transportDagger * transport) - 1) *
          (1 - weightedObliqueProjection frame gramInverse frameDagger
            (transportDagger * transport)) := by
              simpa only [one_mul] using hMoving
    _ = frameDagger * ((transportDagger * transport) - 1) *
          (transportInverse *
            (1 - transportedGramProjection frame frameDagger transport
              transportDagger gramInverse) * transport) := by
                rw [hComplement]
    _ = (frameDagger * transportDagger *
            (transport * transportInverse) -
          frameDagger * transportInverse) *
        (1 - transportedGramProjection frame frameDagger transport
          transportDagger gramInverse) * transport := by
            noncomm_ring
    _ = (frameDagger * transportDagger -
          frameDagger * transportInverse) *
        (1 - transportedGramProjection frame frameDagger transport
          transportDagger gramInverse) * transport := by
            rw [hInverseRight]
            noncomm_ring
    _ = -frameDagger * transportInverse *
        (1 - transportedGramProjection frame frameDagger transport
          transportDagger gramInverse) * transport := by
      calc
        (frameDagger * transportDagger - frameDagger * transportInverse) *
              (1 - transportedGramProjection frame frameDagger transport
                transportDagger gramInverse) * transport =
            (frameDagger * transportDagger *
                (1 - transportedGramProjection frame frameDagger transport
                  transportDagger gramInverse) -
              frameDagger * transportInverse *
                (1 - transportedGramProjection frame frameDagger transport
                  transportDagger gramInverse)) * transport := by
                    noncomm_ring
        _ = -frameDagger * transportInverse *
            (1 - transportedGramProjection frame frameDagger transport
              transportDagger gramInverse) * transport := by
          rw [hTargetDagger]
          noncomm_ring

/-- A detector crossing out of the transported range is exactly the target
projection commutator crossing. -/
theorem targetComplement_detector_transportedFrame_eq_commutator
    (targetProjection detector transportedFrame : A)
    (hProjectionSq : targetProjection * targetProjection = targetProjection)
    (hRange : targetProjection * transportedFrame = transportedFrame) :
    (1 - targetProjection) * detector * transportedFrame =
      (1 - targetProjection) *
        targetDetectorCommutator detector targetProjection *
          transportedFrame := by
  have hComplementProjection :
      (1 - targetProjection) * targetProjection = 0 := by
    calc
      (1 - targetProjection) * targetProjection =
          targetProjection - targetProjection * targetProjection := by
            noncomm_ring
      _ = 0 := by rw [hProjectionSq]; noncomm_ring
  unfold targetDetectorCommutator
  symm
  calc
    (1 - targetProjection) *
          (detector * targetProjection - targetProjection * detector) *
          transportedFrame =
        (1 - targetProjection) * detector *
            (targetProjection * transportedFrame) -
          ((1 - targetProjection) * targetProjection) * detector *
            transportedFrame := by
              noncomm_ring
    _ = (1 - targetProjection) * detector * transportedFrame := by
      rw [hRange, hComplementProjection]
      noncomm_ring

/-- After absorbing the base weight into an isometric frame, Proof 415's
normalized boundary difference has one target detector commutator owner. -/
theorem normalizedBoundary_sub_eq_inverseTargetCommutator
    (frame frameDagger transport transportDagger transportInverse detector
      gramInverse : A)
    (hFrameIsometry : frameDagger * frame = 1)
    (hInverseLeft : transportInverse * transport = 1)
    (hInverseRight : transport * transportInverse = 1)
    (hGramLeft :
      gramInverse *
        weightedGram frameDagger (transportDagger * transport) frame = 1)
    (hGramRight :
      weightedGram frameDagger (transportDagger * transport) frame *
        gramInverse = 1)
    (hDetectorCommutes : transport * detector = detector * transport) :
    normalizedBoundarySemicommutator gramInverse frameDagger
          (transportDagger * transport) detector frame -
        normalizedBoundarySemicommutator 1 frameDagger 1 detector frame =
      -frameDagger * transportInverse *
        (1 - transportedGramProjection frame frameDagger transport
          transportDagger gramInverse) *
        targetDetectorCommutator detector
          (transportedGramProjection frame frameDagger transport
            transportDagger gramInverse) * transport * frame := by
  have hOldLeft :
      (1 : A) * weightedGram frameDagger 1 frame = 1 := by
    unfold weightedGram
    calc
      1 * (frameDagger * 1 * frame) = frameDagger * frame := by noncomm_ring
      _ = 1 := hFrameIsometry
  have hBoundary :=
    normalizedBoundarySemicommutator_sub_eq_retractionDifference frame
      frameDagger 1 (transportDagger * transport) detector 1 gramInverse
      hOldLeft hGramLeft
  have hRetraction :=
    isometricWeightedRetraction_sub_eq_inverseTargetCrossing frame frameDagger
      transport transportDagger transportInverse gramInverse hFrameIsometry
      hInverseLeft hInverseRight hGramRight
  let targetProjection := transportedGramProjection frame frameDagger
    transport transportDagger gramInverse
  have hProjectionSq : targetProjection * targetProjection =
      targetProjection := by
    exact transportedGramProjection_sq frame frameDagger transport
      transportDagger gramInverse hGramLeft
  have hRange : targetProjection * (transport * frame) =
      transport * frame := by
    have hRangeRaw := transportedGramProjection_mul_transportedFrame frame
      frameDagger transport transportDagger gramInverse hGramLeft
    calc
      targetProjection * (transport * frame) =
          targetProjection * transport * frame := by noncomm_ring
      _ = transport * frame := by
        simpa only [targetProjection] using hRangeRaw
  have hCrossing :=
    targetComplement_detector_transportedFrame_eq_commutator targetProjection
      detector (transport * frame) hProjectionSq hRange
  calc
    normalizedBoundarySemicommutator gramInverse frameDagger
          (transportDagger * transport) detector frame -
        normalizedBoundarySemicommutator 1 frameDagger 1 detector frame =
      (weightedRetraction gramInverse frameDagger
            (transportDagger * transport) -
          weightedRetraction 1 frameDagger 1) * detector * frame := hBoundary
    _ = (weightedRetraction gramInverse frameDagger
          (transportDagger * transport) - frameDagger) * detector * frame := by
            unfold weightedRetraction
            noncomm_ring
    _ = (-frameDagger * transportInverse * (1 - targetProjection) *
          transport) * detector * frame := by rw [hRetraction]
    _ = -frameDagger * transportInverse * (1 - targetProjection) *
          detector * transport * frame := by
      calc
        (-frameDagger * transportInverse * (1 - targetProjection) *
              transport) * detector * frame =
            -frameDagger * transportInverse * (1 - targetProjection) *
              (transport * detector) * frame := by noncomm_ring
        _ = -frameDagger * transportInverse * (1 - targetProjection) *
              detector * transport * frame := by
          rw [hDetectorCommutes]
          noncomm_ring
    _ = -frameDagger * transportInverse * (1 - targetProjection) *
          targetDetectorCommutator detector targetProjection *
            transport * frame := by
      calc
        -frameDagger * transportInverse * (1 - targetProjection) *
              detector * transport * frame =
            -frameDagger * transportInverse *
              ((1 - targetProjection) * detector * (transport * frame)) := by
                noncomm_ring
        _ = -frameDagger * transportInverse *
              ((1 - targetProjection) *
                targetDetectorCommutator detector targetProjection *
                  (transport * frame)) := by
          rw [hCrossing]
        _ = -frameDagger * transportInverse * (1 - targetProjection) *
            targetDetectorCommutator detector targetProjection * transport *
              frame := by noncomm_ring

end CCM24FiniteSIsometricTargetCrossing
end CCM25Concrete
end Source
end ConnesWeilRH
