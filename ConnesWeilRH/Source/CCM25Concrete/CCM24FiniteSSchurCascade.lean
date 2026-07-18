/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Tactic.NoncommRing

/-!
# Schur-cascade detector algebra

This module owns the noncommutative ring algebra used by Proofs 390--394.  It
identifies the local detector intertwinement with a completed moving crossing,
expands the Schur co-defect through that crossing, telescopes intertwinement
defects under composition, and records the exact inverse-defect growth.

No adjoint semantics, positivity, Douglas factorization, Schatten estimate,
stable-coframe bound, or Gate 3U premise is stored here.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSSchurCascade

variable {A : Type*} [Ring A]

/-- Formal compression of an operator through a frame/coframe pair. -/
def frameCompression (frameDagger operator frame : A) : A :=
  frameDagger * operator * frame

/-- Formal range projection of a frame/coframe pair. -/
def frameProjection (frame frameDagger : A) : A :=
  frame * frameDagger

/-- Intertwinement defect between consecutive compressed detectors. -/
def intertwiningDefect
    (oldCompression transition newCompression : A) : A :=
  transition * newCompression - oldCompression * transition

/-- Boundary compression from the new frame complement to the old source. -/
def boundaryCompression
    (oldFrameDagger transport newFrame newFrameDagger : A) : A :=
  oldFrameDagger * transport *
    (1 - frameProjection newFrame newFrameDagger)

/-- The detector intertwinement defect is exactly the completed moving
crossing compressed by the normalized ambient transport. -/
theorem detectorIntertwiningDefect_eq_boundary
    (oldFrame oldFrameDagger newFrame newFrameDagger : A)
    (transport transition detector : A)
    (hOldIsometry : oldFrameDagger * oldFrame = 1)
    (hTransport : transport * newFrame = oldFrame * transition)
    (hCommute : transport * detector = detector * transport) :
    intertwiningDefect
        (frameCompression oldFrameDagger detector oldFrame)
        transition
        (frameCompression newFrameDagger detector newFrame) =
      -boundaryCompression oldFrameDagger transport newFrame
          newFrameDagger * detector * newFrame := by
  have hTransportCompression :
      oldFrameDagger * transport * newFrame = transition := by
    calc
      oldFrameDagger * transport * newFrame =
          oldFrameDagger * (transport * newFrame) := by noncomm_ring
      _ = oldFrameDagger * (oldFrame * transition) := by rw [hTransport]
      _ = transition := by rw [← mul_assoc, hOldIsometry, one_mul]
  have hCommuteCompression :
      oldFrameDagger * transport * detector * newFrame =
        oldFrameDagger * detector * transport * newFrame := by
    calc
      oldFrameDagger * transport * detector * newFrame =
          oldFrameDagger * (transport * detector) * newFrame := by
            noncomm_ring
      _ = oldFrameDagger * (detector * transport) * newFrame := by
        rw [hCommute]
      _ = oldFrameDagger * detector * transport * newFrame := by
        noncomm_ring
  have hDetectorTransport :
      oldFrameDagger * detector * transport * newFrame =
        oldFrameDagger * detector * oldFrame * transition := by
    calc
      oldFrameDagger * detector * transport * newFrame =
          oldFrameDagger * detector * (transport * newFrame) := by
            noncomm_ring
      _ = oldFrameDagger * detector * (oldFrame * transition) := by
        rw [hTransport]
      _ = oldFrameDagger * detector * oldFrame * transition := by
        noncomm_ring
  unfold intertwiningDefect frameCompression boundaryCompression
    frameProjection
  symm
  calc
    -(oldFrameDagger * transport * (1 - newFrame * newFrameDagger)) *
          detector * newFrame =
      -(oldFrameDagger * transport * detector * newFrame) +
        (oldFrameDagger * transport * newFrame) *
          (newFrameDagger * detector * newFrame) := by
            noncomm_ring
    _ = -(oldFrameDagger * detector * transport * newFrame) +
        transition * (newFrameDagger * detector * newFrame) := by
          rw [hCommuteCompression, hTransportCompression]
    _ = -(oldFrameDagger * detector * (oldFrame * transition)) +
        transition * (newFrameDagger * detector * newFrame) := by
          rw [hDetectorTransport]
          noncomm_ring
    _ = transition * (newFrameDagger * detector * newFrame) -
        (oldFrameDagger * detector * oldFrame) * transition := by
          noncomm_ring

/-- Formal left co-defect of a transition and its supplied dagger. -/
def transitionCoDefect (transition transitionDagger : A) : A :=
  1 - transition * transitionDagger

/-- Formal ambient left defect of a transport and its supplied dagger. -/
def ambientCoDefect (transport transportDagger : A) : A :=
  1 - transport * transportDagger

/-- Formal dagger of `boundaryCompression`. -/
def boundaryCompressionDagger
    (oldFrame transportDagger newFrame newFrameDagger : A) : A :=
  (1 - frameProjection newFrame newFrameDagger) *
    transportDagger * oldFrame

/-- The Schur co-defect is the sum of the compressed ambient loss and the
boundary-compression square. -/
theorem transitionCoDefect_eq_ambient_add_boundary
    (oldFrame oldFrameDagger newFrame newFrameDagger : A)
    (transport transportDagger transition transitionDagger : A)
    (hOldIsometry : oldFrameDagger * oldFrame = 1)
    (hNewIsometry : newFrameDagger * newFrame = 1)
    (hTransport : transport * newFrame = oldFrame * transition)
    (hTransportDagger :
      newFrameDagger * transportDagger =
        transitionDagger * oldFrameDagger) :
    transitionCoDefect transition transitionDagger =
      oldFrameDagger * ambientCoDefect transport transportDagger *
          oldFrame +
        boundaryCompression oldFrameDagger transport newFrame
          newFrameDagger *
        boundaryCompressionDagger oldFrame transportDagger newFrame
          newFrameDagger := by
  have hProjectionSq :
      (newFrame * newFrameDagger) * (newFrame * newFrameDagger) =
        newFrame * newFrameDagger := by
    calc
      (newFrame * newFrameDagger) * (newFrame * newFrameDagger) =
          newFrame * (newFrameDagger * newFrame) * newFrameDagger := by
            noncomm_ring
      _ = newFrame * newFrameDagger := by rw [hNewIsometry]; noncomm_ring
  have hComplementSq :
      (1 - newFrame * newFrameDagger) *
          (1 - newFrame * newFrameDagger) =
        1 - newFrame * newFrameDagger := by
    calc
      (1 - newFrame * newFrameDagger) *
          (1 - newFrame * newFrameDagger) =
        1 - 2 * (newFrame * newFrameDagger) +
          (newFrame * newFrameDagger) *
            (newFrame * newFrameDagger) := by
              noncomm_ring
      _ = 1 - newFrame * newFrameDagger := by
        rw [hProjectionSq]
        noncomm_ring
  have hLeftTransition :
      oldFrameDagger * transport * newFrame = transition := by
    calc
      oldFrameDagger * transport * newFrame =
          oldFrameDagger * (transport * newFrame) := by noncomm_ring
      _ = oldFrameDagger * (oldFrame * transition) := by rw [hTransport]
      _ = transition := by rw [← mul_assoc, hOldIsometry, one_mul]
  have hRightTransition :
      newFrameDagger * transportDagger * oldFrame = transitionDagger := by
    calc
      newFrameDagger * transportDagger * oldFrame =
          (newFrameDagger * transportDagger) * oldFrame := by
            noncomm_ring
      _ = (transitionDagger * oldFrameDagger) * oldFrame := by
        rw [hTransportDagger]
      _ = transitionDagger := by rw [mul_assoc, hOldIsometry, mul_one]
  have hBoundarySquare :
      (oldFrameDagger * transport *
          (1 - newFrame * newFrameDagger)) *
          ((1 - newFrame * newFrameDagger) *
            transportDagger * oldFrame) =
        oldFrameDagger * transport *
          (1 - newFrame * newFrameDagger) *
          transportDagger * oldFrame := by
    calc
      (oldFrameDagger * transport *
          (1 - newFrame * newFrameDagger)) *
          ((1 - newFrame * newFrameDagger) *
            transportDagger * oldFrame) =
        oldFrameDagger * transport *
          ((1 - newFrame * newFrameDagger) *
            (1 - newFrame * newFrameDagger)) *
          transportDagger * oldFrame := by
            noncomm_ring
      _ = oldFrameDagger * transport *
          (1 - newFrame * newFrameDagger) *
          transportDagger * oldFrame := by
            rw [hComplementSq]
  unfold transitionCoDefect ambientCoDefect boundaryCompression
    boundaryCompressionDagger frameProjection
  symm
  calc
    oldFrameDagger * (1 - transport * transportDagger) * oldFrame +
        (oldFrameDagger * transport *
          (1 - newFrame * newFrameDagger)) *
        ((1 - newFrame * newFrameDagger) * transportDagger * oldFrame) =
      oldFrameDagger * oldFrame -
        (oldFrameDagger * transport * newFrame) *
          (newFrameDagger * transportDagger * oldFrame) := by
            rw [hBoundarySquare]
            noncomm_ring
    _ = 1 - transition * transitionDagger := by
      rw [hOldIsometry, hLeftTransition, hRightTransition]

/-- Intertwinement defects telescope exactly under composition. -/
theorem intertwiningDefect_mul
    (oldCompression middleCompression newCompression : A)
    (firstTransition secondTransition : A) :
    intertwiningDefect oldCompression
        (firstTransition * secondTransition) newCompression =
      firstTransition *
          intertwiningDefect middleCompression secondTransition
            newCompression +
        intertwiningDefect oldCompression firstTransition
          middleCompression * secondTransition := by
  unfold intertwiningDefect
  noncomm_ring

/-- An isometric frame followed by an inverse source coordinate has Gram
`inverseDagger * inverse`. -/
theorem rawFrame_gram_eq_inverseGram
    (frame frameDagger inverse inverseDagger : A)
    (hFrameIsometry : frameDagger * frame = 1) :
    (inverseDagger * frameDagger) * (frame * inverse) =
      inverseDagger * inverse := by
  calc
    (inverseDagger * frameDagger) * (frame * inverse) =
        inverseDagger * (frameDagger * frame) * inverse := by
          noncomm_ring
    _ = inverseDagger * inverse := by rw [hFrameIsometry]; noncomm_ring

/-- Multiplying the Gram-corrected numerator in the required order produces
the Schur ordered similarity. -/
theorem gramInverse_mul_numerator_eq_ordered
    (schur schurDagger inverse inverseDagger detectorCompression : A)
    (hDaggerInverse : schurDagger * inverseDagger = 1) :
    (schur * schurDagger) *
        (inverseDagger * detectorCompression * inverse) =
      schur * detectorCompression * inverse := by
  calc
    (schur * schurDagger) *
        (inverseDagger * detectorCompression * inverse) =
      schur * (schurDagger * inverseDagger) *
        detectorCompression * inverse := by
          noncomm_ring
    _ = schur * detectorCompression * inverse := by
      rw [hDaggerInverse]
      noncomm_ring

/-- A local inverse defect is exactly the growth of the inverse Gram. -/
theorem inverseDefect_eq_inverseGrowth
    (transition transitionDagger inverse inverseDagger : A)
    (hDaggerInverse : inverseDagger * transitionDagger = 1)
    (hInverse : transition * inverse = 1) :
    inverseDagger * (1 - transitionDagger * transition) * inverse =
      inverseDagger * inverse - 1 := by
  calc
    inverseDagger * (1 - transitionDagger * transition) * inverse =
      inverseDagger * inverse -
        (inverseDagger * transitionDagger) *
          (transition * inverse) := by
            noncomm_ring
    _ = inverseDagger * inverse - 1 := by
      rw [hDaggerInverse, hInverse]
      noncomm_ring

/-- Conjugating the local inverse defect gives one increment of the complete
inverse-prefix Gram. -/
theorem conjugated_inverseDefect_eq_delta_sub
    (previousInverse previousInverseDagger : A)
    (transition transitionDagger inverse inverseDagger : A)
    (hDaggerInverse : inverseDagger * transitionDagger = 1)
    (hInverse : transition * inverse = 1) :
    previousInverseDagger *
        (inverseDagger * (1 - transitionDagger * transition) * inverse) *
        previousInverse =
      (previousInverseDagger * inverseDagger) *
          (inverse * previousInverse) -
        previousInverseDagger * previousInverse := by
  rw [inverseDefect_eq_inverseGrowth transition transitionDagger inverse
    inverseDagger hDaggerInverse hInverse]
  noncomm_ring

end CCM24FiniteSSchurCascade
end CCM25Concrete
end Source
end ConnesWeilRH
