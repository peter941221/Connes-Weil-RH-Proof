/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCentralAnomalyGuard
import Mathlib.Tactic.NoncommRing

/-!
# Relative weighted-boundary resolvent algebra

This module owns the noncommutative cancellation behind Proof 415's two-weight
normalized boundary form.  The difference of two weighted retractions is one
weight difference followed by either the fixed or moving oblique complement.
Consequently, the difference of the normalized boundary semicommutators has a
single relative owner.

No adjoint semantics, positivity, trace, trace-class assertion, Schatten
estimate, uniform bound, Gate 3U premise, finite-S sign, Burnol identity, or RH
premise is stored here.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSWeightedBoundaryResolvent

variable {A : Type*} [Ring A]

/-- The frame Gram operator for a weight, with the displayed operator order. -/
def weightedGram (frameDagger weight frame : A) : A :=
  frameDagger * weight * frame

/-- The weighted left retraction from the ambient carrier to the source
frame. -/
def weightedRetraction
    (gramInverse frameDagger weight : A) : A :=
  gramInverse * frameDagger * weight

/-- The ambient oblique projection obtained from the weighted retraction. -/
def weightedObliqueProjection
    (frame gramInverse frameDagger weight : A) : A :=
  frame * weightedRetraction gramInverse frameDagger weight

/-- The unnormalized ordered boundary semicommutator for a weighted frame. -/
def weightedBoundarySemicommutator
    (frameDagger weight detector frame : A) : A :=
  frameDagger * weight * detector * frame -
    weightedGram frameDagger weight frame *
      (frameDagger * detector * frame)

/-- The Gram-normalized ordered boundary semicommutator. -/
def normalizedBoundarySemicommutator
    (gramInverse frameDagger weight detector frame : A) : A :=
  gramInverse *
    weightedBoundarySemicommutator frameDagger weight detector frame

/-- A left Gram inverse makes the weighted retraction a left inverse of the
frame. -/
theorem weightedRetraction_mul_frame_eq_one
    (frame frameDagger weight gramInverse : A)
    (hLeftInverse :
      gramInverse * weightedGram frameDagger weight frame = 1) :
    weightedRetraction gramInverse frameDagger weight * frame = 1 := by
  unfold weightedRetraction weightedGram at *
  calc
    (gramInverse * frameDagger * weight) * frame =
        gramInverse * (frameDagger * weight * frame) := by noncomm_ring
    _ = 1 := hLeftInverse

/-- The weighted frame/retraction product is an oblique projection. -/
theorem weightedObliqueProjection_sq
    (frame frameDagger weight gramInverse : A)
    (hLeftInverse :
      gramInverse * weightedGram frameDagger weight frame = 1) :
    weightedObliqueProjection frame gramInverse frameDagger weight *
        weightedObliqueProjection frame gramInverse frameDagger weight =
      weightedObliqueProjection frame gramInverse frameDagger weight := by
  have hRetraction := weightedRetraction_mul_frame_eq_one
    frame frameDagger weight gramInverse hLeftInverse
  unfold weightedObliqueProjection
  calc
    (frame * weightedRetraction gramInverse frameDagger weight) *
          (frame * weightedRetraction gramInverse frameDagger weight) =
        frame *
          (weightedRetraction gramInverse frameDagger weight * frame) *
          weightedRetraction gramInverse frameDagger weight := by
            noncomm_ring
    _ = frame * weightedRetraction gramInverse frameDagger weight := by
      rw [hRetraction]
      noncomm_ring

/-- The complementary oblique corner kills the original frame. -/
theorem weightedObliqueComplement_mul_frame_eq_zero
    (frame frameDagger weight gramInverse : A)
    (hLeftInverse :
      gramInverse * weightedGram frameDagger weight frame = 1) :
    (1 - weightedObliqueProjection frame gramInverse frameDagger weight) *
        frame = 0 := by
  have hRetraction := weightedRetraction_mul_frame_eq_one
    frame frameDagger weight gramInverse hLeftInverse
  unfold weightedObliqueProjection
  calc
    (1 - frame * weightedRetraction gramInverse frameDagger weight) * frame =
        frame - frame *
          (weightedRetraction gramInverse frameDagger weight * frame) := by
            noncomm_ring
    _ = 0 := by rw [hRetraction]; noncomm_ring

/-- Gram normalization leaves the weighted detector response minus the common
source compression. -/
theorem normalizedBoundarySemicommutator_eq_retraction_sub_source
    (frame frameDagger weight detector gramInverse : A)
    (hLeftInverse :
      gramInverse * weightedGram frameDagger weight frame = 1) :
    normalizedBoundarySemicommutator gramInverse frameDagger weight detector
        frame =
      weightedRetraction gramInverse frameDagger weight * detector * frame -
        frameDagger * detector * frame := by
  unfold normalizedBoundarySemicommutator weightedBoundarySemicommutator
  calc
    gramInverse *
          (frameDagger * weight * detector * frame -
            weightedGram frameDagger weight frame *
              (frameDagger * detector * frame)) =
        weightedRetraction gramInverse frameDagger weight * detector * frame -
          (gramInverse * weightedGram frameDagger weight frame) *
            (frameDagger * detector * frame) := by
              unfold weightedRetraction
              noncomm_ring
    _ = weightedRetraction gramInverse frameDagger weight * detector * frame -
          frameDagger * detector * frame := by
      rw [hLeftInverse]
      noncomm_ring

/-- Resolvent collapse with the old, fixed oblique complement on the right. -/
theorem weightedRetraction_sub_eq_fixedComplement
    (frame frameDagger oldWeight newWeight oldGramInverse newGramInverse : A)
    (hNewLeftInverse :
      newGramInverse * weightedGram frameDagger newWeight frame = 1)
    (hOldRightInverse :
      weightedGram frameDagger oldWeight frame * oldGramInverse = 1) :
    weightedRetraction newGramInverse frameDagger newWeight -
        weightedRetraction oldGramInverse frameDagger oldWeight =
      newGramInverse * frameDagger * (newWeight - oldWeight) *
        (1 - weightedObliqueProjection frame oldGramInverse frameDagger
          oldWeight) := by
  symm
  unfold weightedRetraction weightedObliqueProjection weightedGram at *
  calc
    newGramInverse * frameDagger * (newWeight - oldWeight) *
          (1 - frame * (oldGramInverse * frameDagger * oldWeight)) =
        newGramInverse * frameDagger * newWeight -
          (newGramInverse * (frameDagger * newWeight * frame)) *
            (oldGramInverse * frameDagger * oldWeight) -
          newGramInverse * frameDagger * oldWeight +
          newGramInverse *
            ((frameDagger * oldWeight * frame) * oldGramInverse) *
            frameDagger * oldWeight := by
              noncomm_ring
    _ = newGramInverse * frameDagger * newWeight -
          oldGramInverse * frameDagger * oldWeight := by
      rw [hNewLeftInverse, hOldRightInverse]
      noncomm_ring

/-- Resolvent collapse with the new, moving oblique complement on the right. -/
theorem weightedRetraction_sub_eq_movingComplement
    (frame frameDagger oldWeight newWeight oldGramInverse newGramInverse : A)
    (hOldLeftInverse :
      oldGramInverse * weightedGram frameDagger oldWeight frame = 1)
    (hNewRightInverse :
      weightedGram frameDagger newWeight frame * newGramInverse = 1) :
    weightedRetraction newGramInverse frameDagger newWeight -
        weightedRetraction oldGramInverse frameDagger oldWeight =
      oldGramInverse * frameDagger * (newWeight - oldWeight) *
        (1 - weightedObliqueProjection frame newGramInverse frameDagger
          newWeight) := by
  symm
  unfold weightedRetraction weightedObliqueProjection weightedGram at *
  calc
    oldGramInverse * frameDagger * (newWeight - oldWeight) *
          (1 - frame * (newGramInverse * frameDagger * newWeight)) =
        oldGramInverse * frameDagger * newWeight -
          oldGramInverse *
            ((frameDagger * newWeight * frame) * newGramInverse) *
            frameDagger * newWeight -
          oldGramInverse * frameDagger * oldWeight +
          (oldGramInverse * (frameDagger * oldWeight * frame)) *
            (newGramInverse * frameDagger * newWeight) := by
              noncomm_ring
    _ = newGramInverse * frameDagger * newWeight -
          oldGramInverse * frameDagger * oldWeight := by
      rw [hOldLeftInverse, hNewRightInverse]
      noncomm_ring

/-- The common source compression cancels from the difference of normalized
boundary semicommutators. -/
theorem normalizedBoundarySemicommutator_sub_eq_retractionDifference
    (frame frameDagger oldWeight newWeight detector
      oldGramInverse newGramInverse : A)
    (hOldLeftInverse :
      oldGramInverse * weightedGram frameDagger oldWeight frame = 1)
    (hNewLeftInverse :
      newGramInverse * weightedGram frameDagger newWeight frame = 1) :
    normalizedBoundarySemicommutator newGramInverse frameDagger newWeight
          detector frame -
        normalizedBoundarySemicommutator oldGramInverse frameDagger oldWeight
          detector frame =
      (weightedRetraction newGramInverse frameDagger newWeight -
        weightedRetraction oldGramInverse frameDagger oldWeight) *
          detector * frame := by
  rw [normalizedBoundarySemicommutator_eq_retraction_sub_source
      frame frameDagger newWeight detector newGramInverse hNewLeftInverse,
    normalizedBoundarySemicommutator_eq_retraction_sub_source
      frame frameDagger oldWeight detector oldGramInverse hOldLeftInverse]
  noncomm_ring

/-- Proof 415's completed two-weight boundary difference is one weight
difference followed by the fixed old oblique complement. -/
theorem normalizedBoundarySemicommutator_sub_eq_singleDifference
    (frame frameDagger oldWeight newWeight detector
      oldGramInverse newGramInverse : A)
    (hOldLeftInverse :
      oldGramInverse * weightedGram frameDagger oldWeight frame = 1)
    (hOldRightInverse :
      weightedGram frameDagger oldWeight frame * oldGramInverse = 1)
    (hNewLeftInverse :
      newGramInverse * weightedGram frameDagger newWeight frame = 1) :
    normalizedBoundarySemicommutator newGramInverse frameDagger newWeight
          detector frame -
        normalizedBoundarySemicommutator oldGramInverse frameDagger oldWeight
          detector frame =
      newGramInverse * frameDagger * (newWeight - oldWeight) *
        (1 - weightedObliqueProjection frame oldGramInverse frameDagger
          oldWeight) * detector * frame := by
  rw [normalizedBoundarySemicommutator_sub_eq_retractionDifference
      frame frameDagger oldWeight newWeight detector oldGramInverse
      newGramInverse hOldLeftInverse hNewLeftInverse,
    weightedRetraction_sub_eq_fixedComplement frame frameDagger oldWeight
      newWeight oldGramInverse newGramInverse hNewLeftInverse hOldRightInverse]

/-- The same completed difference can instead use the moving new oblique
complement. -/
theorem normalizedBoundarySemicommutator_sub_eq_singleDifference_moving
    (frame frameDagger oldWeight newWeight detector
      oldGramInverse newGramInverse : A)
    (hOldLeftInverse :
      oldGramInverse * weightedGram frameDagger oldWeight frame = 1)
    (hNewLeftInverse :
      newGramInverse * weightedGram frameDagger newWeight frame = 1)
    (hNewRightInverse :
      weightedGram frameDagger newWeight frame * newGramInverse = 1) :
    normalizedBoundarySemicommutator newGramInverse frameDagger newWeight
          detector frame -
        normalizedBoundarySemicommutator oldGramInverse frameDagger oldWeight
          detector frame =
      oldGramInverse * frameDagger * (newWeight - oldWeight) *
        (1 - weightedObliqueProjection frame newGramInverse frameDagger
          newWeight) * detector * frame := by
  rw [normalizedBoundarySemicommutator_sub_eq_retractionDifference
      frame frameDagger oldWeight newWeight detector oldGramInverse
      newGramInverse hOldLeftInverse hNewLeftInverse,
    weightedRetraction_sub_eq_movingComplement frame frameDagger oldWeight
      newWeight oldGramInverse newGramInverse hOldLeftInverse hNewRightInverse]

end CCM24FiniteSWeightedBoundaryResolvent
end CCM25Concrete
end Source
end ConnesWeilRH
