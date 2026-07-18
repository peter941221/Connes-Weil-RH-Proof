/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSBiSchurRelative

/-!
# Relative-trace cocycle algebra

This module owns the ring algebra used by Proofs 400--404.  A cyclic
trace-like functional removes a completed forward/reverse prefix from a local
relative numerator.  The module also records the two-boundary expansion of a
nested-band first variation.

No analytic trace, trace-class, Schatten, projection, positivity, uniform
bound, Gate 3U, finite-S sign, Burnol, or RH premise is stored here.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSRelativeTraceCocycle

open CCM24FiniteSBiSchurRelative

variable {A : Type*} [Ring A]

/-- The formal off-diagonal first variation of a transported idempotent. -/
def projectionVariation (projection transport transportAdjoint : A) : A :=
  (1 - projection) * transport * projection +
    projection * transportAdjoint * (1 - projection)

/-- The difference of two formal projection variations is the outer boundary
of their band minus its inner boundary. -/
theorem projectionVariation_sub_eq_twoBoundaries
    (outer inner transport transportAdjoint : A) :
    projectionVariation outer transport transportAdjoint -
        projectionVariation inner transport transportAdjoint =
      (1 - outer) * transport * (outer - inner) +
        (outer - inner) * transportAdjoint * (1 - outer) -
        (outer - inner) * transport * inner -
        inner * transportAdjoint * (outer - inner) := by
  unfold projectionVariation
  noncomm_ring

/-- A cyclic trace-like functional removes a completed first prefix from the
two-step relative-numerator telescope. -/
theorem relativeNumerator_two_step_trace_collapse
    {B : Type*} [Add B]
    (traceLike : A -> B)
    (hAdd : forall x y, traceLike (x + y) = traceLike x + traceLike y)
    (hCyclic : forall x y, traceLike (x * y) = traceLike (y * x))
    (oldCompression middleCompression newCompression : A)
    (firstForward secondForward secondReverse firstReverse : A)
    (firstScale secondScale : A)
    (hScaleCommutes : secondScale * firstReverse = firstReverse * secondScale)
    (hReverseForwardPair : firstReverse * firstForward = firstScale) :
    traceLike
        (relativeNumerator oldCompression
          (firstForward * secondForward) newCompression
          (secondReverse * firstReverse) (firstScale * secondScale)) =
      traceLike
          (relativeNumerator middleCompression secondForward newCompression
            secondReverse secondScale * firstScale) +
        traceLike
          (relativeNumerator oldCompression firstForward middleCompression
            firstReverse firstScale * secondScale) := by
  let secondNumerator :=
    relativeNumerator middleCompression secondForward newCompression
      secondReverse secondScale
  let firstNumerator :=
    relativeNumerator oldCompression firstForward middleCompression
      firstReverse firstScale
  have hTelescope :
      relativeNumerator oldCompression
          (firstForward * secondForward) newCompression
          (secondReverse * firstReverse) (firstScale * secondScale) =
        firstForward * secondNumerator * firstReverse +
          firstNumerator * secondScale := by
    exact relativeNumerator_two_step oldCompression middleCompression
      newCompression firstForward secondForward secondReverse firstReverse
      firstScale secondScale hScaleCommutes
  have hFirst :
      traceLike (firstForward * secondNumerator * firstReverse) =
        traceLike (secondNumerator * firstScale) := by
    calc
      traceLike (firstForward * secondNumerator * firstReverse) =
          traceLike (firstForward * (secondNumerator * firstReverse)) := by
            rw [mul_assoc]
      _ = traceLike ((secondNumerator * firstReverse) * firstForward) := by
        rw [hCyclic]
      _ = traceLike (secondNumerator * (firstReverse * firstForward)) := by
        rw [mul_assoc]
      _ = traceLike (secondNumerator * firstScale) := by
        rw [hReverseForwardPair]
  rw [hTelescope, hAdd, hFirst]

end CCM24FiniteSRelativeTraceCocycle
end CCM25Concrete
end Source
end ConnesWeilRH
