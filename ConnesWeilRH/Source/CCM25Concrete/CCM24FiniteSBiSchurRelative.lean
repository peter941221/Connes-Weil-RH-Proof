/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSSchurCascade

/-!
# Bi-Schur relative-numerator algebra

This module owns the noncommutative ring algebra used by Proofs 395--399.  It
composes paired forward/reverse transitions, identifies the local relative
numerator with the forward intertwinement defect followed by the reverse
transition, telescopes two relative steps, and records ordered and scalar-
gauge readbacks.

No adjoint semantics, positivity, contraction, trace-class estimate, Schatten
bound, uniform relative-numerator estimate, or Gate 3U premise is stored here.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSBiSchurRelative

open CCM24FiniteSSchurCascade

variable {A : Type*} [Ring A]

/-- Formal numerator with the paired reverse transition kept on the right. -/
def relativeNumerator
    (oldCompression forward newCompression reverse scale : A) : A :=
  forward * newCompression * reverse - oldCompression * scale

/-- Two forward/reverse pairs compose in chronological order. -/
theorem forwardReversePair_two
    (firstForward secondForward secondReverse firstReverse : A)
    (firstScale secondScale : A)
    (hFirstPair : firstForward * firstReverse = firstScale)
    (hSecondPair : secondForward * secondReverse = secondScale)
    (hScaleCommutes : secondScale * firstReverse = firstReverse * secondScale) :
    (firstForward * secondForward) * (secondReverse * firstReverse) =
      firstScale * secondScale := by
  calc
    (firstForward * secondForward) * (secondReverse * firstReverse) =
        firstForward * (secondForward * secondReverse) * firstReverse := by
          noncomm_ring
    _ = firstForward * secondScale * firstReverse := by rw [hSecondPair]
    _ = firstForward * (secondScale * firstReverse) := by noncomm_ring
    _ = firstForward * (firstReverse * secondScale) := by
      rw [hScaleCommutes]
    _ = (firstForward * firstReverse) * secondScale := by noncomm_ring
    _ = firstScale * secondScale := by rw [hFirstPair]

/-- The reverse/forward products compose in the opposite chronological
order. -/
theorem reverseForwardPair_two
    (secondReverse firstReverse firstForward secondForward : A)
    (firstScale secondScale : A)
    (hFirstPair : firstReverse * firstForward = firstScale)
    (hSecondPair : secondReverse * secondForward = secondScale)
    (hScaleCommutes : secondReverse * firstScale = firstScale * secondReverse) :
    (secondReverse * firstReverse) * (firstForward * secondForward) =
      firstScale * secondScale := by
  calc
    (secondReverse * firstReverse) * (firstForward * secondForward) =
        secondReverse * (firstReverse * firstForward) * secondForward := by
          noncomm_ring
    _ = secondReverse * firstScale * secondForward := by rw [hFirstPair]
    _ = firstScale * secondReverse * secondForward := by
      rw [hScaleCommutes]
    _ = firstScale * (secondReverse * secondForward) := by noncomm_ring
    _ = firstScale * secondScale := by rw [hSecondPair]

/-- A local relative numerator is the forward intertwinement defect followed
by the paired reverse transition. -/
theorem relativeNumerator_eq_intertwiningDefect_mul
    (oldCompression forward newCompression reverse scale : A)
    (hPair : forward * reverse = scale) :
    relativeNumerator oldCompression forward newCompression reverse scale =
      intertwiningDefect oldCompression forward newCompression * reverse := by
  unfold relativeNumerator intertwiningDefect
  calc
    forward * newCompression * reverse - oldCompression * scale =
        forward * newCompression * reverse -
          oldCompression * (forward * reverse) := by rw [hPair]
    _ = (forward * newCompression - oldCompression * forward) * reverse := by
      noncomm_ring

/-- Two local relative numerators telescope without changing the chronological
operator order. -/
theorem relativeNumerator_two_step
    (oldCompression middleCompression newCompression : A)
    (firstForward secondForward secondReverse firstReverse : A)
    (firstScale secondScale : A)
    (hScaleCommutes : secondScale * firstReverse = firstReverse * secondScale) :
    relativeNumerator oldCompression
        (firstForward * secondForward) newCompression
        (secondReverse * firstReverse) (firstScale * secondScale) =
      firstForward *
          relativeNumerator middleCompression secondForward newCompression
            secondReverse secondScale * firstReverse +
        relativeNumerator oldCompression firstForward middleCompression
            firstReverse firstScale * secondScale := by
  have hMove :
      firstForward * middleCompression * secondScale * firstReverse =
        firstForward * middleCompression * firstReverse * secondScale := by
    calc
      firstForward * middleCompression * secondScale * firstReverse =
          firstForward * middleCompression *
            (secondScale * firstReverse) := by
              noncomm_ring
      _ = firstForward * middleCompression *
          (firstReverse * secondScale) := by rw [hScaleCommutes]
      _ = firstForward * middleCompression * firstReverse * secondScale := by
        noncomm_ring
  unfold relativeNumerator
  calc
    (firstForward * secondForward) * newCompression *
          (secondReverse * firstReverse) -
        oldCompression * (firstScale * secondScale) =
      firstForward * secondForward * newCompression * secondReverse *
          firstReverse - oldCompression * firstScale * secondScale := by
            noncomm_ring
    _ = firstForward * secondForward * newCompression * secondReverse *
          firstReverse -
        firstForward * middleCompression * secondScale * firstReverse +
        firstForward * middleCompression * firstReverse * secondScale -
        oldCompression * firstScale * secondScale := by
          rw [hMove]
          noncomm_ring
    _ = firstForward *
          (secondForward * newCompression * secondReverse -
            middleCompression * secondScale) * firstReverse +
        (firstForward * middleCompression * firstReverse -
          oldCompression * firstScale) * secondScale := by
            noncomm_ring

/-- If the reverse product is the ordered inverse followed by the scalar,
the relative numerator is the ordered response followed by that scalar. -/
theorem relativeNumerator_eq_ordered_mul_scale
    (oldCompression forward newCompression reverse inverse scale : A)
    (hReverse : reverse = inverse * scale) :
    relativeNumerator oldCompression forward newCompression reverse scale =
      (forward * newCompression * inverse - oldCompression) * scale := by
  unfold relativeNumerator
  rw [hReverse]
  noncomm_ring

/-- A coherent compression commuting with the forward transition has zero
relative numerator. -/
theorem relativeNumerator_coherent_eq_zero
    (compression forward reverse scale : A)
    (hCommute : forward * compression = compression * forward)
    (hPair : forward * reverse = scale) :
    relativeNumerator compression forward compression reverse scale = 0 := by
  unfold relativeNumerator
  calc
    forward * compression * reverse - compression * scale =
        compression * forward * reverse - compression * scale := by
          rw [hCommute]
    _ = compression * (forward * reverse) - compression * scale := by
      noncomm_ring
    _ = 0 := by rw [hPair]; noncomm_ring

/-- A paired central gauge leaves the relative numerator unchanged. -/
theorem relativeNumerator_gauge_eq
    (oldCompression forward newCompression reverse scale : A)
    (gauge ungauge : A)
    (hGaugeCommutes :
      gauge * (forward * newCompression * reverse) =
        (forward * newCompression * reverse) * gauge)
    (hGaugeInverse : gauge * ungauge = 1) :
    relativeNumerator oldCompression (gauge * forward) newCompression
        (reverse * ungauge) scale =
      relativeNumerator oldCompression forward newCompression reverse scale := by
  unfold relativeNumerator
  calc
    (gauge * forward) * newCompression * (reverse * ungauge) -
        oldCompression * scale =
      gauge * (forward * newCompression * reverse) * ungauge -
        oldCompression * scale := by
          noncomm_ring
    _ = (forward * newCompression * reverse) * gauge * ungauge -
        oldCompression * scale := by rw [hGaugeCommutes]
    _ = (forward * newCompression * reverse) * (gauge * ungauge) -
        oldCompression * scale := by noncomm_ring
    _ = forward * newCompression * reverse - oldCompression * scale := by
      rw [hGaugeInverse]
      noncomm_ring

end CCM24FiniteSBiSchurRelative
end CCM25Concrete
end Source
end ConnesWeilRH
