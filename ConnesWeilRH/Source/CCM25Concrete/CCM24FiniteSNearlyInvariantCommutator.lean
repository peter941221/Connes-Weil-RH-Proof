/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Tactic.NoncommRing

/-!
# Model and band commutator algebra

This module owns the noncommutative algebra used by Proofs 376--378.  It
records how a model projection reduces a commuting multiplier commutator to
two copies of one Hardy-boundary commutator, and how an outer-minus-Sonin band
commutator remains a signed difference.

The analytic nearly-invariant rank theorem and Hilbert--Schmidt estimates are
not stored as premises here.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSNearlyInvariantCommutator

variable {A : Type*} [Ring A]

/-- The additive commutator with the detector in the left slot. -/
def commutator (detector projection : A) : A :=
  detector * projection - projection * detector

/-- Formal model-space projection `P - theta P theta†`. -/
def modelProjection (hardy theta thetaDagger : A) : A :=
  hardy - theta * hardy * thetaDagger

/-- Formal outer-minus-Sonin band projection. -/
def bandProjection (outer sonin : A) : A :=
  outer - sonin

/-- A detector commuting with the inner multipliers sees a model projection
as the signed difference of two copies of the Hardy-boundary commutator. -/
theorem commutator_modelProjection_eq_boundaryDifference
    (detector hardy theta thetaDagger : A)
    (hTheta : detector * theta = theta * detector)
    (hThetaDagger : detector * thetaDagger = thetaDagger * detector) :
    commutator detector (modelProjection hardy theta thetaDagger) =
      commutator detector hardy -
        theta * commutator detector hardy * thetaDagger := by
  unfold commutator modelProjection
  calc
    detector * (hardy - theta * hardy * thetaDagger) -
          (hardy - theta * hardy * thetaDagger) * detector =
        detector * hardy - (detector * theta) * hardy * thetaDagger -
          hardy * detector + theta * hardy * (thetaDagger * detector) := by
      noncomm_ring
    _ = detector * hardy - (theta * detector) * hardy * thetaDagger -
          hardy * detector + theta * hardy * (detector * thetaDagger) := by
      rw [hTheta, ← hThetaDagger]
    _ = detector * hardy - hardy * detector -
          theta * (detector * hardy - hardy * detector) * thetaDagger := by
      noncomm_ring

/-- The quotient-band commutator is the signed outer-minus-Sonin
commutator; no branch is silently discarded. -/
theorem commutator_bandProjection_eq_outer_sub_sonin
    (detector outer sonin : A) :
    commutator detector (bandProjection outer sonin) =
      commutator detector outer - commutator detector sonin := by
  unfold commutator bandProjection
  noncomm_ring

/-- Passing to an orthogonal-complement-shaped expression reverses the
commutator sign at the purely algebraic level. -/
theorem commutator_one_sub_eq_neg
    (detector projection : A) :
    commutator detector (1 - projection) =
      -commutator detector projection := by
  unfold commutator
  noncomm_ring

end CCM24FiniteSNearlyInvariantCommutator
end CCM25Concrete
end Source
end ConnesWeilRH
