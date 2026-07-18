/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Algebra.Group.Idempotent
import Mathlib.Tactic.NoncommRing

/-!
# Detector variance and two-support root renewal

This module owns the ring-level algebra behind Proofs 370--372.  It identifies
an off-diagonal detector covariance with a compression variance, factors a
positive detector crossing through two single-root corners, and eliminates an
explicit prolate commutator through a two-support renewal identity.

No Schatten estimate, trace-class premise, uniform Euler bound, or Gate 3U
producer is stored here.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSDetectorVariance

variable {A : Type*} [Ring A]

/-- Oriented detector crossing from a projection range to its complement. -/
def detectorCrossing (P W : A) : A :=
  (1 - P) * W * P

/-- Formal adjoint-oriented crossing, with the adjoint detector supplied as
an independent ring element. -/
def detectorCrossingAdjoint (P Wdagger : A) : A :=
  P * Wdagger * (1 - P)

/-- Compression variance of a detector and its formal adjoint. -/
def detectorCompressionVariance (P Wdagger W : A) : A :=
  P * Wdagger * W * P -
    (P * Wdagger * P) * (P * W * P)

/-- The covariance of the oriented detector crossing is exactly its
compression variance. -/
theorem detectorCrossingAdjoint_mul_detectorCrossing_eq_variance
    (P Wdagger W : A) (hP : IsIdempotentElem P) :
    detectorCrossingAdjoint P Wdagger * detectorCrossing P W =
      detectorCompressionVariance P Wdagger W := by
  have hPsq : P * P = P := hP
  have hPperpSq : (1 - P) * (1 - P) = 1 - P := by
    calc
      (1 - P) * (1 - P) = 1 - 2 * P + P * P := by
        noncomm_ring
      _ = 1 - P := by rw [hPsq]; noncomm_ring
  have hdiagonal :
      (P * Wdagger * P) * (P * W * P) =
        P * Wdagger * P * W * P := by
    calc
      (P * Wdagger * P) * (P * W * P) =
          P * Wdagger * (P * P) * W * P := by
        noncomm_ring
      _ = P * Wdagger * P * W * P := by rw [hPsq]
  unfold detectorCrossingAdjoint detectorCrossing
    detectorCompressionVariance
  calc
    (P * Wdagger * (1 - P)) * ((1 - P) * W * P) =
        P * Wdagger * ((1 - P) * (1 - P)) * W * P := by
      noncomm_ring
    _ = P * Wdagger * (1 - P) * W * P := by rw [hPperpSq]
    _ = P * Wdagger * W * P -
        P * Wdagger * P * W * P := by noncomm_ring
    _ = P * Wdagger * W * P -
        (P * Wdagger * P) * (P * W * P) := by rw [hdiagonal]

/-- Compression by a frame/coframe pair turns the same covariance into a
multiplicative-domain defect. -/
theorem frameVariance_eq_complement_defect
    (P Vdagger V Wdagger W : A) (hP : P = V * Vdagger) :
    Vdagger * Wdagger * W * V -
        (Vdagger * Wdagger * V) * (Vdagger * W * V) =
      Vdagger * Wdagger * (1 - P) * W * V := by
  rw [hP]
  noncomm_ring

/-- A positive-detector crossing `Cdagger * C` is the sum of two products,
each containing one off-diagonal root corner. -/
theorem positiveDetectorCrossing_eq_rootCorners
    (P Cdagger C : A) (hP : IsIdempotentElem P) :
    detectorCrossing P (Cdagger * C) =
      ((1 - P) * Cdagger * P) * (P * C * P) +
        ((1 - P) * Cdagger * (1 - P)) * ((1 - P) * C * P) := by
  have hPsq : P * P = P := hP
  have hPperpSq : (1 - P) * (1 - P) = 1 - P := by
    calc
      (1 - P) * (1 - P) = 1 - 2 * P + P * P := by
        noncomm_ring
      _ = 1 - P := by rw [hPsq]; noncomm_ring
  have hfirst :
      ((1 - P) * Cdagger * P) * (P * C * P) =
        (1 - P) * Cdagger * P * C * P := by
    calc
      ((1 - P) * Cdagger * P) * (P * C * P) =
          (1 - P) * Cdagger * (P * P) * C * P := by
        noncomm_ring
      _ = (1 - P) * Cdagger * P * C * P := by rw [hPsq]
  have hsecond :
      ((1 - P) * Cdagger * (1 - P)) * ((1 - P) * C * P) =
        (1 - P) * Cdagger * (1 - P) * C * P := by
    calc
      ((1 - P) * Cdagger * (1 - P)) * ((1 - P) * C * P) =
          (1 - P) * Cdagger * ((1 - P) * (1 - P)) * C * P := by
        noncomm_ring
      _ = (1 - P) * Cdagger * (1 - P) * C * P := by
        rw [hPperpSq]
  unfold detectorCrossing
  calc
    (1 - P) * (Cdagger * C) * P =
        (1 - P) * Cdagger * (P + (1 - P)) * C * P := by
      noncomm_ring
    _ = (1 - P) * Cdagger * P * C * P +
        (1 - P) * Cdagger * (1 - P) * C * P := by
      noncomm_ring
    _ = ((1 - P) * Cdagger * P) * (P * C * P) +
        ((1 - P) * Cdagger * (1 - P)) * ((1 - P) * C * P) := by
      rw [hfirst, hsecond]

/-- Prolate compression on the quotient corner of two support projections. -/
def prolateCompression (P Q : A) : A :=
  P * Q * P

/-- Signed outer-minus-second-support numerator for one root crossing. -/
def rootBoundaryNumerator (E Q R P C : A) : A :=
  R * C * (1 - E) * Q * P - R * (C * Q - Q * C) * P

/-- Multiplication by the complementary prolate Gram converts the Sonin to
quotient root crossing into the completed outer-minus-second boundary
numerator. -/
theorem rootCrossing_mul_one_sub_prolate_eq_boundary
    (E Q R P C : A) (hP : IsIdempotentElem P)
    (hRQ : R * Q = R) (hEQP : E * Q * P = P * Q * P) :
    R * C * P * (1 - prolateCompression P Q) =
      rootBoundaryNumerator E Q R P C := by
  have hPsq : P * P = P := hP
  have hPK : P * (P * Q * P) = P * Q * P := by
    calc
      P * (P * Q * P) = (P * P) * Q * P := by noncomm_ring
      _ = P * Q * P := by rw [hPsq]
  have hRQC : R * Q * C * P = R * C * P := by
    calc
      R * Q * C * P = (R * Q) * C * P := by noncomm_ring
      _ = R * C * P := by rw [hRQ]
  unfold prolateCompression rootBoundaryNumerator
  calc
    R * C * P * (1 - P * Q * P) =
        R * C * P - R * C * (P * Q * P) := by
      rw [mul_sub, mul_one]
      rw [show R * C * P * (P * Q * P) =
          R * C * (P * Q * P) by
        calc
          R * C * P * (P * Q * P) =
              R * C * (P * (P * Q * P)) := by noncomm_ring
          _ = R * C * (P * Q * P) := by rw [hPK]]
    _ = R * C * P - R * C * (E * Q * P) := by rw [hEQP]
    _ = R * C * (1 - E) * Q * P -
        R * (C * Q - Q * C) * P := by
      rw [← hRQC]
      noncomm_ring

end CCM24FiniteSDetectorVariance
end CCM25Concrete
end Source
end ConnesWeilRH
