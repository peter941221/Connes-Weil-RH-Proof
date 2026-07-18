/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Algebra.Group.Idempotent
import Mathlib.Tactic.NoncommRing

/-!
# Two-sided root recombination algebra

This module owns the noncommutative ring algebra used by Proofs 385--389.  It
splits a projection commutator into its two oriented crossings, rewrites a
commutator with a square through two square-root legs, and retains both
quotient-compression boundary corrections in the complete physical bracket.

No trace, adjoint, Schatten, Gram/Julia alignment, or Gate 3U premise is
stored here.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSTwoSidedRootRecombination

variable {A : Type*} [Ring A]

/-- The additive commutator with the detector in the left slot. -/
def commutator (detector operator : A) : A :=
  detector * operator - operator * detector

/-- Crossing from a formal projection range to its complement. -/
def orientedCrossing (projection detector : A) : A :=
  (1 - projection) * detector * projection

/-- Crossing in the orientation opposite to `orientedCrossing`. -/
def reverseOrientedCrossing (projection detector : A) : A :=
  projection * detector * (1 - projection)

/-- A projection commutator is the signed pair of its two oriented
crossings.  Idempotence is not needed for this additive identity. -/
theorem commutator_eq_orientedCrossing_sub_reverse
    (projection detector : A) :
    commutator detector projection =
      orientedCrossing projection detector -
        reverseOrientedCrossing projection detector := by
  unfold commutator orientedCrossing reverseOrientedCrossing
  noncomm_ring

/-- The two-sided square-root product for a commutator with `root * root`. -/
def twoSidedSquareRootCommutator (detector root : A) : A :=
  (detector * root) * root - root * (root * detector)

/-- A commutator with a square is exactly its two-sided square-root product. -/
theorem commutator_square_eq_twoSidedSquareRoot
    (detector root : A) :
    commutator detector (root * root) =
      twoSidedSquareRootCommutator detector root := by
  unfold commutator twoSidedSquareRootCommutator
  noncomm_ring

/-- Detector compressed to a fixed quotient carrier. -/
def compressedDetector (support detector : A) : A :=
  support * detector * support

/-- Ambient transport compressed to the same quotient carrier. -/
def compressedPrefix (support transport : A) : A :=
  support * transport * support

/-- Compressing a commuting detector/transport pair produces two mandatory
support-boundary commutators. -/
theorem compressed_commutator_eq_boundary
    (support detector transport : A)
    (hSupport : IsIdempotentElem support)
    (hCommute : detector * transport = transport * detector) :
    commutator (compressedDetector support detector)
        (compressedPrefix support transport) =
      support * commutator detector support * transport * support +
        support * transport * commutator detector support * support := by
  have hSupportSq : support * support = support := hSupport
  have hLeft :
      (support * detector * support) *
          (support * transport * support) =
        support * detector * support * transport * support := by
    calc
      (support * detector * support) *
          (support * transport * support) =
        support * detector * (support * support) * transport * support := by
          noncomm_ring
      _ = support * detector * support * transport * support := by
        rw [hSupportSq]
  have hRight :
      (support * transport * support) *
          (support * detector * support) =
        support * transport * support * detector * support := by
    calc
      (support * transport * support) *
          (support * detector * support) =
        support * transport * (support * support) * detector * support := by
          noncomm_ring
      _ = support * transport * support * detector * support := by
        rw [hSupportSq]
  have hMiddle :
      support * detector * transport * support =
        support * transport * detector * support := by
    calc
      support * detector * transport * support =
          support * (detector * transport) * support := by noncomm_ring
      _ = support * (transport * detector) * support := by rw [hCommute]
      _ = support * transport * detector * support := by noncomm_ring
  have hBoundary :
      support * (detector * support - support * detector) * transport *
            support +
          support * transport *
            (detector * support - support * detector) * support =
        support * detector * support * transport * support -
          support * transport * support * detector * support := by
    calc
      support * (detector * support - support * detector) * transport *
            support +
          support * transport *
            (detector * support - support * detector) * support =
        support * detector * support * transport * support -
          (support * support) * detector * transport * support +
          support * transport * detector * (support * support) -
          support * transport * support * detector * support := by
            noncomm_ring
      _ = support * detector * support * transport * support -
          support * detector * transport * support +
          support * transport * detector * support -
          support * transport * support * detector * support := by
            rw [hSupportSq]
      _ = support * detector * support * transport * support -
          support * transport * support * detector * support := by
            rw [hMiddle]
            noncomm_ring
  unfold commutator compressedDetector compressedPrefix
  rw [hLeft, hRight]
  exact hBoundary.symm

/-- Source Sonin projection written as a compressed second support minus the
prolate remainder. -/
def sourceCompression (support secondSupport prolate : A) : A :=
  support * secondSupport * support - prolate

/-- Fixed outer/second-support/prolate commutator ledger. -/
def fixedPhysicalCommutator
    (support secondSupport prolate detector : A) : A :=
  support * commutator detector support * secondSupport * support +
    support * commutator detector secondSupport * support +
    support * secondSupport * commutator detector support * support -
    support * commutator detector prolate * support

/-- The compressed second-support commutator expands into the three boundary
terms before the prolate correction is inserted. -/
theorem compressed_secondSupport_commutator_eq_threeBoundary
    (support secondSupport detector : A)
    (hSupport : IsIdempotentElem support) :
    commutator (compressedDetector support detector)
        (support * secondSupport * support) =
      support * commutator detector support * secondSupport * support +
        support * commutator detector secondSupport * support +
        support * secondSupport * commutator detector support * support := by
  have hSupportSq : support * support = support := hSupport
  have hLeft :
      (support * detector * support) *
          (support * secondSupport * support) =
        support * detector * support * secondSupport * support := by
    calc
      (support * detector * support) *
          (support * secondSupport * support) =
        support * detector * (support * support) * secondSupport *
          support := by
            noncomm_ring
      _ = support * detector * support * secondSupport * support := by
        rw [hSupportSq]
  have hRight :
      (support * secondSupport * support) *
          (support * detector * support) =
        support * secondSupport * support * detector * support := by
    calc
      (support * secondSupport * support) *
          (support * detector * support) =
        support * secondSupport * (support * support) * detector *
          support := by
            noncomm_ring
      _ = support * secondSupport * support * detector * support := by
        rw [hSupportSq]
  have hBoundary :
      support * (detector * support - support * detector) * secondSupport *
            support +
          support * (detector * secondSupport - secondSupport * detector) *
            support +
          support * secondSupport *
            (detector * support - support * detector) * support =
        support * detector * support * secondSupport * support -
          support * secondSupport * support * detector * support := by
    calc
      support * (detector * support - support * detector) * secondSupport *
            support +
          support * (detector * secondSupport - secondSupport * detector) *
            support +
          support * secondSupport *
            (detector * support - support * detector) * support =
        support * detector * support * secondSupport * support -
          (support * support) * detector * secondSupport * support +
          support * detector * secondSupport * support -
          support * secondSupport * detector * support +
          support * secondSupport * detector * (support * support) -
          support * secondSupport * support * detector * support := by
              noncomm_ring
      _ = support * detector * support * secondSupport * support -
          support * secondSupport * support * detector * support := by
            rw [hSupportSq]
            noncomm_ring
  unfold commutator compressedDetector
  rw [hLeft, hRight]
  exact hBoundary.symm

/-- A prolate operator supported on both sides by the quotient support has
the same commutator before and after quotient compression. -/
theorem compressed_supported_commutator_eq
    (support prolate detector : A)
    (hLeftSupport : support * prolate = prolate)
    (hRightSupport : prolate * support = prolate) :
    commutator (compressedDetector support detector) prolate =
      support * commutator detector prolate * support := by
  have hLeft :
      (support * detector * support) * prolate =
        support * detector * prolate := by
    calc
      (support * detector * support) * prolate =
          support * detector * (support * prolate) := by noncomm_ring
      _ = support * detector * prolate := by rw [hLeftSupport]
  have hRight :
      prolate * (support * detector * support) =
        prolate * detector * support := by
    calc
      prolate * (support * detector * support) =
          (prolate * support) * detector * support := by noncomm_ring
      _ = prolate * detector * support := by rw [hRightSupport]
  have hOuterLeft :
      support * detector * prolate * support =
        support * detector * prolate := by
    calc
      support * detector * prolate * support =
          support * detector * (prolate * support) := by noncomm_ring
      _ = support * detector * prolate := by rw [hRightSupport]
  have hOuterRight :
      support * prolate * detector * support =
        prolate * detector * support := by
    rw [hLeftSupport]
  unfold commutator compressedDetector
  rw [hLeft, hRight]
  calc
    support * detector * prolate - prolate * detector * support =
        support * detector * prolate * support -
          support * prolate * detector * support := by
            rw [hOuterLeft, hOuterRight]
    _ = support * (detector * prolate - prolate * detector) * support := by
      noncomm_ring

/-- The fixed quotient commutator is exactly the signed physical boundary
ledger when the prolate remainder is supported on the quotient carrier. -/
theorem compressed_source_commutator_eq_physical
    (support secondSupport prolate detector : A)
    (hSupport : IsIdempotentElem support)
    (hLeftSupport : support * prolate = prolate)
    (hRightSupport : prolate * support = prolate) :
    commutator (compressedDetector support detector)
        (sourceCompression support secondSupport prolate) =
      fixedPhysicalCommutator support secondSupport prolate detector := by
  calc
    commutator (compressedDetector support detector)
        (sourceCompression support secondSupport prolate) =
      commutator (compressedDetector support detector)
          (support * secondSupport * support) -
        commutator (compressedDetector support detector) prolate := by
          unfold commutator sourceCompression
          noncomm_ring
    _ = (support * commutator detector support * secondSupport * support +
          support * commutator detector secondSupport * support +
          support * secondSupport * commutator detector support * support) -
        support * commutator detector prolate * support := by
          rw [compressed_secondSupport_commutator_eq_threeBoundary
            support secondSupport detector hSupport]
          rw [compressed_supported_commutator_eq support prolate detector
            hLeftSupport hRightSupport]
    _ = fixedPhysicalCommutator support secondSupport prolate detector := by
      rfl

/-- Corrected quotient bracket before its physical boundary expansion. -/
def correctedQuotientBracket
    (support detector transport source : A) : A :=
  -compressedPrefix support transport *
      commutator (compressedDetector support detector) source +
    commutator (compressedDetector support detector)
      (compressedPrefix support transport)

/-- Complete physical bracket with both quotient-compression corrections. -/
def correctedPhysicalBracket
    (support secondSupport prolate detector transport : A) : A :=
  -compressedPrefix support transport *
      fixedPhysicalCommutator support secondSupport prolate detector +
    support * commutator detector support * transport * support +
    support * transport * commutator detector support * support

/-- The corrected quotient bracket equals the complete physical bracket;
neither quotient-boundary correction is omitted. -/
theorem correctedQuotientBracket_eq_physical
    (support secondSupport prolate detector transport : A)
    (hSupport : IsIdempotentElem support)
    (hLeftSupport : support * prolate = prolate)
    (hRightSupport : prolate * support = prolate)
    (hCommute : detector * transport = transport * detector) :
    correctedQuotientBracket support detector transport
        (sourceCompression support secondSupport prolate) =
      correctedPhysicalBracket support secondSupport prolate detector
        transport := by
  unfold correctedQuotientBracket correctedPhysicalBracket
  rw [compressed_source_commutator_eq_physical support secondSupport prolate
    detector hSupport hLeftSupport hRightSupport]
  rw [compressed_commutator_eq_boundary support detector transport hSupport
    hCommute]
  noncomm_ring

/-- Physical ledger after every projection commutator and the prolate square
have been replaced by their two oriented root products. -/
def twoSidedRootLedger
    (support secondSupport prolateRoot detector transport : A) : A :=
  -compressedPrefix support transport *
      (support *
            (orientedCrossing support detector -
              reverseOrientedCrossing support detector) *
            secondSupport * support +
        support *
            (orientedCrossing secondSupport detector -
              reverseOrientedCrossing secondSupport detector) * support +
        support * secondSupport *
            (orientedCrossing support detector -
              reverseOrientedCrossing support detector) * support -
        support * twoSidedSquareRootCommutator detector prolateRoot *
          support) +
    support *
        (orientedCrossing support detector -
          reverseOrientedCrossing support detector) * transport * support +
    support * transport *
      (orientedCrossing support detector -
        reverseOrientedCrossing support detector) * support

/-- The complete physical bracket has the exact two-sided root ledger before
any trace cycle or branch estimate. -/
theorem correctedPhysicalBracket_eq_twoSidedRootLedger
    (support secondSupport prolateRoot detector transport : A) :
    correctedPhysicalBracket support secondSupport
        (prolateRoot * prolateRoot) detector transport =
      twoSidedRootLedger support secondSupport prolateRoot detector
        transport := by
  unfold correctedPhysicalBracket fixedPhysicalCommutator
    twoSidedRootLedger
  rw [commutator_eq_orientedCrossing_sub_reverse support detector]
  rw [commutator_eq_orientedCrossing_sub_reverse secondSupport detector]
  rw [commutator_square_eq_twoSidedSquareRoot detector prolateRoot]

end CCM24FiniteSTwoSidedRootRecombination
end CCM25Concrete
end Source
end ConnesWeilRH
