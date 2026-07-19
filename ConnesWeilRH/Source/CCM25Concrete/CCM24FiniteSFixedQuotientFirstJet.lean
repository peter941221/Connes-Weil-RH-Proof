/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSTwoSidedRootRecombination

/-!
# Fixed-quotient first-jet algebra

This module owns the noncommutative algebra used by Proof 405.  It records the
fixed-quotient band variation, compresses its detector corner to a projection
commutator, and reduces that corner to the second-support and prolate legs.

No analytic derivative, trace, trace-class, Schatten, positivity, uniform
bound, Gate 3U, finite-S sign, Burnol, or RH premise is stored here.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSFixedQuotientFirstJet

open CCM24FiniteSTwoSidedRootRecombination

variable {A : Type*} [Ring A]

/-- Formal first variation of a band transported inside a fixed quotient. -/
def quotientBandVariation
    (band inner transport transportAdjoint : A) : A :=
  inner * transport * band + band * transportAdjoint * inner

/-- Ordered Toeplitz semicommutator on a formal band. -/
def toeplitzSemicommutator
    (band detector transport : A) : A :=
  band * detector * transport * band -
    (band * detector * band) * (band * transport * band)

/-- A detector crossing through the complementary quotient corner is exactly
the ordered Toeplitz semicommutator. -/
theorem detector_complement_transport_eq_toeplitzSemicommutator
    (band detector transport : A)
    (hBand : IsIdempotentElem band) :
    band * detector * (1 - band) * transport * band =
      toeplitzSemicommutator band detector transport := by
  have hBandSq : band * band = band := hBand
  unfold toeplitzSemicommutator
  calc
    band * detector * (1 - band) * transport * band =
        band * detector * transport * band -
          band * detector * band * transport * band := by
            noncomm_ring
    _ = band * detector * transport * band -
          (band * detector * band) *
            (band * transport * band) := by
      rw [show band * detector * band * transport * band =
          (band * detector * band) * (band * transport * band) by
        calc
          band * detector * band * transport * band =
              band * detector * (band * band) * transport * band := by
                rw [hBandSq]
          _ = (band * detector * band) *
              (band * transport * band) := by noncomm_ring]

/-- An off-diagonal detector corner is the corresponding projection
commutator corner. -/
theorem detector_innerCorner_eq_commutator
    (band inner detector : A)
    (hInner : IsIdempotentElem inner)
    (hBandInner : band * inner = 0) :
    band * detector * inner =
      band * commutator detector inner * inner := by
  have hInnerSq : inner * inner = inner := hInner
  unfold commutator
  symm
  calc
    band * (detector * inner - inner * detector) * inner =
        band * detector * (inner * inner) -
          (band * inner) * detector * inner := by
            noncomm_ring
    _ = band * detector * inner := by
      rw [hInnerSq, hBandInner]
      noncomm_ring

/-- If the inner range lies in the second support, its detector corner is the
sum of the second-support range leg and the opposite oriented commutator. -/
theorem detector_innerCorner_eq_secondSupport_twoBranch
    (band inner secondSupport detector : A)
    (hSecond : IsIdempotentElem secondSupport)
    (hSecondInner : secondSupport * inner = inner) :
    band * detector * inner =
      band * secondSupport * detector * inner +
        band * (1 - secondSupport) *
          commutator detector secondSupport * inner := by
  have hSecondSq : secondSupport * secondSupport = secondSupport := hSecond
  have hSecondComplement : (1 - secondSupport) * secondSupport = 0 := by
    calc
      (1 - secondSupport) * secondSupport =
          secondSupport - secondSupport * secondSupport := by
            noncomm_ring
      _ = 0 := by rw [hSecondSq]; noncomm_ring
  unfold commutator
  symm
  calc
    band * secondSupport * detector * inner +
          band * (1 - secondSupport) *
            (detector * secondSupport - secondSupport * detector) * inner =
        band * secondSupport * detector * inner +
          band * (1 - secondSupport) * detector *
            (secondSupport * inner) -
          band * ((1 - secondSupport) * secondSupport) * detector * inner := by
            noncomm_ring
    _ = band * secondSupport * detector * inner +
          band * (1 - secondSupport) * detector * inner := by
      rw [hSecondInner, hSecondComplement]
      noncomm_ring
    _ = band * detector * inner := by noncomm_ring

/-! The two-branch reduction remains exact after the fixed-quotient
transport and its outer band sandwich.  This is the form consumed by the
signed first-jet estimate; no branchwise norm is taken here. -/
theorem detector_innerCorner_transport_eq_secondSupport_twoBranch
    (band inner secondSupport detector transport : A)
    (hInner : IsIdempotentElem inner)
    (hBandInner : band * inner = 0)
    (hSecond : IsIdempotentElem secondSupport)
    (hSecondInner : secondSupport * inner = inner) :
    band * commutator detector inner * inner * transport * band =
      band * secondSupport * detector * inner * transport * band +
        band * (1 - secondSupport) * commutator detector secondSupport *
          inner * transport * band := by
  calc
    band * commutator detector inner * inner * transport * band =
        (band * commutator detector inner * inner) * transport * band := by
          rfl
    _ = (band * detector * inner) * transport * band := by
      rw [detector_innerCorner_eq_commutator band inner detector hInner
        hBandInner]
    _ = (band * secondSupport * detector * inner +
          band * (1 - secondSupport) * commutator detector secondSupport *
            inner) * transport * band := by
      rw [detector_innerCorner_eq_secondSupport_twoBranch band inner
        secondSupport detector hSecond hSecondInner]
    _ = band * secondSupport * detector * inner * transport * band +
          band * (1 - secondSupport) * commutator detector secondSupport *
            inner * transport * band := by
      noncomm_ring

/-! The route notation for Proof 405: the detector is the fixed quotient
compression and the inner range is the complete source compression. -/
theorem sourceCompressionCorner_eq_secondSupport_twoBranch
    (band support secondSupport prolate detector transport : A)
    (hInner : IsIdempotentElem
      (sourceCompression support secondSupport prolate))
    (hBandInner : band * sourceCompression support secondSupport prolate = 0)
    (hSecond : IsIdempotentElem secondSupport)
    (hSecondInner : secondSupport *
        sourceCompression support secondSupport prolate =
      sourceCompression support secondSupport prolate) :
    band * commutator (compressedDetector support detector)
        (sourceCompression support secondSupport prolate) *
        sourceCompression support secondSupport prolate * transport * band =
      band * secondSupport * compressedDetector support detector *
          sourceCompression support secondSupport prolate * transport * band +
        band * (1 - secondSupport) *
          commutator (compressedDetector support detector) secondSupport *
          sourceCompression support secondSupport prolate * transport * band := by
  exact detector_innerCorner_transport_eq_secondSupport_twoBranch band
    (sourceCompression support secondSupport prolate) secondSupport
    (compressedDetector support detector) transport hInner hBandInner hSecond
    hSecondInner

/-- The second-support range leg has the prolate compression as its formal
Gram square. -/
theorem secondSupport_leg_gram
    (band secondSupport : A)
    (hSecond : IsIdempotentElem secondSupport) :
    (band * secondSupport) * (secondSupport * band) =
      band * secondSupport * band := by
  have hSecondSq : secondSupport * secondSupport = secondSupport := hSecond
  calc
    (band * secondSupport) * (secondSupport * band) =
        band * (secondSupport * secondSupport) * band := by
          noncomm_ring
    _ = band * secondSupport * band := by rw [hSecondSq]

/-- The fixed quotient commutator may be replaced by its complete physical
outer/second-support/prolate ledger inside the first-jet corner. -/
theorem firstJetCorner_eq_physical
    (support secondSupport prolate detector transport band : A)
    (hSupport : IsIdempotentElem support)
    (hLeftSupport : support * prolate = prolate)
    (hRightSupport : prolate * support = prolate) :
    band *
          commutator (compressedDetector support detector)
            (sourceCompression support secondSupport prolate) *
          sourceCompression support secondSupport prolate * transport * band =
      band * fixedPhysicalCommutator support secondSupport prolate detector *
        sourceCompression support secondSupport prolate * transport * band := by
  rw [compressed_source_commutator_eq_physical support secondSupport prolate
    detector hSupport hLeftSupport hRightSupport]

end CCM24FiniteSFixedQuotientFirstJet
end CCM25Concrete
end Source
end ConnesWeilRH
