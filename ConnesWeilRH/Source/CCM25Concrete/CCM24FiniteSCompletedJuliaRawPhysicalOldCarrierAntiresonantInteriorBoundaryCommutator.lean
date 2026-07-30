/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorGapNormEquivalence
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCommonBoundaryPair
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSTwoSidedRootRecombination

/-!
# Radial boundary expansion of the compressed adjoint renewal

Proof 619 identifies the surviving old-carrier interior owner with the
synchronized metric/forward gap.  This module supplies the next exact source
identity.  The selected detector commutes with the genuine normalized Euler
inverse and its adjoint.  Consequently the commutator of the radial
compressions

```text
E D E,    E N_p^dagger E
```

is supported entirely at the two radial boundaries.  The final theorem keeps
the two crossing orientations signed and grouped.  It takes no norm and does
not identify this commutator with the complete synchronized gap.

Bone 1, Gate 3U, the finite-S sign, Burnol's identity, and RH remain open.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorBoundaryCommutator

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCausalMarkov
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantGeometricBoundaryResolvent
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSGramResponse
open CCM24FiniteSParameterizedEulerEquiv
open CCM24FiniteSProjectionTrace
open CCM24FiniteSTwoSidedRootRecombination

/-! ## Euler inverse commutation -/

/-- The selected convolution detector commutes with the probability-normalized
one-prime Euler inverse.  This is the inverse counterpart of the existing
forward-transport commutation theorem. -/
theorem detectorOperator_comp_normalizedPrimeEulerInverse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (p : CCM24VisiblePrime) :
    detectorOperator owner ∘L normalizedPrimeEulerInverse p =
      normalizedPrimeEulerInverse p ∘L detectorOperator owner := by
  apply ContinuousLinearMap.ext
  intro x
  have hinverse :
      detectorOperator owner ((ccm24PrimeEulerTransportEquiv p).symm x) =
        (ccm24PrimeEulerTransportEquiv p).symm
          (detectorOperator owner x) := by
    apply (ccm24PrimeEulerTransportEquiv p).injective
    have hcommute := DFunLike.congr_fun
      (CCM24FiniteSGramResponse.detectorOperator_comp_primeEulerTransport
        owner p)
      ((ccm24PrimeEulerTransportEquiv p).symm x)
    simp only [ContinuousLinearMap.comp_apply] at hcommute
    simpa using hcommute.symm
  simp only [normalizedPrimeEulerInverse,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, map_smul]
  exact congrArg
    (fun y : finiteSCarrier =>
      ((1 - ccm24PrimeEulerCoefficient p : ℝ) : ℂ) • y)
    hinverse

/-- Taking adjoints preserves detector commutation because the detector is
self-adjoint. -/
theorem normalizedPrimeEulerInverse_adjoint_comp_detectorOperator
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (p : CCM24VisiblePrime) :
    (normalizedPrimeEulerInverse p)† ∘L detectorOperator owner =
      detectorOperator owner ∘L (normalizedPrimeEulerInverse p)† := by
  have h := congrArg ContinuousLinearMap.adjoint
    (detectorOperator_comp_normalizedPrimeEulerInverse owner p)
  simpa only [ContinuousLinearMap.adjoint_comp,
    (detectorOperator_isSelfAdjoint owner).adjoint_eq] using h

theorem detectorOperator_comp_normalizedPrimeEulerInverse_adjoint
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (p : CCM24VisiblePrime) :
    detectorOperator owner ∘L (normalizedPrimeEulerInverse p)† =
      (normalizedPrimeEulerInverse p)† ∘L detectorOperator owner :=
  (normalizedPrimeEulerInverse_adjoint_comp_detectorOperator owner p).symm

/-! ## Concrete two-boundary owner -/

/-- The detector compressed to the genuine upper radial half-line. -/
noncomputable def primeEulerRadialCompressedDetector
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  compressedDetector (radialSupportProjection lambda) (detectorOperator owner)

/-- The commutator of the compressed detector with the genuine compressed
adjoint renewal is exactly the sum of two radial-boundary commutator terms.
The complete inverse remains inside both terms. -/
theorem radialCompressedDetector_commutator_compressedAdjointRenewal_eq_boundary
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) :
    commutator (primeEulerRadialCompressedDetector owner lambda)
        (primeEulerCompressedAdjointRenewal lambda p) =
      radialSupportProjection lambda *
          commutator (detectorOperator owner)
            (radialSupportProjection lambda) *
          (normalizedPrimeEulerInverse p)† *
          radialSupportProjection lambda +
        radialSupportProjection lambda *
          (normalizedPrimeEulerInverse p)† *
          commutator (detectorOperator owner)
            (radialSupportProjection lambda) *
          radialSupportProjection lambda := by
  have hcommute :
      detectorOperator owner * (normalizedPrimeEulerInverse p)† =
        (normalizedPrimeEulerInverse p)† * detectorOperator owner := by
    simpa only [ContinuousLinearMap.mul_def] using
      (detectorOperator_comp_normalizedPrimeEulerInverse_adjoint owner p)
  have h := compressed_commutator_eq_boundary
    (radialSupportProjection lambda)
    (detectorOperator owner)
    ((normalizedPrimeEulerInverse p)†)
    (radialSupportProjection_isStarProjection lambda).isIdempotentElem
    hcommute
  simpa only [primeEulerRadialCompressedDetector,
    primeEulerCompressedAdjointRenewal, compressedPrefix,
    ContinuousLinearMap.mul_def] using h

/-- Crossing form of the same identity.  Each bracket is kept as one signed
pair `exterior crossing - reflected crossing`; no branchwise norm is taken. -/
theorem radialCompressedDetector_commutator_compressedAdjointRenewal_eq_crossings
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) :
    commutator (primeEulerRadialCompressedDetector owner lambda)
        (primeEulerCompressedAdjointRenewal lambda p) =
      radialSupportProjection lambda *
          (orientedCrossing (radialSupportProjection lambda)
              (detectorOperator owner) -
            reverseOrientedCrossing (radialSupportProjection lambda)
              (detectorOperator owner)) *
          (normalizedPrimeEulerInverse p)† *
          radialSupportProjection lambda +
        radialSupportProjection lambda *
          (normalizedPrimeEulerInverse p)† *
          (orientedCrossing (radialSupportProjection lambda)
              (detectorOperator owner) -
            reverseOrientedCrossing (radialSupportProjection lambda)
              (detectorOperator owner)) *
          radialSupportProjection lambda := by
  rw [radialCompressedDetector_commutator_compressedAdjointRenewal_eq_boundary]
  rw [commutator_eq_orientedCrossing_sub_reverse]

/-! ## Complete outer/second-support/prolate recombination -/

/-- The complete radial quotient bracket with the actual source Sonin
projection and the genuine adjoint Euler renewal. -/
noncomputable def primeEulerRadialCorrectedQuotientBracket
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  correctedQuotientBracket
    (radialSupportProjection lambda)
    (detectorOperator owner)
    ((normalizedPrimeEulerInverse p)†)
    (sourceSoninProjection lambda)

/-- The same object after all fixed physical boundary branches have been
recombined. -/
noncomputable def primeEulerRadialCorrectedPhysicalBracket
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  correctedPhysicalBracket
    (radialSupportProjection lambda)
    (sourceFourierSupportProjection lambda)
    (sourceProlateRemainder lambda)
    (detectorOperator owner)
    ((normalizedPrimeEulerInverse p)†)

/-- Exact same-object passage from the quotient bracket to the complete
outer, second-support, reflected-outer, prolate, and quotient-boundary
physical bracket. -/
theorem primeEulerRadialCorrectedQuotientBracket_eq_physical
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) :
    primeEulerRadialCorrectedQuotientBracket owner lambda p =
      primeEulerRadialCorrectedPhysicalBracket owner lambda p := by
  have hsource :
      sourceCompression
          (radialSupportProjection lambda)
          (sourceFourierSupportProjection lambda)
          (sourceProlateRemainder lambda) =
        sourceSoninProjection lambda := by
    simpa only [sourceCompression, ContinuousLinearMap.mul_def] using
      (sourceSoninProjection_eq_compression_sub_prolate lambda).symm
  have hleft :
      radialSupportProjection lambda * sourceProlateRemainder lambda =
        sourceProlateRemainder lambda := by
    simpa only [ContinuousLinearMap.mul_def] using
      (radialSupportProjection_comp_sourceProlateRemainder lambda)
  have hright :
      sourceProlateRemainder lambda * radialSupportProjection lambda =
        sourceProlateRemainder lambda := by
    simpa only [ContinuousLinearMap.mul_def] using
      (sourceProlateRemainder_comp_radialSupportProjection lambda)
  have hcommute :
      detectorOperator owner * (normalizedPrimeEulerInverse p)† =
        (normalizedPrimeEulerInverse p)† * detectorOperator owner := by
    simpa only [ContinuousLinearMap.mul_def] using
      (detectorOperator_comp_normalizedPrimeEulerInverse_adjoint owner p)
  rw [primeEulerRadialCorrectedQuotientBracket,
    primeEulerRadialCorrectedPhysicalBracket, ← hsource]
  exact correctedQuotientBracket_eq_physical
    (radialSupportProjection lambda)
    (sourceFourierSupportProjection lambda)
    (sourceProlateRemainder lambda)
    (detectorOperator owner)
    ((normalizedPrimeEulerInverse p)†)
    (radialSupportProjection_isStarProjection lambda).isIdempotentElem
    hleft hright hcommute

/-- Fully displayed signed ledger.  The first parenthesis keeps the fixed
outer/second-support/reflected/prolate branches whole, while the last two
summands are the mandatory quotient-compression boundary corrections. -/
theorem primeEulerRadialCorrectedQuotientBracket_eq_completeBoundaryLedger
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) :
    primeEulerRadialCorrectedQuotientBracket owner lambda p =
      -(radialSupportProjection lambda *
          (normalizedPrimeEulerInverse p)† *
          radialSupportProjection lambda) *
        (radialSupportProjection lambda *
              commutator (detectorOperator owner)
                (radialSupportProjection lambda) *
              sourceFourierSupportProjection lambda *
              radialSupportProjection lambda +
            radialSupportProjection lambda *
              commutator (detectorOperator owner)
                (sourceFourierSupportProjection lambda) *
              radialSupportProjection lambda +
            radialSupportProjection lambda *
              sourceFourierSupportProjection lambda *
              commutator (detectorOperator owner)
                (radialSupportProjection lambda) *
              radialSupportProjection lambda -
            radialSupportProjection lambda *
              commutator (detectorOperator owner)
                (sourceProlateRemainder lambda) *
              radialSupportProjection lambda) +
        radialSupportProjection lambda *
          commutator (detectorOperator owner)
            (radialSupportProjection lambda) *
          (normalizedPrimeEulerInverse p)† *
          radialSupportProjection lambda +
        radialSupportProjection lambda *
          (normalizedPrimeEulerInverse p)† *
          commutator (detectorOperator owner)
            (radialSupportProjection lambda) *
          radialSupportProjection lambda := by
  rw [primeEulerRadialCorrectedQuotientBracket_eq_physical]
  rfl

end CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorBoundaryCommutator
end CCM25Concrete
end Source
end ConnesWeilRH
