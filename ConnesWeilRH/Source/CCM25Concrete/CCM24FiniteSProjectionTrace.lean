/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.CCM24SemilocalFourierSupport
import ConnesWeilRH.Source.CCM25Concrete.SelectedCrossingOperatorBridge

/-!
# The finite-S projection/trace ledger on the common logarithmic carrier

This module places two independently constructed objects on the literal same
Hilbert space:

* the source/finite-S CCM24 Sonin projection difference; and
* the selected finite prime-power crossing-operator sum.

Their difference is the canonical same-object residual.  No theorem in this
file asserts that this residual vanishes or has a sign.  The point is to make
that remaining analytic obligation explicit after the carrier and projection
geometry have already been constructed.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSProjectionTrace

open ConnesWeilRH.Source.CC20Concrete
open SelectedCrossingOperatorBridge
open _root_.ConnesWeilRH.CC20Concrete.CCM24SoninTransportData

/-- A finite prime-power family with the arithmetic side conditions needed by
the selected crossing trace theorem. -/
structure FinitePrimePowerFamily where
  terms : Finset (ℕ × ℕ)
  prime : ∀ pm ∈ terms, pm.1.Prime
  exponent_ne_zero : ∀ pm ∈ terms, pm.2 ≠ 0

namespace FinitePrimePowerFamily

/-- The visible finite places are derived from the prime-power terms rather
than supplied as a second, unrelated finite set.  Repeated prime bases are
harmless because the Euler transports commute. -/
noncomputable def visiblePrimes (family : FinitePrimePowerFamily) :
    List CCM24VisiblePrime :=
  family.terms.attach.toList.map fun pm =>
    ⟨pm.1.1, (family.prime pm.1 pm.2).one_lt⟩

theorem mem_visiblePrimes_of_mem
    (family : FinitePrimePowerFamily) {pm : ℕ × ℕ}
    (hpm : pm ∈ family.terms) :
    (⟨pm.1, (family.prime pm hpm).one_lt⟩ : CCM24VisiblePrime) ∈
      family.visiblePrimes := by
  rw [visiblePrimes, List.mem_map]
  refine ⟨⟨pm, hpm⟩, ?_, rfl⟩
  simp

theorem exists_term_of_mem_visiblePrimes
    (family : FinitePrimePowerFamily) {p : CCM24VisiblePrime}
    (hp : p ∈ family.visiblePrimes) :
    ∃ m, (p.1, m) ∈ family.terms := by
  rw [visiblePrimes, List.mem_map] at hp
  obtain ⟨pm, -, rfl⟩ := hp
  exact ⟨pm.1.2, pm.2⟩

end FinitePrimePowerFamily

noncomputable abbrev finiteSCarrier := cc20GlobalLogCrossingL2

/-- The common radial-support projection `E_lambda`. -/
noncomputable def radialSupportProjection (lambda : CCM24SoninScale) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  (ccm24LogRadialSupportClosedSubspace lambda).toSubmodule.starProjection

/-- The archimedean Fourier-support projection `Q_0`. -/
noncomputable def sourceFourierSupportProjection (lambda : CCM24SoninScale) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  (ccm24ArchimedeanFourierSupportClosedSubspace lambda).toSubmodule.starProjection

/-- The semilocal Fourier-support projection `Q_S`, with `S` derived from the
same prime-power family used by the arithmetic operator. -/
noncomputable def targetFourierSupportProjection
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  (ccm24SemilocalFourierSupportClosedSubspace lambda family.visiblePrimes)
    |>.toSubmodule.starProjection

/-- The archimedean complete-Sonin projection `R_0`. -/
noncomputable def sourceSoninProjection (lambda : CCM24SoninScale) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).toSubmodule.starProjection

/-- The finite-S complete-Sonin projection `R_S`. -/
noncomputable def targetSoninProjection
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  (ccm24SemilocalSoninClosedSubspace lambda family.visiblePrimes)
    |>.toSubmodule.starProjection

/-- The concrete bounded-invertible CCM24 Sonin transport selected by the
same finite prime-power family. -/
noncomputable def transportData
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :=
  concreteCCM24SoninTransportData lambda family.visiblePrimes

theorem radialSupportProjection_isStarProjection (lambda : CCM24SoninScale) :
    IsStarProjection (radialSupportProjection lambda) :=
  isStarProjection_starProjection

theorem sourceFourierSupportProjection_isStarProjection
    (lambda : CCM24SoninScale) :
    IsStarProjection (sourceFourierSupportProjection lambda) :=
  isStarProjection_starProjection

theorem targetFourierSupportProjection_isStarProjection
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    IsStarProjection (targetFourierSupportProjection lambda family) :=
  isStarProjection_starProjection

theorem sourceSoninProjection_isStarProjection (lambda : CCM24SoninScale) :
    IsStarProjection (sourceSoninProjection lambda) :=
  isStarProjection_starProjection

theorem targetSoninProjection_isStarProjection
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    IsStarProjection (targetSoninProjection lambda family) :=
  isStarProjection_starProjection

/-- The source projection is the canonical projection from the concrete
CCM24 transport datum. -/
theorem sourceSoninProjection_eq_transportSourceProjection
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninProjection lambda =
      ((_root_.ConnesWeilRH.CC20Concrete.CCM24SoninTransportData.sourceSoninClosedSubspace
        (transportData lambda family)).toSubmodule).starProjection :=
  rfl

/-- The finite-S orthogonal projection is exactly the Gram-corrected frame
operator associated with the bounded invertible CCM24 transport. -/
theorem targetSoninProjection_eq_gramCorrected
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    targetSoninProjection lambda family =
      gramCorrectedTargetSoninProjection
        (transportData lambda family) := by
  symm
  exact gramCorrectedTargetSoninProjection_eq_targetSoninProjection
    (transportData lambda family)

/-- The archimedean prolate remainder `K_0 = E Q_0 E - R_0`. -/
noncomputable def sourceProlateRemainder (lambda : CCM24SoninScale) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  radialSupportProjection lambda ∘L sourceFourierSupportProjection lambda ∘L
      radialSupportProjection lambda - sourceSoninProjection lambda

/-- The finite-S prolate remainder `K_S = E Q_S E - R_S`. -/
noncomputable def targetProlateRemainder
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  radialSupportProjection lambda ∘L
      targetFourierSupportProjection lambda family ∘L
      radialSupportProjection lambda - targetSoninProjection lambda family

theorem sourceProlateRemainder_eq_factor (lambda : CCM24SoninScale) :
    sourceProlateRemainder lambda =
      (radialSupportProjection lambda - sourceSoninProjection lambda) ∘L
        sourceFourierSupportProjection lambda ∘L
        (radialSupportProjection lambda - sourceSoninProjection lambda) := by
  letI : CompleteSpace
      (((ccm24LogRadialSupportClosedSubspace lambda).toSubmodule ⊓
        (ccm24ArchimedeanFourierSupportClosedSubspace lambda).toSubmodule) :
          Submodule ℂ finiteSCarrier) :=
    (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe
  simpa [sourceProlateRemainder, radialSupportProjection,
    sourceFourierSupportProjection, sourceSoninProjection,
    ccm24ArchimedeanSoninClosedSubspace] using
      (_root_.ConnesWeilRH.CC20Concrete.compressed_projection_sub_intersection_eq_factor
        (ccm24LogRadialSupportClosedSubspace lambda).toSubmodule
        (ccm24ArchimedeanFourierSupportClosedSubspace lambda).toSubmodule)

theorem targetProlateRemainder_eq_factor
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    targetProlateRemainder lambda family =
      (radialSupportProjection lambda - targetSoninProjection lambda family) ∘L
        targetFourierSupportProjection lambda family ∘L
        (radialSupportProjection lambda - targetSoninProjection lambda family) := by
  unfold targetProlateRemainder
  rw [targetSoninProjection_eq_gramCorrected]
  simpa [targetProlateRemainder, radialSupportProjection,
    targetFourierSupportProjection] using
      (target_compression_sub_gramCorrected_eq_factor
        (transportData lambda family))

theorem sourceProlateRemainder_isPositive (lambda : CCM24SoninScale) :
    (sourceProlateRemainder lambda).IsPositive := by
  letI : CompleteSpace
      (((ccm24LogRadialSupportClosedSubspace lambda).toSubmodule ⊓
        (ccm24ArchimedeanFourierSupportClosedSubspace lambda).toSubmodule) :
          Submodule ℂ finiteSCarrier) :=
    (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe
  simpa [sourceProlateRemainder, radialSupportProjection,
    sourceFourierSupportProjection, sourceSoninProjection,
    ccm24ArchimedeanSoninClosedSubspace] using
      (_root_.ConnesWeilRH.CC20Concrete.compressed_projection_sub_intersection_isPositive
        (ccm24LogRadialSupportClosedSubspace lambda).toSubmodule
        (ccm24ArchimedeanFourierSupportClosedSubspace lambda).toSubmodule)

theorem targetProlateRemainder_isPositive
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    (targetProlateRemainder lambda family).IsPositive := by
  unfold targetProlateRemainder
  rw [targetSoninProjection_eq_gramCorrected]
  simpa [targetProlateRemainder, radialSupportProjection,
    targetFourierSupportProjection] using
      concreteCCM24_target_compression_sub_gramCorrected_isPositive
        lambda family.visiblePrimes

/-- The actual moving-band endpoint difference `R_S - R_0`. -/
noncomputable def bandDifference
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  targetSoninProjection lambda family - sourceSoninProjection lambda

/-- The compressed second-support change on the same carrier. -/
noncomputable def compressionDifference
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  radialSupportProjection lambda ∘L
      targetFourierSupportProjection lambda family ∘L
      radialSupportProjection lambda -
    radialSupportProjection lambda ∘L
      sourceFourierSupportProjection lambda ∘L
      radialSupportProjection lambda

/-- The finite-S/source prolate difference `K_S - K_0`. -/
noncomputable def prolateDifference
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  targetProlateRemainder lambda family - sourceProlateRemainder lambda

/-- Exact same-object projection bookkeeping:
`R_S - R_0 = E(Q_S-Q_0)E - (K_S-K_0)`. -/
theorem bandDifference_eq_compressionDifference_sub_prolateDifference
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    bandDifference lambda family =
      compressionDifference lambda family - prolateDifference lambda family := by
  simp only [bandDifference, compressionDifference, prolateDifference,
    sourceProlateRemainder, targetProlateRemainder]
  abel

/-- The genuine positive convolution detector belonging to the selected Weil
square owner. -/
noncomputable def detectorOperator
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  cc20GlobalConvolutionPositive owner.sourceTest.involution.test

/-- The selected detector applied to the actual finite-S band difference. -/
noncomputable def projectionResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  detectorOperator owner ∘L bandDifference lambda family

theorem projectionResponse_eq_compression_sub_prolate
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    projectionResponse owner lambda family =
      detectorOperator owner ∘L compressionDifference lambda family -
        detectorOperator owner ∘L prolateDifference lambda family := by
  rw [projectionResponse,
    bandDifference_eq_compressionDifference_sub_prolateDifference]
  exact ContinuousLinearMap.comp_sub _ _ _

/-- The already constructed selected prime-power crossing sum, now indexed by
the same family that determines the finite-S CCM24 projection. -/
noncomputable def arithmeticOperator
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  eulerLogWeightedGlobalPairTraceOperatorSum owner family.terms

theorem arithmeticOperator_isSelfAdjoint
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily) :
    IsSelfAdjoint (arithmeticOperator owner family) :=
  eulerLogWeightedGlobalPairTraceOperatorSum_isSelfAdjoint owner family.terms

/-- The canonical residual.  This is a definition from two actual operators,
not a stored equality premise. -/
noncomputable def sameObjectResidual
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  projectionResponse owner lambda family - arithmeticOperator owner family

theorem projectionResponse_eq_arithmetic_add_residual
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    projectionResponse owner lambda family =
      arithmeticOperator owner family +
        sameObjectResidual owner lambda family := by
  simp [sameObjectResidual]

theorem sameObjectResidual_eq_threePartLedger
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sameObjectResidual owner lambda family =
      (detectorOperator owner ∘L compressionDifference lambda family -
        arithmeticOperator owner family) -
      detectorOperator owner ∘L prolateDifference lambda family := by
  rw [sameObjectResidual, projectionResponse_eq_compression_sub_prolate]
  abel

namespace PositiveTrace

variable {ι H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem isTraceClassAlong_neg
    (basis : HilbertBasis ι ℂ H) (operator : H →L[ℂ] H)
    (hoperator : CC20Concrete.PositiveTrace.IsTraceClassAlong basis operator) :
    CC20Concrete.PositiveTrace.IsTraceClassAlong basis (-operator) := by
  rw [CC20Concrete.PositiveTrace.IsTraceClassAlong] at hoperator ⊢
  simpa only [ContinuousLinearMap.neg_apply, inner_neg_right] using
    hoperator.neg

omit [CompleteSpace H] in
theorem isTraceClassAlong_sub
    (basis : HilbertBasis ι ℂ H) (left right : H →L[ℂ] H)
    (hleft : CC20Concrete.PositiveTrace.IsTraceClassAlong basis left)
    (hright : CC20Concrete.PositiveTrace.IsTraceClassAlong basis right) :
    CC20Concrete.PositiveTrace.IsTraceClassAlong basis (left - right) := by
  rw [sub_eq_add_neg]
  exact CC20Concrete.PositiveTrace.isTraceClassAlong_add basis left (-right)
    hleft (isTraceClassAlong_neg basis right hright)

omit [CompleteSpace H] in
theorem ordinaryTraceAlong_neg
    (basis : HilbertBasis ι ℂ H) (operator : H →L[ℂ] H) :
    CC20Concrete.PositiveTrace.ordinaryTraceAlong basis (-operator) =
      -CC20Concrete.PositiveTrace.ordinaryTraceAlong basis operator := by
  rw [CC20Concrete.PositiveTrace.ordinaryTraceAlong,
    CC20Concrete.PositiveTrace.ordinaryTraceAlong]
  simp only [ContinuousLinearMap.neg_apply, inner_neg_right]
  rw [tsum_neg]

omit [CompleteSpace H] in
theorem ordinaryTraceAlong_sub
    (basis : HilbertBasis ι ℂ H) (left right : H →L[ℂ] H)
    (hleft : CC20Concrete.PositiveTrace.IsTraceClassAlong basis left)
    (hright : CC20Concrete.PositiveTrace.IsTraceClassAlong basis right) :
    CC20Concrete.PositiveTrace.ordinaryTraceAlong basis (left - right) =
      CC20Concrete.PositiveTrace.ordinaryTraceAlong basis left -
        CC20Concrete.PositiveTrace.ordinaryTraceAlong basis right := by
  rw [sub_eq_add_neg]
  rw [CC20Concrete.PositiveTrace.ordinaryTraceAlong_add basis left (-right)
    hleft (isTraceClassAlong_neg basis right hright)]
  rw [ordinaryTraceAlong_neg basis right]
  rfl

end PositiveTrace

theorem arithmeticOperator_isTraceClassAlong
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (a c : ℝ) (family : FinitePrimePowerFamily)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (basisData : ∀ pm : {pm // pm ∈ family.terms},
      GlobalPrimePowerTraceBasisData a c pm.1.1 pm.1.2) :
    CC20Concrete.PositiveTrace.IsTraceClassAlong globalBasis
      (arithmeticOperator owner family) := by
  exact eulerLogWeightedGlobalPairTraceOperatorSum_isTraceClassAlong
    owner a c family.terms family.prime hsupp globalBasis basisData

theorem sameObjectResidual_isTraceClassAlong
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (a c : ℝ) (lambda : CCM24SoninScale)
    (family : FinitePrimePowerFamily)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (basisData : ∀ pm : {pm // pm ∈ family.terms},
      GlobalPrimePowerTraceBasisData a c pm.1.1 pm.1.2)
    (hresponse : CC20Concrete.PositiveTrace.IsTraceClassAlong globalBasis
      (projectionResponse owner lambda family)) :
    CC20Concrete.PositiveTrace.IsTraceClassAlong globalBasis
      (sameObjectResidual owner lambda family) := by
  rw [sameObjectResidual]
  exact PositiveTrace.isTraceClassAlong_sub globalBasis _ _ hresponse
    (arithmeticOperator_isTraceClassAlong owner a c family hsupp
      globalBasis basisData)

/-- Exact ordinary-trace decomposition on the named Hilbert basis.  Fixed-S
trace legality for the full projection response remains an explicit analytic
input; the arithmetic and residual legality are then derived. -/
theorem ordinaryTraceAlong_projectionResponse_eq_arithmetic_add_residual
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (a c : ℝ) (lambda : CCM24SoninScale)
    (family : FinitePrimePowerFamily)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (basisData : ∀ pm : {pm // pm ∈ family.terms},
      GlobalPrimePowerTraceBasisData a c pm.1.1 pm.1.2)
    (hresponse : CC20Concrete.PositiveTrace.IsTraceClassAlong globalBasis
      (projectionResponse owner lambda family)) :
    CC20Concrete.PositiveTrace.ordinaryTraceAlong globalBasis
        (projectionResponse owner lambda family) =
      CC20Concrete.PositiveTrace.ordinaryTraceAlong globalBasis
          (arithmeticOperator owner family) +
        CC20Concrete.PositiveTrace.ordinaryTraceAlong globalBasis
          (sameObjectResidual owner lambda family) := by
  rw [projectionResponse_eq_arithmetic_add_residual]
  exact CC20Concrete.PositiveTrace.ordinaryTraceAlong_add globalBasis _ _
    (arithmeticOperator_isTraceClassAlong owner a c family hsupp
      globalBasis basisData)
    (sameObjectResidual_isTraceClassAlong owner a c lambda family hsupp
      globalBasis basisData hresponse)

/-- Arithmetic readback of the same-object ledger.  The first summand is the
existing selected finite-prime atom sum; every still-unproved finite-S effect
is isolated in the canonical residual trace. -/
theorem ordinaryTraceAlong_projectionResponse_eq_finitePrimeSum_add_residual
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (a c : ℝ) (lambda : CCM24SoninScale)
    (family : FinitePrimePowerFamily)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (basisData : ∀ pm : {pm // pm ∈ family.terms},
      GlobalPrimePowerTraceBasisData a c pm.1.1 pm.1.2)
    (hresponse : CC20Concrete.PositiveTrace.IsTraceClassAlong globalBasis
      (projectionResponse owner lambda family)) :
    CC20Concrete.PositiveTrace.ordinaryTraceAlong globalBasis
        (projectionResponse owner lambda family) =
      (∑ pm ∈ family.terms,
        owner.finitePrimeTerm (pm.1 ^ pm.2)) +
      CC20Concrete.PositiveTrace.ordinaryTraceAlong globalBasis
        (sameObjectResidual owner lambda family) := by
  rw [ordinaryTraceAlong_projectionResponse_eq_arithmetic_add_residual
    owner a c lambda family hsupp globalBasis basisData hresponse]
  rw [arithmeticOperator]
  rw [ordinaryTraceAlong_eulerLogWeightedGlobalPairTraceOperatorSum_eq_finitePrimeTerm_pow_sum
    owner a c family.terms family.prime family.exponent_ne_zero hsupp
      globalBasis basisData]

end CCM24FiniteSProjectionTrace
end CCM25Concrete
end Source
end ConnesWeilRH
