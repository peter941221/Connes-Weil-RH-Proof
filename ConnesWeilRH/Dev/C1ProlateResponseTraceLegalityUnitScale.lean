/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSProjectionTrace
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSBandTrace
import ConnesWeilRH.Source.CCM25Concrete.CCM24SourceProlateTrace
import ConnesWeilRH.Source.CCM25Concrete.CCM24UnitScaleStrictAngle
import ConnesWeilRH.Dev.C1SelectedDetectorSemiLocalEulerBoundary

/-!
# P1: detector-weighted trace legality of the finite-S response at unit scale

This is brick #1 of the Option-C semi-local bridge (doc 1050 section 4).  The
Gate-2 arithmetic readback

```text
ordinaryTraceAlong_projectionResponse_eq_finitePrimeSum_add_residual
```

currently carries one explicit analytic premise,

```text
hresponse : IsTraceClassAlong globalBasis (projectionResponse owner lambda family)
```

which is exactly the trace legality of the selected-detector response
operator.  This file reduces that premise at the canonical unit scale
`lambda = unitSoninScale` to the exact detector-weighted target-prolate
obligation F1' below, plus the two Fourier-compression Hilbert--Schmidt
premises.  It does not claim to discharge F1' analytically.

The response decomposes (Source-side, family form) as a difference of two
detector-weighted band pieces:

```text
projectionResponse owner lambda family
  = detectorOperator ∘ prolateDifference − detectorOperator ∘ compressionDifference
        [CCM24FiniteSProjectionTrace.projectionResponse_eq_compression_sub_prolate]
```

The source prolate and both compression pieces use established
Hilbert--Schmidt pair data.  The finite-S target prolate remainder is consumed
directly in its detector-weighted form, because that is the exact operator
needed by the response.

Two unit-scale contracts are load-bearing:

  F1'. detector-weighted target-prolate trace legality at unit scale;
  F2. named Hilbert--Schmidt summability for the two Fourier-compression
       factors at unit scale.

Record 1063 supplies a numerical guard against spending proof effort on the
stronger raw-F1 statement.  It is not a formal negation of that continuum
statement.  No positivity, no remainder sign, and no RH-facing statement is
asserted here; this file only supplies conditional trace-legality reductions.
-/

namespace ConnesWeilRH
namespace Source
namespace C1ProlateResponseTraceLegalityUnitScale

open CC20Concrete
open CC20Concrete.PositiveTrace
open CCM25Concrete
open CCM25Concrete.CCM24FiniteSProjectionTrace
open CCM25Concrete.CCM24SourceProlateTrace
open CCM25Concrete.CCM24UnitScaleProlateTraceReduction
open C1SelectedDetectorSemiLocalEulerBoundary
open MeasureTheory
open scoped BigOperators InnerProduct

local notation "Op" => finiteSCarrier →L[ℂ] finiteSCarrier

noncomputable section

/-- The bounded target prolate factor `Q_S (E-R_S)`.  It is a factor of the
finite-S remainder, but this leaf makes no raw Hilbert--Schmidt assertion about
it: record 1063 guards against scheduling the corresponding raw target. -/
noncomputable def targetProlateRemainderFactor
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) : Op :=
  targetFourierSupportProjection lambda family ∘L
    (radialSupportProjection lambda - targetSoninProjection lambda family)

/-- The actual finite-S prolate remainder is the positive square of that named
factor. -/
theorem targetProlateRemainderFactor_adjoint_comp_self
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    (targetProlateRemainderFactor lambda family).adjoint ∘L
        targetProlateRemainderFactor lambda family =
      targetProlateRemainder lambda family := by
  rw [targetProlateRemainder_eq_factor]
  unfold targetProlateRemainderFactor
  rw [ContinuousLinearMap.adjoint_comp, map_sub]
  rw [(targetFourierSupportProjection_isStarProjection lambda family)
    |>.isSelfAdjoint.adjoint_eq]
  rw [(radialSupportProjection_isStarProjection lambda)
    |>.isSelfAdjoint.adjoint_eq]
  rw [(targetSoninProjection_isStarProjection lambda family)
    |>.isSelfAdjoint.adjoint_eq]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply]
  have hidempotent := congrArg
    (fun T : Op => T
      ((radialSupportProjection lambda - targetSoninProjection lambda family) u))
    ((targetFourierSupportProjection_isStarProjection lambda family)
      |>.isIdempotentElem)
  exact congrArg
    (radialSupportProjection lambda - targetSoninProjection lambda family)
    (by simpa only [ContinuousLinearMap.mul_apply] using hidempotent)

/-- F1': the exact analytic obligation consumed by the response.  This is an
explicit proposition rather than a stored source-data field or an established
theorem: an eventual producer must prove that the selected detector regularizes
the finite-S target prolate remainder along the named basis consumed downstream. -/
def targetProlateRemainderDetectorWeightedTraceLegality
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily) {ν : Type*}
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier) : Prop :=
  IsTraceClassAlong globalBasis
    (detectorOperator owner ∘L targetProlateRemainder unitSoninScale family)

/-!
The direct F1' contract above is the exact operand of `projectionResponse`.
Write `A† A = K_S` and `D = C† C`, with `C` the selected convolution root.
The active order has the exact decomposition

```text
D K_S = C† K_S C + C† [C, K_S].
```

The first term is the positive square `(A C)† (A C)`.  The second term is the
only root-commutator remainder that must be controlled before the active
response can be read back.  This is not a cyclic trace assertion: both
ingredients below are explicit analytic obligations.
-/

/-- The active-order smoothing factor `A C`, where `A† A = K_S` and `C` is the
selected convolution root. -/
noncomputable def targetProlateDetectorRightSmoothingFactor
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily) : Op :=
  targetProlateRemainderFactor unitSoninScale family ∘L
    CCM25Concrete.CCM24FiniteSBandTrace.rootConvolution owner

/-- The positive active-order sandwich `C† K_S C`. -/
noncomputable def targetProlateDetectorRightSandwich
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily) : Op :=
  (CCM25Concrete.CCM24FiniteSBandTrace.rootConvolution owner)† ∘L
    targetProlateRemainder unitSoninScale family ∘L
      CCM25Concrete.CCM24FiniteSBandTrace.rootConvolution owner

/-- The active-order sandwich is exactly `(A C)† (A C)`. -/
theorem targetProlateDetectorRightSmoothingFactor_adjoint_comp_self
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily) :
    (targetProlateDetectorRightSmoothingFactor owner family).adjoint ∘L
        targetProlateDetectorRightSmoothingFactor owner family =
      targetProlateDetectorRightSandwich owner family := by
  unfold targetProlateDetectorRightSmoothingFactor targetProlateDetectorRightSandwich
  rw [ContinuousLinearMap.adjoint_comp]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply]
  have hfactor := congrArg
    (fun operator : Op => operator
      (CCM25Concrete.CCM24FiniteSBandTrace.rootConvolution owner u))
    (targetProlateRemainderFactor_adjoint_comp_self unitSoninScale family)
  simpa only [ContinuousLinearMap.comp_apply] using
    congrArg (CCM25Concrete.CCM24FiniteSBandTrace.rootConvolution owner).adjoint hfactor

/-- Named-basis Hilbert--Schmidt summability for the active-order smoothing
factor.  This is the S1 analytic obligation. -/
def targetProlateDetectorRightSmoothingFactorSummable
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily) {ν : Type*}
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier) : Prop :=
  Summable fun i =>
    ‖targetProlateDetectorRightSmoothingFactor owner family (globalBasis i)‖ ^ 2

/-- Pair-data owner for the positive active-order sandwich. -/
noncomputable def targetProlateDetectorRightSandwichPairData
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily)
    (hfactor : targetProlateDetectorRightSmoothingFactorSummable owner family globalBasis) :
    BasisHilbertSchmidtPairData (G := finiteSCarrier) globalBasis where
  left := targetProlateDetectorRightSmoothingFactor owner family
  right := targetProlateDetectorRightSmoothingFactor owner family
  left_summable_normSq := hfactor
  right_summable_normSq := hfactor

/-- The pair-data trace product is the active-order positive sandwich. -/
theorem targetProlateDetectorRightSandwichPairData_traceProduct_eq
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily)
    (hfactor : targetProlateDetectorRightSmoothingFactorSummable owner family globalBasis) :
    (targetProlateDetectorRightSandwichPairData globalBasis owner family hfactor).traceProduct =
      targetProlateDetectorRightSandwich owner family := by
  unfold targetProlateDetectorRightSandwichPairData
    BasisHilbertSchmidtPairData.traceProduct
  exact targetProlateDetectorRightSmoothingFactor_adjoint_comp_self owner family

/-- S1 makes the active-order positive sandwich trace-legal along the same
named basis. -/
theorem targetProlateDetectorRightSandwich_isTraceClassAlong
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily)
    (hfactor : targetProlateDetectorRightSmoothingFactorSummable owner family globalBasis) :
    IsTraceClassAlong globalBasis (targetProlateDetectorRightSandwich owner family) := by
  let data := targetProlateDetectorRightSandwichPairData globalBasis owner family hfactor
  have htrace : IsTraceClassAlong globalBasis data.traceProduct :=
    data.traceProduct_isTraceClassAlong
  have hproduct : data.traceProduct = targetProlateDetectorRightSandwich owner family := by
    simpa only [data] using
      targetProlateDetectorRightSandwichPairData_traceProduct_eq globalBasis owner family hfactor
  rw [hproduct] at htrace
  exact htrace

/-- The active-order root-commutator remainder `C† [C, K_S]`. -/
noncomputable def targetProlateDetectorRootCommutatorRemainder
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily) : Op :=
  (CCM25Concrete.CCM24FiniteSBandTrace.rootConvolution owner)† ∘L
    cc20Commutator (CCM25Concrete.CCM24FiniteSBandTrace.rootConvolution owner)
      (targetProlateRemainder unitSoninScale family)

/-- The S2 trace-legality obligation for the active-order root commutator. -/
def targetProlateDetectorRootCommutatorTraceLegality
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily) {ν : Type*}
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier) : Prop :=
  IsTraceClassAlong globalBasis
    (targetProlateDetectorRootCommutatorRemainder owner family)

/-- Two genuine Hilbert--Schmidt legs for `[C, K_S]` supply S2 after bounded
left multiplication by `C†`; no unrestricted trace cyclicity is used. -/
theorem targetProlateDetectorRootCommutatorTraceLegality_of_pairData
    {ν κ G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier) (factorBasis : HilbertBasis κ ℂ G)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily)
    (pairData : BasisHilbertSchmidtPairData (G := G) globalBasis)
    (hpair : pairData.traceProduct =
      cc20Commutator (CCM25Concrete.CCM24FiniteSBandTrace.rootConvolution owner)
        (targetProlateRemainder unitSoninScale family)) :
    targetProlateDetectorRootCommutatorTraceLegality owner family globalBasis := by
  let identity := ContinuousLinearMap.id ℂ finiteSCarrier
  have htrace : IsTraceClassAlong globalBasis
      ((CCM25Concrete.CCM24FiniteSBandTrace.rootConvolution owner).adjoint ∘L
        pairData.traceProduct ∘L identity) := by
    exact pairData.boundedSandwich_isTraceClassAlong factorBasis
      (CCM25Concrete.CCM24FiniteSBandTrace.rootConvolution owner).adjoint identity
  rw [hpair] at htrace
  simpa only [targetProlateDetectorRootCommutatorTraceLegality,
    targetProlateDetectorRootCommutatorRemainder, identity,
    ContinuousLinearMap.comp_id] using htrace

/-- The root/target-prolate commutator is the negative of the concrete
outer/second-support/reflected-outer/Sonin four-branch ledger.  The two outer
branches are the half-line convolution candidates; existing detector-level
machinery for `C† C` is not by itself a producer for this root commutator.
All four branches remain explicit analytic obligations here. -/
theorem rootConvolution_targetProlateRemainder_commutator_eq_neg_threeBranch
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily) :
    cc20Commutator (CCM25Concrete.CCM24FiniteSBandTrace.rootConvolution owner)
        (targetProlateRemainder unitSoninScale family) =
      -cc20ThreeBranchCommutator
        (radialSupportProjection unitSoninScale)
        (targetFourierSupportProjection unitSoninScale family)
        (targetSoninProjection unitSoninScale family)
        (CCM25Concrete.CCM24FiniteSBandTrace.rootConvolution owner) := by
  let C : Op := CCM25Concrete.CCM24FiniteSBandTrace.rootConvolution owner
  let K : Op := targetProlateRemainder unitSoninScale family
  let E : Op := radialSupportProjection unitSoninScale
  let Q : Op := targetFourierSupportProjection unitSoninScale family
  let R : Op := targetSoninProjection unitSoninScale family
  have hK : K = E ∘L Q ∘L E - R := by
    rfl
  have hledger : cc20Commutator K C = cc20ThreeBranchCommutator E Q R C :=
    cc20Commutator_eq_threeBranch_of_eq E Q K R C hK
  have hanti : cc20Commutator C K = -cc20Commutator K C := by
    unfold cc20Commutator
    apply ContinuousLinearMap.ext
    intro u
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.neg_apply,
      ContinuousLinearMap.comp_apply]
    abel
  change cc20Commutator C K = -cc20ThreeBranchCommutator E Q R C
  rw [hanti, hledger]

/-- A pair owner for the complete signed four-branch ledger supplies S2 after
bounded left multiplication by `C†`.  This deliberately does not require the
four terms to be trace-class separately. -/
theorem targetProlateDetectorRootCommutatorTraceLegality_of_threeBranchPairData
    {ν κ G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier) (factorBasis : HilbertBasis κ ℂ G)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily)
    (pairData : BasisHilbertSchmidtPairData (G := G) globalBasis)
    (hpair : pairData.traceProduct =
      -cc20ThreeBranchCommutator
        (radialSupportProjection unitSoninScale)
        (targetFourierSupportProjection unitSoninScale family)
        (targetSoninProjection unitSoninScale family)
        (CCM25Concrete.CCM24FiniteSBandTrace.rootConvolution owner)) :
    targetProlateDetectorRootCommutatorTraceLegality owner family globalBasis := by
  apply targetProlateDetectorRootCommutatorTraceLegality_of_pairData
    globalBasis factorBasis owner family pairData
  exact hpair.trans
    (rootConvolution_targetProlateRemainder_commutator_eq_neg_threeBranch
      owner family).symm

/-- The active-order root-commutator remainder is the same four-branch ledger
after its required bounded left multiplier `C†` is restored. -/
theorem targetProlateDetectorRootCommutatorRemainder_eq_neg_threeBranch
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily) :
    targetProlateDetectorRootCommutatorRemainder owner family =
      -((CCM25Concrete.CCM24FiniteSBandTrace.rootConvolution owner).adjoint ∘L
        cc20ThreeBranchCommutator
          (radialSupportProjection unitSoninScale)
          (targetFourierSupportProjection unitSoninScale family)
          (targetSoninProjection unitSoninScale family)
          (CCM25Concrete.CCM24FiniteSBandTrace.rootConvolution owner)) := by
  let C : Op := CCM25Concrete.CCM24FiniteSBandTrace.rootConvolution owner
  let K : Op := targetProlateRemainder unitSoninScale family
  let E : Op := radialSupportProjection unitSoninScale
  let Q : Op := targetFourierSupportProjection unitSoninScale family
  let R : Op := targetSoninProjection unitSoninScale family
  have hcomm : cc20Commutator C K = -cc20ThreeBranchCommutator E Q R C := by
    simpa only [C, K, E, Q, R] using
      rootConvolution_targetProlateRemainder_commutator_eq_neg_threeBranch
        owner family
  change C.adjoint ∘L cc20Commutator C K =
    -(C.adjoint ∘L cc20ThreeBranchCommutator E Q R C)
  rw [hcomm]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply, map_neg, ContinuousLinearMap.neg_apply]

/-- Exact active-order decomposition.  It isolates the positive S1 square from
the root-commutator S2 remainder. -/
theorem detectorTargetProlate_eq_rightSandwich_add_rootCommutator
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily) :
    detectorOperator owner ∘L targetProlateRemainder unitSoninScale family =
      targetProlateDetectorRightSandwich owner family +
        targetProlateDetectorRootCommutatorRemainder owner family := by
  unfold targetProlateDetectorRightSandwich
    targetProlateDetectorRootCommutatorRemainder cc20Commutator
  let C : Op := CCM25Concrete.CCM24FiniteSBandTrace.rootConvolution owner
  let K : Op := targetProlateRemainder unitSoninScale family
  change ((C.adjoint ∘L C) ∘L K) =
    (C.adjoint ∘L K ∘L C) + C.adjoint ∘L (C ∘L K - K ∘L C)
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, map_sub]
  abel

/-- F1' follows from the active-order smoothing estimate S1 and the
root-commutator trace owner S2. -/
theorem targetProlateRemainderDetectorWeightedTraceLegality_of_rightSmoothing_and_rootCommutator
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily)
    (hfactor : targetProlateDetectorRightSmoothingFactorSummable owner family globalBasis)
    (hcomm : targetProlateDetectorRootCommutatorTraceLegality owner family globalBasis) :
    targetProlateRemainderDetectorWeightedTraceLegality owner family globalBasis := by
  have hright := targetProlateDetectorRightSandwich_isTraceClassAlong
    globalBasis owner family hfactor
  unfold targetProlateRemainderDetectorWeightedTraceLegality
  rw [detectorTargetProlate_eq_rightSandwich_add_rootCommutator]
  exact isTraceClassAlong_add globalBasis _ _ hright hcomm

/-!
F2. The two Fourier-compression factors `Q_S E` and `Q_0 E` are explicit
named-basis Hilbert--Schmidt contracts at the canonical unit scale.  Their
difference is the band compression change; this file consumes, rather than
produces, those contracts.
-/
noncomputable def fourierCompressionFactor
    (lambda : CCM24SoninScale) (fourierSupport : Op) : Op :=
  fourierSupport ∘L radialSupportProjection lambda

/-- Package one Fourier-compression factor `Q E` as an `A^dagger A` trace owner
once its single named-basis Hilbert--Schmidt sum is supplied.  Its trace product
is the positive overlap `E Q E`, because both `Q` and `E` are star projections. -/
noncomputable def compressionFactorPairData
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (lambda : CCM24SoninScale) (fourierSupport : Op)
    (hfactor : Summable fun i =>
      ‖fourierCompressionFactor lambda fourierSupport (globalBasis i)‖ ^ 2) :
    BasisHilbertSchmidtPairData (G := finiteSCarrier) globalBasis where
  left := fourierCompressionFactor lambda fourierSupport
  right := fourierCompressionFactor lambda fourierSupport
  left_summable_normSq := hfactor
  right_summable_normSq := hfactor

/-- The compression difference `E Q_S E - E Q_0 E` is the trace product of an
l2Sum pair carrying both Fourier-compression factors. -/
noncomputable def compressionDifferencePairData
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (hcompressionTarget : Summable fun i =>
      ‖fourierCompressionFactor lambda
          (targetFourierSupportProjection lambda family) (globalBasis i)‖ ^ 2)
    (hcompressionSource : Summable fun i =>
      ‖fourierCompressionFactor lambda
          (sourceFourierSupportProjection lambda) (globalBasis i)‖ ^ 2) :
    BasisHilbertSchmidtPairData
      (G := WithLp 2 (finiteSCarrier × finiteSCarrier)) globalBasis :=
  CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.l2Sum
    (compressionFactorPairData globalBasis lambda
      (targetFourierSupportProjection lambda family) hcompressionTarget)
    ((compressionFactorPairData globalBasis lambda
      (sourceFourierSupportProjection lambda) hcompressionSource).smulRight (-1))

/-! The detector-weighted prolate change is trace-class along any named global
basis at unit scale from F1' and the established source-side HS fact. -/
theorem detectorProlateChange_isTraceClassAlong_at_unit
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily) {ν : Type*} (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (htarget : targetProlateRemainderDetectorWeightedTraceLegality owner family globalBasis) :
    IsTraceClassAlong globalBasis
      (detectorOperator owner ∘L prolateDifference unitSoninScale family) := by
  let sdata := CCM24SourceProlateTrace.sourceProlatePairData globalBasis unitSoninScale
    (sourceProlateHilbertSchmidtFactor_unit_summable globalBasis)
  have hsandTarget : IsTraceClassAlong globalBasis
      (detectorOperator owner ∘L targetProlateRemainder unitSoninScale family) :=
    htarget
  have hsource : sdata.traceProduct = sourceProlateRemainder unitSoninScale := by
    simpa using CCM24SourceProlateTrace.sourceProlatePairData_traceProduct_eq
      globalBasis unitSoninScale _
  -- each detector-weighted single-carrier piece is trace-class along the global basis:
  -- its carrier is `finiteSCarrier`, so the sandwich's target basis IS globalBasis.
  let identity := ContinuousLinearMap.id ℂ finiteSCarrier
  have hsandSource : IsTraceClassAlong globalBasis
      (detectorOperator owner ∘L sdata.traceProduct) := by
    simpa only [identity, ContinuousLinearMap.comp_id] using
      sdata.boundedSandwich_isTraceClassAlong globalBasis
        (detectorOperator owner) identity
  rw [hsource] at hsandSource
  -- left-composition distributes over the band difference `K_S - K_0`
  have hdist : detectorOperator owner ∘L prolateDifference unitSoninScale family =
      detectorOperator owner ∘L targetProlateRemainder unitSoninScale family -
        detectorOperator owner ∘L sourceProlateRemainder unitSoninScale := by
    rw [prolateDifference]
    apply ContinuousLinearMap.ext
    intro u
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply, map_sub]
  rw [hdist]
  exact isTraceClassAlong_sub globalBasis _ _ hsandTarget hsandSource

/-- The trace product of a single-carrier Fourier-compression factor `Q ∘ E` is
the positive overlap `E Q E`: both `fourierSupport` and `radialSupportProjection`
are star projections, so `(Q E)^† (Q E) = E Q Q E = E Q E`. -/
theorem fourierCompressionFactor_adjoint_comp_self
    (lambda : CCM24SoninScale) (fourierSupport : Op)
    (hstar : IsStarProjection fourierSupport) :
    (fourierCompressionFactor lambda fourierSupport).adjoint ∘L
        fourierCompressionFactor lambda fourierSupport =
      radialSupportProjection lambda ∘L fourierSupport ∘L
        radialSupportProjection lambda := by
  unfold fourierCompressionFactor
  have hE : (radialSupportProjection lambda).adjoint =
      radialSupportProjection lambda :=
    (radialSupportProjection_isStarProjection lambda).isSelfAdjoint.adjoint_eq
  have hQ : fourierSupport.adjoint = fourierSupport :=
    hstar.isSelfAdjoint.adjoint_eq
  rw [ContinuousLinearMap.adjoint_comp, hQ, hE]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply]
  have hidem : fourierSupport (fourierSupport ((radialSupportProjection lambda) u)) =
      fourierSupport ((radialSupportProjection lambda) u) := by
    simpa only [ContinuousLinearMap.mul_apply] using
      congrArg (fun T : Op => T ((radialSupportProjection lambda) u)) hstar.isIdempotentElem
  exact congrArg (radialSupportProjection lambda) hidem

/-- The trace product of a Fourier-compression pair owner is exactly the positive
overlap `E Q E`. -/
theorem compressionFactorPairData_traceProduct_eq
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (lambda : CCM24SoninScale) (fourierSupport : Op)
    (hstar : IsStarProjection fourierSupport)
    (hfactor : Summable fun i =>
      ‖fourierCompressionFactor lambda fourierSupport (globalBasis i)‖ ^ 2) :
    (compressionFactorPairData globalBasis lambda fourierSupport hfactor).traceProduct =
      radialSupportProjection lambda ∘L fourierSupport ∘L
        radialSupportProjection lambda := by
  unfold compressionFactorPairData BasisHilbertSchmidtPairData.traceProduct
  exact fourierCompressionFactor_adjoint_comp_self lambda fourierSupport hstar

/-! F2. The detector-weighted compression change is trace-class along any named
global basis at unit scale, from the two Fourier-compression HS premises: each
single-carrier factor `Q ∘ E` has trace product `E Q E`, and a left-bounded
sandwich over it makes the detector-weighted block trace-class; their difference
inherits trace legality. -/
theorem detectorCompressionChange_isTraceClassAlong_at_unit
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily) {ν : Type*} (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (hcompressionTarget : Summable fun i =>
      ‖fourierCompressionFactor unitSoninScale
          (targetFourierSupportProjection unitSoninScale family) (globalBasis i)‖ ^ 2)
    (hcompressionSource : Summable fun i =>
      ‖fourierCompressionFactor unitSoninScale
          (sourceFourierSupportProjection unitSoninScale) (globalBasis i)‖ ^ 2) :
    IsTraceClassAlong globalBasis
      (detectorOperator owner ∘L compressionDifference unitSoninScale family) := by
  let tdata := compressionFactorPairData globalBasis unitSoninScale
      (targetFourierSupportProjection unitSoninScale family) hcompressionTarget
  let sdata := compressionFactorPairData globalBasis unitSoninScale
      (sourceFourierSupportProjection unitSoninScale) hcompressionSource
  have htarget : tdata.traceProduct =
      radialSupportProjection unitSoninScale ∘L targetFourierSupportProjection
        unitSoninScale family ∘L radialSupportProjection unitSoninScale := by
    simpa using compressionFactorPairData_traceProduct_eq globalBasis unitSoninScale
      (targetFourierSupportProjection unitSoninScale family)
        (targetFourierSupportProjection_isStarProjection unitSoninScale family) _
  have hsource : sdata.traceProduct =
      radialSupportProjection unitSoninScale ∘L sourceFourierSupportProjection
        unitSoninScale ∘L radialSupportProjection unitSoninScale := by
    simpa using compressionFactorPairData_traceProduct_eq globalBasis unitSoninScale
      (sourceFourierSupportProjection unitSoninScale)
        (sourceFourierSupportProjection_isStarProjection unitSoninScale) _
  let identity := ContinuousLinearMap.id ℂ finiteSCarrier
  have hsandTarget : IsTraceClassAlong globalBasis
      (detectorOperator owner ∘L tdata.traceProduct) := by
    simpa only [identity, ContinuousLinearMap.comp_id] using
      tdata.boundedSandwich_isTraceClassAlong globalBasis (detectorOperator owner) identity
  rw [htarget] at hsandTarget
  have hsandSource : IsTraceClassAlong globalBasis
      (detectorOperator owner ∘L sdata.traceProduct) := by
    simpa only [identity, ContinuousLinearMap.comp_id] using
      sdata.boundedSandwich_isTraceClassAlong globalBasis (detectorOperator owner) identity
  rw [hsource] at hsandSource
  have hdist : detectorOperator owner ∘L compressionDifference unitSoninScale family =
      detectorOperator owner ∘L (radialSupportProjection unitSoninScale ∘L
          targetFourierSupportProjection unitSoninScale family ∘L
            radialSupportProjection unitSoninScale) -
        detectorOperator owner ∘L (radialSupportProjection unitSoninScale ∘L
          sourceFourierSupportProjection unitSoninScale ∘L
            radialSupportProjection unitSoninScale) := by
    rw [compressionDifference]
    apply ContinuousLinearMap.ext
    intro u
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply, map_sub]
  rw [hdist]
  exact isTraceClassAlong_sub globalBasis _ _ hsandTarget hsandSource

/-!
P1 capstone.  Given F1' and the two F2 named-basis contracts, the
selected-detector response operator is trace-class along the supplied global
basis at the canonical unit scale.  This is the conditional form needed by the
Gate-2 readback premise `hresponse`.
-/
theorem projectionResponse_isTraceClassAlong_at_unit
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily) {ν : Type*} (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (hprolateTarget : targetProlateRemainderDetectorWeightedTraceLegality owner family globalBasis)
    (hcompressionTarget : Summable fun i =>
      ‖fourierCompressionFactor unitSoninScale
          (targetFourierSupportProjection unitSoninScale family) (globalBasis i)‖ ^ 2)
    (hcompressionSource : Summable fun i =>
      ‖fourierCompressionFactor unitSoninScale
          (sourceFourierSupportProjection unitSoninScale) (globalBasis i)‖ ^ 2) :
    IsTraceClassAlong globalBasis
      (projectionResponse owner unitSoninScale family) := by
  have hprolate := detectorProlateChange_isTraceClassAlong_at_unit owner family
    globalBasis hprolateTarget
  have hcompression := detectorCompressionChange_isTraceClassAlong_at_unit owner
    family globalBasis hcompressionTarget hcompressionSource
  rw [projectionResponse_eq_compression_sub_prolate]
  exact isTraceClassAlong_sub globalBasis _ _ hprolate hcompression

end

end C1ProlateResponseTraceLegalityUnitScale
end Source
end ConnesWeilRH
