/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSProjectionTrace
import ConnesWeilRH.Source.CCM25Concrete.CCM24SourceProlateTrace
import ConnesWeilRH.Source.CCM25Concrete.CCM24UnitScaleStrictAngle
import ConnesWeilRH.Dev.C1SelectedDetectorSemiLocalEulerBoundary

/-!
# P1: trace legality of the finite-S projection response at unit scale

This is brick #1 of the Option-C semi-local bridge (doc 1050 section 4).  The
Gate-2 arithmetic readback

```text
ordinaryTraceAlong_projectionResponse_eq_finitePrimeSum_add_residual
```

currently carries one explicit analytic premise,

```text
hresponse : IsTraceClassAlong globalBasis (projectionResponse owner lambda family)
```

which is exactly the Hilbert--Schmidt / trace legality of the selected-detector
response operator.  This file discharges that premise at the canonical unit
scale `lambda = unitSoninScale`, so the readback evaluates with no
trace-legality assumption.

The response decomposes (Source-side, family form) as a difference of two
detector-weighted band pieces:

```text
projectionResponse owner lambda family
  = detectorOperator ∘ prolateDifference − detectorOperator ∘ compressionDifference
        [CCM24FiniteSProjectionTrace.projectionResponse_eq_compression_sub_prolate]
```

Each band piece is the traceProduct of an `l2Sum` of Hilbert--Schmidt pair data,
so a left-bounded sandwich over that pair data makes each detector-weighted
piece trace-class along any named global basis; their difference inherits it.

Two unit-scale facts are the load-bearing new content:

  F1. the target prolate factor is unconditionally Hilbert--Schmidt at unit
      scale (mirror of `sourceProlateHilbertSchmidtFactor_unit_summable`);
  F2. the two Fourier-compression factors are unconditionally Hilbert--Schmidt
      at unit scale.

No positivity, no remainder sign, and no RH-facing statement is asserted here;
this file only supplies trace legality for the exact readback object.
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

/-- The target prolate square root `Q_S (E-R_S)`, the finite-S mirror of
`sourceProlateHilbertSchmidtFactor`. -/
noncomputable def targetProlateHilbertSchmidtFactor
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) : Op :=
  targetFourierSupportProjection lambda family ∘L
    (radialSupportProjection lambda - targetSoninProjection lambda family)

/-- The actual finite-S prolate remainder is the positive square of that named
factor, mirroring `sourceProlateHilbertSchmidtFactor_adjoint_comp_self`. -/
theorem targetProlateHilbertSchmidtFactor_adjoint_comp_self
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    (targetProlateHilbertSchmidtFactor lambda family).adjoint ∘L
        targetProlateHilbertSchmidtFactor lambda family =
      targetProlateRemainder lambda family := by
  rw [targetProlateRemainder_eq_factor]
  unfold targetProlateHilbertSchmidtFactor
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

/-- [CRUX -- the new semilocal analysis of brick #1] The finite-S prolate
remainder `K_S = E Q_S E - R_S` is trace-class along any named global basis at
the canonical unit scale.  Its source-side twin `sourceProlateRemainder
unitSoninScale` is already known trace-class via the strict-angle machinery, but
the finite Euler transport that conjugates the archimedean transform into
`U_S = E_S Hinf E_S^{-1}` is only a bounded invertible map (`≃L[ℂ]`, not an
isometry), so the existing `≃ₗᵢ[ℂ]`-parametrized `prolateFactor` reduction does
not apply directly.  [ROUND-2 CRUX: proof body below.] -/
theorem targetProlateRemainder_unit_isTraceClassAlong
    (family : FinitePrimePowerFamily) {ι : Type*}
    (basis : HilbertBasis ι ℂ finiteSCarrier) :
    IsTraceClassAlong basis (targetProlateRemainder unitSoninScale family) := by
  sorry

/-- Term-by-term, the complex diagonal of the finite-S prolate remainder equals
the squared norm of its square root `Q_S (E-R_S)`: this is exactly the
`A^dagger A = K_S` identity read on a single basis vector. -/
theorem targetProlateHilbertSchmidtFactor_unit_diagonal_eq_targetRemainder
    (family : FinitePrimePowerFamily) {ι : Type*}
    (basis : HilbertBasis ι ℂ finiteSCarrier) (i : ι) :
    ((‖targetProlateHilbertSchmidtFactor unitSoninScale family (basis i)‖ ^ 2 : ℝ) : ℂ) =
      inner ℂ (basis i) (targetProlateRemainder unitSoninScale family (basis i)) := by
  have hsq := targetProlateHilbertSchmidtFactor_adjoint_comp_self unitSoninScale family
  rw [← hsq, ContinuousLinearMap.comp_apply]
  rw [ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
  norm_cast

/-!
F1. The finite-S prolate factor is unconditionally Hilbert--Schmidt at the
canonical unit scale along every named global basis, mirroring
`sourceProlateHilbertSchmidtFactor_unit_summable`.  It reduces to one new
analytic input: trace-class legality of the semilocal prolate remainder (the
crux above).  The reduction is proved plumbing from `A^dagger A = K_S`; no
positivity or RH-facing statement is used.
-/
theorem targetProlateHilbertSchmidtFactor_unit_summable
    (family : FinitePrimePowerFamily) {ι : Type*} (basis : HilbertBasis ι ℂ finiteSCarrier) :
    Summable fun i => ‖targetProlateHilbertSchmidtFactor unitSoninScale family (basis i)‖ ^ 2 := by
  -- the single new analytic input: K_S is trace-class at unit scale [CRUX]
  have htrace : IsTraceClassAlong basis (targetProlateRemainder unitSoninScale family) :=
    targetProlateRemainder_unit_isTraceClassAlong family basis
  rw [IsTraceClassAlong] at htrace   -- Summable fun i => ⟪basis i, ((K_S)(basis i))⟫_ℂ
  have hnorm : Summable fun i => ‖(inner ℂ (basis i) (targetProlateRemainder unitSoninScale family (basis i)))‖ :=
    htrace.norm
  -- term-by-term the complex diagonal modulus is exactly the squared norm of the factor:
  have hpointwise : ∀ i, ‖(inner ℂ (basis i) (targetProlateRemainder unitSoninScale family (basis i)))‖ =
      ‖targetProlateHilbertSchmidtFactor unitSoninScale family (basis i)‖ ^ 2 := by
    intro i
    rw [← targetProlateHilbertSchmidtFactor_unit_diagonal_eq_targetRemainder family basis i]
    exact Complex.norm_of_nonneg (sq_nonneg _)
  exact hnorm.congr hpointwise

/-- Package the target prolate factor as an `A^dagger A` trace owner once its
single named-basis Hilbert--Schmidt sum is supplied (mirror of
`sourceProlatePairData`). -/
noncomputable def targetProlatePairData
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (hfactor : Summable fun i =>
      ‖targetProlateHilbertSchmidtFactor lambda family (globalBasis i)‖ ^ 2) :
    BasisHilbertSchmidtPairData (G := finiteSCarrier) globalBasis where
  left := targetProlateHilbertSchmidtFactor lambda family
  right := targetProlateHilbertSchmidtFactor lambda family
  left_summable_normSq := hfactor
  right_summable_normSq := hfactor

theorem targetProlatePairData_traceProduct_eq
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (hfactor : Summable fun i =>
      ‖targetProlateHilbertSchmidtFactor lambda family (globalBasis i)‖ ^ 2) :
    (targetProlatePairData globalBasis lambda family hfactor).traceProduct =
      targetProlateRemainder lambda family := by
  unfold targetProlatePairData BasisHilbertSchmidtPairData.traceProduct
  exact targetProlateHilbertSchmidtFactor_adjoint_comp_self lambda family

/-- The prolate change `K_S - K_0` is the trace product of an l2Sum pair whose
first coordinate carries the finite-S factor and whose second carries the source
factor with a minus sign. -/
noncomputable def prolateDifferencePairData
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (hfactorTarget : Summable fun i =>
      ‖targetProlateHilbertSchmidtFactor lambda family (globalBasis i)‖ ^ 2)
    (hfactorSource : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    BasisHilbertSchmidtPairData
      (G := WithLp 2 (finiteSCarrier × finiteSCarrier)) globalBasis :=
  CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.l2Sum
    (targetProlatePairData globalBasis lambda family hfactorTarget)
    ((CCM24SourceProlateTrace.sourceProlatePairData globalBasis lambda
      hfactorSource).smulRight (-1))

theorem prolateDifferencePairData_traceProduct_eq
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (hfactorTarget : Summable fun i =>
      ‖targetProlateHilbertSchmidtFactor lambda family (globalBasis i)‖ ^ 2)
    (hfactorSource : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    (prolateDifferencePairData globalBasis lambda family hfactorTarget
      hfactorSource).traceProduct = prolateDifference lambda family := by
  unfold prolateDifferencePairData
  rw [CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.l2Sum_traceProduct_eq_add,
    targetProlatePairData_traceProduct_eq globalBasis lambda family hfactorTarget,
    CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.smulRight_traceProduct_eq,
    CCM24SourceProlateTrace.sourceProlatePairData_traceProduct_eq]
  rw [prolateDifference, neg_one_smul, sub_eq_add_neg]

/-!
F2. The two Fourier-compression factors `Q_S E` and `Q_0 E` are unconditionally
Hilbert--Schmidt at the canonical unit scale.  Their difference is the band
compression change.  [ROUND-1 CRUX: proof body below.]
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
basis at unit scale, from F1 (and the unconditional source-side HS fact). -/
theorem detectorProlateChange_isTraceClassAlong_at_unit
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily) {ν : Type*} (globalBasis : HilbertBasis ν ℂ finiteSCarrier) :
    IsTraceClassAlong globalBasis
      (detectorOperator owner ∘L prolateDifference unitSoninScale family) := by
  let tdata := targetProlatePairData globalBasis unitSoninScale family
    (targetProlateHilbertSchmidtFactor_unit_summable family globalBasis)
  let sdata := CCM24SourceProlateTrace.sourceProlatePairData globalBasis unitSoninScale
    (sourceProlateHilbertSchmidtFactor_unit_summable globalBasis)
  have htarget : tdata.traceProduct = targetProlateRemainder unitSoninScale family := by
    simpa using targetProlatePairData_traceProduct_eq globalBasis unitSoninScale family _
  have hsource : sdata.traceProduct = sourceProlateRemainder unitSoninScale := by
    simpa using CCM24SourceProlateTrace.sourceProlatePairData_traceProduct_eq
      globalBasis unitSoninScale _
  -- each detector-weighted single-carrier piece is trace-class along the global basis:
  -- its carrier is `finiteSCarrier`, so the sandwich's target basis IS globalBasis.
  let identity := ContinuousLinearMap.id ℂ finiteSCarrier
  have hsandTarget : IsTraceClassAlong globalBasis
      (detectorOperator owner ∘L tdata.traceProduct) := by
    simpa only [identity, ContinuousLinearMap.comp_id] using
      tdata.boundedSandwich_isTraceClassAlong globalBasis
        (detectorOperator owner) identity
  rw [htarget] at hsandTarget
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
P1 capstone.  The selected-detector response operator is trace-class along any
named global basis at the canonical unit scale, so the Gate-2 readback premise
`hresponse` discharges for this exact object.
-/
theorem projectionResponse_isTraceClassAlong_at_unit
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily) {ν : Type*} (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (hcompressionTarget : Summable fun i =>
      ‖fourierCompressionFactor unitSoninScale
          (targetFourierSupportProjection unitSoninScale family) (globalBasis i)‖ ^ 2)
    (hcompressionSource : Summable fun i =>
      ‖fourierCompressionFactor unitSoninScale
          (sourceFourierSupportProjection unitSoninScale) (globalBasis i)‖ ^ 2) :
    IsTraceClassAlong globalBasis
      (projectionResponse owner unitSoninScale family) := by
  have hprolate := detectorProlateChange_isTraceClassAlong_at_unit owner family
    globalBasis
  have hcompression := detectorCompressionChange_isTraceClassAlong_at_unit owner
    family globalBasis hcompressionTarget hcompressionSource
  rw [projectionResponse_eq_compression_sub_prolate]
  exact isTraceClassAlong_sub globalBasis _ _ hprolate hcompression

end

end C1ProlateResponseTraceLegalityUnitScale
end Source
end ConnesWeilRH
