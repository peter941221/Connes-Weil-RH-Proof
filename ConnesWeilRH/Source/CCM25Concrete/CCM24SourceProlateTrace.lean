/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24ReflectedCompactRoot

/-!
# Source prolate trace reduction

The source prolate remainder is the positive square of one explicit factor.
This module proves that one Hilbert--Schmidt summability theorem for that
factor supplies every remaining fixed-source trace-legality consumer, while
keeping the second-support and prolate terms coupled for later estimates.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24SourceProlateTrace

open MeasureTheory
open scoped ENNReal InnerProduct
open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open CC20Concrete.CompactConvolutionSupport
open CCM24FiniteSProjectionTrace
open CCM24FiniteSGramResponse
open CCM24RadialBoundaryPairTransport
open CCM24ReflectedCompactRoot

local notation "Op" => finiteSCarrier →L[ℂ] finiteSCarrier

/-- The source prolate square root `Q_0 (E-R_0)`. -/
noncomputable def sourceProlateHilbertSchmidtFactor
    (lambda : CCM24SoninScale) : Op :=
  sourceFourierSupportProjection lambda ∘L
    (radialSupportProjection lambda - sourceSoninProjection lambda)

/-- The actual source prolate remainder is the positive square of the named
factor. -/
theorem sourceProlateHilbertSchmidtFactor_adjoint_comp_self
    (lambda : CCM24SoninScale) :
    (sourceProlateHilbertSchmidtFactor lambda).adjoint ∘L
        sourceProlateHilbertSchmidtFactor lambda =
      sourceProlateRemainder lambda := by
  rw [sourceProlateRemainder_eq_factor]
  unfold sourceProlateHilbertSchmidtFactor
  rw [ContinuousLinearMap.adjoint_comp, map_sub]
  rw [(sourceFourierSupportProjection_isStarProjection lambda)
    |>.isSelfAdjoint.adjoint_eq]
  rw [(radialSupportProjection_isStarProjection lambda)
    |>.isSelfAdjoint.adjoint_eq]
  rw [(sourceSoninProjection_isStarProjection lambda)
    |>.isSelfAdjoint.adjoint_eq]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply]
  have hidempotent := congrArg
    (fun T : Op => T
      ((radialSupportProjection lambda - sourceSoninProjection lambda) u))
    ((sourceFourierSupportProjection_isStarProjection lambda)
      |>.isIdempotentElem)
  exact congrArg
    (radialSupportProjection lambda - sourceSoninProjection lambda)
    (by simpa only [ContinuousLinearMap.mul_apply] using hidempotent)

/-- The CC20-style positive diagonal trace of the actual prolate remainder
upgrades to Hilbert--Schmidt summability of its explicit square root.

The upgrade is valid because the preceding theorem identifies the remainder
with the exact positive square `A† A`; it does not reinterpret an arbitrary
`IsTraceClassAlong` witness as a Schatten-class certificate. -/
theorem sourceProlateHilbertSchmidtFactor_summable_of_isTraceClassAlong
    {nu : Type*} (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
    (lambda : CCM24SoninScale)
    (hremainder : PositiveTrace.IsTraceClassAlong globalBasis
      (sourceProlateRemainder lambda)) :
    Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2 := by
  apply PositiveTrace.summable_normSq_of_isTraceClassAlong_adjoint_comp_self
    globalBasis (sourceProlateHilbertSchmidtFactor lambda)
  rw [sourceProlateHilbertSchmidtFactor_adjoint_comp_self]
  exact hremainder

/-- Package the source prolate factor as an `A^dagger A` trace owner once its
single named-basis Hilbert--Schmidt sum is supplied. -/
noncomputable def sourceProlatePairData
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (lambda : CCM24SoninScale)
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := finiteSCarrier) globalBasis where
  left := sourceProlateHilbertSchmidtFactor lambda
  right := sourceProlateHilbertSchmidtFactor lambda
  left_summable_normSq := hfactor
  right_summable_normSq := hfactor

/-- The genuine prolate pair owner obtained from a positive diagonal trace
of the source remainder.  The resulting object contains two actual
Hilbert--Schmidt factors, so its downstream compactness and trace products no
longer rely on the weak diagonal witness. -/
noncomputable def sourceProlatePairDataOfTraceClassAlong
    {nu : Type*} (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
    (lambda : CCM24SoninScale)
    (hremainder : PositiveTrace.IsTraceClassAlong globalBasis
      (sourceProlateRemainder lambda)) :
    CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := finiteSCarrier) globalBasis :=
  sourceProlatePairData globalBasis lambda
    (sourceProlateHilbertSchmidtFactor_summable_of_isTraceClassAlong
      globalBasis lambda hremainder)

theorem sourceProlatePairDataOfTraceClassAlong_traceProduct_eq
    {nu : Type*} (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
    (lambda : CCM24SoninScale)
    (hremainder : PositiveTrace.IsTraceClassAlong globalBasis
      (sourceProlateRemainder lambda)) :
    PositiveTrace.BasisHilbertSchmidtPairData.traceProduct
        (sourceProlatePairDataOfTraceClassAlong globalBasis lambda
          hremainder) = sourceProlateRemainder lambda := by
  unfold sourceProlatePairDataOfTraceClassAlong sourceProlatePairData
    CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.traceProduct
  exact sourceProlateHilbertSchmidtFactor_adjoint_comp_self lambda

/-- For this exact positive square, the CC20-shaped diagonal theorem also
produces genuine compactness.  Compactness is obtained from the nuclear
rank-one expansion of the upgraded Hilbert--Schmidt pair, not from the weak
diagonal predicate by itself. -/
theorem sourceProlateRemainder_isCompactOperator_of_isTraceClassAlong
    {nu : Type*} (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
    (lambda : CCM24SoninScale)
    (hremainder : PositiveTrace.IsTraceClassAlong globalBasis
      (sourceProlateRemainder lambda)) :
    IsCompactOperator (sourceProlateRemainder lambda) := by
  have hcompact :=
    (sourceProlatePairDataOfTraceClassAlong globalBasis lambda hremainder)
      |>.traceProduct_isCompactOperator globalBasis
  rw [sourceProlatePairDataOfTraceClassAlong_traceProduct_eq globalBasis
    lambda hremainder] at hcompact
  exact hcompact

theorem sourceProlatePairData_traceProduct_eq
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (lambda : CCM24SoninScale)
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    (sourceProlatePairData globalBasis lambda hfactor).traceProduct =
      sourceProlateRemainder lambda := by
  unfold sourceProlatePairData
    CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.traceProduct
  exact sourceProlateHilbertSchmidtFactor_adjoint_comp_self lambda

/-- The prolate commutator is trace legal from the single prolate-factor
Hilbert--Schmidt theorem. -/
theorem sourceProlateCommutator_isTraceClassAlong
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    PositiveTrace.IsTraceClassAlong globalBasis
      (cc20Commutator (sourceProlateRemainder lambda)
        (detectorOperator owner)) := by
  let data := sourceProlatePairData globalBasis lambda hfactor
  let identity := ContinuousLinearMap.id ℂ finiteSCarrier
  have hright : PositiveTrace.IsTraceClassAlong globalBasis
      (data.traceProduct ∘L detectorOperator owner) := by
    simpa only [identity, ContinuousLinearMap.id_comp] using
      (data.boundedSandwich_isTraceClassAlong globalBasis identity
        (detectorOperator owner))
  have hleft : PositiveTrace.IsTraceClassAlong globalBasis
      (detectorOperator owner ∘L data.traceProduct) := by
    simpa only [identity, ContinuousLinearMap.comp_id] using
      (data.boundedSandwich_isTraceClassAlong globalBasis
        (detectorOperator owner) identity)
  rw [← sourceProlatePairData_traceProduct_eq globalBasis lambda hfactor]
  unfold cc20Commutator
  exact CC20Concrete.PositiveTrace.isTraceClassAlong_sub globalBasis _ _
    hright hleft

/-- Consumer form matching CC20's positive trace-class statement for
`K_prol`: the weak named-basis diagonal is first upgraded through the exact
positive square, then used only via the genuine Hilbert--Schmidt pair. -/
theorem sourceProlateCommutator_isTraceClassAlong_of_remainder
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    {nu : Type*} (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
    (hremainder : PositiveTrace.IsTraceClassAlong globalBasis
      (sourceProlateRemainder lambda)) :
    PositiveTrace.IsTraceClassAlong globalBasis
      (cc20Commutator (sourceProlateRemainder lambda)
        (detectorOperator owner)) := by
  exact sourceProlateCommutator_isTraceClassAlong owner lambda globalBasis
    (sourceProlateHilbertSchmidtFactor_summable_of_isTraceClassAlong
      globalBasis lambda hremainder)

/-- The compressed second-support branch inherits the reflected compact-pair
legality under both radial projections. -/
theorem sourceSecondSupportCommutatorBranch_isTraceClassAlong
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier) :
    PositiveTrace.IsTraceClassAlong globalBasis
      (cc20SecondSupportCommutatorBranch (radialSupportProjection lambda)
        (sourceFourierSupportProjection lambda) (detectorOperator owner)) := by
  let data := sourceSecondSupportCompactRootPairData owner lambda a c
    negativeBasis positiveBasis outputBasis globalBasis
  let E := radialSupportProjection lambda
  have hforward : PositiveTrace.IsTraceClassAlong globalBasis
      (E ∘L data.traceProduct ∘L E) :=
    data.boundedSandwich_isTraceClassAlong outputBasis E E
  have hreverse : PositiveTrace.IsTraceClassAlong globalBasis
      (E ∘L data.traceProduct.adjoint ∘L E) := by
    have h := data.swap.boundedSandwich_isTraceClassAlong outputBasis E E
    rw [data.swap_traceProduct_eq_adjoint] at h
    exact h
  have hsigned := CC20Concrete.PositiveTrace.isTraceClassAlong_sub
    globalBasis _ _ hreverse hforward
  have hcrossing := sourceSecondSupportCompactRootPairData_traceProduct_eq
    owner lambda a c hac hsupp negativeBasis positiveBasis outputBasis
      globalBasis
  unfold cc20SecondSupportCommutatorBranch
  rw [cc20Commutator_eq_orientedBoundaryCrossing_adjoint_sub
    (sourceFourierSupportProjection lambda) (detectorOperator owner)
    (sourceFourierSupportProjection_isStarProjection lambda).isSelfAdjoint
    (detectorOperator_isSelfAdjoint owner)]
  rw [← hcrossing]
  have heq : E ∘L (data.traceProduct.adjoint - data.traceProduct) ∘L E =
      (E ∘L data.traceProduct.adjoint ∘L E) -
        (E ∘L data.traceProduct ∘L E) := by
    apply ContinuousLinearMap.ext
    intro u
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.sub_apply, map_sub]
  rw [heq]
  exact hsigned

/-- The complete coupled second-support/prolate remainder is trace legal.
The two terms remain in one signed owner for all later estimates. -/
theorem sourceSecondSupportProlateRemainder_isTraceClassAlong
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    PositiveTrace.IsTraceClassAlong globalBasis
      (sourceSecondSupportProlateRemainder owner lambda) := by
  unfold sourceSecondSupportProlateRemainder
    cc20ProlateCommutatorBranch
  exact CC20Concrete.PositiveTrace.isTraceClassAlong_sub globalBasis _ _
    (sourceSecondSupportCommutatorBranch_isTraceClassAlong owner lambda a c
      hac hsupp negativeBasis positiveBasis outputBasis globalBasis)
    (sourceProlateCommutator_isTraceClassAlong owner lambda globalBasis
      hfactor)

/-- The coupled reflected-second-support/prolate owner is legal from the
actual CC20-shaped positive diagonal theorem for `K_prol`. -/
theorem sourceSecondSupportProlateRemainder_isTraceClassAlong_of_remainder
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ nu : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
    (hremainder : PositiveTrace.IsTraceClassAlong globalBasis
      (sourceProlateRemainder lambda)) :
    PositiveTrace.IsTraceClassAlong globalBasis
      (sourceSecondSupportProlateRemainder owner lambda) := by
  exact sourceSecondSupportProlateRemainder_isTraceClassAlong owner lambda
    a c hac hsupp negativeBasis positiveBasis outputBasis globalBasis
      (sourceProlateHilbertSchmidtFactor_summable_of_isTraceClassAlong
        globalBasis lambda hremainder)

/-- The complete fixed-source three-branch ledger is trace legal once the
single explicit prolate factor is Hilbert--Schmidt. -/
theorem sourceThreeBranchCommutator_isTraceClassAlong
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ιr κr τr ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis ιr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis κr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis τr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    PositiveTrace.IsTraceClassAlong globalBasis
      (cc20ThreeBranchCommutator (radialSupportProjection lambda)
        (sourceFourierSupportProjection lambda)
        (sourceProlateRemainder lambda) (detectorOperator owner)) := by
  apply sourceThreeBranchCommutator_isTraceClassAlong_of_remainder owner
    lambda a c hac hsupp negativeBasis positiveBasis outputBasis globalBasis
  exact sourceSecondSupportProlateRemainder_isTraceClassAlong owner lambda
    a c hac hsupp reflectedNegativeBasis reflectedPositiveBasis
      reflectedOutputBasis globalBasis hfactor

/-- Complete fixed-source legality in the premise shape supplied by CC20's
positive prolate spectral theorem.  No branch is discarded and the
second-support/prolate cancellation remains inside the same signed owner. -/
theorem sourceThreeBranchCommutator_isTraceClassAlong_of_prolateRemainder
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ιr κr τr nu : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis ιr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis κr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis τr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
    (hremainder : PositiveTrace.IsTraceClassAlong globalBasis
      (sourceProlateRemainder lambda)) :
    PositiveTrace.IsTraceClassAlong globalBasis
      (cc20ThreeBranchCommutator (radialSupportProjection lambda)
        (sourceFourierSupportProjection lambda)
        (sourceProlateRemainder lambda) (detectorOperator owner)) := by
  exact sourceThreeBranchCommutator_isTraceClassAlong owner lambda a c hac
    hsupp negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis
        (sourceProlateHilbertSchmidtFactor_summable_of_isTraceClassAlong
          globalBasis lambda hremainder)

end CCM24SourceProlateTrace
end CCM25Concrete
end Source
end ConnesWeilRH
