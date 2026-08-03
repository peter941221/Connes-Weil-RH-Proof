/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSGatePhysicalPrefixFullKernelPairing

/-!
# Real directed crossing normal form for the physical Gate prefix

The physical full-kernel scalar has two coframe orientations,

```text
Omega(J, U) - Omega(F, J),
```

where `Omega(x,y) = <x, [P,W] y>`, `P` is the source Sonin projection,
`J` is its inclusion, `U` is the endpoint cancellation residual, and `F` is
the actual forward coframe.  Since the completed commutator is skew-adjoint,
the real part has the exact one-direction form

```text
Re (Omega(J,U) - Omega(F,J)) = Re Omega(J,U+F).
```

The full outer/reflected-second-support/prolate commutator remains intact.
In particular, this is not a termwise norm bound and it does not cancel the
endpoint residual: the surviving coframe is `U + F`, not `U - F` or zero.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSGatePhysicalRealDirectedCrossing

open MeasureTheory
open scoped BigOperators InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open CC20Concrete.PositiveTrace
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSGatePhysicalPrefixBoundaryKernelPairing
open CCM24FiniteSGatePhysicalPrefixFullKernelPairing
open CCM24FiniteSGramResponse
open CCM24FiniteSPhysicalCancellationEndpointNormalForm
open CCM24FiniteSProjectionTrace
open CCM24FiniteSRawRemainderCommonPair
open CCM24FiniteSRootCompletedDetectorPhysicalDiagonal
open CCM24FiniteSRootCompletedDetectorSignedKernelResponse
open CCM24SourceProlateTrace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- The one surviving directed full-kernel scalar for the real physical Gate
prefix.  The second argument deliberately contains `U + F`; compact-root
support must act on this complete sum before any estimate is taken. -/
noncomputable def sourceGatePhysicalRealDirectedKernelScalar
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (x : sourceSoninCarrier lambda) : ℝ :=
  let Jx := sourceInclusion lambda x
  let Ux := sourceEndpointCancellationResidual lambda family x
  let Fx := sourceActualBandForwardCoframe lambda family x
  (sourceTranslatedCompactRootSignedKernelPairing owner lambda a c Jx (Ux + Fx) +
    sourceSecondSupportProlateFullKernelPairing owner lambda a c Jx (Ux + Fx)).re

/-- The ordered real prefix of the directed complete physical crossing. -/
noncomputable def sourceGatePhysicalPrefixRealDirectedKernelPairing
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (sourceBasis : HilbertBasis ℕ ℂ (sourceSoninCarrier lambda))
    (N : ℕ) : ℝ :=
  ∑ i ∈ Finset.range N,
    sourceGatePhysicalRealDirectedKernelScalar owner lambda family a c
      (sourceBasis i)

private theorem threeBranchCommutator_adjoint_eq_neg
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    (cc20ThreeBranchCommutator (radialSupportProjection lambda)
      (sourceFourierSupportProjection lambda) (sourceProlateRemainder lambda)
      (detectorOperator owner))† =
      -cc20ThreeBranchCommutator (radialSupportProjection lambda)
        (sourceFourierSupportProjection lambda) (sourceProlateRemainder lambda)
        (detectorOperator owner) := by
  rw [← sourceSoninCommutator_eq_threeBranch]
  exact cc20Commutator_adjoint_eq_neg _ _
    (sourceSoninProjection_isStarProjection lambda).isSelfAdjoint
    (detectorOperator_isSelfAdjoint owner)

private theorem fullKernelPairing_eq_inner_threeBranch
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
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    (x y : finiteSCarrier) :
    sourceTranslatedCompactRootSignedKernelPairing owner lambda a c x y +
        sourceSecondSupportProlateFullKernelPairing owner lambda a c x y =
      inner ℂ x
        (cc20ThreeBranchCommutator (radialSupportProjection lambda)
          (sourceFourierSupportProjection lambda) (sourceProlateRemainder lambda)
          (detectorOperator owner) y) := by
  calc
    sourceTranslatedCompactRootSignedKernelPairing owner lambda a c x y +
        sourceSecondSupportProlateFullKernelPairing owner lambda a c x y =
      sourceTranslatedCompactRootSignedKernelPairing owner lambda a c x y +
        inner ℂ
          ((secondSupportProlateRemainderPairData owner lambda a c hac hsupp
            reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
            globalBasis hfactor).left x)
          ((secondSupportProlateRemainderPairData owner lambda a c hac hsupp
            reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
            globalBasis hfactor).right y) := by
        rw [inner_secondSupportProlateRemainderPairData_eq_fullKernelPairing]
    _ = sourceThreeBranchPhysicalPairing owner lambda a c hac hsupp
        negativeBasis positiveBasis outputBasis reflectedNegativeBasis
        reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor x y := by
        rw [sourceThreeBranchPhysicalPairing_eq_signedKernel_add_remainder]
    _ = inner ℂ x
        (cc20ThreeBranchCommutator (radialSupportProjection lambda)
          (sourceFourierSupportProjection lambda) (sourceProlateRemainder lambda)
          (detectorOperator owner) y) :=
        sourceThreeBranchPhysicalPairing_eq_inner_threeBranchCommutator owner
          lambda a c hac hsupp negativeBasis positiveBasis outputBasis
          reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
          globalBasis hfactor x y

private theorem real_centered_pairing_eq_directed
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (K : H →L[ℂ] H) (hK : K† = -K)
    (J U F : H) :
    (inner ℂ J (K U) - inner ℂ F (K J)).re =
      (inner ℂ J (K (U + F))).re := by
  have hcross : inner ℂ J (K F) = -star (inner ℂ F (K J)) := by
    calc
      inner ℂ J (K F) = inner ℂ ((K†) J) F := by
        rw [ContinuousLinearMap.adjoint_inner_left]
      _ = inner ℂ (-(K J)) F := by
        simp only [hK, ContinuousLinearMap.neg_apply]
      _ = -inner ℂ (K J) F := by rw [inner_neg_left]
      _ = -star (inner ℂ F (K J)) := by
        rw [(inner_conj_symm (𝕜 := ℂ) (K J) F).symm]
        rfl
  rw [map_add, inner_add_right, hcross]
  simp only [Complex.sub_re, Complex.add_re, Complex.neg_re, Complex.star_def,
    Complex.conj_re]
  ring

/-- The real part of the two-orientation full-kernel scalar is exactly one
directed completed commutator crossing. -/
theorem sourceGatePhysicalFullKernelScalar_re_eq_realDirectedKernelScalar
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
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
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    (x : sourceSoninCarrier lambda) :
    (sourceGatePhysicalFullKernelScalar owner lambda family a c x).re =
      sourceGatePhysicalRealDirectedKernelScalar owner lambda family a c x := by
  let K := cc20ThreeBranchCommutator (radialSupportProjection lambda)
    (sourceFourierSupportProjection lambda) (sourceProlateRemainder lambda)
    (detectorOperator owner)
  let Jx := sourceInclusion lambda x
  let Ux := sourceEndpointCancellationResidual lambda family x
  let Fx := sourceActualBandForwardCoframe lambda family x
  have hpair (u v : finiteSCarrier) :
      sourceTranslatedCompactRootSignedKernelPairing owner lambda a c u v +
          sourceSecondSupportProlateFullKernelPairing owner lambda a c u v =
        inner ℂ u (K v) := by
    exact fullKernelPairing_eq_inner_threeBranch owner lambda a c hac hsupp
      negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor u v
  change
    ((sourceTranslatedCompactRootSignedKernelPairing owner lambda a c Jx Ux +
        sourceSecondSupportProlateFullKernelPairing owner lambda a c Jx Ux) -
      (sourceTranslatedCompactRootSignedKernelPairing owner lambda a c Fx Jx +
        sourceSecondSupportProlateFullKernelPairing owner lambda a c Fx Jx)).re =
      (sourceTranslatedCompactRootSignedKernelPairing owner lambda a c Jx (Ux + Fx) +
        sourceSecondSupportProlateFullKernelPairing owner lambda a c Jx (Ux + Fx)).re
  rw [hpair Jx Ux, hpair Fx Jx, hpair Jx (Ux + Fx)]
  exact real_centered_pairing_eq_directed K
    (threeBranchCommutator_adjoint_eq_neg owner lambda) Jx Ux Fx

/-- The real part of every ordered full-kernel prefix is the ordered prefix of
the single directed crossing. -/
theorem sourceGatePhysicalPrefixFullKernelPairing_re_eq_realDirectedKernelPairing
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
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
    (sourceBasis : HilbertBasis ℕ ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    (N : ℕ) :
    (sourceGatePhysicalPrefixFullKernelPairing owner lambda family a c
      sourceBasis N).re =
      sourceGatePhysicalPrefixRealDirectedKernelPairing owner lambda family a c
        sourceBasis N := by
  rw [sourceGatePhysicalPrefixFullKernelPairing,
    sourceGatePhysicalPrefixRealDirectedKernelPairing, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact sourceGatePhysicalFullKernelScalar_re_eq_realDirectedKernelScalar owner
    lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis globalBasis
    hfactor (sourceBasis i)

end CCM24FiniteSGatePhysicalRealDirectedCrossing
end CCM25Concrete
end Source
end ConnesWeilRH
