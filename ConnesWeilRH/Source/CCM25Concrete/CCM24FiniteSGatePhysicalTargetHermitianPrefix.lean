/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSGatePhysicalPrefixCompression
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSGatePhysicalRealTraceHandoff

/-!
# Hermitian ordered prefixes for the physical target response

The physical target response is `T_S = L_S^dagger W J`.  Its real diagonal
readout belongs to the actual Hermitian crossing

`H_S = (L_S^dagger W J + J^dagger W L_S) / 2`.

For one natural source Hilbert basis, the finite `Fin N` compression trace of
`H_S` is exactly the ordered prefix of the real parts of the same complete
outer/reflected-second-support/prolate kernel scalar used by Proof 746.

This creates the real target-prefix owner required by a support-first uniform
estimate.  It does not prove such an estimate, does not bound any physical
branch separately, and does not close Gate 3U, the finite-S sign, or RH.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSGatePhysicalTargetHermitianPrefix

open MeasureTheory
open scoped BigOperators InnerProduct InnerProductSpace Matrix

open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open CC20Concrete.PositiveTrace
open CCM24FiniteSActualBandJetOrientation
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSGramResponse
open CCM24FiniteSGramOrderingBridge
open CCM24FiniteSPhysicalLeakage
open CCM24FiniteSGatePhysicalObliqueShearKernelReduction
open CCM24FiniteSGatePhysicalRealTraceHandoff
open CCM24FiniteSGatePhysicalTargetCommutatorReduction
open CCM24FiniteSMovingBandPrefixCompression
open CCM24FiniteSProjectionTrace
open CCM24SourceProlateTrace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

private theorem half_mul_add_star_eq_re (z : ℂ) :
    (1 / 2 : ℂ) * (z + star z) = (z.re : ℂ) := by
  rw [Complex.star_def]
  apply Complex.ext
  · norm_num [Complex.mul_re]
    ring
  · norm_num [Complex.mul_im]

private theorem half_smul_add_adjoint_isSelfAdjoint
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (operator : H →L[ℂ] H) :
    IsSelfAdjoint ((1 / 2 : ℂ) • (operator + operator†)) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  have hhalfCast : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by
    norm_num
  have hhalf : (starRingEnd ℂ) (1 / 2 : ℂ) = (1 / 2 : ℂ) := by
    rw [hhalfCast, starRingEnd_apply, Complex.star_def, Complex.conj_ofReal]
  rw [ContinuousLinearMap.adjoint.map_smulₛₗ,
    ContinuousLinearMap.adjoint.map_add, hhalf,
    ContinuousLinearMap.adjoint_adjoint, add_comm]

/-- The Hermitian part of the actual target-commutator response. -/
noncomputable def finiteEulerTargetHermitianResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
  (1 / 2 : ℂ) •
    (finiteEulerTargetCommutatorResponse owner lambda family +
      (finiteEulerTargetCommutatorResponse owner lambda family)†)

/-- The same Hermitian response in its physical coframe orientation.  Both
directions of the crossing remain inside one operator. -/
noncomputable def finiteEulerPhysicalCoframeHermitianResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
  (1 / 2 : ℂ) •
    ((sourcePhysicalCoframeLeakage lambda family)† ∘L
        detectorOperator owner ∘L sourceInclusion lambda +
      (sourceInclusion lambda)† ∘L detectorOperator owner ∘L
        sourcePhysicalCoframeLeakage lambda family)

/-- The target Hermitian part is exactly the bidirectional physical coframe
crossing. -/
theorem finiteEulerTargetHermitianResponse_eq_physicalCoframeHermitian
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteEulerTargetHermitianResponse owner lambda family =
      finiteEulerPhysicalCoframeHermitianResponse owner lambda family := by
  rw [finiteEulerTargetHermitianResponse,
    finiteEulerPhysicalCoframeHermitianResponse,
    finiteEulerTargetCommutatorResponse_eq_physicalCoframeLeakage]
  unfold finiteEulerPhysicalCoframeLeakageResponse
  simp only [ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
    (detectorOperator_isSelfAdjoint owner).adjoint_eq,
    ContinuousLinearMap.comp_assoc]

/-- The physical target response has a self-adjoint real owner. -/
theorem finiteEulerTargetHermitianResponse_isSelfAdjoint
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    IsSelfAdjoint (finiteEulerTargetHermitianResponse owner lambda family) := by
  unfold finiteEulerTargetHermitianResponse
  exact half_smul_add_adjoint_isSelfAdjoint _

/-- Each Hermitian target diagonal is the real part of the target diagonal. -/
theorem inner_targetHermitianResponse_eq_target_re
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (x : sourceSoninCarrier lambda) :
    inner ℂ x (finiteEulerTargetHermitianResponse owner lambda family x) =
      ((inner ℂ x (finiteEulerTargetCommutatorResponse owner lambda family x)).re : ℂ) := by
  rw [finiteEulerTargetHermitianResponse]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    inner_smul_right, inner_add_right]
  rw [ContinuousLinearMap.adjoint_inner_right]
  have hstar :
      inner ℂ (finiteEulerTargetCommutatorResponse owner lambda family x) x =
        star (inner ℂ x
          (finiteEulerTargetCommutatorResponse owner lambda family x)) :=
    (inner_conj_symm (𝕜 := ℂ)
      (finiteEulerTargetCommutatorResponse owner lambda family x) x).symm
  rw [hstar]
  exact half_mul_add_star_eq_re _

/-- Fixed-family trace legality passes from the target response to its
Hermitian part. -/
theorem finiteEulerTargetHermitianResponse_isTraceClassAlong
    {rho : Type*} (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (htrace : IsTraceClassAlong sourceBasis
      (finiteEulerTargetCommutatorResponse owner lambda family)) :
    IsTraceClassAlong sourceBasis
      (finiteEulerTargetHermitianResponse owner lambda family) := by
  rw [finiteEulerTargetHermitianResponse]
  exact isTraceClassAlong_smul sourceBasis _ _
    (isTraceClassAlong_add sourceBasis _ _ htrace
      (isTraceClassAlong_adjoint sourceBasis _ htrace))

/-- Taking the ordinary trace of the Hermitian target response takes exactly
the real part of the original target trace. -/
theorem ordinaryTraceAlong_targetHermitianResponse_eq_target_re
    {rho : Type*} (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (htrace : IsTraceClassAlong sourceBasis
      (finiteEulerTargetCommutatorResponse owner lambda family)) :
    ordinaryTraceAlong sourceBasis
        (finiteEulerTargetHermitianResponse owner lambda family) =
      ((ordinaryTraceAlong sourceBasis
        (finiteEulerTargetCommutatorResponse owner lambda family)).re : ℂ) := by
  have hadjoint := isTraceClassAlong_adjoint sourceBasis
    (finiteEulerTargetCommutatorResponse owner lambda family) htrace
  rw [finiteEulerTargetHermitianResponse]
  rw [ordinaryTraceAlong_smul sourceBasis _ _
    (isTraceClassAlong_add sourceBasis _ _ htrace hadjoint)]
  rw [ordinaryTraceAlong_add sourceBasis _ _ htrace hadjoint,
    ordinaryTraceAlong_adjoint]
  simpa only [smul_eq_mul] using half_mul_add_star_eq_re
    (ordinaryTraceAlong sourceBasis
      (finiteEulerTargetCommutatorResponse owner lambda family))

/-- The literal `Fin N` compression trace of the Hermitian target response. -/
noncomputable def sourceTargetHermitianPrefixCompressionTrace
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (sourceBasis : HilbertBasis ℕ ℂ (sourceSoninCarrier lambda))
    (N : ℕ) : ℂ :=
  Matrix.trace (basisPrefixMatrix sourceBasis N
    (finiteEulerTargetHermitianResponse owner lambda family))

/-- The ordered real full-kernel prefix.  The branches remain combined in each
summand before its real part is taken. -/
noncomputable def sourceTargetHermitianFullKernelRePrefix
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (sourceBasis : HilbertBasis ℕ ℂ (sourceSoninCarrier lambda))
    (N : ℕ) : ℂ :=
  ∑ i ∈ Finset.range N,
    ((sourceObliqueShearPhysicalFullKernelScalar owner lambda family a c
      (sourceBasis i)).re : ℂ)

/-- The physical Hermitian prefix is exactly the ordered real prefix of the
same complete full-kernel scalar. -/
theorem sourceTargetHermitianPrefixCompressionTrace_eq_fullKernelRePrefix
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {iota kappa tau iotaR kappaR tauR nu : Type*}
    (negativeBasis : HilbertBasis iota ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis kappa ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis tau ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis iotaR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis kappaR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis tauR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ℕ ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    (N : ℕ) :
    sourceTargetHermitianPrefixCompressionTrace owner lambda family sourceBasis N =
      sourceTargetHermitianFullKernelRePrefix owner lambda family a c sourceBasis N := by
  rw [sourceTargetHermitianPrefixCompressionTrace,
    trace_basisPrefixMatrix_eq_rangeDiagonal,
    sourceTargetHermitianFullKernelRePrefix]
  apply Finset.sum_congr rfl
  intro i _
  rw [inner_targetHermitianResponse_eq_target_re]
  rw [inner_targetCommutatorResponse_eq_obliqueShearFullKernelScalar owner
    lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis hfactor]

/-- A uniform bound for all ordered Hermitian target prefixes passes to the
ordinary Hermitian target trace without requiring an arbitrary-finset bound. -/
theorem norm_ordinaryTraceAlong_targetHermitianResponse_le_of_prefixBound
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (sourceBasis : HilbertBasis ℕ ℂ (sourceSoninCarrier lambda))
    (bound : ℝ)
    (htrace : IsTraceClassAlong sourceBasis
      (finiteEulerTargetCommutatorResponse owner lambda family))
    (hbound : ∀ N : ℕ,
      ‖sourceTargetHermitianPrefixCompressionTrace
        owner lambda family sourceBasis N‖ ≤ bound) :
    ‖ordinaryTraceAlong sourceBasis
      (finiteEulerTargetHermitianResponse owner lambda family)‖ ≤ bound := by
  have hhermitian := finiteEulerTargetHermitianResponse_isTraceClassAlong
    owner lambda family sourceBasis htrace
  rw [IsTraceClassAlong] at hhermitian
  rw [ordinaryTraceAlong]
  exact le_of_tendsto'
    (continuous_norm.continuousAt.tendsto.comp hhermitian.hasSum.tendsto_sum_nat)
    (by
      intro N
      change ‖∑ i ∈ Finset.range N,
        inner ℂ (sourceBasis i)
          (finiteEulerTargetHermitianResponse owner lambda family
            (sourceBasis i))‖ ≤ bound
      simpa only [sourceTargetHermitianPrefixCompressionTrace,
        trace_basisPrefixMatrix_eq_rangeDiagonal] using hbound N)

/-- The norm of the real full-kernel prefix is the absolute value of its
literal real scalar sum. -/
theorem norm_sourceTargetHermitianFullKernelRePrefix_eq_abs
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (sourceBasis : HilbertBasis ℕ ℂ (sourceSoninCarrier lambda))
    (N : ℕ) :
    ‖sourceTargetHermitianFullKernelRePrefix owner lambda family a c
      sourceBasis N‖ =
      |∑ i ∈ Finset.range N,
        (sourceObliqueShearPhysicalFullKernelScalar owner lambda family a c
          (sourceBasis i)).re| := by
  rw [sourceTargetHermitianFullKernelRePrefix, ← Complex.ofReal_sum]
  simp only [Complex.norm_real, Real.norm_eq_abs]

/-- The Hermitian target trace is the absolute real part of the complete
full-kernel trace. -/
theorem norm_ordinaryTraceAlong_targetHermitianResponse_eq_abs_fullKernel_re
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {iota kappa tau iotaR kappaR tauR nu : Type*}
    (negativeBasis : HilbertBasis iota ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis kappa ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis tau ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis iotaR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis kappaR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis tauR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ℕ ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    (htrace : IsTraceClassAlong sourceBasis
      (finiteEulerTargetCommutatorResponse owner lambda family)) :
    ‖ordinaryTraceAlong sourceBasis
      (finiteEulerTargetHermitianResponse owner lambda family)‖ =
      |(finiteEulerObliqueShearFullKernelTrace owner lambda family a c
        sourceBasis).re| := by
  rw [ordinaryTraceAlong_targetHermitianResponse_eq_target_re owner lambda
    family sourceBasis htrace]
  rw [ordinaryTraceAlong_targetCommutator_eq_obliqueShearFullKernelTrace
    owner lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis sourceBasis hfactor]
  simp only [Complex.norm_real, Real.norm_eq_abs]

/-- An ordered bound on the complete Hermitian target prefixes bounds the real
full-kernel trace.  No all-finsets or branchwise estimate is introduced. -/
theorem abs_fullKernel_re_le_of_targetHermitianPrefixBound
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {iota kappa tau iotaR kappaR tauR nu : Type*}
    (negativeBasis : HilbertBasis iota ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis kappa ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis tau ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis iotaR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis kappaR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis tauR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ℕ ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    (bound : ℝ)
    (htrace : IsTraceClassAlong sourceBasis
      (finiteEulerTargetCommutatorResponse owner lambda family))
    (hbound : ∀ N : ℕ,
      ‖sourceTargetHermitianPrefixCompressionTrace
        owner lambda family sourceBasis N‖ ≤ bound) :
    |(finiteEulerObliqueShearFullKernelTrace owner lambda family a c
      sourceBasis).re| ≤ bound := by
  rw [← norm_ordinaryTraceAlong_targetHermitianResponse_eq_abs_fullKernel_re
    owner lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis sourceBasis hfactor htrace]
  exact norm_ordinaryTraceAlong_targetHermitianResponse_le_of_prefixBound
    owner lambda family sourceBasis bound htrace hbound

/-- The same handoff stated directly as the intended real scalar inequality.
Compact-root support must establish this bound before any absolute value is
taken over the physical branches. -/
theorem abs_fullKernel_re_le_of_realFullKernelPrefixBound
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {iota kappa tau iotaR kappaR tauR nu : Type*}
    (negativeBasis : HilbertBasis iota ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis kappa ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis tau ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis iotaR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis kappaR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis tauR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ℕ ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    (bound : ℝ)
    (htrace : IsTraceClassAlong sourceBasis
      (finiteEulerTargetCommutatorResponse owner lambda family))
    (hbound : ∀ N : ℕ,
      |∑ i ∈ Finset.range N,
        (sourceObliqueShearPhysicalFullKernelScalar owner lambda family a c
          (sourceBasis i)).re| ≤ bound) :
    |(finiteEulerObliqueShearFullKernelTrace owner lambda family a c
      sourceBasis).re| ≤ bound := by
  apply abs_fullKernel_re_le_of_targetHermitianPrefixBound owner lambda family
    a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis sourceBasis hfactor bound htrace
  intro N
  rw [sourceTargetHermitianPrefixCompressionTrace_eq_fullKernelRePrefix owner
    lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis sourceBasis hfactor N]
  rw [norm_sourceTargetHermitianFullKernelRePrefix_eq_abs]
  exact hbound N

end CCM24FiniteSGatePhysicalTargetHermitianPrefix
end CCM25Concrete
end Source
end ConnesWeilRH
