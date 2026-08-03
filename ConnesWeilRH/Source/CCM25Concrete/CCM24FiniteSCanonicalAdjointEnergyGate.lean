/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCanonicalRealGate
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCombinedPhysicalEnergyGate

/-!
# Adjoint completed-kernel energy handoff

The direct completed-kernel pair of Proof 758 places the finite-Euler
coframe leakage in the left physical leg.  Taking the adjoint of the target
and using the skew-adjoint completed boundary instead gives the exact pair

```text
left  = completedLeft  o sourceInclusion,
right = completedRight o sourcePhysicalCoframeLeakage.
```

This is the orientation compatible with a future completed-Julia synthesis
or compact-support-first estimate of the leakage leg.  The fixed left energy
is already bounded by `fixedPhysicalEnergyMajorant`; the right leakage energy
is the only producer obligation retained by this module.

No estimate of that right energy is assumed implicitly.  In particular, this
module proves a Gate 3U handoff, not Gate 3U itself, a finite-S sign theorem,
Burnol's identity, or RH.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCanonicalAdjointEnergyGate

open MeasureTheory
open scoped BigOperators InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open CC20Concrete.PositiveTrace
open CCM24FiniteSCanonicalRealGate
open CCM24FiniteSCombinedPhysicalEnergyGate
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSFixedPhysicalEnergyBound
open CCM24FiniteSFixedQuotientContractionBound
open CCM24FiniteSGatePhysicalCanonicalCompletedKernelTraceLegality
open CCM24FiniteSGatePhysicalCompletedKernelBridge
open CCM24FiniteSGatePhysicalNormalizedAnomalyBoundaryReadout
open CCM24FiniteSGatePhysicalObliqueShearKernelReduction
open CCM24FiniteSGramOrderingBridge
open CCM24FiniteSGramResponse
open CCM24FiniteSPhysicalLeakage
open CCM24FiniteSProjectionTrace
open CCM24FiniteSRootCompletedDetectorCompletedKernelOperator
open CCM24SourceProlateTrace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

private theorem adjoint_neg_eq_neg_adjoint
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (operator : H →L[ℂ] H) :
    (-operator)† = -(operator†) := by
  apply ContinuousLinearMap.ext
  intro u
  exact ext_inner_right ℂ fun v => by
    simp only [ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearMap.neg_apply, inner_neg_left, inner_neg_right]

/-! ## The adjoint target pair -/

/-- The completed physical owner of the adjoint canonical target.  The
finite-family-dependent leakage is kept in the complete right leg, while the
left leg contains only the fixed source inclusion. -/
noncomputable def finiteEulerCompletedKernelAdjointTargetPairData
    {rho : Type*} (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {iota kappa tau iotaR kappaR tauR nu mu : Type*}
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
    (boundaryBasis : HilbertBasis mu ℂ (commonBoundaryCarrier a c))
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    BasisHilbertSchmidtPairData
      (G := commonBoundaryCarrier a c) sourceBasis :=
  BasisHilbertSchmidtPairData.boundedPrecomp boundaryBasis sourceBasis
    (sourceThreeBranchPairData owner lambda a c hac hsupp negativeBasis
      positiveBasis outputBasis reflectedNegativeBasis reflectedPositiveBasis
      reflectedOutputBasis globalBasis hfactor)
    (sourceInclusion lambda) (sourcePhysicalCoframeLeakage lambda family)

/-- The new pair owns the Hilbert adjoint of the literal target.  This uses
the genuine skew-adjoint source boundary; no trace cycle or branchwise
rearrangement is involved. -/
theorem finiteEulerCompletedKernelAdjointTargetPairData_traceProduct_eq
    {rho : Type*} (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {iota kappa tau iotaR kappaR tauR nu mu : Type*}
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
    (boundaryBasis : HilbertBasis mu ℂ (commonBoundaryCarrier a c))
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    (finiteEulerCompletedKernelAdjointTargetPairData owner lambda family
      a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis sourceBasis hfactor).traceProduct =
      (finiteEulerTargetCommutatorResponse owner lambda family)† := by
  let kernel := sourceCompletedSignedKernelBoundaryOperator owner lambda
    a c hac hsupp reflectedNegativeBasis reflectedPositiveBasis
    reflectedOutputBasis globalBasis hfactor
  have hboundary : sourceBoundaryCommutator owner lambda = -kernel := by
    dsimp only [kernel]
    exact sourceBoundaryCommutator_eq_neg_completedKernelBoundaryOperator owner
      lambda a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis hfactor
  have hkernel : kernel† = -kernel := by
    have hkernel_eq : kernel = -sourceBoundaryCommutator owner lambda := by
      have hneg := congrArg Neg.neg hboundary
      simpa only [neg_neg] using hneg.symm
    rw [hkernel_eq, adjoint_neg_eq_neg_adjoint,
      sourceBoundaryCommutator_adjoint_eq_neg]
  rw [finiteEulerCompletedKernelAdjointTargetPairData,
    BasisHilbertSchmidtPairData.boundedPrecomp_traceProduct_eq,
    sourceThreeBranchPairData_traceProduct_eq_completedKernelOperator owner
      lambda a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis hfactor,
    finiteEulerTargetCommutatorResponse_eq_completedKernelLeakageResponse owner
      lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis hfactor]
  unfold finiteEulerCompletedKernelLeakageResponse
  rw [adjoint_neg_eq_neg_adjoint,
    ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint]
  change (sourceInclusion lambda)† ∘L kernel ∘L
      sourcePhysicalCoframeLeakage lambda family =
    -((sourceInclusion lambda)† ∘L kernel† ∘L
      sourcePhysicalCoframeLeakage lambda family)
  rw [hkernel]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply,
    map_neg, neg_neg]

/-! ## The one remaining square energy -/

/-- Square energy of the complete root-smoothed physical leakage leg.  The
three physical branches remain packed in `sourceThreeBranchPairData.right`
and the complete finite-Euler leakage acts before the norm. -/
noncomputable def sourcePhysicalCoframeCompletedKernelRightEnergy
    {rho : Type*} (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
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
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) : ℝ :=
  ∑' i, ‖(sourceThreeBranchPairData owner lambda a c hac hsupp
      negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor).right
      (sourcePhysicalCoframeLeakage lambda family (sourceBasis i))‖ ^ 2

/-- The adjoint pair's right energy is definitionally the complete smoothed
leakage energy. -/
theorem finiteEulerCompletedKernelAdjointTargetPairData_right_energy_eq
    {rho : Type*} (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {iota kappa tau iotaR kappaR tauR nu mu : Type*}
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
    (boundaryBasis : HilbertBasis mu ℂ (commonBoundaryCarrier a c))
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    (∑' i, ‖(finiteEulerCompletedKernelAdjointTargetPairData owner lambda
      family a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis sourceBasis hfactor).right
      (sourceBasis i)‖ ^ 2) =
      sourcePhysicalCoframeCompletedKernelRightEnergy owner lambda family
        a c hac hsupp negativeBasis positiveBasis outputBasis
        reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
        globalBasis sourceBasis hfactor := by
  rfl

/-- The adjoint pair's fixed inclusion leg already has the standard physical
energy majorant, independently of the finite Euler family. -/
theorem finiteEulerCompletedKernelAdjointTargetPairData_left_energy_le
    {rho : Type*} (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {iota kappa tau iotaR kappaR tauR nu mu : Type*}
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
    (boundaryBasis : HilbertBasis mu ℂ (commonBoundaryCarrier a c))
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    (∑' i, ‖(finiteEulerCompletedKernelAdjointTargetPairData owner lambda
      family a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis sourceBasis hfactor).left
      (sourceBasis i)‖ ^ 2) ≤
      fixedPhysicalEnergyMajorant owner lambda a c globalBasis := by
  let base := sourceThreeBranchPairData owner lambda a c hac hsupp
    negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor
  have hJ : ‖sourceInclusion lambda‖ ≤ 1 := Submodule.norm_subtypeL_le _
  have hpre := boundedPrecomp_left_tsum_le_of_norm_le_one boundaryBasis
    sourceBasis base (sourceInclusion lambda)
      (sourcePhysicalCoframeLeakage lambda family) hJ
  have hbase := sourceThreeBranchPairData_left_basisEnergy_le_fixedMajorant
    owner lambda a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis hfactor
  simpa only [finiteEulerCompletedKernelAdjointTargetPairData, base] using
    hpre.trans hbase

/-! ## Gate handoff -/

/-- A fixed-majorant bound for the one complete leakage energy closes the
real target bound for that family.  This is one Hilbert--Schmidt
Cauchy--Schwarz operation on the already completed pair. -/
theorem abs_re_ordinaryTraceAlong_targetCommutator_le_of_rightEnergy
    {rho : Type*} (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {iota kappa tau iotaR kappaR tauR nu mu : Type*}
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
    (boundaryBasis : HilbertBasis mu ℂ (commonBoundaryCarrier a c))
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    (hright : sourcePhysicalCoframeCompletedKernelRightEnergy owner lambda
      family a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis sourceBasis hfactor ≤
        fixedPhysicalEnergyMajorant owner lambda a c globalBasis) :
    |(ordinaryTraceAlong sourceBasis
      (finiteEulerTargetCommutatorResponse owner lambda family)).re| ≤
        fixedPhysicalEnergyMajorant owner lambda a c globalBasis := by
  let pair := finiteEulerCompletedKernelAdjointTargetPairData owner lambda
    family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis sourceBasis hfactor
  let majorant := fixedPhysicalEnergyMajorant owner lambda a c globalBasis
  have hleft : (∑' i, ‖pair.left (sourceBasis i)‖ ^ 2) ≤ majorant := by
    dsimp only [pair, majorant]
    exact finiteEulerCompletedKernelAdjointTargetPairData_left_energy_le
      owner lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis sourceBasis hfactor
  have hright' : (∑' i, ‖pair.right (sourceBasis i)‖ ^ 2) ≤ majorant := by
    rw [show (∑' i, ‖pair.right (sourceBasis i)‖ ^ 2) =
        sourcePhysicalCoframeCompletedKernelRightEnergy owner lambda family
          a c hac hsupp negativeBasis positiveBasis outputBasis
          reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
          globalBasis sourceBasis hfactor by
      dsimp only [pair]
      exact finiteEulerCompletedKernelAdjointTargetPairData_right_energy_eq
        owner lambda family a c hac hsupp negativeBasis positiveBasis
        outputBasis reflectedNegativeBasis reflectedPositiveBasis
        reflectedOutputBasis globalBasis boundaryBasis sourceBasis hfactor]
    exact hright
  have hmajorant : 0 ≤ majorant := by
    dsimp only [majorant, fixedPhysicalEnergyMajorant]
    positivity
  have htrace := ordinaryTraceAlong_traceProduct_norm_le_of_energy_bounds
    sourceBasis pair majorant majorant hleft hright' hmajorant hmajorant
  rw [show pair.traceProduct =
      (finiteEulerTargetCommutatorResponse owner lambda family)† by
    dsimp only [pair]
    exact finiteEulerCompletedKernelAdjointTargetPairData_traceProduct_eq
      owner lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis sourceBasis hfactor,
    ordinaryTraceAlong_adjoint, norm_star] at htrace
  calc
    |(ordinaryTraceAlong sourceBasis
        (finiteEulerTargetCommutatorResponse owner lambda family)).re| ≤
        (majorant + majorant) / 2 :=
      (Complex.abs_re_le_norm
        (ordinaryTraceAlong sourceBasis
          (finiteEulerTargetCommutatorResponse owner lambda family))).trans htrace
    _ = majorant := by ring

/-- Canonical-family specialization of the adjoint energy handoff.  The
displayed right-energy premise is the remaining analytic producer, not a
field hidden inside `canonicalRealGate3UAt`. -/
theorem canonicalRealGate3UAt_of_completedKernelRightEnergy
    {rho : Type*} (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {iota kappa tau iotaR kappaR tauR nu mu : Type*}
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
    (boundaryBasis : HilbertBasis mu ℂ (commonBoundaryCarrier a c))
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    (hright : sourcePhysicalCoframeCompletedKernelRightEnergy owner lambda
      (CCM24FiniteSCanonicalCompletedResponse.canonicalFamily owner)
      a c hac hsupp negativeBasis positiveBasis
      outputBasis reflectedNegativeBasis reflectedPositiveBasis
      reflectedOutputBasis globalBasis sourceBasis hfactor ≤
        fixedPhysicalEnergyMajorant owner lambda a c globalBasis) :
    canonicalRealGate3UAt owner lambda sourceBasis
      (fixedPhysicalEnergyMajorant owner lambda a c globalBasis) := by
  exact abs_re_ordinaryTraceAlong_targetCommutator_le_of_rightEnergy owner
    lambda (CCM24FiniteSCanonicalCompletedResponse.canonicalFamily owner)
    a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis sourceBasis hfactor hright

end CCM24FiniteSCanonicalAdjointEnergyGate
end CCM25Concrete
end Source
end ConnesWeilRH
