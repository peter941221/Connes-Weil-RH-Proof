/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSGatePhysicalNormalizedGradedCoboundary
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSMovingBandSelfAdjointTrace

/-!
# Trace readout of the normalized Gram-order anomaly

Proof 748 splits the target response into a symmetric normalized boundary and
an ordered Gram-similarity anomaly.  This module gives the two summands genuine
fixed-family trace-ideal owners by recovering the normalized right boundary
numerator from the completed four-branch Hilbert--Schmidt pair.

The resulting legal cycle does not erase the anomaly.  Its ordinary trace is
exactly half the difference between the right-ordered source-band trace and
its complex conjugate.  It vanishes precisely when that source trace is real.
The self-adjoint ambient endpoint would imply this reality only after a
source/ambient ordinary-trace identity is supplied; the existing finite-prefix
cycles do not provide that limiting identity.

No Gate 3U estimate, finite-S sign, Burnol identity, or RH premise is asserted.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSGatePhysicalNormalizedAnomalyTrace

open MeasureTheory
open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.PositiveTrace
open CCM24FiniteSActualBandQuadraticCycle
open CCM24FiniteSBandTrace
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSGatePhysicalNormalizedDoubleBoundaryReduction
open CCM24FiniteSGatePhysicalNormalizedGradedCoboundary
open CCM24FiniteSGramOrderingBridge
open CCM24FiniteSGramResponse
open CCM24FiniteSMovingBandSelfAdjointTrace
open CCM24FiniteSProjectionTrace
open CCM24SourceProlateTrace
open CC20Concrete.CompactRootHalfLinePair

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

private theorem ordinaryTraceAlong_left_comp_traceProduct_eq_right_comp
    {H G iota kappa : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (sourceBasis : HilbertBasis iota ℂ H)
    (targetBasis : HilbertBasis kappa ℂ G)
    (data : BasisHilbertSchmidtPairData (G := G) sourceBasis)
    (bounded : H →L[ℂ] H) :
    ordinaryTraceAlong sourceBasis (bounded ∘L data.traceProduct) =
      ordinaryTraceAlong sourceBasis (data.traceProduct ∘L bounded) := by
  let leftPair := data.boundedSandwich targetBasis bounded
    (ContinuousLinearMap.id ℂ H)
  let rightPair := data.boundedSandwich targetBasis
    (ContinuousLinearMap.id ℂ H) bounded
  have hleftProduct : leftPair.traceProduct =
      bounded ∘L data.traceProduct := by
    dsimp only [leftPair]
    rw [BasisHilbertSchmidtPairData.boundedSandwich_traceProduct_eq]
    apply ContinuousLinearMap.ext
    intro u
    rfl
  have hrightProduct : rightPair.traceProduct =
      data.traceProduct ∘L bounded := by
    dsimp only [rightPair]
    rw [BasisHilbertSchmidtPairData.boundedSandwich_traceProduct_eq]
    apply ContinuousLinearMap.ext
    intro u
    rfl
  have htarget :
      leftPair.right ∘L leftPair.left† =
        rightPair.right ∘L rightPair.left† := by
    apply ContinuousLinearMap.ext
    intro u
    simp only [leftPair, rightPair,
      BasisHilbertSchmidtPairData.boundedSandwich,
      ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint,
      ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply]
  calc
    ordinaryTraceAlong sourceBasis (bounded ∘L data.traceProduct) =
        ordinaryTraceAlong sourceBasis leftPair.traceProduct := by
      rw [hleftProduct]
    _ = ordinaryTraceAlong targetBasis
        (leftPair.right ∘L leftPair.left†) :=
      leftPair.ordinaryTraceAlong_traceProduct_eq_cyclic targetBasis
    _ = ordinaryTraceAlong targetBasis
        (rightPair.right ∘L rightPair.left†) := by rw [htarget]
    _ = ordinaryTraceAlong sourceBasis rightPair.traceProduct :=
      (rightPair.ordinaryTraceAlong_traceProduct_eq_cyclic targetBasis).symm
    _ = ordinaryTraceAlong sourceBasis
        (data.traceProduct ∘L bounded) := by rw [hrightProduct]

private theorem left_comp_traceProduct_isTraceClassAlong
    {H G iota kappa : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (sourceBasis : HilbertBasis iota ℂ H)
    (targetBasis : HilbertBasis kappa ℂ G)
    (data : BasisHilbertSchmidtPairData (G := G) sourceBasis)
    (bounded : H →L[ℂ] H) :
    IsTraceClassAlong sourceBasis (bounded ∘L data.traceProduct) := by
  have hclass := data.boundedSandwich_isTraceClassAlong targetBasis bounded
    (ContinuousLinearMap.id ℂ H)
  simpa only [ContinuousLinearMap.comp_id] using hclass

/-- Multiplying the route right-ordered response by the normalized Gram
recovers the negative normalized right boundary numerator. -/
theorem sourceBandGramResponse_comp_normalizedSourceGram
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceBandGramResponse owner lambda family ∘L
        finiteEulerLowerFactorNormalizedSourceGram lambda family =
      -finiteEulerNormalizedRightBoundaryNumerator owner lambda family := by
  apply ContinuousLinearMap.ext
  intro u
  have hcancel := congrArg
    (fun operator : sourceSoninCarrier lambda →L[ℂ]
      sourceSoninCarrier lambda => operator u)
    (finiteEulerGramInv_comp_gram lambda family)
  simp only [sourceBandGramResponse, sourceGramResponse_eq_centered,
    finiteEulerLowerFactorNormalizedSourceGram,
    finiteEulerNormalizedRightBoundaryNumerator,
    finiteEulerRightBoundaryNumerator,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
    map_smul] at hcancel ⊢
  rw [hcancel]
  exact smul_neg _ _

/-- The normalized right boundary followed by the normalized inverse Gram is
the original right-ordered source Gram response. -/
theorem normalizedRightBoundary_comp_normalizedGramInv
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteEulerNormalizedRightBoundaryNumerator owner lambda family ∘L
        finiteEulerNormalizedSourceGramInv lambda family =
      sourceGramResponse owner lambda family := by
  have hc : (finiteEulerLowerFactor family.visiblePrimes : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr
      (ne_of_gt (finiteEulerLowerFactor_pos family.visiblePrimes))
  apply ContinuousLinearMap.ext
  intro u
  simp only [finiteEulerNormalizedRightBoundaryNumerator,
    finiteEulerRightBoundaryNumerator, finiteEulerNormalizedSourceGramInv,
    sourceGramResponse_eq_centered, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, map_smul, smul_smul]
  rw [mul_inv_cancel₀ (pow_ne_zero 2 hc), one_smul]

/-- Reversing the already proved adjoint identity makes the normalized right
boundary's adjoint the normalized left boundary. -/
theorem finiteEulerNormalizedRightBoundaryNumerator_adjoint_eq_left
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    (finiteEulerNormalizedRightBoundaryNumerator owner lambda family)† =
      finiteEulerNormalizedLeftBoundaryNumerator owner lambda family := by
  have h := congrArg ContinuousLinearMap.adjoint
    (finiteEulerNormalizedLeftBoundaryNumerator_adjoint_eq_right
      owner lambda family)
  simpa only [ContinuousLinearMap.adjoint_adjoint] using h.symm

/-- The completed four-branch pair with its right source leg closed by the
normalized Gram.  The two scalar gauges cancel before the final minus sign,
so this pair owns the normalized right boundary numerator itself. -/
noncomputable def finiteEulerNormalizedRightBoundaryPairData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {iota kappa tau iotaR kappaR tauR nu mu rho : Type*}
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
  let base := sourceThreeBranchSourcePairData owner lambda family a c hac hsupp
    negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
    sourceBasis hfactor
  (base.boundedSandwich boundaryBasis
    (ContinuousLinearMap.id ℂ (sourceSoninCarrier lambda))
    (finiteEulerLowerFactorNormalizedSourceGram lambda family)).smulRight (-1)

theorem finiteEulerNormalizedRightBoundaryPairData_traceProduct_eq
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {iota kappa tau iotaR kappaR tauR nu mu rho : Type*}
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
    (finiteEulerNormalizedRightBoundaryPairData owner lambda family a c hac
      hsupp negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
      sourceBasis hfactor).traceProduct =
        finiteEulerNormalizedRightBoundaryNumerator owner lambda family := by
  let base := sourceThreeBranchSourcePairData owner lambda family a c hac hsupp
    negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
    sourceBasis hfactor
  have hbase : base.traceProduct =
      sourceBandGramResponse owner lambda family := by
    exact sourceThreeBranchSourcePairData_traceProduct_eq owner lambda family
      a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis sourceBasis hfactor
  rw [finiteEulerNormalizedRightBoundaryPairData,
    BasisHilbertSchmidtPairData.smulRight_traceProduct_eq,
    BasisHilbertSchmidtPairData.boundedSandwich_traceProduct_eq]
  rw [hbase, sourceBandGramResponse_comp_normalizedSourceGram]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.id_comp, neg_one_smul, neg_neg]

private theorem normalizedLeftBoundaryResponse_eq_target
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteEulerNormalizedSourceGramInv lambda family ∘L
        finiteEulerNormalizedLeftBoundaryNumerator owner lambda family =
      finiteEulerTargetCommutatorResponse owner lambda family := by
  rw [← finiteEulerNormalizedGradedCoboundaryResponse_eq_leftBoundary,
    ← finiteEulerTargetCommutatorResponse_eq_normalizedGradedCoboundary]

private theorem normalizedSymmetricBoundaryResponse_eq_average
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteEulerNormalizedSymmetricBoundaryResponse owner lambda family =
      (1 / 2 : ℂ) •
        (finiteEulerNormalizedSourceGramInv lambda family ∘L
            finiteEulerNormalizedLeftBoundaryNumerator owner lambda family +
          finiteEulerNormalizedSourceGramInv lambda family ∘L
            finiteEulerNormalizedRightBoundaryNumerator owner lambda family) := by
  rw [finiteEulerNormalizedSymmetricBoundaryResponse,
    finiteEulerNormalizedSymmetricBoundaryNumerator]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply]
  rw [map_smul, map_add, smul_add]

private theorem normalizedGramSimilarityAnomaly_eq_difference
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteEulerNormalizedGramSimilarityAnomaly owner lambda family =
      (1 / 2 : ℂ) •
        (finiteEulerNormalizedSourceGramInv lambda family ∘L
            finiteEulerNormalizedLeftBoundaryNumerator owner lambda family -
          finiteEulerNormalizedSourceGramInv lambda family ∘L
            finiteEulerNormalizedRightBoundaryNumerator owner lambda family) := by
  rw [finiteEulerNormalizedGramSimilarityAnomaly_eq_boundaryDifference]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply]
  rw [map_sub, smul_sub]

/-- Both terms in Proof 748's symmetric response are trace legal for every
fixed family because the normalized right numerator has one completed pair. -/
theorem finiteEulerNormalizedSymmetricBoundaryResponse_isTraceClassAlong
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {iota kappa tau iotaR kappaR tauR nu mu rho : Type*}
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
    IsTraceClassAlong sourceBasis
      (finiteEulerNormalizedSymmetricBoundaryResponse owner lambda family) := by
  let rightPair := finiteEulerNormalizedRightBoundaryPairData owner lambda
    family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis sourceBasis hfactor
  let leftPair := rightPair.swap
  have hright : rightPair.traceProduct =
      finiteEulerNormalizedRightBoundaryNumerator owner lambda family := by
    exact finiteEulerNormalizedRightBoundaryPairData_traceProduct_eq owner
      lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis sourceBasis hfactor
  have hleft : leftPair.traceProduct =
      finiteEulerNormalizedLeftBoundaryNumerator owner lambda family := by
    dsimp only [leftPair]
    rw [BasisHilbertSchmidtPairData.swap_traceProduct_eq_adjoint, hright,
      finiteEulerNormalizedRightBoundaryNumerator_adjoint_eq_left]
  have hleftClass : IsTraceClassAlong sourceBasis
      (finiteEulerNormalizedSourceGramInv lambda family ∘L
        finiteEulerNormalizedLeftBoundaryNumerator owner lambda family) := by
    have hclass := left_comp_traceProduct_isTraceClassAlong sourceBasis
      boundaryBasis leftPair
      (finiteEulerNormalizedSourceGramInv lambda family)
    rw [hleft] at hclass
    exact hclass
  have hrightClass : IsTraceClassAlong sourceBasis
      (finiteEulerNormalizedSourceGramInv lambda family ∘L
        finiteEulerNormalizedRightBoundaryNumerator owner lambda family) := by
    have hclass := left_comp_traceProduct_isTraceClassAlong sourceBasis
      boundaryBasis rightPair
      (finiteEulerNormalizedSourceGramInv lambda family)
    rw [hright] at hclass
    exact hclass
  rw [normalizedSymmetricBoundaryResponse_eq_average]
  exact isTraceClassAlong_smul sourceBasis _ _
    (isTraceClassAlong_add sourceBasis _ _ hleftClass hrightClass)

/-- The ordered Gram-similarity anomaly is separately trace legal for every
fixed family.  This is an ideal-membership theorem, not a uniform estimate. -/
theorem finiteEulerNormalizedGramSimilarityAnomaly_isTraceClassAlong
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {iota kappa tau iotaR kappaR tauR nu mu rho : Type*}
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
    IsTraceClassAlong sourceBasis
      (finiteEulerNormalizedGramSimilarityAnomaly owner lambda family) := by
  let rightPair := finiteEulerNormalizedRightBoundaryPairData owner lambda
    family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis sourceBasis hfactor
  let leftPair := rightPair.swap
  have hright : rightPair.traceProduct =
      finiteEulerNormalizedRightBoundaryNumerator owner lambda family := by
    exact finiteEulerNormalizedRightBoundaryPairData_traceProduct_eq owner
      lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis sourceBasis hfactor
  have hleft : leftPair.traceProduct =
      finiteEulerNormalizedLeftBoundaryNumerator owner lambda family := by
    dsimp only [leftPair]
    rw [BasisHilbertSchmidtPairData.swap_traceProduct_eq_adjoint, hright,
      finiteEulerNormalizedRightBoundaryNumerator_adjoint_eq_left]
  have hleftClass : IsTraceClassAlong sourceBasis
      (finiteEulerNormalizedSourceGramInv lambda family ∘L
        finiteEulerNormalizedLeftBoundaryNumerator owner lambda family) := by
    have hclass := left_comp_traceProduct_isTraceClassAlong sourceBasis
      boundaryBasis leftPair
      (finiteEulerNormalizedSourceGramInv lambda family)
    rw [hleft] at hclass
    exact hclass
  have hrightClass : IsTraceClassAlong sourceBasis
      (finiteEulerNormalizedSourceGramInv lambda family ∘L
        finiteEulerNormalizedRightBoundaryNumerator owner lambda family) := by
    have hclass := left_comp_traceProduct_isTraceClassAlong sourceBasis
      boundaryBasis rightPair
      (finiteEulerNormalizedSourceGramInv lambda family)
    rw [hright] at hclass
    exact hclass
  rw [normalizedGramSimilarityAnomaly_eq_difference]
  exact isTraceClassAlong_smul sourceBasis _ _
    (CCM24FiniteSProjectionTrace.PositiveTrace.isTraceClassAlong_sub
      sourceBasis _ _ hleftClass hrightClass)

/-- The symmetric response trace is the negative Hermitian part of the
right-ordered source-band trace. -/
theorem ordinaryTraceAlong_normalizedSymmetricBoundaryResponse_eq
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {iota kappa tau iotaR kappaR tauR nu mu rho : Type*}
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
    ordinaryTraceAlong sourceBasis
        (finiteEulerNormalizedSymmetricBoundaryResponse owner lambda family) =
      -(1 / 2 : ℂ) *
        (ordinaryTraceAlong sourceBasis
            (sourceBandGramResponse owner lambda family) +
          star (ordinaryTraceAlong sourceBasis
            (sourceBandGramResponse owner lambda family))) := by
  let rightPair := finiteEulerNormalizedRightBoundaryPairData owner lambda
    family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis sourceBasis hfactor
  let leftPair := rightPair.swap
  let gramInv := finiteEulerNormalizedSourceGramInv lambda family
  have hright : rightPair.traceProduct =
      finiteEulerNormalizedRightBoundaryNumerator owner lambda family := by
    exact finiteEulerNormalizedRightBoundaryPairData_traceProduct_eq owner
      lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis sourceBasis hfactor
  have hleft : leftPair.traceProduct =
      finiteEulerNormalizedLeftBoundaryNumerator owner lambda family := by
    dsimp only [leftPair]
    rw [BasisHilbertSchmidtPairData.swap_traceProduct_eq_adjoint, hright,
      finiteEulerNormalizedRightBoundaryNumerator_adjoint_eq_left]
  have hleftClass : IsTraceClassAlong sourceBasis
      (gramInv ∘L finiteEulerNormalizedLeftBoundaryNumerator
        owner lambda family) := by
    have hclass := left_comp_traceProduct_isTraceClassAlong sourceBasis
      boundaryBasis leftPair gramInv
    rw [hleft] at hclass
    exact hclass
  have hrightClass : IsTraceClassAlong sourceBasis
      (gramInv ∘L finiteEulerNormalizedRightBoundaryNumerator
        owner lambda family) := by
    have hclass := left_comp_traceProduct_isTraceClassAlong sourceBasis
      boundaryBasis rightPair gramInv
    rw [hright] at hclass
    exact hclass
  have hcycle : ordinaryTraceAlong sourceBasis
      (gramInv ∘L finiteEulerNormalizedRightBoundaryNumerator
        owner lambda family) =
      ordinaryTraceAlong sourceBasis
        (finiteEulerNormalizedRightBoundaryNumerator owner lambda family ∘L
          gramInv) := by
    simpa only [gramInv, hright] using
      (ordinaryTraceAlong_left_comp_traceProduct_eq_right_comp
        sourceBasis boundaryBasis rightPair gramInv)
  have hleftTrace : ordinaryTraceAlong sourceBasis
      (gramInv ∘L finiteEulerNormalizedLeftBoundaryNumerator
        owner lambda family) =
      star (ordinaryTraceAlong sourceBasis
        (sourceGramResponse owner lambda family)) := by
    rw [normalizedLeftBoundaryResponse_eq_target]
    rw [← leftOrderedSourceGramResponse_eq_targetCommutator,
      leftOrderedSourceGramResponse_eq_adjoint,
      ordinaryTraceAlong_adjoint]
  have hrightTrace : ordinaryTraceAlong sourceBasis
      (gramInv ∘L finiteEulerNormalizedRightBoundaryNumerator
        owner lambda family) =
      ordinaryTraceAlong sourceBasis
        (sourceGramResponse owner lambda family) := by
    rw [hcycle, normalizedRightBoundary_comp_normalizedGramInv]
  rw [normalizedSymmetricBoundaryResponse_eq_average]
  rw [ordinaryTraceAlong_smul sourceBasis _ _
    (isTraceClassAlong_add sourceBasis _ _ hleftClass hrightClass)]
  rw [ordinaryTraceAlong_add sourceBasis _ _ hleftClass hrightClass,
    hleftTrace, hrightTrace, sourceBandGramResponse]
  rw [CCM24FiniteSProjectionTrace.PositiveTrace.ordinaryTraceAlong_neg]
  simp only [star_neg]
  ring

/-- The anomaly trace is exactly the anti-Hermitian boundary part retained by
the right-ordered source-band owner.  No infinite-dimensional trace cycle is
hidden in this identity. -/
theorem ordinaryTraceAlong_normalizedGramSimilarityAnomaly_eq
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {iota kappa tau iotaR kappaR tauR nu mu rho : Type*}
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
    ordinaryTraceAlong sourceBasis
        (finiteEulerNormalizedGramSimilarityAnomaly owner lambda family) =
      (1 / 2 : ℂ) *
        (ordinaryTraceAlong sourceBasis
            (sourceBandGramResponse owner lambda family) -
          star (ordinaryTraceAlong sourceBasis
            (sourceBandGramResponse owner lambda family))) := by
  let rightPair := finiteEulerNormalizedRightBoundaryPairData owner lambda
    family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis sourceBasis hfactor
  let leftPair := rightPair.swap
  let gramInv := finiteEulerNormalizedSourceGramInv lambda family
  have hright : rightPair.traceProduct =
      finiteEulerNormalizedRightBoundaryNumerator owner lambda family := by
    exact finiteEulerNormalizedRightBoundaryPairData_traceProduct_eq owner
      lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis sourceBasis hfactor
  have hleft : leftPair.traceProduct =
      finiteEulerNormalizedLeftBoundaryNumerator owner lambda family := by
    dsimp only [leftPair]
    rw [BasisHilbertSchmidtPairData.swap_traceProduct_eq_adjoint, hright,
      finiteEulerNormalizedRightBoundaryNumerator_adjoint_eq_left]
  have hleftClass : IsTraceClassAlong sourceBasis
      (gramInv ∘L finiteEulerNormalizedLeftBoundaryNumerator
        owner lambda family) := by
    have hclass := left_comp_traceProduct_isTraceClassAlong sourceBasis
      boundaryBasis leftPair gramInv
    rw [hleft] at hclass
    exact hclass
  have hrightClass : IsTraceClassAlong sourceBasis
      (gramInv ∘L finiteEulerNormalizedRightBoundaryNumerator
        owner lambda family) := by
    have hclass := left_comp_traceProduct_isTraceClassAlong sourceBasis
      boundaryBasis rightPair gramInv
    rw [hright] at hclass
    exact hclass
  have hcycle : ordinaryTraceAlong sourceBasis
      (gramInv ∘L finiteEulerNormalizedRightBoundaryNumerator
        owner lambda family) =
      ordinaryTraceAlong sourceBasis
        (finiteEulerNormalizedRightBoundaryNumerator owner lambda family ∘L
          gramInv) := by
    simpa only [gramInv, hright] using
      (ordinaryTraceAlong_left_comp_traceProduct_eq_right_comp
        sourceBasis boundaryBasis rightPair gramInv)
  have hleftTrace : ordinaryTraceAlong sourceBasis
      (gramInv ∘L finiteEulerNormalizedLeftBoundaryNumerator
        owner lambda family) =
      star (ordinaryTraceAlong sourceBasis
        (sourceGramResponse owner lambda family)) := by
    rw [normalizedLeftBoundaryResponse_eq_target]
    rw [← leftOrderedSourceGramResponse_eq_targetCommutator,
      leftOrderedSourceGramResponse_eq_adjoint,
      ordinaryTraceAlong_adjoint]
  have hrightTrace : ordinaryTraceAlong sourceBasis
      (gramInv ∘L finiteEulerNormalizedRightBoundaryNumerator
        owner lambda family) =
      ordinaryTraceAlong sourceBasis
        (sourceGramResponse owner lambda family) := by
    rw [hcycle, normalizedRightBoundary_comp_normalizedGramInv]
  rw [normalizedGramSimilarityAnomaly_eq_difference]
  rw [ordinaryTraceAlong_smul sourceBasis _ _
    (CCM24FiniteSProjectionTrace.PositiveTrace.isTraceClassAlong_sub
      sourceBasis _ _ hleftClass hrightClass)]
  rw [CCM24FiniteSProjectionTrace.PositiveTrace.ordinaryTraceAlong_sub
    sourceBasis _ _ hleftClass hrightClass]
  rw [hleftTrace, hrightTrace, sourceBandGramResponse]
  rw [CCM24FiniteSProjectionTrace.PositiveTrace.ordinaryTraceAlong_neg]
  simp only [star_neg]
  ring

/-- Proof 299's proposed cancellation is equivalent to reality of the
right-ordered source-band trace.  Reality is not inferred here. -/
theorem ordinaryTraceAlong_normalizedGramSimilarityAnomaly_eq_zero_iff
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {iota kappa tau iotaR kappaR tauR nu mu rho : Type*}
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
    ordinaryTraceAlong sourceBasis
        (finiteEulerNormalizedGramSimilarityAnomaly owner lambda family) = 0 ↔
      ordinaryTraceAlong sourceBasis
          (sourceBandGramResponse owner lambda family) =
        star (ordinaryTraceAlong sourceBasis
          (sourceBandGramResponse owner lambda family)) := by
  rw [ordinaryTraceAlong_normalizedGramSimilarityAnomaly_eq owner lambda family
    a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis sourceBasis hfactor]
  constructor
  · intro hzero
    have hhalf : (1 / 2 : ℂ) ≠ 0 := by norm_num
    have hdiff : ordinaryTraceAlong sourceBasis
          (sourceBandGramResponse owner lambda family) -
        star (ordinaryTraceAlong sourceBasis
          (sourceBandGramResponse owner lambda family)) = 0 :=
      (mul_eq_zero.mp hzero).resolve_left hhalf
    exact sub_eq_zero.mp hdiff
  · intro hreal
    have hdiff : ordinaryTraceAlong sourceBasis
          (sourceBandGramResponse owner lambda family) -
        star (ordinaryTraceAlong sourceBasis
          (sourceBandGramResponse owner lambda family)) = 0 :=
      sub_eq_zero.mpr hreal
    rw [hdiff, mul_zero]

/-- A genuine source/ambient trace identity would kill the anomaly because the
ambient root-sandwiched endpoint is self-adjoint.  This theorem isolates that
still-missing boundary-closing premise exactly. -/
theorem ordinaryTraceAlong_normalizedGramSimilarityAnomaly_eq_zero_of_endpointCycle
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {iota kappa tau iotaR kappaR tauR nu mu rho : Type*}
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
    (hcycle : ordinaryTraceAlong sourceBasis
        (sourceBandGramResponse owner lambda family) =
      ordinaryTraceAlong globalBasis
        (rootSandwichedBandResponse owner lambda family)) :
    ordinaryTraceAlong sourceBasis
      (finiteEulerNormalizedGramSimilarityAnomaly owner lambda family) = 0 := by
  rw [ordinaryTraceAlong_normalizedGramSimilarityAnomaly_eq_zero_iff owner
    lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis sourceBasis hfactor]
  rw [hcycle]
  have htrace := ordinaryTraceAlong_adjoint globalBasis
    (rootSandwichedBandResponse owner lambda family)
  rw [rootSandwichedBandResponse_adjoint_eq] at htrace
  exact htrace

end CCM24FiniteSGatePhysicalNormalizedAnomalyTrace
end CCM25Concrete
end Source
end ConnesWeilRH
