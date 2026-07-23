/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCombinedCoframeGuard
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSActualSchurCascade
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSFixedPhysicalEnergyBound

/-!
# Combined physical-column energy gate

Proof 492 puts the raw endpoint and the forward actual-band first jet in one
physical right column.  Proof 493 identifies its coframe as `J + L_S`.  This
module closes every other Hilbert--Schmidt energy in that pair and isolates
the remaining source theorem as the energy of the single column

```text
M (V_S + C_S).
```

It also gives the carrier-correct way to produce that estimate from the
actual rectangular Schur boundary history.  The physical column must factor
through one bounded readout of the complete packed history; the readout is
not inferred from biorthogonality or from the Julia contraction alone.

No such physical readout is constructed here.  Consequently this module is
a sharp Gate 3U consumer, not a Gate 3U proof or a sign theorem.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCombinedPhysicalEnergyGate

open MeasureTheory
open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.PositiveTrace
open CC20Concrete.CompactRootHalfLinePair
open CCM24FiniteSProjectionTrace
open CCM24FiniteSGramResponse
open CCM24FiniteSInverseMetric
open CCM24FiniteSCoframeResponse
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSFixedQuotientContractionBound
open CCM24FiniteSFixedQuotientCarrier
open CCM24FiniteSFixedPhysicalEnergyBound
open CCM24FiniteSRawRemainderCommonPair
open CCM24FiniteSCombinedCoframeGuard
open CCM24FiniteSRootCompletedFirstJet
open CCM24SourceProlateTrace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! ## A type-correct rectangular-history readout -/

/-- A contractive readout of the complete rectangular Schur boundary history
cannot increase the square energy of a Hilbert--Schmidt source input.  The
packed boundary column remains whole until after its Julia co-defect
contraction is applied. -/
theorem rectangularBoundaryReadout_tsum_normSq_le
    {iota H K G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (steps : List
      (CCM24FiniteSJuliaCoDefect.RectangularSchurCoDefectStepData H K))
    (sourceBasis : HilbertBasis iota ℂ H)
    (input : H →L[ℂ] H)
    (hinput : Summable fun i => ‖input (sourceBasis i)‖ ^ 2)
    (readout : PiLp 2
      (fun _ : Fin (steps.map
        (fun step => step.toAdjointCoDefectJuliaStep)).length => K) →L[ℂ] G)
    (hreadout : ‖readout‖ ≤ 1) :
    (∑' i, ‖(readout ∘L rectangularBoundaryDaggerColumn steps ∘L input)
        (sourceBasis i)‖ ^ 2) ≤
      ∑' i, ‖input (sourceBasis i)‖ ^ 2 := by
  let column := rectangularBoundaryDaggerColumn steps ∘L input
  have hcolumn : Summable fun i => ‖column (sourceBasis i)‖ ^ 2 := by
    simpa only [column, ContinuousLinearMap.comp_apply] using
      rectangularBoundaryDaggerColumn_summable_normSq_of_summable_input
        steps sourceBasis input hinput
  have hreadoutColumn : Summable fun i =>
      ‖(readout ∘L column) (sourceBasis i)‖ ^ 2 :=
    summable_normSq_postcomp sourceBasis column readout hcolumn
  have hpoint : ∀ i,
      ‖(readout ∘L column) (sourceBasis i)‖ ^ 2 ≤
        ‖column (sourceBasis i)‖ ^ 2 := by
    intro i
    have hnorm : ‖readout (column (sourceBasis i))‖ ≤
        ‖column (sourceBasis i)‖ := by
      calc
        ‖readout (column (sourceBasis i))‖ ≤
            ‖readout‖ * ‖column (sourceBasis i)‖ :=
          readout.le_opNorm _
        _ ≤ 1 * ‖column (sourceBasis i)‖ := by
          exact mul_le_mul_of_nonneg_right hreadout (norm_nonneg _)
        _ = ‖column (sourceBasis i)‖ := one_mul _
    simpa only [ContinuousLinearMap.comp_apply] using
      (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hnorm
  calc
    (∑' i, ‖(readout ∘L rectangularBoundaryDaggerColumn steps ∘L input)
        (sourceBasis i)‖ ^ 2) =
        ∑' i, ‖(readout ∘L column) (sourceBasis i)‖ ^ 2 := by
      rfl
    _ ≤ ∑' i, ‖column (sourceBasis i)‖ ^ 2 :=
      hreadoutColumn.tsum_le_tsum hpoint hcolumn
    _ ≤ ∑' i, ‖input (sourceBasis i)‖ ^ 2 := by
      simpa only [column, ContinuousLinearMap.comp_apply] using
        rectangularBoundaryDaggerColumn_tsum_normSq_le_of_summable_input
          steps sourceBasis input hinput

/-! The quantitative form keeps the actual readout norm visible.  The Julia
history is contractive, but a source-specific physical readout need not be;
its squared operator norm is the exact factor paid by the Hilbert--Schmidt
energy consumer. -/
theorem rectangularBoundaryReadout_tsum_normSq_le_of_norm_le
    {iota H K G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (steps : List
      (CCM24FiniteSJuliaCoDefect.RectangularSchurCoDefectStepData H K))
    (sourceBasis : HilbertBasis iota ℂ H)
    (input : H →L[ℂ] H)
    (hinput : Summable fun i => ‖input (sourceBasis i)‖ ^ 2)
    (readout : PiLp 2
      (fun _ : Fin (steps.map
        (fun step => step.toAdjointCoDefectJuliaStep)).length => K) →L[ℂ] G)
    (bound : ℝ) (hbound : 0 ≤ bound) (hreadout : ‖readout‖ ≤ bound) :
    (∑' i, ‖(readout ∘L rectangularBoundaryDaggerColumn steps ∘L input)
        (sourceBasis i)‖ ^ 2) ≤
      bound ^ 2 * (∑' i, ‖input (sourceBasis i)‖ ^ 2) := by
  let column := rectangularBoundaryDaggerColumn steps ∘L input
  have hcolumn : Summable fun i => ‖column (sourceBasis i)‖ ^ 2 := by
    simpa only [column, ContinuousLinearMap.comp_apply] using
      rectangularBoundaryDaggerColumn_summable_normSq_of_summable_input
        steps sourceBasis input hinput
  have hreadoutColumn : Summable fun i =>
      ‖(readout ∘L column) (sourceBasis i)‖ ^ 2 :=
    summable_normSq_postcomp sourceBasis column readout hcolumn
  have hpoint : ∀ i,
      ‖(readout ∘L column) (sourceBasis i)‖ ^ 2 ≤
        bound ^ 2 * ‖column (sourceBasis i)‖ ^ 2 := by
    intro i
    have hnorm : ‖readout (column (sourceBasis i))‖ ≤
        bound * ‖column (sourceBasis i)‖ := by
      calc
        ‖readout (column (sourceBasis i))‖ ≤
            ‖readout‖ * ‖column (sourceBasis i)‖ := readout.le_opNorm _
        _ ≤ bound * ‖column (sourceBasis i)‖ := by
          exact mul_le_mul_of_nonneg_right hreadout (norm_nonneg _)
    simpa only [ContinuousLinearMap.comp_apply, mul_pow] using
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hbound
        (norm_nonneg _))).mpr hnorm
  have hcolumnBound :
      (∑' i, bound ^ 2 * ‖column (sourceBasis i)‖ ^ 2) =
        bound ^ 2 * (∑' i, ‖column (sourceBasis i)‖ ^ 2) := by
    rw [tsum_mul_left]
  calc
    (∑' i, ‖(readout ∘L rectangularBoundaryDaggerColumn steps ∘L input)
        (sourceBasis i)‖ ^ 2) =
        ∑' i, ‖(readout ∘L column) (sourceBasis i)‖ ^ 2 := by rfl
    _ ≤ ∑' i, bound ^ 2 * ‖column (sourceBasis i)‖ ^ 2 :=
      hreadoutColumn.tsum_le_tsum hpoint
        (hcolumn.mul_left (bound ^ 2))
    _ = bound ^ 2 * (∑' i, ‖column (sourceBasis i)‖ ^ 2) := hcolumnBound
    _ ≤ bound ^ 2 * (∑' i, ‖input (sourceBasis i)‖ ^ 2) := by
      exact mul_le_mul_of_nonneg_left
        (by
          simpa only [column, ContinuousLinearMap.comp_apply] using
            rectangularBoundaryDaggerColumn_tsum_normSq_le_of_summable_input
              steps sourceBasis input hinput)
        (sq_nonneg bound)

/-! ## The one unresolved actual physical column -/

/-- The forward actual-band coframe is a contraction.  This closes the
reverse-first-jet energy; it does not control the raw metric coframe in the
combined forward/endpoint column. -/
theorem norm_sourceActualBandForwardCoframe_le_one
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    ‖sourceActualBandForwardCoframe lambda family‖ ≤ 1 := by
  have hband : ‖sourceBandProjection lambda‖ ≤ 1 :=
    IsStarProjection.norm_le _ (sourceBandProjection_isStarProjection lambda)
  have hinverse : ‖normalizedFiniteEulerInverse family‖ ≤ 1 :=
    norm_normalizedFiniteEulerInverse_le_one family
  have hinclusion : ‖sourceInclusion lambda‖ ≤ 1 :=
    Submodule.norm_subtypeL_le _
  have hbandInverse :
      ‖sourceBandProjection lambda ∘L
          normalizedFiniteEulerInverse family‖ ≤ 1 := by
    calc
      _ ≤ ‖sourceBandProjection lambda‖ *
          ‖normalizedFiniteEulerInverse family‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 :=
        mul_le_mul hband hinverse (norm_nonneg _) (by norm_num)
      _ = 1 := one_mul _
  change ‖sourceBandProjection lambda ∘L
      normalizedFiniteEulerInverse family ∘L sourceInclusion lambda‖ ≤ 1
  calc
    _ ≤
        ‖sourceBandProjection lambda ∘L
          normalizedFiniteEulerInverse family‖ *
          ‖sourceInclusion lambda‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * 1 :=
      mul_le_mul hbandInverse hinclusion
        (norm_nonneg (sourceInclusion lambda)) (by norm_num)
    _ = 1 := one_mul _

/-- The exact square energy of the only unresolved Proof 492 column.  The
definition deliberately retains the complete physical right leg and the sum
`V_S + C_S` before taking a norm. -/
noncomputable def sourceActualBandCombinedPhysicalRightEnergy
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {iota kappa tau iotaR kappaR tauR nu rho : Type*}
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
      (sourceActualBandForwardEndpointCoframe lambda family
        (sourceBasis i))‖ ^ 2

/-- A genuine actual-Schur readout produces the unresolved combined-column
energy estimate.  The source input is required to be Hilbert--Schmidt; using
the identity input would give an infinite and therefore useless bound. -/
theorem sourceActualBandCombinedPhysicalRightEnergy_le_of_actualSchurReadout
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {iota kappa tau iotaR kappaR tauR nu rho : Type*}
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
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      CCM24FiniteSActualJuliaInput.SuffixPrimeEulerProjectedJuliaSchurFrameStepData
        lambda (commonBoundaryCarrier a c) p S)
    (sourceInput : sourceSoninCarrier lambda →L[ℂ]
      sourceSoninCarrier lambda)
    (hinput : Summable fun i => ‖sourceInput (sourceBasis i)‖ ^ 2)
    (readout : PiLp 2
      (fun _ : Fin (suffixActualSchurCoDefectSteps lambda stepData
        family.visiblePrimes).length => finiteSCarrier) →L[ℂ]
          commonBoundaryCarrier a c)
    (hreadout : ‖readout‖ ≤ 1)
    (hphysical :
      (sourceThreeBranchPairData owner lambda a c hac hsupp negativeBasis
          positiveBasis outputBasis reflectedNegativeBasis
          reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor).right
          ∘L sourceActualBandForwardEndpointCoframe lambda family =
        readout ∘L rectangularBoundaryDaggerColumn
          (suffixActualSchurFrameSteps lambda stepData family.visiblePrimes) ∘L
            sourceInput) :
    sourceActualBandCombinedPhysicalRightEnergy owner lambda family a c hac
        hsupp negativeBasis positiveBasis outputBasis reflectedNegativeBasis
        reflectedPositiveBasis reflectedOutputBasis globalBasis sourceBasis
        hfactor ≤
      ∑' i, ‖sourceInput (sourceBasis i)‖ ^ 2 := by
  have henergy := rectangularBoundaryReadout_tsum_normSq_le
    (steps := suffixActualSchurFrameSteps lambda stepData family.visiblePrimes)
    sourceBasis sourceInput hinput readout hreadout
  have hphysicalApply : ∀ i,
      (readout ∘L rectangularBoundaryDaggerColumn
          (suffixActualSchurFrameSteps lambda stepData family.visiblePrimes) ∘L
            sourceInput) (sourceBasis i) =
        (sourceThreeBranchPairData owner lambda a c hac hsupp negativeBasis
            positiveBasis outputBasis reflectedNegativeBasis
            reflectedPositiveBasis reflectedOutputBasis globalBasis
            hfactor).right
          (sourceActualBandForwardEndpointCoframe lambda family
            (sourceBasis i)) := by
    intro i
    have happ := congrArg
      (fun operator : sourceSoninCarrier lambda →L[ℂ] commonBoundaryCarrier a c =>
        operator (sourceBasis i)) hphysical.symm
    simpa only [ContinuousLinearMap.comp_apply] using happ
  rw [sourceActualBandCombinedPhysicalRightEnergy]
  calc
    (∑' i, ‖(sourceThreeBranchPairData owner lambda a c hac hsupp
          negativeBasis positiveBasis outputBasis reflectedNegativeBasis
          reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor).right
        (sourceActualBandForwardEndpointCoframe lambda family
          (sourceBasis i))‖ ^ 2) =
        ∑' i, ‖(readout ∘L rectangularBoundaryDaggerColumn
            (suffixActualSchurFrameSteps lambda stepData family.visiblePrimes) ∘L
              sourceInput) (sourceBasis i)‖ ^ 2 := by
      apply tsum_congr
      intro i
      rw [hphysicalApply i]
    _ ≤ ∑' i, ‖sourceInput (sourceBasis i)‖ ^ 2 := henergy

/-! The same consumer with an explicit readout constant.  This is the useful
quantitative fallback when a source producer supplies `‖readout‖ ≤ C` but has
not yet established the sharper contraction `C ≤ 1`. -/
theorem sourceActualBandCombinedPhysicalRightEnergy_le_of_actualSchurReadout_of_norm_le
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {iota kappa tau iotaR kappaR tauR nu rho : Type*}
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
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      CCM24FiniteSActualJuliaInput.SuffixPrimeEulerProjectedJuliaSchurFrameStepData
        lambda (commonBoundaryCarrier a c) p S)
    (sourceInput : sourceSoninCarrier lambda →L[ℂ]
      sourceSoninCarrier lambda)
    (hinput : Summable fun i => ‖sourceInput (sourceBasis i)‖ ^ 2)
    (readout : PiLp 2
      (fun _ : Fin (suffixActualSchurCoDefectSteps lambda stepData
        family.visiblePrimes).length => finiteSCarrier) →L[ℂ]
          commonBoundaryCarrier a c)
    (bound : ℝ) (hbound : 0 ≤ bound) (hreadout : ‖readout‖ ≤ bound)
    (hphysical :
      (sourceThreeBranchPairData owner lambda a c hac hsupp negativeBasis
          positiveBasis outputBasis reflectedNegativeBasis reflectedPositiveBasis
          reflectedOutputBasis globalBasis hfactor).right
          ∘L sourceActualBandForwardEndpointCoframe lambda family =
        readout ∘L rectangularBoundaryDaggerColumn
          (suffixActualSchurFrameSteps lambda stepData family.visiblePrimes) ∘L
            sourceInput) :
    sourceActualBandCombinedPhysicalRightEnergy owner lambda family a c hac
        hsupp negativeBasis positiveBasis outputBasis reflectedNegativeBasis
        reflectedPositiveBasis reflectedOutputBasis globalBasis sourceBasis
        hfactor ≤
      bound ^ 2 * (∑' i, ‖sourceInput (sourceBasis i)‖ ^ 2) := by
  have henergy := rectangularBoundaryReadout_tsum_normSq_le_of_norm_le
    (steps := suffixActualSchurFrameSteps lambda stepData family.visiblePrimes)
    sourceBasis sourceInput hinput readout bound hbound hreadout
  have hphysicalApply : ∀ i,
      (readout ∘L rectangularBoundaryDaggerColumn
          (suffixActualSchurFrameSteps lambda stepData family.visiblePrimes) ∘L
            sourceInput) (sourceBasis i) =
        (sourceThreeBranchPairData owner lambda a c hac hsupp negativeBasis
            positiveBasis outputBasis reflectedNegativeBasis
            reflectedPositiveBasis reflectedOutputBasis globalBasis
            hfactor).right
          (sourceActualBandForwardEndpointCoframe lambda family
            (sourceBasis i)) := by
    intro i
    have happ := congrArg
      (fun operator : sourceSoninCarrier lambda →L[ℂ]
          commonBoundaryCarrier a c => operator (sourceBasis i)) hphysical.symm
    simpa only [ContinuousLinearMap.comp_apply] using happ
  rw [sourceActualBandCombinedPhysicalRightEnergy]
  calc
    (∑' i, ‖(sourceThreeBranchPairData owner lambda a c hac hsupp
          negativeBasis positiveBasis outputBasis reflectedNegativeBasis
          reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor).right
        (sourceActualBandForwardEndpointCoframe lambda family
          (sourceBasis i))‖ ^ 2) =
        ∑' i, ‖(readout ∘L rectangularBoundaryDaggerColumn
            (suffixActualSchurFrameSteps lambda stepData family.visiblePrimes) ∘L
              sourceInput) (sourceBasis i)‖ ^ 2 := by
      apply tsum_congr
      intro i
      rw [hphysicalApply i]
    _ ≤ bound ^ 2 * (∑' i, ‖sourceInput (sourceBasis i)‖ ^ 2) := henergy

/-! ## The sharp raw-remainder consumer -/

set_option maxHeartbeats 3000000 in
-- Expanding both `l2Sum` energies and the exact raw trace owner is elaborate.
/-- Once the single combined physical right column has the fixed physical
energy bound, every other column in Proof 492 is already contractive.  The
complete lower-factor-gauged raw remainder then has a family-independent
trace bound with no inverse Euler lower factor. -/
theorem lowerFactorGaugedActualBandCompletedRelativeResponse_trace_norm_le_of_combinedEnergy
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
    (hcombined :
      sourceActualBandCombinedPhysicalRightEnergy owner lambda family a c hac
          hsupp negativeBasis positiveBasis outputBasis reflectedNegativeBasis
          reflectedPositiveBasis reflectedOutputBasis globalBasis sourceBasis
          hfactor ≤
        fixedPhysicalEnergyMajorant owner lambda a c globalBasis) :
    ‖ordinaryTraceAlong sourceBasis
        (CCM24FiniteSRawCompletedGaugeOwner.lowerFactorGaugedActualBandCompletedRelativeResponse
          owner lambda family)‖ ≤
      2 * fixedPhysicalEnergyMajorant owner lambda a c globalBasis := by
  let base := sourceThreeBranchPairData owner lambda a c hac hsupp
    negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor
  let J := sourceInclusion lambda
  let V := sourceActualBandForwardCoframe lambda family
  let C := finiteEulerMetricCoframe lambda family
  let first := sourceActualBandForwardEndpointPairData owner lambda family
    a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis sourceBasis hfactor
  let second :=
    (BasisHilbertSchmidtPairData.boundedPrecomp boundaryBasis sourceBasis
      base V J).smulRight (-1)
  let pair := sourceActualBandRawRemainderCommonPairData owner lambda family
    a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis sourceBasis hfactor
  let M := fixedPhysicalEnergyMajorant owner lambda a c globalBasis
  have hJ : ‖J‖ ≤ 1 := by
    dsimp only [J]
    exact Submodule.norm_subtypeL_le _
  have hV : ‖V‖ ≤ 1 := by
    dsimp only [V]
    exact norm_sourceActualBandForwardCoframe_le_one lambda family
  have hbaseLeft :
      (∑' i, ‖base.left (globalBasis i)‖ ^ 2) ≤ M := by
    dsimp only [base, M]
    exact sourceThreeBranchPairData_left_basisEnergy_le_fixedMajorant
      owner lambda a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis hfactor
  have hbaseRight :
      (∑' i, ‖base.right (globalBasis i)‖ ^ 2) ≤ M := by
    dsimp only [base, M]
    exact sourceThreeBranchPairData_right_basisEnergy_le_fixedMajorant
      owner lambda a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis hfactor
  have hfirstLeftOperator : first.left = base.left ∘L J := by
    dsimp only [first, base, J, V, C]
    exact boundedPrecompAddRight_left_eq boundaryBasis sourceBasis
      (sourceThreeBranchPairData owner lambda a c hac hsupp negativeBasis
        positiveBasis outputBasis reflectedNegativeBasis
        reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor)
      (sourceInclusion lambda)
      (sourceActualBandForwardCoframe lambda family)
      (finiteEulerMetricCoframe lambda family)
  have hfirstLeft :
      (∑' i, ‖first.left (sourceBasis i)‖ ^ 2) ≤ M := by
    rw [hfirstLeftOperator]
    exact (boundedPrecomp_left_tsum_le_of_norm_le_one boundaryBasis sourceBasis
      base J J hJ).trans hbaseLeft
  have hfirstRight :
      (∑' i, ‖first.right (sourceBasis i)‖ ^ 2) ≤ M := by
    calc
      (∑' i, ‖first.right (sourceBasis i)‖ ^ 2) =
          sourceActualBandCombinedPhysicalRightEnergy owner lambda family
            a c hac hsupp negativeBasis positiveBasis outputBasis
            reflectedNegativeBasis reflectedPositiveBasis
            reflectedOutputBasis globalBasis sourceBasis hfactor := by
        apply tsum_congr
        intro i
        rw [show first.right (sourceBasis i) =
            base.right (sourceActualBandForwardEndpointCoframe lambda family
              (sourceBasis i)) by
          dsimp only [first, base]
          exact sourceActualBandForwardEndpointPairData_right_apply owner
            lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
            reflectedNegativeBasis reflectedPositiveBasis
            reflectedOutputBasis globalBasis boundaryBasis sourceBasis hfactor
            (sourceBasis i)]
      _ ≤ M := by simpa only [M] using hcombined
  have hsecondLeft :
      (∑' i, ‖second.left (sourceBasis i)‖ ^ 2) ≤ M := by
    have h := boundedPrecomp_left_tsum_le_of_norm_le_one boundaryBasis
      sourceBasis base V J hV
    simpa only [second, BasisHilbertSchmidtPairData.smulRight] using
      h.trans hbaseLeft
  have hsecondRight :
      (∑' i, ‖second.right (sourceBasis i)‖ ^ 2) ≤ M := by
    have h := boundedPrecomp_right_tsum_le_of_norm_le_one boundaryBasis
      sourceBasis base V J hJ
    simpa only [second, BasisHilbertSchmidtPairData.smulRight,
      neg_smul, one_smul, ContinuousLinearMap.neg_apply, norm_neg] using
      h.trans hbaseRight
  have hpair : pair = BasisHilbertSchmidtPairData.l2Sum first second := by
    rfl
  have hpairLeft :
      (∑' i, ‖pair.left (sourceBasis i)‖ ^ 2) ≤ 2 * M := by
    rw [hpair, l2Sum_left_basisEnergy_eq_add]
    linarith
  have hpairRight :
      (∑' i, ‖pair.right (sourceBasis i)‖ ^ 2) ≤ 2 * M := by
    rw [hpair, l2Sum_right_basisEnergy_eq_add]
    linarith
  have hM : 0 ≤ M := by
    dsimp only [M, fixedPhysicalEnergyMajorant]
    positivity
  have htrace := ordinaryTraceAlong_traceProduct_norm_le_geometricEnergy pair
  rw [sourceActualBandRawRemainderCommonPairData_traceProduct_eq_gauged
    owner lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis sourceBasis hfactor] at htrace
  calc
    ‖ordinaryTraceAlong sourceBasis
        (CCM24FiniteSRawCompletedGaugeOwner.lowerFactorGaugedActualBandCompletedRelativeResponse
          owner lambda family)‖ ≤
        Real.sqrt (∑' i, ‖pair.left (sourceBasis i)‖ ^ 2) *
          Real.sqrt (∑' i, ‖pair.right (sourceBasis i)‖ ^ 2) := htrace
    _ ≤ Real.sqrt (2 * M) * Real.sqrt (2 * M) := by
      exact mul_le_mul (Real.sqrt_le_sqrt hpairLeft)
        (Real.sqrt_le_sqrt hpairRight)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = 2 * M := by
      rw [← pow_two, Real.sq_sqrt (mul_nonneg (by norm_num) hM)]
    _ = 2 * fixedPhysicalEnergyMajorant owner lambda a c globalBasis := rfl

end CCM24FiniteSCombinedPhysicalEnergyGate
end CCM25Concrete
end Source
end ConnesWeilRH
