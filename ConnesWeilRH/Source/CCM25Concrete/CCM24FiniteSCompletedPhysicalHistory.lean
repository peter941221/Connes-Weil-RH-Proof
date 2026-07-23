/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCombinedPhysicalEnergyGate

/-!
# Completed rectangular Schur history

The rectangular boundary-dagger column records only the local Schur defects.
For an empty suffix it is the zero column, so it cannot read back the fixed
physical base column.  The correct causal history also retains the terminal
survivor.

This module packs

```text
terminal survivor + rectangular boundary-dagger history
```

in one `L2` product.  The exact Julia Pythagorean telescope and the
rectangular boundary domination prove that this completed column is still a
contraction.  The Gate-facing consumer may therefore read the complete
physical column from this history without losing the empty-family base term.

The source-specific readout identity remains the analytic producer.  No such
identity, Gate 3U estimate, sign theorem, or RH conclusion is assumed here.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedPhysicalHistory

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
open CCM24FiniteSJuliaBessel
open CCM24FiniteSFixedPhysicalEnergyBound
open CCM24FiniteSRawRemainderCommonPair
open CCM24FiniteSCombinedPhysicalEnergyGate
open CCM24FiniteSRootCompletedFirstJet
open CCM24SourceProlateTrace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! ## The missing terminal survivor -/

/-- The carrier of the completed rectangular history.  Its first coordinate
is the terminal source survivor; its second coordinate is the complete
rectangular boundary-dagger history. -/
noncomputable abbrev completedRectangularBoundaryCarrier
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (steps : List (CCM24FiniteSJuliaCoDefect.RectangularSchurCoDefectStepData
      H K)) :=
  WithLp 2
    (H × PiLp 2
      (fun _ : Fin (steps.map
        (fun step => step.toAdjointCoDefectJuliaStep)).length => K))

/-- The completed Schur history consists of the terminal survivor and every
rectangular boundary-dagger coordinate, packed before any readout or norm. -/
noncomputable def completedRectangularBoundaryColumn
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (steps : List (CCM24FiniteSJuliaCoDefect.RectangularSchurCoDefectStepData
      H K)) :
    H →L[ℂ] completedRectangularBoundaryCarrier steps :=
  ((WithLp.prodContinuousLinearEquiv 2 ℂ H
    (PiLp 2 (fun _ : Fin (steps.map
      (fun step => step.toAdjointCoDefectJuliaStep)).length => K))).symm.toContinuousLinearMap) ∘L
    (juliaSurvivor
      (steps.map (fun step => step.toAdjointCoDefectJuliaStep))).prod
        (rectangularBoundaryDaggerColumn steps)

@[simp]
theorem completedRectangularBoundaryColumn_apply
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (steps : List (CCM24FiniteSJuliaCoDefect.RectangularSchurCoDefectStepData
      H K)) (x : H) :
    completedRectangularBoundaryColumn steps x =
      WithLp.toLp 2
        (juliaSurvivor
            (steps.map (fun step => step.toAdjointCoDefectJuliaStep)) x,
          rectangularBoundaryDaggerColumn steps x) := by
  rfl

/-- The old defect-only history has no empty-family base coordinate. -/
theorem rectangularBoundaryDaggerColumn_nil_eq_zero
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] :
    rectangularBoundaryDaggerColumn
        ([] : List
          (CCM24FiniteSJuliaCoDefect.RectangularSchurCoDefectStepData H K)) =
      0 := by
  apply ContinuousLinearMap.ext
  intro x
  apply PiLp.ext
  intro i
  exact Fin.elim0 i

/-- The completed history retains the input in its survivor coordinate when
there are no Euler steps. -/
theorem completedRectangularBoundaryColumn_nil_apply
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (x : H) :
    completedRectangularBoundaryColumn
        ([] : List
          (CCM24FiniteSJuliaCoDefect.RectangularSchurCoDefectStepData H K)) x =
      WithLp.toLp 2 (x, 0) := by
  rw [completedRectangularBoundaryColumn_apply]
  simp only [List.map_nil, juliaSurvivor, ContinuousLinearMap.id_apply]
  have hzero : rectangularBoundaryDaggerColumn
      ([] : List
        (CCM24FiniteSJuliaCoDefect.RectangularSchurCoDefectStepData H K)) x =
      0 := by
    apply PiLp.ext
    intro i
    exact Fin.elim0 i
  apply congrArg (WithLp.toLp 2)
  exact Prod.ext rfl hzero

/-! ## Completed-history contraction -/

theorem completedRectangularBoundaryColumn_normSq_eq
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (steps : List (CCM24FiniteSJuliaCoDefect.RectangularSchurCoDefectStepData
      H K)) (x : H) :
    ‖completedRectangularBoundaryColumn steps x‖ ^ 2 =
      ‖juliaSurvivor
        (steps.map (fun step => step.toAdjointCoDefectJuliaStep)) x‖ ^ 2 +
      ‖rectangularBoundaryDaggerColumn steps x‖ ^ 2 := by
  rw [completedRectangularBoundaryColumn_apply]
  exact WithLp.prod_norm_sq_eq_of_L2 _

/-- The terminal survivor fills exactly the energy omitted by the defect
history.  Replacing the Julia defects by the smaller rectangular boundary
coordinates therefore preserves the constant-one contraction. -/
theorem completedRectangularBoundaryColumn_normSq_le
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (steps : List (CCM24FiniteSJuliaCoDefect.RectangularSchurCoDefectStepData
      H K)) (x : H) :
    ‖completedRectangularBoundaryColumn steps x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  let defectSteps :=
    steps.map (fun step => step.toAdjointCoDefectJuliaStep)
  have hboundary :
      ‖rectangularBoundaryDaggerColumn steps x‖ ^ 2 ≤
        juliaDefectEnergy defectSteps x := by
    have h := rectangularBoundaryDaggerColumn_normSq_le steps x
    simpa only [defectSteps, juliaDefectColumn_normSq_eq] using h
  rw [completedRectangularBoundaryColumn_normSq_eq]
  calc
    ‖juliaSurvivor defectSteps x‖ ^ 2 +
          ‖rectangularBoundaryDaggerColumn steps x‖ ^ 2 ≤
        ‖juliaSurvivor defectSteps x‖ ^ 2 +
          juliaDefectEnergy defectSteps x :=
      add_le_add_right hboundary _
    _ = juliaDefectEnergy defectSteps x +
          ‖juliaSurvivor defectSteps x‖ ^ 2 := add_comm _ _
    _ = ‖x‖ ^ 2 := juliaDefectEnergy_add_survivor_normSq defectSteps x

theorem completedRectangularBoundaryColumn_summable_normSq_of_summable_input
    {iota H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (steps : List (CCM24FiniteSJuliaCoDefect.RectangularSchurCoDefectStepData
      H K))
    (sourceBasis : HilbertBasis iota ℂ H)
    (input : H →L[ℂ] H)
    (hinput : Summable fun i => ‖input (sourceBasis i)‖ ^ 2) :
    Summable fun i =>
      ‖completedRectangularBoundaryColumn steps
        (input (sourceBasis i))‖ ^ 2 := by
  exact Summable.of_nonneg_of_le
    (fun i => sq_nonneg _)
    (fun i => completedRectangularBoundaryColumn_normSq_le steps
      (input (sourceBasis i))) hinput

theorem completedRectangularBoundaryColumn_tsum_normSq_le_of_summable_input
    {iota H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (steps : List (CCM24FiniteSJuliaCoDefect.RectangularSchurCoDefectStepData
      H K))
    (sourceBasis : HilbertBasis iota ℂ H)
    (input : H →L[ℂ] H)
    (hinput : Summable fun i => ‖input (sourceBasis i)‖ ^ 2) :
    (∑' i, ‖completedRectangularBoundaryColumn steps
        (input (sourceBasis i))‖ ^ 2) ≤
      ∑' i, ‖input (sourceBasis i)‖ ^ 2 := by
  have hcolumn :=
    completedRectangularBoundaryColumn_summable_normSq_of_summable_input
      steps sourceBasis input hinput
  exact hcolumn.tsum_le_tsum
    (fun i => completedRectangularBoundaryColumn_normSq_le steps
      (input (sourceBasis i))) hinput

/-- A contractive readout of the completed Schur history preserves the
Hilbert--Schmidt input energy.  Unlike the defect-only theorem, this statement
has the correct nonzero base channel for an empty suffix. -/
theorem completedRectangularBoundaryReadout_tsum_normSq_le
    {iota H K G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (steps : List (CCM24FiniteSJuliaCoDefect.RectangularSchurCoDefectStepData
      H K))
    (sourceBasis : HilbertBasis iota ℂ H)
    (input : H →L[ℂ] H)
    (hinput : Summable fun i => ‖input (sourceBasis i)‖ ^ 2)
    (readout : completedRectangularBoundaryCarrier steps →L[ℂ] G)
    (hreadout : ‖readout‖ ≤ 1) :
    (∑' i, ‖(readout ∘L completedRectangularBoundaryColumn steps ∘L input)
        (sourceBasis i)‖ ^ 2) ≤
      ∑' i, ‖input (sourceBasis i)‖ ^ 2 := by
  let column := completedRectangularBoundaryColumn steps ∘L input
  have hcolumn : Summable fun i => ‖column (sourceBasis i)‖ ^ 2 := by
    simpa only [column, ContinuousLinearMap.comp_apply] using
      completedRectangularBoundaryColumn_summable_normSq_of_summable_input
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
            ‖readout‖ * ‖column (sourceBasis i)‖ := readout.le_opNorm _
        _ ≤ 1 * ‖column (sourceBasis i)‖ := by
          exact mul_le_mul_of_nonneg_right hreadout (norm_nonneg _)
        _ = ‖column (sourceBasis i)‖ := one_mul _
    simpa only [ContinuousLinearMap.comp_apply] using
      (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hnorm
  calc
    (∑' i, ‖(readout ∘L completedRectangularBoundaryColumn steps ∘L input)
        (sourceBasis i)‖ ^ 2) =
        ∑' i, ‖(readout ∘L column) (sourceBasis i)‖ ^ 2 := by rfl
    _ ≤ ∑' i, ‖column (sourceBasis i)‖ ^ 2 :=
      hreadoutColumn.tsum_le_tsum hpoint hcolumn
    _ ≤ ∑' i, ‖input (sourceBasis i)‖ ^ 2 := by
      simpa only [column, ContinuousLinearMap.comp_apply] using
        completedRectangularBoundaryColumn_tsum_normSq_le_of_summable_input
          steps sourceBasis input hinput

/-! ## Quantitative readout bounds -/

/- A readout need not be contractive merely because the Julia history is.  The
   following version keeps its actual operator bound visible and is the form
   needed by source-specific terminal readouts whose norm is not yet known to
   be one. -/
theorem completedRectangularBoundaryReadout_tsum_normSq_le_of_norm_le
    {iota H K G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (steps : List (CCM24FiniteSJuliaCoDefect.RectangularSchurCoDefectStepData
      H K))
    (sourceBasis : HilbertBasis iota ℂ H)
    (input : H →L[ℂ] H)
    (hinput : Summable fun i => ‖input (sourceBasis i)‖ ^ 2)
    (readout : completedRectangularBoundaryCarrier steps →L[ℂ] G)
    (bound : ℝ) (hbound : 0 ≤ bound) (hreadout : ‖readout‖ ≤ bound) :
    (∑' i, ‖(readout ∘L completedRectangularBoundaryColumn steps ∘L input)
        (sourceBasis i)‖ ^ 2) ≤
      bound ^ 2 * (∑' i, ‖input (sourceBasis i)‖ ^ 2) := by
  let column := completedRectangularBoundaryColumn steps ∘L input
  have hcolumn : Summable fun i => ‖column (sourceBasis i)‖ ^ 2 := by
    simpa only [column, ContinuousLinearMap.comp_apply] using
      completedRectangularBoundaryColumn_summable_normSq_of_summable_input
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
    (∑' i, ‖(readout ∘L completedRectangularBoundaryColumn steps ∘L input)
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
            completedRectangularBoundaryColumn_tsum_normSq_le_of_summable_input
              steps sourceBasis input hinput)
        (sq_nonneg bound)

/-! ## Component readout factorization -/

/-- Combine a terminal-survivor readout and a raw boundary-dagger readout on
the completed history carrier.  The two maps are kept separate until the
`WithLp` product is formed, so a source producer cannot silently replace the
terminal channel by the defect-only history. -/
noncomputable def completedRectangularBoundaryReadoutOfComponents
    {H K G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (steps : List
      (CCM24FiniteSJuliaCoDefect.RectangularSchurCoDefectStepData H K))
    (terminalReadout : H →L[ℂ] G)
    (boundaryReadout : PiLp 2
      (fun _ : Fin (steps.map
        (fun step => step.toAdjointCoDefectJuliaStep)).length => K) →L[ℂ] G) :
    completedRectangularBoundaryCarrier steps →L[ℂ] G :=
  (ContinuousLinearMap.coprod terminalReadout boundaryReadout) ∘L
    (WithLp.prodContinuousLinearEquiv 2 ℂ H
      (PiLp 2 (fun _ : Fin (steps.map
        (fun step => step.toAdjointCoDefectJuliaStep)).length => K))).toContinuousLinearMap

@[simp]
theorem completedRectangularBoundaryReadoutOfComponents_apply
    {H K G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (steps : List
      (CCM24FiniteSJuliaCoDefect.RectangularSchurCoDefectStepData H K))
    (terminalReadout : H →L[ℂ] G)
    (boundaryReadout : PiLp 2
      (fun _ : Fin (steps.map
        (fun step => step.toAdjointCoDefectJuliaStep)).length => K) →L[ℂ] G)
    (x : completedRectangularBoundaryCarrier steps) :
    completedRectangularBoundaryReadoutOfComponents steps terminalReadout
        boundaryReadout x =
      terminalReadout x.fst + boundaryReadout x.snd := by
  change terminalReadout (WithLp.fst x) + boundaryReadout (WithLp.snd x) = _
  rfl

/-- The component equations are exactly sufficient to recover the complete
physical-column factorization.  This is an algebraic bridge only: the two
component equations and the final readout norm remain source obligations. -/
theorem completedRectangularBoundaryReadoutOfComponents_comp_column_eq_add
    {H K G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (steps : List
      (CCM24FiniteSJuliaCoDefect.RectangularSchurCoDefectStepData H K))
    (sourceInput : H →L[ℂ] H)
    (terminalReadout : H →L[ℂ] G)
    (boundaryReadout : PiLp 2
      (fun _ : Fin (steps.map
        (fun step => step.toAdjointCoDefectJuliaStep)).length => K) →L[ℂ] G)
    (terminalColumn boundaryColumn : H →L[ℂ] G)
    (hterminal : terminalReadout ∘L
        juliaSurvivor
          (steps.map (fun step => step.toAdjointCoDefectJuliaStep)) ∘L
          sourceInput = terminalColumn)
    (hboundary : boundaryReadout ∘L rectangularBoundaryDaggerColumn steps ∘L
        sourceInput = boundaryColumn) :
    completedRectangularBoundaryReadoutOfComponents steps terminalReadout
        boundaryReadout ∘L completedRectangularBoundaryColumn steps ∘L
        sourceInput = terminalColumn + boundaryColumn := by
  apply ContinuousLinearMap.ext
  intro x
  have hterminalPoint := congrArg
    (fun operator : H →L[ℂ] G => operator x) hterminal
  have hboundaryPoint := congrArg
    (fun operator : H →L[ℂ] G => operator x) hboundary
  change terminalReadout
      (juliaSurvivor
        (steps.map (fun step => step.toAdjointCoDefectJuliaStep))
        (sourceInput x)) +
      boundaryReadout (rectangularBoundaryDaggerColumn steps (sourceInput x)) =
    terminalColumn x + boundaryColumn x
  have hterminalPoint' :
      terminalReadout
          (juliaSurvivor
            (steps.map (fun step => step.toAdjointCoDefectJuliaStep))
            (sourceInput x)) = terminalColumn x := by
    simpa only [ContinuousLinearMap.comp_apply] using hterminalPoint
  have hboundaryPoint' :
      boundaryReadout (rectangularBoundaryDaggerColumn steps (sourceInput x)) =
        boundaryColumn x := by
    simpa only [ContinuousLinearMap.comp_apply] using hboundaryPoint
  rw [hterminalPoint', hboundaryPoint']


/-! ## Gate-facing completed-history consumer -/

/-- The corrected actual-Schur readout controls the unresolved Proof 492
physical column.  The readout sees the terminal survivor and the boundary
history together, so the statement remains meaningful for the empty family. -/
theorem sourceActualBandCombinedPhysicalRightEnergy_le_of_completedActualSchurReadout
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
    (readout : completedRectangularBoundaryCarrier
      (suffixActualSchurFrameSteps lambda stepData family.visiblePrimes) →L[ℂ]
        commonBoundaryCarrier a c)
    (hreadout : ‖readout‖ ≤ 1)
    (hphysical :
      (sourceThreeBranchPairData owner lambda a c hac hsupp negativeBasis
          positiveBasis outputBasis reflectedNegativeBasis
          reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor).right
          ∘L sourceActualBandForwardEndpointCoframe lambda family =
        readout ∘L completedRectangularBoundaryColumn
          (suffixActualSchurFrameSteps lambda stepData family.visiblePrimes) ∘L
            sourceInput) :
    sourceActualBandCombinedPhysicalRightEnergy owner lambda family a c hac
        hsupp negativeBasis positiveBasis outputBasis reflectedNegativeBasis
        reflectedPositiveBasis reflectedOutputBasis globalBasis sourceBasis
        hfactor ≤
      ∑' i, ‖sourceInput (sourceBasis i)‖ ^ 2 := by
  have henergy := completedRectangularBoundaryReadout_tsum_normSq_le
    (steps := suffixActualSchurFrameSteps lambda stepData family.visiblePrimes)
    sourceBasis sourceInput hinput readout hreadout
  have hphysicalApply : ∀ i,
      (readout ∘L completedRectangularBoundaryColumn
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
        ∑' i, ‖(readout ∘L completedRectangularBoundaryColumn
            (suffixActualSchurFrameSteps lambda stepData family.visiblePrimes) ∘L
              sourceInput) (sourceBasis i)‖ ^ 2 := by
      apply tsum_congr
      intro i
      rw [hphysicalApply i]
    _ ≤ ∑' i, ‖sourceInput (sourceBasis i)‖ ^ 2 := henergy

set_option maxHeartbeats 4000000 in
-- Elaborating the fully concrete Gate-facing carrier tuple is expensive.
/-- Once the completed source history has fixed physical energy, Proof 494's
same-object raw-remainder consumer gives the family-independent trace bound.
The only source-specific premise is the completed-history readout identity. -/
theorem lowerFactorGaugedActualBandCompletedRelativeResponse_trace_norm_le_of_completedHistory
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
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      CCM24FiniteSActualJuliaInput.SuffixPrimeEulerProjectedJuliaSchurFrameStepData
        lambda (commonBoundaryCarrier a c) p S)
    (sourceInput : sourceSoninCarrier lambda →L[ℂ]
      sourceSoninCarrier lambda)
    (hinput : Summable fun i => ‖sourceInput (sourceBasis i)‖ ^ 2)
    (hinputEnergy : (∑' i, ‖sourceInput (sourceBasis i)‖ ^ 2) ≤
      fixedPhysicalEnergyMajorant owner lambda a c globalBasis)
    (readout : completedRectangularBoundaryCarrier
      (suffixActualSchurFrameSteps lambda stepData family.visiblePrimes) →L[ℂ]
        commonBoundaryCarrier a c)
    (hreadout : ‖readout‖ ≤ 1)
    (hphysical :
      (sourceThreeBranchPairData owner lambda a c hac hsupp negativeBasis
          positiveBasis outputBasis reflectedNegativeBasis
          reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor).right
          ∘L sourceActualBandForwardEndpointCoframe lambda family =
        readout ∘L completedRectangularBoundaryColumn
          (suffixActualSchurFrameSteps lambda stepData family.visiblePrimes) ∘L
            sourceInput) :
    ‖ordinaryTraceAlong sourceBasis
        (CCM24FiniteSRawCompletedGaugeOwner.lowerFactorGaugedActualBandCompletedRelativeResponse
          owner lambda family)‖ ≤
      2 * fixedPhysicalEnergyMajorant owner lambda a c globalBasis := by
  apply
    lowerFactorGaugedActualBandCompletedRelativeResponse_trace_norm_le_of_combinedEnergy
      owner lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis sourceBasis hfactor
  exact
    (sourceActualBandCombinedPhysicalRightEnergy_le_of_completedActualSchurReadout
      owner lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis sourceBasis hfactor stepData sourceInput hinput readout
      hreadout hphysical).trans hinputEnergy

end CCM24FiniteSCompletedPhysicalHistory
end CCM25Concrete
end Source
end ConnesWeilRH
