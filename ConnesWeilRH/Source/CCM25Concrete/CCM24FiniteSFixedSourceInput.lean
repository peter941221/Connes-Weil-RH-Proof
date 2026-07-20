/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSFixedSourcePolar
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSInputSideTraceConsumer
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCoDefectConsumer
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSJuliaCoDefect
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSActualSchurCascade

/-!
# Fixed-source input-side package

The generic input-side consumer already knows how to turn a Julia range column
and a finite coordinate readout into a Douglas-aligned root.  This module feeds
it the actual suffix-generated cascade after the polar carrier correction, but
only after the input-side base has already been aligned to the fixed source
carrier.  The physical boundary-to-source alignment and the boundary-column
equality remain explicit source obligations; Gate 3U cancellation is not
silently assumed.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSFixedSourceInput

open CC20Concrete
open _root_.ConnesWeilRH.CC20Concrete
open CC20Concrete.CompactConvolutionSupport
open CC20Concrete.CompactRootHalfLinePair
open MeasureTheory
open RCLike
open CCM24FiniteSActualJuliaInput
open CCM24FiniteSBandTrace
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSFixedSourcePolar
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSInputSideTraceConsumer
open CCM24FiniteSJuliaBessel
open CCM24FiniteSJuliaCausal
open CCM24FiniteSJuliaSchur
open CCM24FiniteSJuliaCoDefect
open CCM24FiniteSCoDefectConsumer
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSProjectionTrace
open CCM24SourceProlateTrace
open scoped InnerProduct InnerProductSpace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-!
An actual suffix-generated fixed-source readout package.  The `stepData` field
is the physical per-suffix input; the readout is indexed by the generated
fixed-source Julia column, not by an unrelated bookkeeping list.
-/
structure SuffixFixedSourceJuliaCoordinateReadoutData
    (lambda : CCM24SoninScale) {ι G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda))
    (S : List CCM24VisiblePrime) where
  /-- This base is already aligned to the fixed source carrier. -/
  base : InputSideRootS2Producer
    (K := sourceSoninCarrier lambda) (G := G) sourceBasis
  stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
    SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S
  physicalColumn_eq_readout :
    base.rightFactor ∘L base.root ∘L base.rightInput =
      inputSidePiLpReadoutSum
          (fixedSourceCurrentRangeJuliaReadout lambda stepData S) ∘L
      (juliaRangeColumn
          (currentRangeJuliaSteps
            (fixedSourceCurrentRangeJuliaSteps lambda stepData
              S)) ∘L
          base.root ∘L base.rightInput)

/-!
This companion package stores the exact operator-level condition needed by
Douglas, without storing a factor or a coordinate readout.  Its step list is
still the suffix-generated fixed-source cascade, so the carrier and the
chronological suffix are fixed by construction.
-/
structure SuffixFixedSourceJuliaOperatorDominationData
    (lambda : CCM24SoninScale) {ι G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda))
    (S : List CCM24VisiblePrime) where
  base : InputSideRootS2Producer
    (K := sourceSoninCarrier lambda) (G := G) sourceBasis
  stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
    SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S
  factorBound : ℝ
  factorBound_nonneg : 0 ≤ factorBound
  operator_domination : ∀ x : sourceSoninCarrier lambda,
    ‖base.rightFactor (base.root (base.rightInput x))‖ ≤
      factorBound *
        ‖juliaRangeColumn
          (currentRangeJuliaSteps
            (fixedSourceCurrentRangeJuliaSteps lambda stepData S))
          (base.root (base.rightInput x))‖

noncomputable def SuffixFixedSourceJuliaOperatorDominationData.toDouglas
    {lambda : CCM24SoninScale} {ι G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda)}
    {S : List CCM24VisiblePrime}
    (data : SuffixFixedSourceJuliaOperatorDominationData
      (G := G) lambda sourceBasis S) :
    DouglasAlignedInputSideRootS2Producer
      (K := sourceSoninCarrier lambda) (G := G) sourceBasis :=
  douglasAlignedInputSideRootS2ProducerOfOperatorDomination
    (ι := ι) (H := sourceSoninCarrier lambda)
    (K := sourceSoninCarrier lambda) (G := G)
    (sourceBasis := sourceBasis) data.base
    (currentRangeJuliaSteps
      (fixedSourceCurrentRangeJuliaSteps lambda data.stepData S))
    data.factorBound data.factorBound_nonneg data.operator_domination

theorem SuffixFixedSourceJuliaOperatorDominationData.toDouglas_rangeColumn
    {lambda : CCM24SoninScale} {ι G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda)}
    {S : List CCM24VisiblePrime}
    (data : SuffixFixedSourceJuliaOperatorDominationData
      (G := G) lambda sourceBasis S) :
    data.toDouglas.rangeColumn =
      juliaRangeColumn
        (currentRangeJuliaSteps
          (fixedSourceCurrentRangeJuliaSteps lambda data.stepData S)) ∘L
        data.base.root ∘L data.base.rightInput := by
  rfl

theorem SuffixFixedSourceJuliaOperatorDominationData.ordinaryTrace_norm_le
    {lambda : CCM24SoninScale} {ι G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda)}
    {S : List CCM24VisiblePrime}
    (data : SuffixFixedSourceJuliaOperatorDominationData
      (G := G) lambda sourceBasis S) :
    ‖CC20Concrete.PositiveTrace.ordinaryTraceAlong sourceBasis
        data.base.response‖ ≤
      (1 / 2 : ℝ) *
        (‖data.base.leftFactor‖ ^ 2 *
            (∑' i, ‖data.base.root
              (data.base.leftInput (sourceBasis i))‖ ^ 2) +
          data.factorBound ^ 2 *
            (∑' i, ‖data.base.root
              (data.base.rightInput (sourceBasis i))‖ ^ 2)) := by
  simpa only [SuffixFixedSourceJuliaOperatorDominationData.toDouglas] using
    (douglasAlignedInputSideRootS2Producer_ordinaryTrace_norm_le data.toDouglas)

/-!
The co-defect-side fixed-source package mirrors the range-column package, but
uses the adjoint Schur schedule generated by
`suffixFixedSourceJuliaCoDefectSteps`.  The physical left column is required
to dominate that genuine co-defect column on the full source carrier.
-/
structure SuffixFixedSourceCoDefectOperatorDominationData
    (lambda : CCM24SoninScale) {ι G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda))
    (S : List CCM24VisiblePrime) where
  base : InputSideRootS2Producer
    (K := sourceSoninCarrier lambda) (G := G) sourceBasis
  stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
    SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S
  defectFactorBound : ℝ
  defectFactorBound_nonneg : 0 ≤ defectFactorBound
  operator_domination : ∀ x : sourceSoninCarrier lambda,
    ‖base.leftFactor (base.root (base.leftInput x))‖ ≤
      defectFactorBound *
        ‖juliaDefectColumn
          (suffixFixedSourceJuliaCoDefectSteps lambda stepData S)
          (base.root (base.leftInput x))‖

noncomputable def SuffixFixedSourceCoDefectOperatorDominationData.toProducer
    {lambda : CCM24SoninScale} {ι G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda)}
    {S : List CCM24VisiblePrime}
    (data : SuffixFixedSourceCoDefectOperatorDominationData
      (G := G) lambda sourceBasis S) :
    CoDefectAlignedInputSideRootS2Producer
      (K := sourceSoninCarrier lambda) (D := sourceSoninCarrier lambda)
      (G := G) sourceBasis :=
  CoDefectAlignedInputSideRootS2Producer.ofNormDomination
    (K := sourceSoninCarrier lambda) (D := sourceSoninCarrier lambda) (G := G)
    data.base
    (suffixFixedSourceJuliaCoDefectSteps lambda data.stepData S)
    data.defectFactorBound data.defectFactorBound_nonneg
    data.operator_domination

theorem SuffixFixedSourceCoDefectOperatorDominationData.toProducer_defectSteps
    {lambda : CCM24SoninScale} {ι G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda)}
    {S : List CCM24VisiblePrime}
    (data : SuffixFixedSourceCoDefectOperatorDominationData
      (G := G) lambda sourceBasis S) :
    data.toProducer.defectSteps =
      suffixFixedSourceJuliaCoDefectSteps lambda data.stepData S := by
  rfl

theorem SuffixFixedSourceCoDefectOperatorDominationData.ordinaryTrace_norm_le
    {lambda : CCM24SoninScale} {ι G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda)}
    {S : List CCM24VisiblePrime}
    (data : SuffixFixedSourceCoDefectOperatorDominationData
      (G := G) lambda sourceBasis S) :
    ‖CC20Concrete.PositiveTrace.ordinaryTraceAlong sourceBasis
        data.base.response‖ ≤
      (1 / 2 : ℝ) *
        (data.defectFactorBound ^ 2 *
            (∑' i, ‖data.base.root
              (data.base.leftInput (sourceBasis i))‖ ^ 2) +
          ‖data.base.rightFactor‖ ^ 2 *
            (∑' i, ‖data.base.root
              (data.base.rightInput (sourceBasis i))‖ ^ 2)) := by
  simpa only [SuffixFixedSourceCoDefectOperatorDominationData.toProducer] using
    (coDefectAlignedInputSideRootS2Producer_ordinaryTrace_norm_le
      data.toProducer)

/-!
The actual consecutive-frame owner is a separate route entry point.  It does
not reuse the suffix Schur-frame adapter above: its history is built from the
genuine normalized Schur transport between the `p :: S` and `S` polar frames.
The remaining physical producer obligation is therefore stated against the
correct co-defect column and cannot be discharged by a single-slice norm
bound.
-/

structure SuffixFixedSourceActualCoDefectOperatorDominationData
    (lambda : CCM24SoninScale) {ι G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda))
    (S : List CCM24VisiblePrime) where
  base : InputSideRootS2Producer
    (K := sourceSoninCarrier lambda) (G := G) sourceBasis
  stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
    SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S
  defectFactorBound : ℝ
  defectFactorBound_nonneg : 0 ≤ defectFactorBound
  operator_domination : ∀ x : sourceSoninCarrier lambda,
    ‖base.leftFactor (base.root (base.leftInput x))‖ ≤
      defectFactorBound *
        ‖juliaDefectColumn
          (suffixActualSchurCoDefectSteps lambda stepData S)
          (base.root (base.leftInput x))‖

/-!
The actual cascade supplies a norm-one map from its co-defect history to the
packed boundary-dagger history.  This constructor keeps the physical signed
ledger as one readout of that packed boundary column and derives the old
pointwise domination field automatically.
-/

noncomputable def SuffixFixedSourceActualCoDefectOperatorDominationData.ofBoundaryReadout
    {lambda : CCM24SoninScale} {ι G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda)}
    {S : List CCM24VisiblePrime}
    (base : InputSideRootS2Producer
      (K := sourceSoninCarrier lambda) (G := G) sourceBasis)
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (factorBound : ℝ) (factorBound_nonneg : 0 ≤ factorBound)
    (readout : PiLp 2
      (fun _ : Fin (suffixActualSchurCoDefectSteps lambda stepData S).length =>
        finiteSCarrier) →L[ℂ] G)
    (readout_norm_le : ‖readout‖ ≤ factorBound)
    (physicalColumn_eq_readout :
      base.leftFactor ∘L base.root ∘L base.leftInput =
        readout ∘L
          rectangularBoundaryDaggerColumn
            (suffixActualSchurFrameSteps lambda stepData S) ∘L
          base.root ∘L base.leftInput) :
    SuffixFixedSourceActualCoDefectOperatorDominationData
      (G := G) lambda sourceBasis S := by
  let cascade := suffixActualSchurBoundaryCoDefectFactor lambda stepData S
  let defectFactor := readout ∘L cascade.factor
  have hfactor_norm_le : ‖defectFactor‖ ≤ factorBound := by
    calc
      ‖defectFactor‖ ≤ ‖readout‖ * ‖cascade.factor‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ factorBound * 1 := by
        exact mul_le_mul readout_norm_le cascade.factor_norm_le_one
          (norm_nonneg _) factorBound_nonneg
      _ = factorBound := by ring
  have hfactorization :
      base.leftFactor ∘L base.root ∘L base.leftInput =
        defectFactor ∘L
          (juliaDefectColumn
            (suffixActualSchurCoDefectSteps lambda stepData S) ∘L
            base.root ∘L base.leftInput) := by
    calc
      base.leftFactor ∘L base.root ∘L base.leftInput =
          readout ∘L
            rectangularBoundaryDaggerColumn
              (suffixActualSchurFrameSteps lambda stepData S) ∘L
            base.root ∘L base.leftInput := physicalColumn_eq_readout
      _ = readout ∘L cascade.factor ∘L
            (juliaDefectColumn
              (suffixActualSchurCoDefectSteps lambda stepData S) ∘L
              base.root ∘L base.leftInput) := by
        rw [← cascade.factorization]
        rfl
      _ = defectFactor ∘L
            (juliaDefectColumn
              (suffixActualSchurCoDefectSteps lambda stepData S) ∘L
              base.root ∘L base.leftInput) := by
        rfl
  refine
    { base := base
      stepData := stepData
      defectFactorBound := factorBound
      defectFactorBound_nonneg := factorBound_nonneg
      operator_domination := ?_ }
  intro x
  have hpoint := congrArg (fun T : sourceSoninCarrier lambda →L[ℂ] G => T x)
    hfactorization
  rw [show base.leftFactor (base.root (base.leftInput x)) =
      defectFactor
        (juliaDefectColumn
          (suffixActualSchurCoDefectSteps lambda stepData S)
          (base.root (base.leftInput x))) by
        simpa only [ContinuousLinearMap.comp_apply] using hpoint]
  calc
    ‖defectFactor
        (juliaDefectColumn
          (suffixActualSchurCoDefectSteps lambda stepData S)
          (base.root (base.leftInput x)))‖ ≤
        ‖defectFactor‖ *
          ‖juliaDefectColumn
            (suffixActualSchurCoDefectSteps lambda stepData S)
            (base.root (base.leftInput x))‖ :=
      defectFactor.le_opNorm _
    _ ≤ factorBound *
        ‖juliaDefectColumn
          (suffixActualSchurCoDefectSteps lambda stepData S)
          (base.root (base.leftInput x))‖ := by
      exact mul_le_mul_of_nonneg_right hfactor_norm_le (norm_nonneg _)

noncomputable def SuffixFixedSourceActualCoDefectOperatorDominationData.toProducer
    {lambda : CCM24SoninScale} {ι G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda)}
    {S : List CCM24VisiblePrime}
    (data : SuffixFixedSourceActualCoDefectOperatorDominationData
      (G := G) lambda sourceBasis S) :
    CoDefectAlignedInputSideRootS2Producer
      (K := sourceSoninCarrier lambda) (D := sourceSoninCarrier lambda)
      (G := G) sourceBasis :=
  CoDefectAlignedInputSideRootS2Producer.ofNormDomination
    (H := sourceSoninCarrier lambda) (K := sourceSoninCarrier lambda)
    (D := sourceSoninCarrier lambda) (G := G) data.base
    (suffixActualSchurCoDefectSteps lambda data.stepData S)
    data.defectFactorBound data.defectFactorBound_nonneg
    data.operator_domination

theorem SuffixFixedSourceActualCoDefectOperatorDominationData.toProducer_defectSteps
  {lambda : CCM24SoninScale} {ι G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda)}
    {S : List CCM24VisiblePrime}
    (data : SuffixFixedSourceActualCoDefectOperatorDominationData
      (G := G) lambda sourceBasis S) :
    data.toProducer.defectSteps =
      suffixActualSchurCoDefectSteps lambda data.stepData S := by
  rfl

theorem SuffixFixedSourceActualCoDefectOperatorDominationData.ordinaryTrace_norm_le
    {lambda : CCM24SoninScale} {ι G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda)}
    {S : List CCM24VisiblePrime}
    (data : SuffixFixedSourceActualCoDefectOperatorDominationData
      (G := G) lambda sourceBasis S) :
    ‖CC20Concrete.PositiveTrace.ordinaryTraceAlong sourceBasis
        data.base.response‖ ≤
      (1 / 2 : ℝ) *
        (data.defectFactorBound ^ 2 *
            (∑' i, ‖data.base.root
              (data.base.leftInput (sourceBasis i))‖ ^ 2) +
          ‖data.base.rightFactor‖ ^ 2 *
            (∑' i, ‖data.base.root
              (data.base.rightInput (sourceBasis i))‖ ^ 2)) := by
  simpa only [SuffixFixedSourceActualCoDefectOperatorDominationData.toProducer] using
    (coDefectAlignedInputSideRootS2Producer_ordinaryTrace_norm_le
      data.toProducer)

theorem sourceBandGramResponse_ordinaryTrace_norm_le_of_actualCoDefect
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    {ι G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda)}
    {S : List CCM24VisiblePrime}
    (data : SuffixFixedSourceActualCoDefectOperatorDominationData
      (G := G) lambda sourceBasis S)
    (hresponse : data.base.response =
      sourceBandGramResponse owner lambda family) :
    ‖CC20Concrete.PositiveTrace.ordinaryTraceAlong sourceBasis
        (sourceBandGramResponse owner lambda family)‖ ≤
      (1 / 2 : ℝ) *
        (data.defectFactorBound ^ 2 *
            (∑' i, ‖data.base.root
              (data.base.leftInput (sourceBasis i))‖ ^ 2) +
          ‖data.base.rightFactor‖ ^ 2 *
            (∑' i, ‖data.base.root
              (data.base.rightInput (sourceBasis i))‖ ^ 2)) := by
  rw [← hresponse]
  exact data.ordinaryTrace_norm_le

/-!
The physical root owner has a second, unavoidable carrier pattern.  Its root
may land in the common boundary carrier, while the actual Schur co-defect is
an operator on the fixed source carrier.  The source-input variant below keeps
those carriers distinct and applies the co-defect column to `base.leftInput`.
This is the type-correct interface for the complete signed ledger; it does not
silently identify the boundary root carrier with the source carrier.
-/
structure SuffixFixedSourceActualCoDefectSourceInputData
    (lambda : CCM24SoninScale) {ι K G : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda))
    (S : List CCM24VisiblePrime) where
  base : InputSideRootS2Producer
    (H := sourceSoninCarrier lambda) (K := K) (G := G) sourceBasis
  stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
    SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S
  defectFactorBound : ℝ
  defectFactorBound_nonneg : 0 ≤ defectFactorBound
  readout : PiLp 2
      (fun _ : Fin (suffixActualSchurCoDefectSteps lambda stepData S).length =>
        finiteSCarrier) →L[ℂ] G
  readout_norm_le : ‖readout‖ ≤ defectFactorBound
  physicalColumn_eq_readout :
    base.leftFactor ∘L base.root ∘L base.leftInput =
      readout ∘L
        rectangularBoundaryDaggerColumn
          (suffixActualSchurFrameSteps lambda stepData S) ∘L
        base.leftInput
  operator_domination : ∀ x : sourceSoninCarrier lambda,
    ‖base.leftFactor (base.root (base.leftInput x))‖ ≤
      defectFactorBound *
        ‖juliaDefectColumn
          (suffixActualSchurCoDefectSteps lambda stepData S)
          (base.leftInput x)‖
  column_energy_bound : ℝ
  column_energy_summable : Summable (fun i =>
    ‖juliaDefectColumn
        (suffixActualSchurCoDefectSteps lambda stepData S)
        (base.leftInput (sourceBasis i))‖ ^ 2)
  column_energy_bound_le :
    (∑' i, ‖juliaDefectColumn
        (suffixActualSchurCoDefectSteps lambda stepData S)
        (base.leftInput (sourceBasis i))‖ ^ 2) ≤
      column_energy_bound

/-!
This constructor is the carrier-correct analogue of
`ofBoundaryReadout`.  The readout sees the boundary-dagger column directly;
the physical Hilbert--Schmidt root is retained only on the left and right
energy ledgers.  The source obligation is now the correct trace-level
stable-coframe estimate: the complete co-defect column must be square
summable with one total bound.  No pointwise lower-frame comparison with the
compact root is assumed.
-/
noncomputable def SuffixFixedSourceActualCoDefectSourceInputData.ofBoundaryReadout
    {lambda : CCM24SoninScale} {ι K G : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda)}
    {S : List CCM24VisiblePrime}
    (base : InputSideRootS2Producer
      (H := sourceSoninCarrier lambda) (K := K) (G := G) sourceBasis)
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (factorBound : ℝ) (factorBound_nonneg : 0 ≤ factorBound)
    (readout : PiLp 2
      (fun _ : Fin (suffixActualSchurCoDefectSteps lambda stepData S).length =>
        finiteSCarrier) →L[ℂ] G)
    (readout_norm_le : ‖readout‖ ≤ factorBound)
    (physicalColumn_eq_readout :
      base.leftFactor ∘L base.root ∘L base.leftInput =
        readout ∘L
          rectangularBoundaryDaggerColumn
            (suffixActualSchurFrameSteps lambda stepData S) ∘L
          base.leftInput)
    (column_energy_bound : ℝ)
    (column_energy_summable : Summable (fun i =>
      ‖juliaDefectColumn
          (suffixActualSchurCoDefectSteps lambda stepData S)
          (base.leftInput (sourceBasis i))‖ ^ 2))
    (column_energy_bound_le :
      (∑' i, ‖juliaDefectColumn
          (suffixActualSchurCoDefectSteps lambda stepData S)
          (base.leftInput (sourceBasis i))‖ ^ 2) ≤
        column_energy_bound) :
    SuffixFixedSourceActualCoDefectSourceInputData
      (K := K) (G := G) lambda sourceBasis S := by
  let cascade := suffixActualSchurBoundaryCoDefectFactor lambda stepData S
  let defectFactor := readout ∘L cascade.factor
  have hfactor_norm_le : ‖defectFactor‖ ≤ factorBound := by
    calc
      ‖defectFactor‖ ≤ ‖readout‖ * ‖cascade.factor‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ factorBound * 1 := by
        exact mul_le_mul readout_norm_le cascade.factor_norm_le_one
          (norm_nonneg _) factorBound_nonneg
      _ = factorBound := by ring
  have hfactorization :
      base.leftFactor ∘L base.root ∘L base.leftInput =
        defectFactor ∘L
          (juliaDefectColumn
            (suffixActualSchurCoDefectSteps lambda stepData S) ∘L
            base.leftInput) := by
    calc
      base.leftFactor ∘L base.root ∘L base.leftInput =
          readout ∘L
            rectangularBoundaryDaggerColumn
              (suffixActualSchurFrameSteps lambda stepData S) ∘L
            base.leftInput := physicalColumn_eq_readout
      _ = readout ∘L cascade.factor ∘L
            (juliaDefectColumn
              (suffixActualSchurCoDefectSteps lambda stepData S) ∘L
              base.leftInput) := by
        rw [← cascade.factorization]
        rfl
      _ = defectFactor ∘L
            (juliaDefectColumn
              (suffixActualSchurCoDefectSteps lambda stepData S) ∘L
              base.leftInput) := by
        rfl
  refine
    { base := base
      stepData := stepData
      defectFactorBound := factorBound
      defectFactorBound_nonneg := factorBound_nonneg
      readout := readout
      readout_norm_le := readout_norm_le
      physicalColumn_eq_readout := physicalColumn_eq_readout
      operator_domination := ?_
      column_energy_summable := column_energy_summable
      column_energy_bound := column_energy_bound
      column_energy_bound_le := column_energy_bound_le }
  intro x
  have hpoint := congrArg
      (fun T : sourceSoninCarrier lambda →L[ℂ] G => T x) hfactorization
  rw [show base.leftFactor (base.root (base.leftInput x)) =
      defectFactor
        (juliaDefectColumn
          (suffixActualSchurCoDefectSteps lambda stepData S)
          (base.leftInput x)) by
        simpa only [ContinuousLinearMap.comp_apply] using hpoint]
  calc
    ‖defectFactor
        (juliaDefectColumn
          (suffixActualSchurCoDefectSteps lambda stepData S)
          (base.leftInput x))‖ ≤
        ‖defectFactor‖ *
          ‖juliaDefectColumn
            (suffixActualSchurCoDefectSteps lambda stepData S)
            (base.leftInput x)‖ :=
      defectFactor.le_opNorm _
    _ ≤ factorBound *
        ‖juliaDefectColumn
          (suffixActualSchurCoDefectSteps lambda stepData S)
          (base.leftInput x)‖ := by
      exact mul_le_mul_of_nonneg_right hfactor_norm_le (norm_nonneg _)

/-!
The column ledger can be generated from a genuine Hilbert--Schmidt source
input.  This is the only unconditional energy transfer available here: the
Julia defect column is contractive on each source vector, so its total square
sum is bounded by the input square sum.  The physical readout identity and
its uniform norm remain explicit in `ofBoundaryReadout`.
-/
noncomputable def SuffixFixedSourceActualCoDefectSourceInputData.ofBoundaryReadout_of_summableInput
    {lambda : CCM24SoninScale} {ι K G : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda)}
    {S : List CCM24VisiblePrime}
    (base : InputSideRootS2Producer
      (H := sourceSoninCarrier lambda) (K := K) (G := G) sourceBasis)
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (factorBound : ℝ) (factorBound_nonneg : 0 ≤ factorBound)
    (readout : PiLp 2
      (fun _ : Fin (suffixActualSchurCoDefectSteps lambda stepData S).length =>
        finiteSCarrier) →L[ℂ] G)
    (readout_norm_le : ‖readout‖ ≤ factorBound)
    (physicalColumn_eq_readout :
      base.leftFactor ∘L base.root ∘L base.leftInput =
        readout ∘L
          rectangularBoundaryDaggerColumn
            (suffixActualSchurFrameSteps lambda stepData S) ∘L
          base.leftInput)
    (hinput : Summable (fun i =>
      ‖base.leftInput (sourceBasis i)‖ ^ 2)) :
    SuffixFixedSourceActualCoDefectSourceInputData
      (K := K) (G := G) lambda sourceBasis S := by
  have hcolumn : Summable (fun i =>
      ‖juliaDefectColumn
          (suffixActualSchurCoDefectSteps lambda stepData S)
          (base.leftInput (sourceBasis i))‖ ^ 2) :=
    Summable.of_nonneg_of_le
      (fun i => sq_nonneg _)
      (fun i => juliaDefectColumn_normSq_le_normSq
        (suffixActualSchurCoDefectSteps lambda stepData S)
        (base.leftInput (sourceBasis i)))
      hinput
  exact SuffixFixedSourceActualCoDefectSourceInputData.ofBoundaryReadout
    base stepData factorBound factorBound_nonneg readout readout_norm_le
    physicalColumn_eq_readout
    (∑' i, ‖base.leftInput (sourceBasis i)‖ ^ 2)
    hcolumn
    (tsum_juliaDefectColumn_normSq_le sourceBasis
      (suffixActualSchurCoDefectSteps lambda stepData S)
      base.leftInput hinput)

/-!
The canonical common source input for a Hilbert--Schmidt pair is the positive
Gram square root

```text
  A = (left† left + right† right)^(1/2).
```

It lives on the source carrier itself.  Both physical legs factor through
`A` by Douglas with contraction norm at most one, and the named-basis energy
of `A` is exactly the sum of the two physical leg energies.  This removes the
carrier error caused by feeding an identity source input to the actual
Schur co-defect column.
-/

noncomputable def pairSourceGram
    {ι H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ H}
    (pair : CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := G) sourceBasis) :
    H →L[ℂ] H :=
  ContinuousLinearMap.adjoint pair.left ∘L pair.left +
    ContinuousLinearMap.adjoint pair.right ∘L pair.right

theorem pairSourceGram_nonneg
    {ι H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ H}
    (pair : CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := G) sourceBasis) :
    (0 : H →L[ℂ] H) ≤ pairSourceGram pair := by
  apply (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
  simpa only [pairSourceGram] using
    (ContinuousLinearMap.isPositive_adjoint_comp_self pair.left).add
      (ContinuousLinearMap.isPositive_adjoint_comp_self pair.right)

noncomputable def pairSourceGramSqrt
    {ι H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ H}
    (pair : CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := G) sourceBasis) :
    H →L[ℂ] H :=
  CFC.sqrt (pairSourceGram pair)

theorem pairSourceGramSqrt_isSelfAdjoint
    {ι H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ H}
    (pair : CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := G) sourceBasis) :
    IsSelfAdjoint (pairSourceGramSqrt pair) := by
  have hnonneg : (0 : H →L[ℂ] H) ≤ pairSourceGramSqrt pair := by
    exact CFC.sqrt_nonneg _
  exact (ContinuousLinearMap.nonneg_iff_isPositive _).mp hnonneg |>.isSelfAdjoint

theorem pairSourceGramSqrt_adjoint_comp_self
    {ι H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ H}
    (pair : CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := G) sourceBasis) :
    ContinuousLinearMap.adjoint (pairSourceGramSqrt pair) ∘L
        pairSourceGramSqrt pair =
      pairSourceGram pair := by
  have hself := pairSourceGramSqrt_isSelfAdjoint pair
  rw [hself.adjoint_eq, pairSourceGramSqrt, ← ContinuousLinearMap.mul_def]
  exact CFC.sqrt_mul_sqrt_self _ (pairSourceGram_nonneg pair)

theorem pairSourceGramSqrt_normSq_eq
    {ι H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ H}
    (pair : CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := G) sourceBasis) (x : H) :
    ‖pairSourceGramSqrt pair x‖ ^ 2 =
      ‖pair.left x‖ ^ 2 + ‖pair.right x‖ ^ 2 := by
  calc
    ‖pairSourceGramSqrt pair x‖ ^ 2 =
        re ⟪(ContinuousLinearMap.adjoint (pairSourceGramSqrt pair) ∘L
          pairSourceGramSqrt pair) x, x⟫_ℂ := by
      rw [ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_left]
    _ = re ⟪(pairSourceGram pair) x, x⟫_ℂ := by
      rw [pairSourceGramSqrt_adjoint_comp_self pair]
    _ = ‖pair.left x‖ ^ 2 + ‖pair.right x‖ ^ 2 := by
      simp only [pairSourceGram, ContinuousLinearMap.add_apply,
        inner_add_left, map_add, Complex.add_re]
      rw [← ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_left,
        ← ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_left]

theorem pairSourceGramSqrt_summable_normSq
    {ι H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ H}
    (pair : CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := G) sourceBasis) :
    Summable (fun i => ‖pairSourceGramSqrt pair (sourceBasis i)‖ ^ 2) := by
  apply (pair.left_summable_normSq.add pair.right_summable_normSq).congr
  intro i
  exact (pairSourceGramSqrt_normSq_eq pair (sourceBasis i)).symm

theorem pairSourceGramSqrt_left_normSq_le
    {ι H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ H}
    (pair : CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := G) sourceBasis) (x : H) :
    ‖pair.left x‖ ^ 2 ≤ ‖pairSourceGramSqrt pair x‖ ^ 2 := by
  calc
    ‖pair.left x‖ ^ 2 ≤
        ‖pair.left x‖ ^ 2 + ‖pair.right x‖ ^ 2 :=
      le_add_of_nonneg_right (sq_nonneg _)
    _ = ‖pairSourceGramSqrt pair x‖ ^ 2 :=
      (pairSourceGramSqrt_normSq_eq pair x).symm

theorem pairSourceGramSqrt_right_normSq_le
    {ι H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ H}
    (pair : CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := G) sourceBasis) (x : H) :
    ‖pair.right x‖ ^ 2 ≤ ‖pairSourceGramSqrt pair x‖ ^ 2 := by
  calc
    ‖pair.right x‖ ^ 2 ≤
        ‖pair.left x‖ ^ 2 + ‖pair.right x‖ ^ 2 :=
      le_add_of_nonneg_left (sq_nonneg _)
    _ = ‖pairSourceGramSqrt pair x‖ ^ 2 :=
      (pairSourceGramSqrt_normSq_eq pair x).symm

structure SourceGramInputFactorData
    {ι H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ H}
    (pair : CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := G) sourceBasis) where
  input : H →L[ℂ] H
  input_adjoint_comp_self :
    ContinuousLinearMap.adjoint input ∘L input = pairSourceGram pair
  input_summable_normSq : Summable fun i =>
    ‖input (sourceBasis i)‖ ^ 2
  leftFactor : H →L[ℂ] G
  rightFactor : H →L[ℂ] G
  leftFactor_norm_le_one : ‖leftFactor‖ ≤ 1
  rightFactor_norm_le_one : ‖rightFactor‖ ≤ 1
  leftFactorization : leftFactor ∘L input = pair.left
  rightFactorization : rightFactor ∘L input = pair.right

theorem SourceGramInputFactorData.input_normSq_eq
    {ι H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ H}
    {pair : CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := G) sourceBasis}
    (data : SourceGramInputFactorData pair) (x : H) :
    ‖data.input x‖ ^ 2 = ‖pair.left x‖ ^ 2 + ‖pair.right x‖ ^ 2 := by
  calc
    ‖data.input x‖ ^ 2 =
        re ⟪(ContinuousLinearMap.adjoint data.input ∘L data.input) x,
          x⟫_ℂ := by
      rw [ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_left]
    _ = re ⟪(pairSourceGram pair) x, x⟫_ℂ := by
      rw [data.input_adjoint_comp_self]
    _ = ‖pair.left x‖ ^ 2 + ‖pair.right x‖ ^ 2 := by
      simp only [pairSourceGram, ContinuousLinearMap.add_apply,
        inner_add_left, map_add, Complex.add_re]
      rw [← ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_left,
        ← ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_left]

noncomputable def SourceGramInputFactorData.ofPairData
    {ι H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ H}
    (pair : CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := G) sourceBasis) :
    SourceGramInputFactorData pair := by
  let input := pairSourceGramSqrt pair
  let leftWitness :=
    CCM24FiniteSDouglasFactor.exists_factor_of_norm_le
      pair.left input 1 (by norm_num) (by
        intro x
        have hnorm : ‖pair.left x‖ ≤ ‖input x‖ := by
          apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
          simpa only [input] using pairSourceGramSqrt_left_normSq_le pair x
        simpa only [one_mul] using hnorm)
  let leftFactor := Classical.choose leftWitness
  have leftSpec := Classical.choose_spec leftWitness
  let rightWitness :=
    CCM24FiniteSDouglasFactor.exists_factor_of_norm_le
      pair.right input 1 (by norm_num) (by
        intro x
        have hnorm : ‖pair.right x‖ ≤ ‖input x‖ := by
          apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
          simpa only [input] using pairSourceGramSqrt_right_normSq_le pair x
        simpa only [one_mul] using hnorm)
  let rightFactor := Classical.choose rightWitness
  have rightSpec := Classical.choose_spec rightWitness
  refine
    { input := input
      input_adjoint_comp_self := by
        simpa only [input] using pairSourceGramSqrt_adjoint_comp_self pair
      input_summable_normSq := by
        simpa only [input] using pairSourceGramSqrt_summable_normSq pair
      leftFactor := leftFactor
      rightFactor := rightFactor
      leftFactor_norm_le_one := by simpa using leftSpec.1
      rightFactor_norm_le_one := by simpa using rightSpec.1
      leftFactorization := leftSpec.2
      rightFactorization := rightSpec.2 }

@[simp]
theorem SourceGramInputFactorData.ofPairData_input
    {ι H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ H}
    (pair : CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := G) sourceBasis) :
    (SourceGramInputFactorData.ofPairData pair).input =
      pairSourceGramSqrt pair := by
  rfl

/-!
The direct pair consumer keeps the two physical legs on the same source
carrier.  The common input is supplied by `SourceGramInputFactorData`; each
leg has its own bounded readout from the actual rectangular boundary column.
No Julia range row or identity-input bookkeeping is part of this owner.
-/
structure SuffixFixedSourceActualCoDefectPairReadoutData
    (lambda : CCM24SoninScale) {ι G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda))
    (S : List CCM24VisiblePrime) where
  pair : CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
    (G := G) sourceBasis
  stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
    SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S
  gramInput : SourceGramInputFactorData pair
  leftReadout : PiLp 2
      (fun _ : Fin (suffixActualSchurCoDefectSteps lambda stepData S).length =>
        finiteSCarrier) →L[ℂ] G
  rightReadout : PiLp 2
      (fun _ : Fin (suffixActualSchurCoDefectSteps lambda stepData S).length =>
        finiteSCarrier) →L[ℂ] G
  factorBound : ℝ
  factorBound_nonneg : 0 ≤ factorBound
  leftReadout_norm_le : ‖leftReadout‖ ≤ factorBound
  rightReadout_norm_le : ‖rightReadout‖ ≤ factorBound
  left_eq_readout :
    pair.left =
      leftReadout ∘L
        rectangularBoundaryDaggerColumn
          (suffixActualSchurFrameSteps lambda stepData S) ∘L
        gramInput.input
  right_eq_readout :
    pair.right =
      rightReadout ∘L
        rectangularBoundaryDaggerColumn
          (suffixActualSchurFrameSteps lambda stepData S) ∘L
        gramInput.input

noncomputable def SuffixFixedSourceActualCoDefectPairReadoutData.ofPairData
    {lambda : CCM24SoninScale} {ι G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda)}
    {S : List CCM24VisiblePrime}
    (pair : CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := G) sourceBasis)
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (leftReadout rightReadout : PiLp 2
      (fun _ : Fin (suffixActualSchurCoDefectSteps lambda stepData S).length =>
        finiteSCarrier) →L[ℂ] G)
    (factorBound : ℝ) (factorBound_nonneg : 0 ≤ factorBound)
    (leftReadout_norm_le : ‖leftReadout‖ ≤ factorBound)
    (rightReadout_norm_le : ‖rightReadout‖ ≤ factorBound)
    (left_eq_readout :
      pair.left =
        leftReadout ∘L
          rectangularBoundaryDaggerColumn
            (suffixActualSchurFrameSteps lambda stepData S) ∘L
          pairSourceGramSqrt pair)
    (right_eq_readout :
      pair.right =
        rightReadout ∘L
          rectangularBoundaryDaggerColumn
            (suffixActualSchurFrameSteps lambda stepData S) ∘L
          pairSourceGramSqrt pair) :
    SuffixFixedSourceActualCoDefectPairReadoutData
      (G := G) lambda sourceBasis S := by
  let gramInput := SourceGramInputFactorData.ofPairData pair
  refine
    { pair := pair
      stepData := stepData
      gramInput := gramInput
      leftReadout := leftReadout
      rightReadout := rightReadout
      factorBound := factorBound
      factorBound_nonneg := factorBound_nonneg
      leftReadout_norm_le := leftReadout_norm_le
      rightReadout_norm_le := rightReadout_norm_le
      left_eq_readout := ?_
      right_eq_readout := ?_ }
  · simpa only [gramInput, SourceGramInputFactorData.ofPairData_input] using
      left_eq_readout
  · simpa only [gramInput, SourceGramInputFactorData.ofPairData_input] using
      right_eq_readout

noncomputable def SuffixFixedSourceActualCoDefectPairReadoutData.ofPairData_ofReadouts
    {lambda : CCM24SoninScale} {ι G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda)}
    {S : List CCM24VisiblePrime}
    (pair : CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := G) sourceBasis)
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (leftReadout rightReadout : PiLp 2
      (fun _ : Fin (suffixActualSchurCoDefectSteps lambda stepData S).length =>
        finiteSCarrier) →L[ℂ] G)
    (left_eq_readout :
      pair.left =
        leftReadout ∘L
          rectangularBoundaryDaggerColumn
            (suffixActualSchurFrameSteps lambda stepData S) ∘L
          pairSourceGramSqrt pair)
    (right_eq_readout :
      pair.right =
        rightReadout ∘L
          rectangularBoundaryDaggerColumn
            (suffixActualSchurFrameSteps lambda stepData S) ∘L
          pairSourceGramSqrt pair) :
    SuffixFixedSourceActualCoDefectPairReadoutData
      (G := G) lambda sourceBasis S :=
  SuffixFixedSourceActualCoDefectPairReadoutData.ofPairData
    pair stepData leftReadout rightReadout
    (max ‖leftReadout‖ ‖rightReadout‖)
    (by positivity)
    (le_max_left _ _)
    (le_max_right _ _) left_eq_readout right_eq_readout

/-!
The two physical legs have one common source geometry.  Pack them before
Douglas factorization so the source obligation is a single same-object
estimate rather than two independent lower bounds.  The coordinate readouts
below are contractions, so unpacking the factor does not introduce a
branchwise constant.
-/

noncomputable def sourcePairPackedColumn
    {lambda : CCM24SoninScale} {ι G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda)}
    (pair : CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := G) sourceBasis) :
    sourceSoninCarrier lambda →L[ℂ] WithLp 2 (G × G) :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ G G).symm.toContinuousLinearMap ∘L
    pair.left.prod pair.right

@[simp]
theorem sourcePairPackedColumn_apply
    {lambda : CCM24SoninScale} {ι G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda)}
    (pair : CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := G) sourceBasis) (x : sourceSoninCarrier lambda) :
    sourcePairPackedColumn pair x =
      WithLp.toLp 2 (pair.left x, pair.right x) := by
  simp [sourcePairPackedColumn]

theorem sourcePairPackedColumn_normSq_eq
    {lambda : CCM24SoninScale} {ι G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda)}
    (pair : CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := G) sourceBasis) (x : sourceSoninCarrier lambda) :
    ‖sourcePairPackedColumn pair x‖ ^ 2 =
      ‖pair.left x‖ ^ 2 + ‖pair.right x‖ ^ 2 := by
  rw [sourcePairPackedColumn_apply]
  exact WithLp.prod_norm_sq_eq_of_L2 _

noncomputable def sourcePairPackedLeftProjection
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G] :
    WithLp 2 (G × G) →L[ℂ] G :=
  WithLp.fstL (p := 2) (𝕜 := ℂ) (α := G) (β := G)

noncomputable def sourcePairPackedRightProjection
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G] :
    WithLp 2 (G × G) →L[ℂ] G :=
  WithLp.sndL (p := 2) (𝕜 := ℂ) (α := G) (β := G)

theorem sourcePairPackedLeftProjection_norm_le_one
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G] :
    ‖sourcePairPackedLeftProjection (G := G)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [sourcePairPackedLeftProjection, one_mul] using
    WithLp.norm_fst_le (α := G) (β := G) (p := 2) x

theorem sourcePairPackedRightProjection_norm_le_one
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G] :
    ‖sourcePairPackedRightProjection (G := G)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [sourcePairPackedRightProjection, one_mul] using
    WithLp.norm_snd_le (α := G) (β := G) (p := 2) x

theorem sourcePairPackedLeftProjection_comp_column
    {lambda : CCM24SoninScale} {ι G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda)}
    (pair : CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := G) sourceBasis) :
    sourcePairPackedLeftProjection ∘L sourcePairPackedColumn pair =
      pair.left := by
  apply ContinuousLinearMap.ext
  intro x
  simp [sourcePairPackedLeftProjection, sourcePairPackedColumn]

theorem sourcePairPackedRightProjection_comp_column
    {lambda : CCM24SoninScale} {ι G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda)}
    (pair : CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := G) sourceBasis) :
    sourcePairPackedRightProjection ∘L sourcePairPackedColumn pair =
      pair.right := by
  apply ContinuousLinearMap.ext
  intro x
  simp [sourcePairPackedRightProjection, sourcePairPackedColumn]

/-!
This is the common-readout form of the actual consumer.  It is deliberately
stronger than the two-leg constructor below: the physical pair must factor
through one packed readout, and the proof never estimates its coordinates
separately before the factorization is made.
-/
noncomputable def SuffixFixedSourceActualCoDefectPairReadoutData.ofPackedNormDomination
    {lambda : CCM24SoninScale} {ι G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda)}
    {S : List CCM24VisiblePrime}
    (pair : CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := G) sourceBasis)
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (factorBound : ℝ) (factorBound_nonneg : 0 ≤ factorBound)
    (packed_domination : ∀ x : sourceSoninCarrier lambda,
      ‖sourcePairPackedColumn pair x‖ ≤ factorBound *
        ‖rectangularBoundaryDaggerColumn
          (suffixActualSchurFrameSteps lambda stepData S)
          (pairSourceGramSqrt pair x)‖) :
    SuffixFixedSourceActualCoDefectPairReadoutData
      (G := G) lambda sourceBasis S := by
  let boundaryColumn : sourceSoninCarrier lambda →L[ℂ]
      PiLp 2
        (fun _ : Fin (suffixActualSchurCoDefectSteps lambda stepData S).length =>
          finiteSCarrier) :=
    rectangularBoundaryDaggerColumn
      (suffixActualSchurFrameSteps lambda stepData S) ∘L
      pairSourceGramSqrt pair
  let packedWitness :=
    CCM24FiniteSDouglasFactor.exists_factor_of_norm_le
      (sourcePairPackedColumn pair) boundaryColumn factorBound
      factorBound_nonneg (by
        intro x
        simpa only [boundaryColumn] using packed_domination x)
  let packedReadout := Classical.choose packedWitness
  have packedSpec := Classical.choose_spec packedWitness
  let leftReadout :
      PiLp 2
        (fun _ : Fin (suffixActualSchurCoDefectSteps lambda stepData S).length =>
          finiteSCarrier) →L[ℂ] G :=
    sourcePairPackedLeftProjection ∘L packedReadout
  let rightReadout :
      PiLp 2
        (fun _ : Fin (suffixActualSchurCoDefectSteps lambda stepData S).length =>
          finiteSCarrier) →L[ℂ] G :=
    sourcePairPackedRightProjection ∘L packedReadout
  have hleftNorm : ‖leftReadout‖ ≤ factorBound := by
    calc
      ‖leftReadout‖ ≤
          ‖sourcePairPackedLeftProjection‖ * ‖packedReadout‖ := by
        exact ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * factorBound := by
        exact mul_le_mul
          (sourcePairPackedLeftProjection_norm_le_one (G := G))
           packedSpec.1 (norm_nonneg _) zero_le_one
      _ = factorBound := one_mul _
  have hrightNorm : ‖rightReadout‖ ≤ factorBound := by
    calc
      ‖rightReadout‖ ≤
          ‖sourcePairPackedRightProjection‖ * ‖packedReadout‖ := by
        exact ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * factorBound := by
        exact mul_le_mul
          (sourcePairPackedRightProjection_norm_le_one (G := G))
           packedSpec.1 (norm_nonneg _) zero_le_one
      _ = factorBound := one_mul _
  have hleftPacked :
      sourcePairPackedLeftProjection ∘L sourcePairPackedColumn pair =
        pair.left := sourcePairPackedLeftProjection_comp_column pair
  have hrightPacked :
      sourcePairPackedRightProjection ∘L sourcePairPackedColumn pair =
        pair.right := sourcePairPackedRightProjection_comp_column pair
  have hleftFactorization : leftReadout ∘L boundaryColumn = pair.left := by
    calc
      leftReadout ∘L boundaryColumn =
          sourcePairPackedLeftProjection ∘L
            (packedReadout ∘L boundaryColumn) := by
        simp only [leftReadout, ContinuousLinearMap.comp_assoc]
      _ = sourcePairPackedLeftProjection ∘L
          sourcePairPackedColumn pair := by rw [packedSpec.2]
      _ = pair.left := hleftPacked
  have hrightFactorization : rightReadout ∘L boundaryColumn = pair.right := by
    calc
      rightReadout ∘L boundaryColumn =
          sourcePairPackedRightProjection ∘L
            (packedReadout ∘L boundaryColumn) := by
        simp only [rightReadout, ContinuousLinearMap.comp_assoc]
      _ = sourcePairPackedRightProjection ∘L
          sourcePairPackedColumn pair := by rw [packedSpec.2]
      _ = pair.right := hrightPacked
  exact SuffixFixedSourceActualCoDefectPairReadoutData.ofPairData
    pair stepData leftReadout rightReadout factorBound factorBound_nonneg
    hleftNorm hrightNorm (by
      simpa only [boundaryColumn, ContinuousLinearMap.comp_assoc] using
        hleftFactorization.symm) (by
      simpa only [boundaryColumn, ContinuousLinearMap.comp_assoc] using
        hrightFactorization.symm)

/-!
The readout can itself be produced by Douglas.  This version exposes the
source-facing obligation in its irreducible form: both physical legs must be
dominated on the whole source carrier by the same actual rectangular boundary
column.  Basis-only domination is deliberately not accepted.
-/
noncomputable def SuffixFixedSourceActualCoDefectPairReadoutData.ofNormDomination
    {lambda : CCM24SoninScale} {ι G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda)}
    {S : List CCM24VisiblePrime}
    (pair : CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := G) sourceBasis)
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (factorBound : ℝ) (factorBound_nonneg : 0 ≤ factorBound)
    (left_domination : ∀ x : sourceSoninCarrier lambda,
      ‖pair.left x‖ ≤ factorBound *
        ‖rectangularBoundaryDaggerColumn
          (suffixActualSchurFrameSteps lambda stepData S)
          (pairSourceGramSqrt pair x)‖)
    (right_domination : ∀ x : sourceSoninCarrier lambda,
      ‖pair.right x‖ ≤ factorBound *
        ‖rectangularBoundaryDaggerColumn
          (suffixActualSchurFrameSteps lambda stepData S)
          (pairSourceGramSqrt pair x)‖) :
    SuffixFixedSourceActualCoDefectPairReadoutData
      (G := G) lambda sourceBasis S := by
  let boundaryColumn : sourceSoninCarrier lambda →L[ℂ]
      PiLp 2
        (fun _ : Fin (suffixActualSchurCoDefectSteps lambda stepData S).length =>
          finiteSCarrier) :=
    rectangularBoundaryDaggerColumn
      (suffixActualSchurFrameSteps lambda stepData S) ∘L
      pairSourceGramSqrt pair
  let leftWitness :=
    CCM24FiniteSDouglasFactor.exists_factor_of_norm_le
      pair.left boundaryColumn factorBound factorBound_nonneg (by
        intro x
        simpa only [boundaryColumn] using left_domination x)
  let leftReadout := Classical.choose leftWitness
  have leftSpec := Classical.choose_spec leftWitness
  let rightWitness :=
    CCM24FiniteSDouglasFactor.exists_factor_of_norm_le
      pair.right boundaryColumn factorBound factorBound_nonneg (by
        intro x
        simpa only [boundaryColumn] using right_domination x)
  let rightReadout := Classical.choose rightWitness
  have rightSpec := Classical.choose_spec rightWitness
  exact SuffixFixedSourceActualCoDefectPairReadoutData.ofPairData
    pair stepData leftReadout rightReadout factorBound factorBound_nonneg
    leftSpec.1 rightSpec.1 (by
      simpa only [boundaryColumn, ContinuousLinearMap.comp_assoc] using
        leftSpec.2.symm) (by
      simpa only [boundaryColumn, ContinuousLinearMap.comp_assoc] using
        rightSpec.2.symm)

theorem SuffixFixedSourceActualCoDefectPairReadoutData.ordinaryTrace_norm_le
    {lambda : CCM24SoninScale} {ι G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda)}
    {S : List CCM24VisiblePrime}
    (data : SuffixFixedSourceActualCoDefectPairReadoutData
      (G := G) lambda sourceBasis S) :
    ‖CC20Concrete.PositiveTrace.ordinaryTraceAlong sourceBasis
        data.pair.traceProduct‖ ≤
      data.factorBound ^ 2 *
        (∑' i, (‖data.pair.left (sourceBasis i)‖ ^ 2 +
          ‖data.pair.right (sourceBasis i)‖ ^ 2)) := by
  have hinput : Summable (fun i =>
      ‖data.gramInput.input (sourceBasis i)‖ ^ 2) :=
    data.gramInput.input_summable_normSq
  have hmajorant : Summable (fun i =>
      data.factorBound ^ 2 *
        ‖data.gramInput.input (sourceBasis i)‖ ^ 2) :=
    hinput.mul_left (data.factorBound ^ 2)
  have htraceDiag : Summable (fun i =>
      ‖⟪sourceBasis i,
        data.pair.traceProduct (sourceBasis i)⟫_ℂ‖) :=
    data.pair.traceProduct_isTraceClassAlong.norm
  have hcolumn_norm : ∀ i,
      ‖rectangularBoundaryDaggerColumn
          (suffixActualSchurFrameSteps lambda data.stepData S)
          (data.gramInput.input (sourceBasis i))‖ ≤
        ‖data.gramInput.input (sourceBasis i)‖ := by
    intro i
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    calc
      ‖rectangularBoundaryDaggerColumn
          (suffixActualSchurFrameSteps lambda data.stepData S)
          (data.gramInput.input (sourceBasis i))‖ ^ 2 ≤
          ‖juliaDefectColumn
            ((suffixActualSchurFrameSteps lambda data.stepData S).map
              (fun step => step.toAdjointCoDefectJuliaStep))
            (data.gramInput.input (sourceBasis i))‖ ^ 2 :=
        rectangularBoundaryDaggerColumn_normSq_le
          (suffixActualSchurFrameSteps lambda data.stepData S)
          (data.gramInput.input (sourceBasis i))
      _ ≤ ‖data.gramInput.input (sourceBasis i)‖ ^ 2 :=
        juliaDefectColumn_normSq_le_normSq
          ((suffixActualSchurFrameSteps lambda data.stepData S).map
            (fun step => step.toAdjointCoDefectJuliaStep))
          (data.gramInput.input (sourceBasis i))
  have hleftPoint : ∀ i,
      ‖data.pair.left (sourceBasis i)‖ ^ 2 ≤
        data.factorBound ^ 2 *
          ‖data.gramInput.input (sourceBasis i)‖ ^ 2 := by
    intro i
    have hidentity := congrArg
      (fun T : sourceSoninCarrier lambda →L[ℂ] G => T (sourceBasis i))
      data.left_eq_readout
    have hnorm :
        ‖data.leftReadout
            (rectangularBoundaryDaggerColumn
              (suffixActualSchurFrameSteps lambda data.stepData S)
              (data.gramInput.input (sourceBasis i)))‖ ≤
          data.factorBound *
            ‖data.gramInput.input (sourceBasis i)‖ := by
      calc
        ‖data.leftReadout
            (rectangularBoundaryDaggerColumn
              (suffixActualSchurFrameSteps lambda data.stepData S)
              (data.gramInput.input (sourceBasis i)))‖ ≤
            ‖data.leftReadout‖ *
              ‖rectangularBoundaryDaggerColumn
                (suffixActualSchurFrameSteps lambda data.stepData S)
                (data.gramInput.input (sourceBasis i))‖ :=
          data.leftReadout.le_opNorm _
        _ ≤ data.factorBound *
              ‖rectangularBoundaryDaggerColumn
                (suffixActualSchurFrameSteps lambda data.stepData S)
                (data.gramInput.input (sourceBasis i))‖ := by
          exact mul_le_mul_of_nonneg_right data.leftReadout_norm_le
            (norm_nonneg _)
        _ ≤ data.factorBound *
              ‖data.gramInput.input (sourceBasis i)‖ := by
          exact mul_le_mul_of_nonneg_left (hcolumn_norm i)
            data.factorBound_nonneg
    rw [show data.pair.left (sourceBasis i) =
        data.leftReadout
          (rectangularBoundaryDaggerColumn
            (suffixActualSchurFrameSteps lambda data.stepData S)
            (data.gramInput.input (sourceBasis i))) by
          simpa only [ContinuousLinearMap.comp_apply] using hidentity]
    have hsq := (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg data.factorBound_nonneg (norm_nonneg _))).mpr hnorm
    simpa only [mul_pow] using hsq
  have hrightPoint : ∀ i,
      ‖data.pair.right (sourceBasis i)‖ ^ 2 ≤
        data.factorBound ^ 2 *
          ‖data.gramInput.input (sourceBasis i)‖ ^ 2 := by
    intro i
    have hidentity := congrArg
      (fun T : sourceSoninCarrier lambda →L[ℂ] G => T (sourceBasis i))
      data.right_eq_readout
    have hnorm :
        ‖data.rightReadout
            (rectangularBoundaryDaggerColumn
              (suffixActualSchurFrameSteps lambda data.stepData S)
              (data.gramInput.input (sourceBasis i)))‖ ≤
          data.factorBound *
            ‖data.gramInput.input (sourceBasis i)‖ := by
      calc
        ‖data.rightReadout
            (rectangularBoundaryDaggerColumn
              (suffixActualSchurFrameSteps lambda data.stepData S)
              (data.gramInput.input (sourceBasis i)))‖ ≤
            ‖data.rightReadout‖ *
              ‖rectangularBoundaryDaggerColumn
                (suffixActualSchurFrameSteps lambda data.stepData S)
                (data.gramInput.input (sourceBasis i))‖ :=
          data.rightReadout.le_opNorm _
        _ ≤ data.factorBound *
              ‖rectangularBoundaryDaggerColumn
                (suffixActualSchurFrameSteps lambda data.stepData S)
                (data.gramInput.input (sourceBasis i))‖ := by
          exact mul_le_mul_of_nonneg_right data.rightReadout_norm_le
            (norm_nonneg _)
        _ ≤ data.factorBound *
              ‖data.gramInput.input (sourceBasis i)‖ := by
          exact mul_le_mul_of_nonneg_left (hcolumn_norm i)
            data.factorBound_nonneg
    rw [show data.pair.right (sourceBasis i) =
        data.rightReadout
          (rectangularBoundaryDaggerColumn
            (suffixActualSchurFrameSteps lambda data.stepData S)
            (data.gramInput.input (sourceBasis i))) by
          simpa only [ContinuousLinearMap.comp_apply] using hidentity]
    have hsq := (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg data.factorBound_nonneg (norm_nonneg _))).mpr hnorm
    simpa only [mul_pow] using hsq
  have hpoint : ∀ i, ‖⟪sourceBasis i,
      data.pair.traceProduct (sourceBasis i)⟫_ℂ‖ ≤
      data.factorBound ^ 2 *
        ‖data.gramInput.input (sourceBasis i)‖ ^ 2 := by
    intro i
    rw [data.pair.traceProduct_diagonal]
    calc
      ‖⟪data.pair.left (sourceBasis i),
          data.pair.right (sourceBasis i)⟫_ℂ‖ ≤
          ‖data.pair.left (sourceBasis i)‖ *
            ‖data.pair.right (sourceBasis i)‖ :=
        norm_inner_le_norm _ _
      _ ≤ (1 / 2 : ℝ) *
          (‖data.pair.left (sourceBasis i)‖ ^ 2 +
            ‖data.pair.right (sourceBasis i)‖ ^ 2) := by
        nlinarith [sq_nonneg
          (‖data.pair.left (sourceBasis i)‖ -
            ‖data.pair.right (sourceBasis i)‖)]
      _ ≤ (1 / 2 : ℝ) *
          (data.factorBound ^ 2 *
              ‖data.gramInput.input (sourceBasis i)‖ ^ 2 +
            data.factorBound ^ 2 *
              ‖data.gramInput.input (sourceBasis i)‖ ^ 2) := by
        exact mul_le_mul_of_nonneg_left
          (add_le_add (hleftPoint i) (hrightPoint i)) (by norm_num)
      _ = data.factorBound ^ 2 *
          ‖data.gramInput.input (sourceBasis i)‖ ^ 2 := by ring
  have hinputEnergy :
      (∑' i, ‖data.gramInput.input (sourceBasis i)‖ ^ 2) =
        ∑' i, (‖data.pair.left (sourceBasis i)‖ ^ 2 +
          ‖data.pair.right (sourceBasis i)‖ ^ 2) := by
    apply tsum_congr
    intro i
    exact data.gramInput.input_normSq_eq (sourceBasis i)
  rw [CC20Concrete.PositiveTrace.ordinaryTraceAlong]
  calc
    ‖∑' i, ⟪sourceBasis i,
        data.pair.traceProduct (sourceBasis i)⟫_ℂ‖ ≤
        ∑' i, ‖⟪sourceBasis i,
          data.pair.traceProduct (sourceBasis i)⟫_ℂ‖ :=
      norm_tsum_le_tsum_norm htraceDiag
    _ ≤ ∑' i, data.factorBound ^ 2 *
        ‖data.gramInput.input (sourceBasis i)‖ ^ 2 :=
      htraceDiag.tsum_le_tsum hpoint hmajorant
    _ = data.factorBound ^ 2 *
        (∑' i, ‖data.gramInput.input (sourceBasis i)‖ ^ 2) := by
      rw [tsum_mul_left]
    _ = data.factorBound ^ 2 *
        (∑' i, (‖data.pair.left (sourceBasis i)‖ ^ 2 +
          ‖data.pair.right (sourceBasis i)‖ ^ 2)) := by
      rw [hinputEnergy]

theorem sourceBandGramResponse_ordinaryTrace_norm_le_of_actualPairReadout
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    {ι G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda)}
    {S : List CCM24VisiblePrime}
    (data : SuffixFixedSourceActualCoDefectPairReadoutData
      (G := G) lambda sourceBasis S)
    (hresponse : data.pair.traceProduct =
      sourceBandGramResponse owner lambda family) :
    ‖CC20Concrete.PositiveTrace.ordinaryTraceAlong sourceBasis
        (sourceBandGramResponse owner lambda family)‖ ≤
      data.factorBound ^ 2 *
        (∑' i, (‖data.pair.left (sourceBasis i)‖ ^ 2 +
          ‖data.pair.right (sourceBasis i)‖ ^ 2)) := by
  rw [← hresponse]
  exact data.ordinaryTrace_norm_le

/-!
The existing three-branch pair is now admitted only through an explicit pair
equality.  The returned owner uses the Gram input and the actual rectangular
Schur column; the old identity-input producer is not consulted.
-/
noncomputable def sourceThreeBranchActualCoDefectPairReadoutData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ tau ιr κr taur nu mu rho : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis tau ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis ιr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis κr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis taur ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis mu ℂ (commonBoundaryCarrier a c))
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    {S : List CCM24VisiblePrime}
    (pair : CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := commonBoundaryCarrier a c) sourceBasis)
    (hpair : pair = sourceThreeBranchSourcePairData owner lambda family a c
      hac hsupp negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
      sourceBasis hfactor)
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda
        (commonBoundaryCarrier a c) p S)
    (factorBound : ℝ) (factorBound_nonneg : 0 ≤ factorBound)
    (left_domination : ∀ x : sourceSoninCarrier lambda,
      ‖pair.left x‖ ≤ factorBound *
        ‖rectangularBoundaryDaggerColumn
          (suffixActualSchurFrameSteps lambda stepData S)
          (pairSourceGramSqrt pair x)‖)
    (right_domination : ∀ x : sourceSoninCarrier lambda,
      ‖pair.right x‖ ≤ factorBound *
        ‖rectangularBoundaryDaggerColumn
          (suffixActualSchurFrameSteps lambda stepData S)
          (pairSourceGramSqrt pair x)‖) :
    SuffixFixedSourceActualCoDefectPairReadoutData
      (G := commonBoundaryCarrier a c) lambda sourceBasis S :=
  SuffixFixedSourceActualCoDefectPairReadoutData.ofNormDomination
    pair stepData factorBound factorBound_nonneg left_domination
      right_domination

/-!
Route-facing packed variant.  The owner and pair equality are retained in the
signature so this constructor can replace the two-leg compatibility entry
without changing the concrete source ledger.
-/
noncomputable def sourceThreeBranchActualCoDefectPairReadoutData_ofPackedNormDomination
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ tau ιr κr taur nu mu rho : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis tau ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis ιr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis κr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis taur ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis mu ℂ (commonBoundaryCarrier a c))
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    {S : List CCM24VisiblePrime}
    (pair : CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := commonBoundaryCarrier a c) sourceBasis)
    (hpair : pair = sourceThreeBranchSourcePairData owner lambda family a c
      hac hsupp negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
      sourceBasis hfactor)
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda
        (commonBoundaryCarrier a c) p S)
    (factorBound : ℝ) (factorBound_nonneg : 0 ≤ factorBound)
    (packed_domination : ∀ x : sourceSoninCarrier lambda,
      ‖sourcePairPackedColumn pair x‖ ≤ factorBound *
        ‖rectangularBoundaryDaggerColumn
          (suffixActualSchurFrameSteps lambda stepData S)
          (pairSourceGramSqrt pair x)‖) :
    SuffixFixedSourceActualCoDefectPairReadoutData
      (G := commonBoundaryCarrier a c) lambda sourceBasis S :=
  SuffixFixedSourceActualCoDefectPairReadoutData.ofPackedNormDomination
    pair stepData factorBound factorBound_nonneg packed_domination

theorem sourceThreeBranchActualCoDefectPairReadoutData_ofPackedNormDomination_traceProduct_eq
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ tau ιr κr taur nu mu rho : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis tau ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis ιr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis κr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis taur ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis mu ℂ (commonBoundaryCarrier a c))
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    {S : List CCM24VisiblePrime}
    (pair : CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := commonBoundaryCarrier a c) sourceBasis)
    (hpair : pair = sourceThreeBranchSourcePairData owner lambda family a c
      hac hsupp negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
      sourceBasis hfactor)
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda
        (commonBoundaryCarrier a c) p S)
    (factorBound : ℝ) (factorBound_nonneg : 0 ≤ factorBound)
    (packed_domination : ∀ x : sourceSoninCarrier lambda,
      ‖sourcePairPackedColumn pair x‖ ≤ factorBound *
        ‖rectangularBoundaryDaggerColumn
          (suffixActualSchurFrameSteps lambda stepData S)
          (pairSourceGramSqrt pair x)‖) :
    (sourceThreeBranchActualCoDefectPairReadoutData_ofPackedNormDomination
      owner lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis sourceBasis hfactor pair hpair stepData
      factorBound factorBound_nonneg packed_domination).pair.traceProduct =
      sourceBandGramResponse owner lambda family := by
  change pair.traceProduct = sourceBandGramResponse owner lambda family
  rw [hpair]
  exact sourceThreeBranchSourcePairData_traceProduct_eq owner lambda family
    a c hac hsupp negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
    sourceBasis hfactor

/-!
Uniformity guard for the finite-prime suffix.  A fixed-suffix readout is not
enough for Gate 3U; this package quantifies the same factor bound over every
suffix before producing any readout.
-/
structure SuffixFixedSourceActualCoDefectUniformPackedDominationData
    {lambda : CCM24SoninScale} {ι G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda))
    (pair : CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := G) sourceBasis) where
  stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
    SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S
  factorBound : ℝ
  factorBound_nonneg : 0 ≤ factorBound
  packed_domination : ∀ (S : List CCM24VisiblePrime)
    (x : sourceSoninCarrier lambda),
      ‖sourcePairPackedColumn pair x‖ ≤ factorBound *
        ‖rectangularBoundaryDaggerColumn
          (suffixActualSchurFrameSteps lambda stepData S)
          (pairSourceGramSqrt pair x)‖

noncomputable def SuffixFixedSourceActualCoDefectUniformPackedDominationData.forSuffix
    {lambda : CCM24SoninScale} {ι G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda)}
    {pair : CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := G) sourceBasis}
    (data : SuffixFixedSourceActualCoDefectUniformPackedDominationData
      sourceBasis pair) (S : List CCM24VisiblePrime) :
    SuffixFixedSourceActualCoDefectPairReadoutData
      (G := G) lambda sourceBasis S :=
  SuffixFixedSourceActualCoDefectPairReadoutData.ofPackedNormDomination
    pair data.stepData data.factorBound data.factorBound_nonneg
    (data.packed_domination S)

theorem SuffixFixedSourceActualCoDefectUniformPackedDominationData.forSuffix_ordinaryTrace_norm_le
    {lambda : CCM24SoninScale} {ι G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda)}
    {pair : CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := G) sourceBasis}
    (data : SuffixFixedSourceActualCoDefectUniformPackedDominationData
      sourceBasis pair) (S : List CCM24VisiblePrime) :
    ‖CC20Concrete.PositiveTrace.ordinaryTraceAlong sourceBasis
        (data.forSuffix S).pair.traceProduct‖ ≤
      data.factorBound ^ 2 *
        (∑' i, (‖pair.left (sourceBasis i)‖ ^ 2 +
          ‖pair.right (sourceBasis i)‖ ^ 2)) := by
  exact (data.forSuffix S).ordinaryTrace_norm_le

theorem sourceThreeBranchActualCoDefectPairReadoutData_traceProduct_eq
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ tau ιr κr taur nu mu rho : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis tau ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis ιr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis κr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis taur ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis mu ℂ (commonBoundaryCarrier a c))
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    {S : List CCM24VisiblePrime}
    (pair : CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := commonBoundaryCarrier a c) sourceBasis)
    (hpair : pair = sourceThreeBranchSourcePairData owner lambda family a c
      hac hsupp negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
      sourceBasis hfactor)
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda
        (commonBoundaryCarrier a c) p S)
    (factorBound : ℝ) (factorBound_nonneg : 0 ≤ factorBound)
    (left_domination : ∀ x : sourceSoninCarrier lambda,
      ‖pair.left x‖ ≤ factorBound *
        ‖rectangularBoundaryDaggerColumn
          (suffixActualSchurFrameSteps lambda stepData S)
          (pairSourceGramSqrt pair x)‖)
    (right_domination : ∀ x : sourceSoninCarrier lambda,
      ‖pair.right x‖ ≤ factorBound *
        ‖rectangularBoundaryDaggerColumn
          (suffixActualSchurFrameSteps lambda stepData S)
          (pairSourceGramSqrt pair x)‖) :
    (sourceThreeBranchActualCoDefectPairReadoutData owner lambda family a c
      hac hsupp negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
      sourceBasis hfactor pair hpair stepData factorBound factorBound_nonneg
      left_domination right_domination).pair.traceProduct =
      sourceBandGramResponse owner lambda family := by
  change pair.traceProduct = sourceBandGramResponse owner lambda family
  rw [hpair]
  exact sourceThreeBranchSourcePairData_traceProduct_eq owner lambda family
    a c hac hsupp negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
    sourceBasis hfactor

/-!
The actual physical energy comparison is now a total square-summability
contract on the complete co-defect column.  This is the invariant needed by
the trace consumer; a pointwise comparison with the compact root would be a
strictly stronger and generally invalid lower-frame assumption.
-/
/-!
The cascade contraction is already proved independently, so the remaining
comparison must be supplied by the physical producer itself.
-/
/-!
The route response is an existing theorem, not a new premise.  This generic
bridge lets the concrete source pair be substituted without duplicating the
pair-to-input-side algebra at every Gate 3U call site.
-/
theorem inputSideRootS2ProducerOfPairData_response_eq_of_traceProduct
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    {ι G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda))
    (data : CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := G) sourceBasis)
    (hresponse : data.traceProduct =
      sourceBandGramResponse owner lambda family) :
    (inputSideRootS2ProducerOfPairData data).response =
      sourceBandGramResponse owner lambda family := by
  rw [inputSideRootS2ProducerOfPairData_response_eq data, hresponse]

/-!
The concrete signed three-branch ledger has a canonical input-side base on
the source Sonin carrier.  Its response and root energy are inherited from
the already proved pair owner; no new trace identity is introduced here.

This compatibility wrapper still carries the old identity-input Julia row and
is not an actual Gate 3U producer.  Use
`sourceThreeBranchActualCoDefectPairReadoutData` for the actual cascade path.
-/
noncomputable def sourceThreeBranchSourceInputSideProducer
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ tau ιr κr taur nu mu rho : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis tau ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis ιr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis κr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis taur ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis mu ℂ (commonBoundaryCarrier a c))
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    InputSideRootS2Producer
      (K := WithLp 2 (commonBoundaryCarrier a c × commonBoundaryCarrier a c))
      (G := WithLp 2 (commonBoundaryCarrier a c × commonBoundaryCarrier a c))
      sourceBasis :=
  inputSideRootS2ProducerOfPairData
    (sourceThreeBranchSourcePairData owner lambda family a c hac hsupp
      negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
      sourceBasis hfactor)

theorem sourceThreeBranchSourceInputSideProducer_response_eq
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ tau ιr κr taur nu mu rho : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis tau ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis ιr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis κr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis taur ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis mu ℂ (commonBoundaryCarrier a c))
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    (sourceThreeBranchSourceInputSideProducer owner lambda family a c hac
      hsupp negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
      sourceBasis hfactor).response =
      sourceBandGramResponse owner lambda family := by
  unfold sourceThreeBranchSourceInputSideProducer
  rw [inputSideRootS2ProducerOfPairData_response_eq,
    sourceThreeBranchSourcePairData_traceProduct_eq owner lambda family a c
      hac hsupp negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
      sourceBasis hfactor]

set_option maxHeartbeats 800000 in
-- The balanced four-coordinate boundary carrier enlarges this readback.
theorem sourceThreeBranchSourceInputSideProducer_root_energy_eq
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ tau ιr κr taur nu mu rho : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis tau ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis ιr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis κr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis taur ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis mu ℂ (commonBoundaryCarrier a c))
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    ∑' i, ‖(sourceThreeBranchSourceInputSideProducer owner lambda family a c
        hac hsupp negativeBasis positiveBasis outputBasis reflectedNegativeBasis
        reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
        sourceBasis hfactor).root (sourceBasis i)‖ ^ 2 =
      ∑' i, (‖(sourceThreeBranchSourcePairData owner lambda family a c hac
        hsupp negativeBasis positiveBasis outputBasis reflectedNegativeBasis
        reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
        sourceBasis hfactor).left (sourceBasis i)‖ ^ 2 +
        ‖(sourceThreeBranchSourcePairData owner lambda family a c hac hsupp
        negativeBasis positiveBasis outputBasis reflectedNegativeBasis
        reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
        sourceBasis hfactor).right (sourceBasis i)‖ ^ 2) := by
  unfold sourceThreeBranchSourceInputSideProducer
  exact inputSideRootS2ProducerOfPairData_root_energy_eq
    (sourceThreeBranchSourcePairData owner lambda family a c hac hsupp
      negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
      sourceBasis hfactor)

theorem SuffixFixedSourceActualCoDefectSourceInputData.ordinaryTrace_norm_le
    {lambda : CCM24SoninScale} {ι K G : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda)}
    {S : List CCM24VisiblePrime}
    (data : SuffixFixedSourceActualCoDefectSourceInputData
      (K := K) (G := G) lambda sourceBasis S) :
    ‖CC20Concrete.PositiveTrace.ordinaryTraceAlong sourceBasis
        data.base.response‖ ≤
      (1 / 2 : ℝ) *
        (data.defectFactorBound ^ 2 * data.column_energy_bound +
          ‖data.base.rightFactor‖ ^ 2 *
            (∑' i, ‖data.base.root
              (data.base.rightInput (sourceBasis i))‖ ^ 2)) := by
  let leftMajorant : ι → ℝ := fun i =>
    data.defectFactorBound ^ 2 *
      ‖juliaDefectColumn
        (suffixActualSchurCoDefectSteps lambda data.stepData S)
        (data.base.leftInput (sourceBasis i))‖ ^ 2
  let rightMajorant : ι → ℝ := fun i =>
    ‖data.base.rightFactor‖ ^ 2 *
      ‖data.base.root (data.base.rightInput (sourceBasis i))‖ ^ 2
  have hleft_nonneg : ∀ i, 0 ≤ leftMajorant i := by
    intro i
    exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hright_nonneg : ∀ i, 0 ≤ rightMajorant i := by
    intro i
    exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hleft_summable : Summable leftMajorant := by
    simpa only [leftMajorant] using
      data.column_energy_summable.mul_left
        (data.defectFactorBound ^ 2)
  have hright_summable : Summable rightMajorant := by
    simpa only [rightMajorant] using
      data.base.rightRoot_summable_normSq.mul_left
        (‖data.base.rightFactor‖ ^ 2)
  have hleftPoint : ∀ i,
      ‖data.base.leftFactor
          (data.base.root (data.base.leftInput (sourceBasis i)))‖ ^ 2 ≤
        leftMajorant i := by
    intro i
    have hdom := data.operator_domination (sourceBasis i)
    have hsq := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg
      data.defectFactorBound_nonneg (norm_nonneg _))).mpr hdom
    calc
      ‖data.base.leftFactor
          (data.base.root (data.base.leftInput (sourceBasis i)))‖ ^ 2 ≤
          (data.defectFactorBound *
            ‖juliaDefectColumn
              (suffixActualSchurCoDefectSteps lambda data.stepData S)
              (data.base.leftInput (sourceBasis i))‖) ^ 2 := hsq
      _ = data.defectFactorBound ^ 2 *
          ‖juliaDefectColumn
            (suffixActualSchurCoDefectSteps lambda data.stepData S)
            (data.base.leftInput (sourceBasis i))‖ ^ 2 := by ring
      _ = leftMajorant i := by rfl
  have hrightPoint : ∀ i,
      ‖data.base.rightFactor
          (data.base.root (data.base.rightInput (sourceBasis i)))‖ ^ 2 ≤
        rightMajorant i := by
    intro i
    change ‖data.base.rightFactor
        (data.base.root (data.base.rightInput (sourceBasis i)))‖ ^ 2 ≤ _
    calc
      ‖data.base.rightFactor
          (data.base.root (data.base.rightInput (sourceBasis i)))‖ ^ 2 ≤
          (‖data.base.rightFactor‖ *
            ‖data.base.root (data.base.rightInput (sourceBasis i))‖) ^ 2 := by
        gcongr
        exact data.base.rightFactor.le_opNorm _
      _ = rightMajorant i := by ring
  have hbound := inputSideRootS2Producer_ordinaryTrace_norm_le_of_two_majorants
    data.base leftMajorant rightMajorant hleft_nonneg hright_nonneg
    hleft_summable hright_summable hleftPoint hrightPoint
  have hleft_sum :
      (∑' i, leftMajorant i) ≤
        data.defectFactorBound ^ 2 * data.column_energy_bound := by
    calc
      (∑' i, leftMajorant i) =
          data.defectFactorBound ^ 2 *
            (∑' i, ‖juliaDefectColumn
              (suffixActualSchurCoDefectSteps lambda data.stepData S)
              (data.base.leftInput (sourceBasis i))‖ ^ 2) := by
        simp only [leftMajorant]
        rw [tsum_mul_left]
      _ ≤ data.defectFactorBound ^ 2 * data.column_energy_bound := by
        exact mul_le_mul_of_nonneg_left data.column_energy_bound_le
          (sq_nonneg _)
  have hright_sum :
      (∑' i, rightMajorant i) =
        ‖data.base.rightFactor‖ ^ 2 *
          (∑' i, ‖data.base.root
            (data.base.rightInput (sourceBasis i))‖ ^ 2) := by
    simp only [rightMajorant]
    rw [tsum_mul_left]
  calc
    ‖CC20Concrete.PositiveTrace.ordinaryTraceAlong sourceBasis
        data.base.response‖ ≤
        (1 / 2 : ℝ) *
          ((∑' i, leftMajorant i) + ∑' i, rightMajorant i) := hbound
    _ ≤ (1 / 2 : ℝ) *
        (data.defectFactorBound ^ 2 * data.column_energy_bound +
          ∑' i, rightMajorant i) := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add hleft_sum (le_refl _)) (by norm_num)
    _ = (1 / 2 : ℝ) *
        (data.defectFactorBound ^ 2 * data.column_energy_bound +
          ‖data.base.rightFactor‖ ^ 2 *
            (∑' i, ‖data.base.root
              (data.base.rightInput (sourceBasis i))‖ ^ 2)) := by
      rw [hright_sum]

theorem sourceBandGramResponse_ordinaryTrace_norm_le_of_actualSourceInputCoDefect
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    {ι K G : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda)}
    {S : List CCM24VisiblePrime}
    (data : SuffixFixedSourceActualCoDefectSourceInputData
      (K := K) (G := G) lambda sourceBasis S)
    (hresponse : data.base.response =
      sourceBandGramResponse owner lambda family) :
    ‖CC20Concrete.PositiveTrace.ordinaryTraceAlong sourceBasis
        (sourceBandGramResponse owner lambda family)‖ ≤
      (1 / 2 : ℝ) *
        (data.defectFactorBound ^ 2 * data.column_energy_bound +
          ‖data.base.rightFactor‖ ^ 2 *
            (∑' i, ‖data.base.root
              (data.base.rightInput (sourceBasis i))‖ ^ 2)) := by
  rw [← hresponse]
  exact data.ordinaryTrace_norm_le

noncomputable def SuffixFixedSourceJuliaCoordinateReadoutData.toInputSideData
    {lambda : CCM24SoninScale} {ι G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda)}
    {S : List CCM24VisiblePrime}
    (data : SuffixFixedSourceJuliaCoordinateReadoutData
      (G := G) lambda sourceBasis S) :
    InputSideJuliaCoordinateReadoutData
      (K := sourceSoninCarrier lambda) (G := G) sourceBasis :=
  { base := data.base
    steps := currentRangeJuliaSteps
      (fixedSourceCurrentRangeJuliaSteps lambda data.stepData S)
    readout := fixedSourceCurrentRangeJuliaReadout lambda data.stepData S
    physicalColumn_eq_readout := data.physicalColumn_eq_readout }

noncomputable def SuffixFixedSourceJuliaCoordinateReadoutData.toDouglas
    {lambda : CCM24SoninScale} {ι G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda)}
    {S : List CCM24VisiblePrime}
    (data : SuffixFixedSourceJuliaCoordinateReadoutData
      (G := G) lambda sourceBasis S) :
    DouglasAlignedInputSideRootS2Producer
      (K := sourceSoninCarrier lambda) (G := G) sourceBasis :=
  data.toInputSideData.toDouglas

theorem SuffixFixedSourceJuliaCoordinateReadoutData.toDouglas_rangeColumn
    {lambda : CCM24SoninScale} {ι G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda)}
    {S : List CCM24VisiblePrime}
    (data : SuffixFixedSourceJuliaCoordinateReadoutData
      (G := G) lambda sourceBasis S) :
    data.toDouglas.rangeColumn =
      juliaRangeColumn
        (currentRangeJuliaSteps
          (fixedSourceCurrentRangeJuliaSteps lambda data.stepData S)) ∘L
        data.base.root ∘L data.base.rightInput := by
  rfl

theorem SuffixFixedSourceJuliaCoordinateReadoutData.ordinaryTrace_norm_le
    {lambda : CCM24SoninScale} {ι G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda)}
    {S : List CCM24VisiblePrime}
    (data : SuffixFixedSourceJuliaCoordinateReadoutData
      (G := G) lambda sourceBasis S) :
    ‖CC20Concrete.PositiveTrace.ordinaryTraceAlong sourceBasis
        data.base.response‖ ≤
      (1 / 2 : ℝ) *
        (‖data.base.leftFactor‖ ^ 2 *
          (∑' i, ‖data.base.root
              (data.base.leftInput (sourceBasis i))‖ ^ 2) +
          (∑ i, ‖fixedSourceCurrentRangeJuliaReadout lambda data.stepData
              S i‖) ^ 2 *
            (∑' i, ‖data.base.root
              (data.base.rightInput (sourceBasis i))‖ ^ 2)) := by
  exact inputSideJuliaCoordinateReadout_ordinaryTrace_norm_le
    data.toInputSideData

theorem SuffixFixedSourceJuliaCoordinateReadoutData.ordinaryTrace_norm_le_of_response
    {lambda : CCM24SoninScale} {ι G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda)}
    {S : List CCM24VisiblePrime}
    (data : SuffixFixedSourceJuliaCoordinateReadoutData
      (G := G) lambda sourceBasis S)
    (corner : sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda)
    (hresponse : data.base.response = corner) :
    ‖CC20Concrete.PositiveTrace.ordinaryTraceAlong sourceBasis corner‖ ≤
      (1 / 2 : ℝ) *
        (‖data.base.leftFactor‖ ^ 2 *
          (∑' i, ‖data.base.root
              (data.base.leftInput (sourceBasis i))‖ ^ 2) +
          (∑ i, ‖fixedSourceCurrentRangeJuliaReadout lambda data.stepData
              S i‖) ^ 2 *
            (∑' i, ‖data.base.root
              (data.base.rightInput (sourceBasis i))‖ ^ 2)) := by
  rw [← hresponse]
  exact data.ordinaryTrace_norm_le

end CCM24FiniteSFixedSourceInput
end CCM25Concrete
end Source
end ConnesWeilRH
