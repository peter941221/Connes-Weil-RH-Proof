import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSGatePhysicalObliqueShearKernelReduction
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedMetricCoframeReadout
import ConnesWeilRH.Dev.C1Stage3ProjectionWindow

/-!
# G8 adjoint-shear Gram compression

This leaf records the first owner-level algebraic identity for the live G8
candidate.  The adjoint shear is placed on the input side, so the source
compression retains the physical oblique-shear response.  No trace estimate,
`qw` readback, sign theorem, or RH conclusion is asserted here.
-/

namespace ConnesWeilRH
namespace Source
namespace C1G8AdjointShearGram

open CCM25Concrete
open CC20Concrete
open CCM25Concrete.CCM24FiniteSProjectionTrace
open CCM25Concrete.CCM24FiniteSGatePhysicalObliqueShearReduction
open CCM25Concrete.CCM24FiniteSGatePhysicalObliqueShearKernelReduction
open CCM25Concrete.CCM24FiniteSGatePhysicalTargetCommutatorReduction
open CCM25Concrete.CCM24FiniteSGramResponse
open CCM25Concrete.CCM24FiniteSPhysicalLeakage
open CCM25Concrete.CCM24FiniteSCoframeResponse
open CCM25Concrete.CCM24FiniteSCompletedMetricCoframeReadout
open CCM25Concrete.CCM24FiniteSFixedSourcePolar
open CCM24FiniteSGramOrderingBridge
open CCM24FiniteSPhysicalLeakage
open CCM24FiniteSGatePhysicalTargetCommutatorReduction
open CC20Concrete.PositiveTrace
open Dev.C1PositiveTraceCutoffAdapter
open Dev.C1PositiveTraceWindowProducer
open Dev.C1Stage3ProjectionWindow
open scoped InnerProduct InnerProductSpace

noncomputable section

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

local notation "SourceOp" lambda =>
  sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda

local notation "AmbientOp" =>
  finiteSCarrier →L[ℂ] finiteSCarrier

/-- The G8 positive Gram kernel before any trace is taken. -/
noncomputable def g8AdjointShearGram
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) : AmbientOp :=
  (ContinuousLinearMap.id ℂ finiteSCarrier +
      (finiteEulerPulledObliqueShear lambda family)†)† ∘L
    detectorOperator owner ∘L
        (ContinuousLinearMap.id ℂ finiteSCarrier +
          (finiteEulerPulledObliqueShear lambda family)†)

/-- The selected convolution detector is positive on the ambient carrier. -/
theorem detectorOperator_isPositive_for_g8
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) :
    (detectorOperator owner).IsPositive := by
  unfold detectorOperator
  exact ContinuousLinearMap.isPositive_adjoint_comp_self _

/-- G8 is positive before any trace or readback is introduced. -/
theorem g8AdjointShearGram_isPositive
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    (g8AdjointShearGram owner lambda family).IsPositive := by
  unfold g8AdjointShearGram
  exact (detectorOperator_isPositive_for_g8 owner).adjoint_conj _

/-- Compression of G8 to the healthy source owner keeps all four Gram terms.
The second term is the active oblique-shear response orientation. -/
theorem sourceCompression_g8AdjointShearGram_eq_fourTerms
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    (sourceInclusion lambda)† ∘L
        g8AdjointShearGram owner lambda family ∘L
          sourceInclusion lambda =
      (sourceInclusion lambda)† ∘L detectorOperator owner ∘L
          sourceInclusion lambda +
        (sourceInclusion lambda)† ∘L
          finiteEulerPulledObliqueShear lambda family ∘L
            detectorOperator owner ∘L sourceInclusion lambda +
        (sourceInclusion lambda)† ∘L detectorOperator owner ∘L
          (finiteEulerPulledObliqueShear lambda family)† ∘L
            sourceInclusion lambda +
        (sourceInclusion lambda)† ∘L
          finiteEulerPulledObliqueShear lambda family ∘L
            detectorOperator owner ∘L
              (finiteEulerPulledObliqueShear lambda family)† ∘L
                sourceInclusion lambda := by
  let J := sourceInclusion lambda
  let N := finiteEulerPulledObliqueShear lambda family
  let W := detectorOperator owner
  have hadjoint_add (A B : finiteSCarrier →L[ℂ] finiteSCarrier) :
      (A + B)† = A† + B† := by
    apply ContinuousLinearMap.ext
    intro y
    exact ext_inner_right ℂ fun z => by
      simp only [ContinuousLinearMap.adjoint_inner_left,
        ContinuousLinearMap.add_apply, inner_add_left, inner_add_right]
  change J† ∘L ((ContinuousLinearMap.id ℂ finiteSCarrier + N†)† ∘L W ∘L
      (ContinuousLinearMap.id ℂ finiteSCarrier + N†)) ∘L J = _
  rw [hadjoint_add, ContinuousLinearMap.adjoint_adjoint,
    ContinuousLinearMap.adjoint_id]
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.id_apply, map_add]
  abel

/-- The second Gram term is exactly the already-owned oblique-shear response,
with no trace cycle or adjoint rearrangement. -/
theorem sourceCompression_g8AdjointShearGram_cross_eq_targetResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    (sourceInclusion lambda)† ∘L
        finiteEulerPulledObliqueShear lambda family ∘L
      detectorOperator owner ∘L sourceInclusion lambda =
      finiteEulerTargetCommutatorResponse owner lambda family := by
  change finiteEulerPulledObliqueShearResponse owner lambda family = _
  exact (finiteEulerTargetCommutatorResponse_eq_pulledObliqueShear
    owner lambda family).symm

theorem sourceCompression_g8AdjointShearGram_adjointCross_eq_targetResponse_adjoint
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    (sourceInclusion lambda)† ∘L detectorOperator owner ∘L
        (finiteEulerPulledObliqueShear lambda family)† ∘L
          sourceInclusion lambda =
      (finiteEulerTargetCommutatorResponse owner lambda family)† := by
  have h := congrArg ContinuousLinearMap.adjoint
    (sourceCompression_g8AdjointShearGram_cross_eq_targetResponse
      owner lambda family)
  simpa only [ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint,
    (detectorOperator_isSelfAdjoint owner).adjoint_eq,
    ContinuousLinearMap.comp_assoc] using h

/- The fourth source-compression channel is the internal physical leakage
square.  The source inclusion is an isometry, so no trace cyclicity is used
to identify this term. -/
theorem sourceCompression_g8AdjointShearGram_eq_leakageSquare
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    (sourceInclusion lambda)† ∘L
        finiteEulerPulledObliqueShear lambda family ∘L
          detectorOperator owner ∘L
            (finiteEulerPulledObliqueShear lambda family)† ∘L
              sourceInclusion lambda =
      (sourcePhysicalCoframeLeakage lambda family)† ∘L
        detectorOperator owner ∘L sourcePhysicalCoframeLeakage lambda family := by
  rw [finiteEulerPulledObliqueShear_eq_inclusion_comp_physicalLeakageAdjoint]
  rw [ContinuousLinearMap.adjoint_comp]
  rw [ContinuousLinearMap.adjoint_adjoint]
  let J := sourceInclusion lambda
  let L := sourcePhysicalCoframeLeakage lambda family
  let W := detectorOperator owner
  have hJJ : J† ∘L J = ContinuousLinearMap.id ℂ (sourceSoninCarrier lambda) := by
    dsimp [J]
    exact sourceInclusion_adjoint_comp_self lambda
  change ((J† ∘L J) ∘L (L† ∘L W ∘L L)) ∘L (J† ∘L J) =
    L† ∘L W ∘L L
  rw [hJJ]
  simp only [ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id]

theorem sourceCompression_g8AdjointShearGram_leakageSquare_isPositive
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    (((sourcePhysicalCoframeLeakage lambda family)†) ∘L
        detectorOperator owner ∘L sourcePhysicalCoframeLeakage lambda family).IsPositive := by
  exact (detectorOperator_isPositive_for_g8 owner).adjoint_conj _

theorem sourceCompression_g8AdjointShearGram_eq_metricCoframeGram
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    (sourceInclusion lambda)† ∘L
        g8AdjointShearGram owner lambda family ∘L
          sourceInclusion lambda =
      (finiteEulerMetricCoframe lambda family)† ∘L
        detectorOperator owner ∘L finiteEulerMetricCoframe lambda family := by
  let J := sourceInclusion lambda
  let L := sourcePhysicalCoframeLeakage lambda family
  let N := finiteEulerPulledObliqueShear lambda family
  let W := detectorOperator owner
  have hN : N = J ∘L L† := by
    dsimp [N, J, L]
    exact finiteEulerPulledObliqueShear_eq_inclusion_comp_physicalLeakageAdjoint
      lambda family
  have hNAdj : N† = L ∘L J† := by
    rw [hN, ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint]
  have hCoframe :
      finiteEulerMetricCoframe lambda family = J + L := by
    dsimp [J, L]
    rw [← sourceSoninCoframeLeakage_eq_physical,
      sourceSoninCoframeLeakage_eq_coframe_sub_inclusion]
    abel
  have hTJ :
      (ContinuousLinearMap.id ℂ finiteSCarrier + N†) ∘L J =
        finiteEulerMetricCoframe lambda family := by
    rw [hNAdj, hCoframe]
    apply ContinuousLinearMap.ext
    intro u
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.id_apply]
    have hIso : (J†) (J u) = u := by
      have h := congrArg (fun T : sourceSoninCarrier lambda →L[ℂ]
          sourceSoninCarrier lambda => T u)
        (sourceInclusion_adjoint_comp_self lambda)
      simpa only [J, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.id_apply] using h
    rw [hIso]
  unfold g8AdjointShearGram
  change J† ∘L
      ((ContinuousLinearMap.id ℂ finiteSCarrier + N†)†) ∘L W ∘L
        ((ContinuousLinearMap.id ℂ finiteSCarrier + N†) ∘L J) = _
  rw [hTJ]
  change (J† ∘L
      ((ContinuousLinearMap.id ℂ finiteSCarrier + N†)†)) ∘L W ∘L
        finiteEulerMetricCoframe lambda family = _
  rw [← ContinuousLinearMap.adjoint_comp]
  rw [hTJ]

theorem sourceCompression_g8AdjointShearGram_eq_metricHistoryGram
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    (sourceInclusion lambda)† ∘L
        g8AdjointShearGram owner lambda family ∘L
          sourceInclusion lambda =
      (finiteEulerMetricCoframeHistoryColumn lambda family.visiblePrimes ∘L
          parameterizedSoninGramInvSqrt lambda 1 family.visiblePrimes
            (by norm_num))† ∘L
        (finiteEulerMetricCoframeHistoryReadout lambda family)† ∘L
          detectorOperator owner ∘L
            finiteEulerMetricCoframeHistoryReadout lambda family ∘L
              finiteEulerMetricCoframeHistoryColumn lambda family.visiblePrimes ∘L
                parameterizedSoninGramInvSqrt lambda 1 family.visiblePrimes
                  (by norm_num) := by
  let C := finiteEulerMetricCoframeHistoryColumn lambda family.visiblePrimes ∘L
    parameterizedSoninGramInvSqrt lambda 1 family.visiblePrimes (by norm_num)
  let R := finiteEulerMetricCoframeHistoryReadout lambda family
  let W := detectorOperator owner
  have hRC : R ∘L C = finiteEulerMetricCoframe lambda family := by
    dsimp [R, C]
    exact finiteEulerMetricCoframeHistoryReadout_comp_column_eq lambda family
  calc
    (sourceInclusion lambda)† ∘L
        g8AdjointShearGram owner lambda family ∘L sourceInclusion lambda =
        (finiteEulerMetricCoframe lambda family)† ∘L
          detectorOperator owner ∘L finiteEulerMetricCoframe lambda family :=
      sourceCompression_g8AdjointShearGram_eq_metricCoframeGram owner lambda family
    _ = (R ∘L C)† ∘L W ∘L (R ∘L C) := by rw [hRC]
    _ = C† ∘L R† ∘L W ∘L R ∘L C := by
      simpa only [ContinuousLinearMap.adjoint_comp,
        ContinuousLinearMap.comp_assoc]

theorem sourceCompression_g8AdjointShearGram_metricHistoryGram_isPositive
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    ((finiteEulerMetricCoframeHistoryColumn lambda family.visiblePrimes ∘L
        parameterizedSoninGramInvSqrt lambda 1 family.visiblePrimes
          (by norm_num))† ∘L
      (finiteEulerMetricCoframeHistoryReadout lambda family)† ∘L
        detectorOperator owner ∘L
          finiteEulerMetricCoframeHistoryReadout lambda family ∘L
            finiteEulerMetricCoframeHistoryColumn lambda family.visiblePrimes ∘L
              parameterizedSoninGramInvSqrt lambda 1 family.visiblePrimes
                (by norm_num)).IsPositive := by
  rw [← sourceCompression_g8AdjointShearGram_eq_metricHistoryGram]
  rw [sourceCompression_g8AdjointShearGram_eq_metricCoframeGram]
  exact (detectorOperator_isPositive_for_g8 owner).adjoint_conj _

/-! ### Same-owner finite-window trace carrier -/

/-- The concrete finite-window factor is inserted on both sides of the G8
Gram kernel.  This is the first traceable G8 owner: the window factor is
Hilbert--Schmidt, while the middle G8 kernel is the already-proved positive
ambient operator. -/
noncomputable def g8CutoffPairData
    {ν : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier) (n : Nat) :
    BasisHilbertSchmidtPairData (G := finiteSCarrier) globalBasis :=
  kernelSandwichPairData globalBasis
    (fullBoundaryPositiveOperator owner.sourceTest
      (cutoffLower owner.sourceTest n) (cutoffUpper owner.sourceTest n))
    (g8AdjointShearGram owner lambda family)
    (fullBoundaryPositiveOperator_basis_normSq_summable
      owner.sourceTest (cutoffLower owner.sourceTest n)
      (cutoffUpper owner.sourceTest n)
      (cutoffFullBasis owner.sourceTest n)
      (cutoffOutputBasis owner.sourceTest n) globalBasis)

theorem g8CutoffPairData_traceProduct_eq
    {ν : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier) (n : Nat) :
    (g8CutoffPairData owner lambda family globalBasis n).traceProduct =
      (fullBoundaryPositiveOperator owner.sourceTest
        (cutoffLower owner.sourceTest n) (cutoffUpper owner.sourceTest n)).adjoint ∘L
        g8AdjointShearGram owner lambda family ∘L
          fullBoundaryPositiveOperator owner.sourceTest
            (cutoffLower owner.sourceTest n) (cutoffUpper owner.sourceTest n) := by
  exact kernelSandwichPairData_traceProduct_eq _ _ _ _

theorem g8CutoffPairData_traceProduct_isTraceClassAlong
    {ν : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier) (n : Nat) :
    IsTraceClassAlong globalBasis (g8CutoffPairData owner lambda family globalBasis n).traceProduct := by
  exact kernelSandwichPairData_traceProduct_isTraceClassAlong _ _ _ _

theorem g8CutoffPairData_traceProduct_isPositive
    {ν : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier) (n : Nat) :
    (g8CutoffPairData owner lambda family globalBasis n).traceProduct.IsPositive := by
  exact kernelSandwichPairData_traceProduct_isPositive _ _ _ _
    (g8AdjointShearGram_isPositive owner lambda family)

theorem g8CutoffPairData_trace_re_nonnegative
    {ν : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier) (n : Nat) :
    0 ≤ (ordinaryTraceAlong globalBasis
      (g8CutoffPairData owner lambda family globalBasis n).traceProduct).re := by
  exact ordinaryTraceAlong_re_nonnegative_of_positive globalBasis _
    (g8CutoffPairData_traceProduct_isPositive owner lambda family globalBasis n)
    (g8CutoffPairData_traceProduct_isTraceClassAlong owner lambda family globalBasis n)

/-! ### Source/ambient trace transport -/

noncomputable def g8SourceCutoffPairData
    {ν ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) (n : Nat) :
    BasisHilbertSchmidtPairData (G := finiteSCarrier) sourceBasis :=
  let data := g8CutoffPairData owner lambda family globalBasis n
  { left := data.left ∘L sourceInclusion lambda
    right := data.right ∘L sourceInclusion lambda
    left_summable_normSq :=
      PositiveTrace.summable_normSq_precomp globalBasis globalBasis sourceBasis
        data.left (sourceInclusion lambda) data.left_summable_normSq
    right_summable_normSq :=
      PositiveTrace.summable_normSq_precomp globalBasis globalBasis sourceBasis
        data.right (sourceInclusion lambda) data.right_summable_normSq }

theorem g8SourceCutoffPairData_traceProduct_eq
    {ν ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) (n : Nat) :
    (g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n).traceProduct =
      (sourceInclusion lambda)† ∘L
        (g8CutoffPairData owner lambda family globalBasis n).traceProduct ∘L
          sourceInclusion lambda := by
  unfold g8SourceCutoffPairData
  dsimp
  rw [BasisHilbertSchmidtPairData.traceProduct,
    ContinuousLinearMap.adjoint_comp]
  apply ContinuousLinearMap.ext
  intro u
  rfl

theorem g8SourceCutoffPairData_traceProduct_isTraceClassAlong
    {ν ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) (n : Nat) :
    IsTraceClassAlong sourceBasis
      ((sourceInclusion lambda)† ∘L
        (g8CutoffPairData owner lambda family globalBasis n).traceProduct ∘L
          sourceInclusion lambda) := by
  rw [← g8SourceCutoffPairData_traceProduct_eq]
  exact (g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n).traceProduct_isTraceClassAlong

theorem g8SourceCutoffPairData_traceProduct_isPositive
    {ν ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) (n : Nat) :
    (g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n).traceProduct.IsPositive := by
  rw [g8SourceCutoffPairData_traceProduct_eq]
  exact (g8CutoffPairData_traceProduct_isPositive owner lambda family globalBasis n).adjoint_conj _

theorem g8SourceCutoffPairData_trace_re_nonnegative
    {ν ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) (n : Nat) :
    0 ≤ (ordinaryTraceAlong sourceBasis
      (g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n).traceProduct).re := by
  have htrace := (g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n).traceProduct_isTraceClassAlong
  rw [ordinaryTraceAlong]
  rw [Complex.re_tsum htrace]
  exact tsum_nonneg (fun i =>
    (g8SourceCutoffPairData_traceProduct_isPositive owner lambda family globalBasis
      sourceBasis n).re_inner_nonneg_right (sourceBasis i))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem g8SourceCutoffPairData_trace_cycle
    {ν ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) (n : Nat) :
    ordinaryTraceAlong sourceBasis
        ((sourceInclusion lambda)† ∘L
          (g8CutoffPairData owner lambda family globalBasis n).traceProduct ∘L
            sourceInclusion lambda) =
      ordinaryTraceAlong globalBasis
        ((g8CutoffPairData owner lambda family globalBasis n).traceProduct ∘L
          sourceInclusion lambda ∘L (sourceInclusion lambda)†) := by
  let data := g8CutoffPairData owner lambda family globalBasis n
  let sourceData :=
    g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n
  let ambientData := data.boundedSandwich globalBasis
    (ContinuousLinearMap.id ℂ finiteSCarrier)
      (sourceInclusion lambda ∘L (sourceInclusion lambda)†)
  have hsource : sourceData.traceProduct =
      (sourceInclusion lambda)† ∘L data.traceProduct ∘L
        sourceInclusion lambda := by
    exact g8SourceCutoffPairData_traceProduct_eq owner lambda family
      globalBasis sourceBasis n
  have hambient : ambientData.traceProduct =
      data.traceProduct ∘L sourceInclusion lambda ∘L
        (sourceInclusion lambda)† := by
    dsimp only [ambientData]
    rw [BasisHilbertSchmidtPairData.boundedSandwich_traceProduct_eq]
    apply ContinuousLinearMap.ext
    intro u
    rfl
  have htarget : sourceData.right ∘L sourceData.left† =
      ambientData.right ∘L ambientData.left† := by
    dsimp [data, sourceData, ambientData, g8SourceCutoffPairData,
      BasisHilbertSchmidtPairData.boundedSandwich]
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp]
    simp only [ContinuousLinearMap.adjoint_id,
      ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id,
      ContinuousLinearMap.comp_assoc]
  calc
    ordinaryTraceAlong sourceBasis
        ((sourceInclusion lambda)† ∘L data.traceProduct ∘L
          sourceInclusion lambda) =
        ordinaryTraceAlong sourceBasis sourceData.traceProduct := by
      rw [hsource]
    _ = ordinaryTraceAlong globalBasis
        (sourceData.right ∘L sourceData.left†) :=
      sourceData.ordinaryTraceAlong_traceProduct_eq_cyclic globalBasis
    _ = ordinaryTraceAlong globalBasis
        (ambientData.right ∘L ambientData.left†) := by
      rw [htarget]
    _ = ordinaryTraceAlong globalBasis ambientData.traceProduct :=
      (ambientData.ordinaryTraceAlong_traceProduct_eq_cyclic globalBasis).symm
    _ = ordinaryTraceAlong globalBasis
        (data.traceProduct ∘L sourceInclusion lambda ∘L
          (sourceInclusion lambda)†) := by
      rw [hambient]

end
end C1G8AdjointShearGram
end Source
end ConnesWeilRH
