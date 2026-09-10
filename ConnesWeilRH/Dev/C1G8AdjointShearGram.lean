import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSGatePhysicalObliqueShearKernelReduction
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedMetricCoframeReadout
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSSchurPolarTelescoping
import ConnesWeilRH.Dev.C1PositiveTraceLimitBridge
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
open CCM25Concrete.CCM24FiniteSRawRemainderCommonPair
open CCM25Concrete.CCM24FiniteSCompletedMetricCoframeReadout
open CCM25Concrete.CCM24FiniteSFixedSourcePolar
open CCM24FiniteSGramOrderingBridge
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSPhysicalLeakage
open CCM24FiniteSGatePhysicalTargetCommutatorReduction
open CCM24FiniteSSchurPolarTelescoping
open CCM24FiniteSTransportBounds
open CC20Concrete.PositiveTrace
open Dev.C1PositiveTraceCutoffAdapter
open Dev.C1PositiveTraceWindowProducer
open C1PositiveTraceLimitBridge
open Dev.C1Stage3ProjectionWindow
open Filter
open scoped InnerProduct InnerProductSpace Topology

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

/-! ### Internal forward correction candidate -/

/-- The physical endpoint coframe gives the same-owner positive kernel after
the forward actual-band channel is restored.  This is a candidate corrected
kernel, not an assertion that its trace already reads back to `qw`. -/
noncomputable def g8PhysicalEndpointGram
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    SourceOp lambda :=
  (sourceActualBandForwardEndpointCoframe lambda family)† ∘L
    detectorOperator owner ∘L
      sourceActualBandForwardEndpointCoframe lambda family

/-- The internal correction generated by restoring the forward actual-band
coframe.  Every term stays inside the kernel; no external subtraction is
used. -/
noncomputable def g8InternalForwardCorrection
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    SourceOp lambda :=
  (sourceActualBandForwardCoframe lambda family)† ∘L detectorOperator owner ∘L
      finiteEulerMetricCoframe lambda family +
    (finiteEulerMetricCoframe lambda family)† ∘L detectorOperator owner ∘L
      sourceActualBandForwardCoframe lambda family +
    (sourceActualBandForwardCoframe lambda family)† ∘L detectorOperator owner ∘L
      sourceActualBandForwardCoframe lambda family

/- The internal correction is self-adjoint: the two mixed channels are
adjoints of one another, and the forward Gram channel is self-adjoint. -/
set_option maxHeartbeats 800000 in
theorem g8InternalForwardCorrection_isSelfAdjoint
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    IsSelfAdjoint (g8InternalForwardCorrection owner lambda family) := by
  have hadjoint_add
      (A B : sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda) :
      (A + B)† = A† + B† := by
    apply ContinuousLinearMap.ext
    intro y
    exact ext_inner_right ℂ fun z => by
      simp only [ContinuousLinearMap.adjoint_inner_left,
        ContinuousLinearMap.add_apply, inner_add_left, inner_add_right]
  have hW := detectorOperator_isSelfAdjoint owner
  let F := sourceActualBandForwardCoframe lambda family
  let M := finiteEulerMetricCoframe lambda family
  let W := detectorOperator owner
  have hW' : W† = W := by
    dsimp [W]
    exact hW.adjoint_eq
  have hFM : (F† ∘L W ∘L M)† = M† ∘L W ∘L F := by
    simp only [ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint, hW',
      ContinuousLinearMap.comp_assoc]
  have hMF : (M† ∘L W ∘L F)† = F† ∘L W ∘L M := by
    simp only [ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint, hW',
      ContinuousLinearMap.comp_assoc]
  have hFF : (F† ∘L W ∘L F)† = F† ∘L W ∘L F := by
    simp only [ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint, hW',
      ContinuousLinearMap.comp_assoc]
  change ((F† ∘L W ∘L M + M† ∘L W ∘L F) +
      F† ∘L W ∘L F)† =
    (F† ∘L W ∘L M + M† ∘L W ∘L F) + F† ∘L W ∘L F
  rw [hadjoint_add, hadjoint_add, hFM, hMF, hFF]
  abel

/-- Exact internal-correction expansion: the physical endpoint Gram is the
G8 metric Gram plus the three forward-channel terms.  This is the algebraic
location where a future finite-prime readback correction must live. -/
theorem g8PhysicalEndpointGram_eq_metricGram_add_internalForwardCorrection
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    g8PhysicalEndpointGram owner lambda family =
      (finiteEulerMetricCoframe lambda family)† ∘L
          detectorOperator owner ∘L finiteEulerMetricCoframe lambda family +
        g8InternalForwardCorrection owner lambda family := by
  have hadjoint_add
      (A B : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier) :
      (A + B)† = A† + B† := by
    apply ContinuousLinearMap.ext
    intro y
    exact ext_inner_right ℂ fun z => by
      simp only [ContinuousLinearMap.adjoint_inner_left,
        ContinuousLinearMap.add_apply, inner_add_left, inner_add_right]
  unfold g8PhysicalEndpointGram g8InternalForwardCorrection
  rw [sourceActualBandForwardEndpointCoframe]
  have hsum :
      (sourceActualBandForwardCoframe lambda family +
        finiteEulerMetricCoframe lambda family)† =
      (sourceActualBandForwardCoframe lambda family)† +
        (finiteEulerMetricCoframe lambda family)† :=
    hadjoint_add _ _
  rw [hsum]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    map_add]
  abel

theorem g8PhysicalEndpointGram_isPositive
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    (g8PhysicalEndpointGram owner lambda family).IsPositive := by
  unfold g8PhysicalEndpointGram
  exact (detectorOperator_isPositive_for_g8 owner).adjoint_conj _

/- The same-owner G8 compression admits the exact Schur--polar split into
the terminal survivor and the finite visible-prime boundary sum.  This is an
operator identity only: no sign is assigned to the individual boundary
channels, and no `qw` readback is claimed here. -/
noncomputable def g8MetricCoframeSurvivor
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninCarrier lambda →L[ℂ] finiteSCarrier :=
  newSuffixFrame lambda [] ∘L
    (suffixEulerTransitionProduct lambda family.visiblePrimes)† ∘L
      parameterizedSoninGramInvSqrt lambda 1 family.visiblePrimes
        (by norm_num)

noncomputable def g8MetricCoframeBoundarySum
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninCarrier lambda →L[ℂ] finiteSCarrier :=
  (finiteEulerMetricCoframeBoundaryMaps lambda family).sum

theorem finiteEulerMetricCoframe_eq_g8Survivor_add_boundary
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteEulerMetricCoframe lambda family =
      (finiteEulerUpperFactor family.visiblePrimes : ℂ) •
        (g8MetricCoframeSurvivor lambda family +
          g8MetricCoframeBoundarySum lambda family) := by
  exact finiteEulerMetricCoframe_eq_survivor_add_boundarySum lambda family

theorem sourceCompression_g8AdjointShearGram_eq_survivorBoundaryGram
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    (sourceInclusion lambda)† ∘L
        g8AdjointShearGram owner lambda family ∘L
          sourceInclusion lambda =
      ((finiteEulerUpperFactor family.visiblePrimes : ℂ) •
        (g8MetricCoframeSurvivor lambda family +
          g8MetricCoframeBoundarySum lambda family))† ∘L
        detectorOperator owner ∘L
          ((finiteEulerUpperFactor family.visiblePrimes : ℂ) •
            (g8MetricCoframeSurvivor lambda family +
              g8MetricCoframeBoundarySum lambda family)) := by
  rw [sourceCompression_g8AdjointShearGram_eq_metricCoframeGram]
  rw [finiteEulerMetricCoframe_eq_g8Survivor_add_boundary]

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
  have hcut := g8CutoffPairData_traceProduct_eq owner lambda family globalBasis n
  simp only [hcut]
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

/-! ### Physical-endpoint source cutoff carrier -/

/-- A source-level finite-window pair for the corrected physical endpoint
Gram.  The left leg is the adjoint source inclusion applied to the existing
G8 window leg; the physical endpoint Gram is kept as the middle owner. -/
noncomputable def g8PhysicalEndpointSourceCutoffPairData
    {ι ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ι ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) (n : Nat) :
    BasisHilbertSchmidtPairData (G := sourceSoninCarrier lambda) sourceBasis := by
  let sourceData := g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n
  let F := ContinuousLinearMap.adjoint (sourceInclusion lambda) ∘L sourceData.left
  have hF : Summable fun i => ‖F (sourceBasis i)‖ ^ 2 := by
    exact PositiveTrace.summable_normSq_postcomp sourceBasis sourceData.left
      (ContinuousLinearMap.adjoint (sourceInclusion lambda))
      sourceData.left_summable_normSq
  exact
    { left := F
      right := g8PhysicalEndpointGram owner lambda family ∘L F
      left_summable_normSq := hF
      right_summable_normSq :=
        PositiveTrace.summable_normSq_postcomp sourceBasis F
          (g8PhysicalEndpointGram owner lambda family) hF }

theorem g8PhysicalEndpointSourceCutoffPairData_traceProduct_eq
    {ι ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ι ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) (n : Nat) :
    (g8PhysicalEndpointSourceCutoffPairData owner lambda family globalBasis sourceBasis n).traceProduct =
      ContinuousLinearMap.adjoint
          (ContinuousLinearMap.adjoint (sourceInclusion lambda) ∘L
            (g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n).left) ∘L
        g8PhysicalEndpointGram owner lambda family ∘L
      (ContinuousLinearMap.adjoint (sourceInclusion lambda) ∘L
        (g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n).left) := by
  simp only [g8PhysicalEndpointSourceCutoffPairData,
    BasisHilbertSchmidtPairData.traceProduct]

/- The finite-cutoff physical endpoint keeps the internal correction inside
the same source sandwich.  This is the first cutoff-level algebraic bridge
for the readback: no scalar counterterm or separate owner is introduced. -/
theorem g8PhysicalEndpointSourceCutoffPairData_traceProduct_eq_metric_add_internal
    {ι ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ι ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) (n : Nat) :
    (g8PhysicalEndpointSourceCutoffPairData owner lambda family globalBasis sourceBasis n).traceProduct =
      let C := ContinuousLinearMap.adjoint (sourceInclusion lambda) ∘L
        (g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n).left
      C† ∘L ((finiteEulerMetricCoframe lambda family)† ∘L
        detectorOperator owner ∘L finiteEulerMetricCoframe lambda family) ∘L C +
      C† ∘L (g8InternalForwardCorrection owner lambda family) ∘L C := by
  rw [g8PhysicalEndpointSourceCutoffPairData_traceProduct_eq]
  rw [g8PhysicalEndpointGram_eq_metricGram_add_internalForwardCorrection]
  dsimp
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.add_apply, map_add]

/-- The part of the literal G8 cutoff leg outside the healthy source image.
This is an actual same-owner cutoff defect, not an auxiliary interface: it is
forced by decomposing the existing G8 leg through `sourceInclusion`. -/
noncomputable def g8SourceCutoffComplementLeg
    {ι ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ι ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) (n : Nat) :
    sourceSoninCarrier lambda →L[ℂ] finiteSCarrier :=
  let A := (g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n).left
  A - sourceInclusion lambda ∘L (sourceInclusion lambda)† ∘L A

/- The P1 complement is itself a genuine Hilbert--Schmidt leg.  This is the
first analytic control on the three forced remainder channels: it is proved
from the existing cutoff leg by bounded postcomposition, not by unfolding the
large cutoff construction. -/
theorem g8SourceCutoffComplementLeg_summable_normSq
    {ι ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ι ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) (n : Nat) :
    Summable fun i => ‖g8SourceCutoffComplementLeg owner lambda family globalBasis
      sourceBasis n (sourceBasis i)‖ ^ 2 := by
  let A := (g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n).left
  have hA := (g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n).left_summable_normSq
  have hPA := PositiveTrace.summable_normSq_postcomp sourceBasis A
    (sourceInclusion lambda ∘L (sourceInclusion lambda)†) hA
  have hneg : Summable fun i => ‖(-(sourceInclusion lambda ∘L
      (sourceInclusion lambda)†) ∘L A) (sourceBasis i)‖ ^ 2 := by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply,
      norm_neg] using hPA
  have hadd := PositiveTrace.summable_normSq_add sourceBasis A
    (-(sourceInclusion lambda ∘L (sourceInclusion lambda)†) ∘L A) hA hneg
  simpa only [g8SourceCutoffComplementLeg, sub_eq_add_neg] using hadd

/- Exact P0 carrier alignment.  The physical cutoff is the original G8
cutoff plus the internal forward correction, minus the three terms forced by
the literal cutoff leg's complement to the healthy source image.  Thus a
future zero-remainder argument must control these named complement channels;
it may not pretend that `P_n` and `T_n` differ only by `K_forward`. -/
/- The proof expands a concrete Hilbert-space Gram after the named source
projection split; the larger budget is confined to this actual P0 algebra. -/
set_option maxHeartbeats 1000000 in
theorem g8PhysicalEndpointSourceCutoffPairData_traceProduct_eq_g8_add_internal_sub_complement
    {ι ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ι ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) (n : Nat) :
    (g8PhysicalEndpointSourceCutoffPairData owner lambda family globalBasis sourceBasis n).traceProduct =
      (g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n).traceProduct +
        let A := (g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n).left
        let J := sourceInclusion lambda
        let C := J† ∘L A
        let D := g8SourceCutoffComplementLeg owner lambda family globalBasis sourceBasis n
        C† ∘L g8InternalForwardCorrection owner lambda family ∘L C -
          (C† ∘L J† ∘L g8AdjointShearGram owner lambda family ∘L D +
            D† ∘L g8AdjointShearGram owner lambda family ∘L J ∘L C +
            D† ∘L g8AdjointShearGram owner lambda family ∘L D) := by
  let A := (g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n).left
  let J := sourceInclusion lambda
  let G := g8AdjointShearGram owner lambda family
  let C := J† ∘L A
  let D := g8SourceCutoffComplementLeg owner lambda family globalBasis sourceBasis n
  let K := g8InternalForwardCorrection owner lambda family
  have hA : A = J ∘L C + D := by
    dsimp [A, J, C, D, g8SourceCutoffComplementLeg]
    apply ContinuousLinearMap.ext
    intro u
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.add_apply]
    abel
  have hmetric : C† ∘L ((finiteEulerMetricCoframe lambda family)† ∘L
      detectorOperator owner ∘L finiteEulerMetricCoframe lambda family) ∘L C =
      (J ∘L C)† ∘L G ∘L (J ∘L C) := by
    rw [← sourceCompression_g8AdjointShearGram_eq_metricCoframeGram]
    change C† ∘L ((sourceInclusion lambda)† ∘L
      g8AdjointShearGram owner lambda family ∘L sourceInclusion lambda) ∘L C = _
    simp only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_assoc]
    dsimp only [J, G]
  have hmetricExpanded :
      (ContinuousLinearMap.adjoint
          (ContinuousLinearMap.adjoint (sourceInclusion lambda) ∘L
            (g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n).left) ∘L
        (finiteEulerMetricCoframe lambda family)† ∘L
          detectorOperator owner ∘L finiteEulerMetricCoframe lambda family ∘L
      (ContinuousLinearMap.adjoint (sourceInclusion lambda) ∘L
        (g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n).left)) =
      (J ∘L C)† ∘L G ∘L (J ∘L C) := by
    simpa only [A, J, C] using hmetric
  let B := fullBoundaryPositiveOperator owner.sourceTest
    (cutoffLower owner.sourceTest n) (cutoffUpper owner.sourceTest n)
  have hA_eq : A = B ∘L J := by
    rfl
  have hTA :
      (g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n).traceProduct =
        A† ∘L G ∘L A := by
    rw [g8SourceCutoffPairData_traceProduct_eq]
    rw [g8CutoffPairData_traceProduct_eq]
    rw [hA_eq]
    rw [ContinuousLinearMap.adjoint_comp]
    apply ContinuousLinearMap.ext
    intro u
    rfl
  have hadjoint_add
      (X Y : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier) :
      (X + Y)† = X† + Y† := by
    apply ContinuousLinearMap.ext
    intro y
    exact ext_inner_right ℂ fun z => by
      simp only [ContinuousLinearMap.adjoint_inner_left,
        ContinuousLinearMap.add_apply, inner_add_left, inner_add_right]
  have hT :
      (g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n).traceProduct =
        (J ∘L C)† ∘L G ∘L (J ∘L C) +
          ((J ∘L C)† ∘L G ∘L D + D† ∘L G ∘L (J ∘L C) + D† ∘L G ∘L D) := by
    rw [hTA]
    rw [hA]
    rw [hadjoint_add]
    apply ContinuousLinearMap.ext
    intro u
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
      map_add]
    abel
  rw [g8PhysicalEndpointSourceCutoffPairData_traceProduct_eq_metric_add_internal]
  simp (config := { zeta := true }) only [ContinuousLinearMap.comp_assoc]
  rw [hmetricExpanded, hT]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.adjoint_comp,
    J, C, D, G, neg_smul, one_smul, neg_one_smul, smul_eq_mul]
  module

theorem g8PhysicalEndpointSourceCutoffPairData_traceProduct_isTraceClassAlong
    {ι ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ι ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) (n : Nat) :
    IsTraceClassAlong sourceBasis
      (g8PhysicalEndpointSourceCutoffPairData owner lambda family globalBasis sourceBasis n).traceProduct := by
  exact (g8PhysicalEndpointSourceCutoffPairData owner lambda family globalBasis sourceBasis n).traceProduct_isTraceClassAlong

theorem g8PhysicalEndpointSourceCutoffPairData_traceProduct_isPositive
    {ι ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ι ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) (n : Nat) :
    (g8PhysicalEndpointSourceCutoffPairData owner lambda family globalBasis sourceBasis n).traceProduct.IsPositive := by
  let sourceData := g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n
  let C := ContinuousLinearMap.adjoint (sourceInclusion lambda) ∘L sourceData.left
  rw [BasisHilbertSchmidtPairData.traceProduct]
  exact (g8PhysicalEndpointGram_isPositive owner lambda family).adjoint_conj C

theorem g8PhysicalEndpointSourceCutoffPairData_traceProduct_isSelfAdjoint
    {ι ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ι ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) (n : Nat) :
    IsSelfAdjoint
      (g8PhysicalEndpointSourceCutoffPairData owner lambda family globalBasis sourceBasis n).traceProduct := by
  let sourceData := g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n
  let C := ContinuousLinearMap.adjoint (sourceInclusion lambda) ∘L sourceData.left
  rw [g8PhysicalEndpointSourceCutoffPairData_traceProduct_eq]
  exact (g8PhysicalEndpointGram_isPositive owner lambda family).adjoint_conj C |>.isSelfAdjoint

theorem g8PhysicalEndpointSourceCutoffPairData_trace_im_eq_zero
    {ι ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ι ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) (n : Nat) :
    (ordinaryTraceAlong sourceBasis
      (g8PhysicalEndpointSourceCutoffPairData owner lambda family globalBasis sourceBasis n).traceProduct).im = 0 := by
  let T := g8PhysicalEndpointSourceCutoffPairData owner lambda family globalBasis sourceBasis n
  have hself := g8PhysicalEndpointSourceCutoffPairData_traceProduct_isSelfAdjoint
    owner lambda family globalBasis sourceBasis n
  have htrace := ordinaryTraceAlong_adjoint sourceBasis T.traceProduct
  rw [hself.adjoint_eq] at htrace
  have him := congrArg Complex.im htrace
  have him' :
      (ordinaryTraceAlong sourceBasis
        (g8PhysicalEndpointSourceCutoffPairData owner lambda family globalBasis sourceBasis n).traceProduct).im =
        -(ordinaryTraceAlong sourceBasis
          (g8PhysicalEndpointSourceCutoffPairData owner lambda family globalBasis sourceBasis n).traceProduct).im := by
    simpa [Complex.star_def, T] using him
  linarith

theorem g8PhysicalEndpointSourceCutoffPairData_trace_re_nonnegative
    {ι ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ι ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) (n : Nat) :
    0 ≤ (ordinaryTraceAlong sourceBasis
      (g8PhysicalEndpointSourceCutoffPairData owner lambda family globalBasis sourceBasis n).traceProduct).re := by
  have htrace :=
    g8PhysicalEndpointSourceCutoffPairData_traceProduct_isTraceClassAlong
      owner lambda family globalBasis sourceBasis n
  rw [ordinaryTraceAlong]
  rw [Complex.re_tsum htrace]
  exact tsum_nonneg (fun i =>
    (g8PhysicalEndpointSourceCutoffPairData_traceProduct_isPositive
      owner lambda family globalBasis sourceBasis n).re_inner_nonneg_right (sourceBasis i))

/-! ### G8-specific same-owner readback contract -/

/-- The only analytic datum still needed by the G8 positive-trace route.
Each cutoff operator is already tied to the fixed G8 owner and has a formal
trace-class/positivity proof above; this contract records only the remainder
and its same-owner limit readback. -/
structure G8SameOwnerReadbackData
    {ν ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) where
  remainder : Nat → Real
  remainder_tendsto_zero :
    Tendsto remainder atTop (𝓝 (0 : Real))
  readback_tendsto_qw :
    Tendsto
      (fun n =>
        (ordinaryTraceAlong sourceBasis
          (g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n).traceProduct).re -
            remainder n)
      atTop (𝓝 (C1SameOwnerWeil.qw owner.sourceTest))

/-- The concrete G8 cutoff family is accepted by the existing positive-trace
consumer without changing its owner or quantifiers. -/
noncomputable def g8PositiveTraceOperatorLimitFamily
    {ν ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda))
    (data : G8SameOwnerReadbackData owner lambda family globalBasis sourceBasis) :
    PositiveTraceOperatorLimitFamily sourceBasis owner.sourceTest :=
  { traceOperator := fun n =>
      (g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n).traceProduct
    traceClass := fun n => by
      rw [g8SourceCutoffPairData_traceProduct_eq]
      exact g8SourceCutoffPairData_traceProduct_isTraceClassAlong owner lambda family
        globalBasis sourceBasis n
    positive := fun n =>
      g8SourceCutoffPairData_traceProduct_isPositive owner lambda family
        globalBasis sourceBasis n
    remainder := data.remainder
    remainder_tendsto_zero := data.remainder_tendsto_zero
    readback_tendsto_qw := data.readback_tendsto_qw }

theorem qw_nonnegative_of_g8SameOwnerReadbackData
    {ν ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda))
    (data : G8SameOwnerReadbackData owner lambda family globalBasis sourceBasis) :
    0 ≤ C1SameOwnerWeil.qw owner.sourceTest := by
  exact qw_nonnegative_of_positiveTraceOperatorLimitFamily
    (g8PositiveTraceOperatorLimitFamily owner lambda family globalBasis sourceBasis data)

/-! ### Four-channel finite-window ledger -/

noncomputable def g8SourceCutoffBaseOperator
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) (n : Nat) :
    sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
  (sourceInclusion lambda)† ∘L
    (fullBoundaryPositiveOperator owner.sourceTest
      (cutoffLower owner.sourceTest n) (cutoffUpper owner.sourceTest n))† ∘L
    detectorOperator owner ∘L
    fullBoundaryPositiveOperator owner.sourceTest
      (cutoffLower owner.sourceTest n) (cutoffUpper owner.sourceTest n) ∘L
    sourceInclusion lambda

noncomputable def g8SourceCutoffCrossOperator
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) (n : Nat) :
    sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
  (sourceInclusion lambda)† ∘L
    (fullBoundaryPositiveOperator owner.sourceTest
      (cutoffLower owner.sourceTest n) (cutoffUpper owner.sourceTest n))† ∘L
    finiteEulerPulledObliqueShear lambda family ∘L detectorOperator owner ∘L
    fullBoundaryPositiveOperator owner.sourceTest
      (cutoffLower owner.sourceTest n) (cutoffUpper owner.sourceTest n) ∘L
    sourceInclusion lambda

noncomputable def g8SourceCutoffAdjointCrossOperator
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) (n : Nat) :
    sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
  (sourceInclusion lambda)† ∘L
    (fullBoundaryPositiveOperator owner.sourceTest
      (cutoffLower owner.sourceTest n) (cutoffUpper owner.sourceTest n))† ∘L
    detectorOperator owner ∘L (finiteEulerPulledObliqueShear lambda family)† ∘L
    fullBoundaryPositiveOperator owner.sourceTest
      (cutoffLower owner.sourceTest n) (cutoffUpper owner.sourceTest n) ∘L
    sourceInclusion lambda

noncomputable def g8SourceCutoffLeakageOperator
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) (n : Nat) :
    sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
  (sourceInclusion lambda)† ∘L
    (fullBoundaryPositiveOperator owner.sourceTest
      (cutoffLower owner.sourceTest n) (cutoffUpper owner.sourceTest n))† ∘L
    finiteEulerPulledObliqueShear lambda family ∘L detectorOperator owner ∘L
    (finiteEulerPulledObliqueShear lambda family)† ∘L
    fullBoundaryPositiveOperator owner.sourceTest
      (cutoffLower owner.sourceTest n) (cutoffUpper owner.sourceTest n) ∘L
    sourceInclusion lambda

/-! A channel-specific pair keeps the existing source Hilbert--Schmidt leg and
postcomposes it by one bounded finite-S channel.  This is the trace-class
carrier needed before applying ordinary trace additivity to the four-channel
ledger. -/
noncomputable def g8SourceCutoffChannelPairData
    {ν ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) (n : Nat)
    (channel : finiteSCarrier →L[ℂ] finiteSCarrier) :
    BasisHilbertSchmidtPairData (G := finiteSCarrier) sourceBasis :=
  let sourceData :=
    g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n
  { left := sourceData.left
    right := channel ∘L sourceData.left
    left_summable_normSq := sourceData.left_summable_normSq
    right_summable_normSq :=
      PositiveTrace.summable_normSq_postcomp sourceBasis sourceData.left channel
        sourceData.left_summable_normSq }

theorem g8SourceCutoffChannelPairData_traceProduct_eq
    {ν ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) (n : Nat)
    (channel : finiteSCarrier →L[ℂ] finiteSCarrier) :
    (g8SourceCutoffChannelPairData owner lambda family globalBasis sourceBasis n
      channel).traceProduct =
      ((g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n).left)† ∘L
        channel ∘L
          (g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n).left := by
  simp only [g8SourceCutoffChannelPairData,
    BasisHilbertSchmidtPairData.traceProduct]

theorem g8SourceCutoffChannelPairData_traceProduct_eq_explicit
    {ν ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) (n : Nat)
    (channel : finiteSCarrier →L[ℂ] finiteSCarrier) :
    (g8SourceCutoffChannelPairData owner lambda family globalBasis sourceBasis n
      channel).traceProduct =
      (((sourceInclusion lambda)† ∘L
          (fullBoundaryPositiveOperator owner.sourceTest
            (cutoffLower owner.sourceTest n) (cutoffUpper owner.sourceTest n))†) ∘L
        channel ∘L fullBoundaryPositiveOperator owner.sourceTest
          (cutoffLower owner.sourceTest n) (cutoffUpper owner.sourceTest n)) ∘L
        sourceInclusion lambda := by
  rw [g8SourceCutoffChannelPairData_traceProduct_eq]
  dsimp [g8SourceCutoffPairData, g8CutoffPairData, kernelSandwichPairData]
  rw [ContinuousLinearMap.adjoint_comp]
  simp only [ContinuousLinearMap.comp_assoc]

theorem g8SourceCutoffBaseOperator_isTraceClassAlong
    {ν ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) (n : Nat) :
    IsTraceClassAlong sourceBasis
      (g8SourceCutoffBaseOperator owner lambda family n) := by
  let data := g8SourceCutoffChannelPairData owner lambda family globalBasis sourceBasis n
    (detectorOperator owner)
  have htrace := data.traceProduct_isTraceClassAlong
  have heq : data.traceProduct = g8SourceCutoffBaseOperator owner lambda family n := by
    rw [g8SourceCutoffChannelPairData_traceProduct_eq]
    dsimp [data, g8SourceCutoffChannelPairData, g8SourceCutoffPairData,
      g8CutoffPairData, kernelSandwichPairData]
    rw [ContinuousLinearMap.adjoint_comp]
    unfold g8SourceCutoffBaseOperator
    let C := fullBoundaryPositiveOperator owner.sourceTest
      (cutoffLower owner.sourceTest n) (cutoffUpper owner.sourceTest n)
    let J := sourceInclusion lambda
    change (((J)† ∘L C†) ∘L detectorOperator owner ∘L C ∘L J) = _
    rfl
  rw [← heq]
  exact htrace

theorem g8SourceCutoffCrossOperator_isTraceClassAlong
    {ν ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) (n : Nat) :
    IsTraceClassAlong sourceBasis
      (g8SourceCutoffCrossOperator owner lambda family n) := by
  let N := finiteEulerPulledObliqueShear lambda family
  let W := detectorOperator owner
  let data := g8SourceCutoffChannelPairData owner lambda family globalBasis sourceBasis n
    (N ∘L W)
  have htrace := data.traceProduct_isTraceClassAlong
  have heq : data.traceProduct = g8SourceCutoffCrossOperator owner lambda family n := by
    rw [g8SourceCutoffChannelPairData_traceProduct_eq_explicit]
    unfold g8SourceCutoffCrossOperator
    rfl
  rw [← heq]
  exact htrace

theorem g8SourceCutoffAdjointCrossOperator_isTraceClassAlong
    {ν ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) (n : Nat) :
    IsTraceClassAlong sourceBasis
      (g8SourceCutoffAdjointCrossOperator owner lambda family n) := by
  let N := finiteEulerPulledObliqueShear lambda family
  let W := detectorOperator owner
  let data := g8SourceCutoffChannelPairData owner lambda family globalBasis sourceBasis n
    (W ∘L N†)
  have htrace := data.traceProduct_isTraceClassAlong
  have heq : data.traceProduct = g8SourceCutoffAdjointCrossOperator owner lambda family n := by
    rw [g8SourceCutoffChannelPairData_traceProduct_eq_explicit]
    unfold g8SourceCutoffAdjointCrossOperator
    rfl
  rw [← heq]
  exact htrace

theorem g8SourceCutoffLeakageOperator_isTraceClassAlong
    {ν ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) (n : Nat) :
    IsTraceClassAlong sourceBasis
      (g8SourceCutoffLeakageOperator owner lambda family n) := by
  let N := finiteEulerPulledObliqueShear lambda family
  let W := detectorOperator owner
  let data := g8SourceCutoffChannelPairData owner lambda family globalBasis sourceBasis n
    (N ∘L W ∘L N†)
  have htrace := data.traceProduct_isTraceClassAlong
  have heq : data.traceProduct = g8SourceCutoffLeakageOperator owner lambda family n := by
    rw [g8SourceCutoffChannelPairData_traceProduct_eq_explicit]
    unfold g8SourceCutoffLeakageOperator
    rfl
  rw [← heq]
  exact htrace

theorem g8SourceCutoffBaseOperator_isPositive
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) (n : Nat) :
    (g8SourceCutoffBaseOperator owner lambda family n).IsPositive := by
  let C := fullBoundaryPositiveOperator owner.sourceTest
    (cutoffLower owner.sourceTest n) (cutoffUpper owner.sourceTest n)
  let J := sourceInclusion lambda
  unfold g8SourceCutoffBaseOperator
  change (((J)† ∘L C†) ∘L detectorOperator owner ∘L C ∘L J).IsPositive
  have h := (detectorOperator_isPositive_for_g8 owner).adjoint_conj (C ∘L J)
  simpa only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_assoc] using h

theorem g8SourceCutoffLeakageOperator_isPositive
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) (n : Nat) :
    (g8SourceCutoffLeakageOperator owner lambda family n).IsPositive := by
  let C := fullBoundaryPositiveOperator owner.sourceTest
    (cutoffLower owner.sourceTest n) (cutoffUpper owner.sourceTest n)
  let J := sourceInclusion lambda
  let E := (finiteEulerPulledObliqueShear lambda family)† ∘L C ∘L J
  unfold g8SourceCutoffLeakageOperator
  change ((((J)† ∘L C†) ∘L finiteEulerPulledObliqueShear lambda family) ∘L
      detectorOperator owner ∘L (finiteEulerPulledObliqueShear lambda family)† ∘L C ∘L J).IsPositive
  have h := (detectorOperator_isPositive_for_g8 owner).adjoint_conj E
  simpa only [E, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.comp_assoc] using h

theorem g8SourceCutoffAdjointCrossOperator_eq_crossOperator_adjoint
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) (n : Nat) :
    g8SourceCutoffAdjointCrossOperator owner lambda family n =
      (g8SourceCutoffCrossOperator owner lambda family n)† := by
  unfold g8SourceCutoffCrossOperator g8SourceCutoffAdjointCrossOperator
  simp only [ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint,
    (detectorOperator_isSelfAdjoint owner).adjoint_eq,
    ContinuousLinearMap.comp_assoc]

theorem g8SourceCutoffPairData_traceProduct_eq_fourChannelLedger
    {ν ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) (n : Nat) :
    (g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n).traceProduct =
      g8SourceCutoffBaseOperator owner lambda family n +
      g8SourceCutoffCrossOperator owner lambda family n +
      g8SourceCutoffAdjointCrossOperator owner lambda family n +
      g8SourceCutoffLeakageOperator owner lambda family n := by
  rw [g8SourceCutoffPairData_traceProduct_eq]
  have hcut := g8CutoffPairData_traceProduct_eq owner lambda family globalBasis n
  simp only [hcut]
  have hadjoint_add (A B : finiteSCarrier →L[ℂ] finiteSCarrier) :
      (A + B)† = A† + B† := by
    apply ContinuousLinearMap.ext
    intro y
    exact ext_inner_right ℂ fun z => by
      simp only [ContinuousLinearMap.adjoint_inner_left,
        ContinuousLinearMap.add_apply, inner_add_left, inner_add_right]
  unfold g8AdjointShearGram
  unfold g8SourceCutoffBaseOperator g8SourceCutoffCrossOperator
    g8SourceCutoffAdjointCrossOperator g8SourceCutoffLeakageOperator
  rw [hadjoint_add, ContinuousLinearMap.adjoint_adjoint,
    ContinuousLinearMap.adjoint_id]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.add_apply, map_add]
  abel_nf

theorem g8SourceCutoffPairData_ordinaryTrace_eq_fourChannelLedger
    {ν ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) (n : Nat) :
    ordinaryTraceAlong sourceBasis
        (g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n).traceProduct =
      ordinaryTraceAlong sourceBasis (g8SourceCutoffBaseOperator owner lambda family n) +
        ordinaryTraceAlong sourceBasis (g8SourceCutoffCrossOperator owner lambda family n) +
        ordinaryTraceAlong sourceBasis
          (g8SourceCutoffAdjointCrossOperator owner lambda family n) +
        ordinaryTraceAlong sourceBasis (g8SourceCutoffLeakageOperator owner lambda family n) := by
  rw [g8SourceCutoffPairData_traceProduct_eq_fourChannelLedger]
  have hbase := g8SourceCutoffBaseOperator_isTraceClassAlong
    owner lambda family globalBasis sourceBasis n
  have hcross := g8SourceCutoffCrossOperator_isTraceClassAlong
    owner lambda family globalBasis sourceBasis n
  have hadjoint := g8SourceCutoffAdjointCrossOperator_isTraceClassAlong
    owner lambda family globalBasis sourceBasis n
  have hleakage := g8SourceCutoffLeakageOperator_isTraceClassAlong
    owner lambda family globalBasis sourceBasis n
  have hbaseCross := isTraceClassAlong_add sourceBasis
    (g8SourceCutoffBaseOperator owner lambda family n)
    (g8SourceCutoffCrossOperator owner lambda family n) hbase hcross
  have hbaseCrossAdjoint := isTraceClassAlong_add sourceBasis
    (g8SourceCutoffBaseOperator owner lambda family n +
      g8SourceCutoffCrossOperator owner lambda family n)
    (g8SourceCutoffAdjointCrossOperator owner lambda family n)
    hbaseCross hadjoint
  rw [ordinaryTraceAlong_add sourceBasis _ _ hbaseCrossAdjoint hleakage]
  rw [ordinaryTraceAlong_add sourceBasis _ _ hbaseCross hadjoint]
  rw [ordinaryTraceAlong_add sourceBasis _ _ hbase hcross]

theorem g8SourceCutoffCross_trace_add_adjointCross_eq_two_re
    {ν ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) (n : Nat) :
    ordinaryTraceAlong sourceBasis
        (g8SourceCutoffCrossOperator owner lambda family n +
          g8SourceCutoffAdjointCrossOperator owner lambda family n) =
      ((2 * (ordinaryTraceAlong sourceBasis
        (g8SourceCutoffCrossOperator owner lambda family n)).re : ℝ) : ℂ) := by
  have hcross := g8SourceCutoffCrossOperator_isTraceClassAlong
    owner lambda family globalBasis sourceBasis n
  have hadjoint := g8SourceCutoffAdjointCrossOperator_isTraceClassAlong
    owner lambda family globalBasis sourceBasis n
  rw [ordinaryTraceAlong_add sourceBasis _ _ hcross hadjoint]
  rw [g8SourceCutoffAdjointCrossOperator_eq_crossOperator_adjoint]
  rw [ordinaryTraceAlong_adjoint, Complex.star_def, Complex.add_conj]

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
