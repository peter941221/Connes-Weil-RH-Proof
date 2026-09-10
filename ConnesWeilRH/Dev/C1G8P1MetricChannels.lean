import ConnesWeilRH.Dev.C1G8P1MetricBoundary
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSGatePhysicalObliqueShearKernelReduction

/-!
# G8 P1 literal-cutoff metric channels

The finite Euler metric Gram is expanded before taking a trace.  The four
summands retain the literal G8 cutoff; this is only the operator ledger needed
before a separate aggregate prime-power readback theorem can be stated.
-/

namespace ConnesWeilRH
namespace Source
namespace C1G8P1MetricChannels

open CCM25Concrete
open CC20Concrete
open CCM25Concrete.CCM24FiniteSProjectionTrace
open CCM25Concrete.CCM24FiniteSGramResponse
open CCM25Concrete.CCM24FiniteSCoframeResponse
open CCM25Concrete.CCM24FiniteSFixedSourcePolar
open CCM25Concrete.CCM24FiniteSGramInverseCalculus
open CCM25Concrete.CCM24FiniteSActualSchurCascade
open CCM25Concrete.CCM24FiniteSSchurPolarTelescoping
open CCM25Concrete.CCM24FiniteSParameterizedEulerProduct
open CCM25Concrete.CCM24FiniteSTransportBounds
open CCM25Concrete.CCM24FiniteSPhysicalLeakage
open CCM25Concrete.CCM24FiniteSGramOrderingBridge
open CCM25Concrete.CCM24FiniteSGatePhysicalObliqueShearKernelReduction
open C1G8AdjointShearGram
open C1G8P1MetricBoundary
open Dev.C1Stage3ProjectionWindow
open CC20Concrete.PositiveTrace
open scoped InnerProduct InnerProductSpace Topology

noncomputable section

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- The survivor component of the finite Euler metric coframe. -/
noncomputable def g8MetricSurvivorCoframe
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninCarrier lambda →L[ℂ] finiteSCarrier :=
  (finiteEulerUpperFactor family.visiblePrimes : ℂ) •
    newSuffixFrame lambda [] ∘L
      (suffixEulerTransitionProduct lambda family.visiblePrimes)† ∘L
        parameterizedSoninGramInvSqrt lambda 1 family.visiblePrimes (by norm_num)

/-- The aggregate visible-place boundary component of the metric coframe.
It is indexed by visible primes, not separately by prime powers. -/
noncomputable def g8MetricVisibleBoundaryCoframe
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninCarrier lambda →L[ℂ] finiteSCarrier :=
  (finiteEulerUpperFactor family.visiblePrimes : ℂ) •
  (finiteEulerMetricCoframeBoundaryMaps lambda family).sum

/-- The physical finite-Euler leakage coframe.  This is the coframe whose
uncut cross response is already the selected Euler target operator. -/
noncomputable def g8MetricLeakageCoframe
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninCarrier lambda →L[ℂ] finiteSCarrier :=
  finiteEulerMetricCoframe lambda family - sourceInclusion lambda

theorem g8MetricLeakageCoframe_eq_sourcePhysicalCoframeLeakage
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    g8MetricLeakageCoframe lambda family =
      sourcePhysicalCoframeLeakage lambda family := by
  unfold g8MetricLeakageCoframe
  rw [← sourceSoninCoframeLeakage_eq_physical,
    sourceSoninCoframeLeakage_eq_coframe_sub_inclusion]

/-- The uncut leakage/source cross is exactly the existing finite-Euler target
response, with no cutoff or owner substitution. -/
theorem finiteEulerTargetCommutatorResponse_eq_g8MetricLeakageCross
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteEulerTargetCommutatorResponse owner lambda family =
      (g8MetricLeakageCoframe lambda family)† ∘L detectorOperator owner ∘L
        sourceInclusion lambda := by
  rw [finiteEulerTargetCommutatorResponse_eq_physicalCoframeLeakage,
    g8MetricLeakageCoframe_eq_sourcePhysicalCoframeLeakage]
  rfl

/-- The actual metric coframe splits into its survivor and aggregate boundary
components. -/
theorem finiteEulerMetricCoframe_eq_g8MetricSurvivor_add_visibleBoundary
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteEulerMetricCoframe lambda family =
      g8MetricSurvivorCoframe lambda family +
        g8MetricVisibleBoundaryCoframe lambda family := by
  rw [finiteEulerMetricCoframe_eq_survivor_add_boundarySum]
  rw [smul_add]
  rfl

/-- One ordered literal-cutoff channel in the metric Gram expansion. -/
noncomputable def g8MetricCutoffChannel
    {ι ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ι ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) (n : Nat)
    (left right : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier) :
    sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
  let C := (sourceInclusion lambda)† ∘L
    (g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n).left
  C† ∘L left† ∘L detectorOperator owner ∘L right ∘L C

/-- A concrete Hilbert--Schmidt owner for any ordered literal-cutoff metric
channel.  Both legs start from the same cutoff source leg. -/
noncomputable def g8MetricCutoffChannelPairData
    {ι ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ι ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) (n : Nat)
    (left right : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier) :
    BasisHilbertSchmidtPairData (G := finiteSCarrier) sourceBasis := by
  let A := (g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n).left
  let C := (sourceInclusion lambda)† ∘L A
  have hA := (g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n).left_summable_normSq
  have hC : Summable fun i => ‖C (sourceBasis i)‖ ^ 2 := by
    exact PositiveTrace.summable_normSq_postcomp sourceBasis A
      ((sourceInclusion lambda)†) hA
  have hleft : Summable fun i => ‖(left ∘L C) (sourceBasis i)‖ ^ 2 := by
    exact PositiveTrace.summable_normSq_postcomp sourceBasis C left hC
  have hrightBase : Summable fun i => ‖(right ∘L C) (sourceBasis i)‖ ^ 2 := by
    exact PositiveTrace.summable_normSq_postcomp sourceBasis C right hC
  have hright : Summable fun i =>
      ‖(detectorOperator owner ∘L right ∘L C) (sourceBasis i)‖ ^ 2 := by
    exact PositiveTrace.summable_normSq_postcomp sourceBasis (right ∘L C)
      (detectorOperator owner) hrightBase
  exact
    { left := left ∘L C
      right := detectorOperator owner ∘L right ∘L C
      left_summable_normSq := hleft
      right_summable_normSq := hright }

/-- The generic channel pair's trace product is precisely its named ordered
literal-cutoff channel. -/
theorem g8MetricCutoffChannelPairData_traceProduct_eq
    {ι ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ι ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) (n : Nat)
    (left right : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier) :
    (g8MetricCutoffChannelPairData owner lambda family globalBasis sourceBasis n left right).traceProduct =
      g8MetricCutoffChannel owner lambda family globalBasis sourceBasis n left right := by
  simp only [g8MetricCutoffChannelPairData, g8MetricCutoffChannel,
    BasisHilbertSchmidtPairData.traceProduct, ContinuousLinearMap.adjoint_comp]
  rfl

theorem g8MetricCutoffChannel_isTraceClassAlong
    {ι ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ι ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) (n : Nat)
    (left right : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier) :
    PositiveTrace.IsTraceClassAlong sourceBasis
      (g8MetricCutoffChannel owner lambda family globalBasis sourceBasis n left right) := by
  rw [← g8MetricCutoffChannelPairData_traceProduct_eq]
  exact (g8MetricCutoffChannelPairData owner lambda family globalBasis sourceBasis n left right).traceProduct_isTraceClassAlong

/-- The literal-cutoff leakage/source cross channel. -/
noncomputable def g8MetricCutoffLeakageSourceCrossOperator
    {ι ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ι ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) (n : Nat) :
    sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
  g8MetricCutoffChannel owner lambda family globalBasis sourceBasis n
    (g8MetricLeakageCoframe lambda family) (sourceInclusion lambda)

theorem g8MetricCutoffLeakageSourceCrossOperator_eq_literal_sandwich
    {ι ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ι ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) (n : Nat) :
    g8MetricCutoffLeakageSourceCrossOperator owner lambda family globalBasis sourceBasis n =
      let C := (sourceInclusion lambda)† ∘L
        (g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n).left
      C† ∘L (g8MetricLeakageCoframe lambda family)† ∘L detectorOperator owner ∘L
        sourceInclusion lambda ∘L C := by
  rfl

theorem g8MetricCutoffLeakageSourceCrossOperator_eq_metric_sub_source
    {ι ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ι ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) (n : Nat) :
    g8MetricCutoffLeakageSourceCrossOperator owner lambda family globalBasis sourceBasis n =
      g8MetricCutoffChannel owner lambda family globalBasis sourceBasis n
          (finiteEulerMetricCoframe lambda family) (sourceInclusion lambda) -
        g8MetricCutoffChannel owner lambda family globalBasis sourceBasis n
          (sourceInclusion lambda) (sourceInclusion lambda) := by
  unfold g8MetricCutoffLeakageSourceCrossOperator g8MetricLeakageCoframe
    g8MetricCutoffChannel
  have hadjoint_sub
      (A B : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier) :
      (A - B)† = A† - B† := by
    apply ContinuousLinearMap.ext
    intro y
    exact ext_inner_right ℂ fun z => by
      simp only [ContinuousLinearMap.adjoint_inner_left,
        ContinuousLinearMap.sub_apply, inner_sub_left, inner_sub_right]
  rw [hadjoint_sub]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply, map_sub]

theorem g8MetricCutoffLeakageSourceCrossOperator_isTraceClassAlong
    {ι ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ι ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) (n : Nat) :
    PositiveTrace.IsTraceClassAlong sourceBasis
      (g8MetricCutoffLeakageSourceCrossOperator owner lambda family globalBasis sourceBasis n) := by
  exact g8MetricCutoffChannel_isTraceClassAlong owner lambda family globalBasis sourceBasis n
    (g8MetricLeakageCoframe lambda family) (sourceInclusion lambda)

/-- The transpose leakage/source cross channel, retained separately for the
ordinary-trace adjoint ledger. -/
noncomputable def g8MetricCutoffSourceLeakageCrossOperator
    {ι ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ι ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) (n : Nat) :
    sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
  g8MetricCutoffChannel owner lambda family globalBasis sourceBasis n
    (sourceInclusion lambda) (g8MetricLeakageCoframe lambda family)

theorem g8MetricCutoffSourceLeakageCrossOperator_isTraceClassAlong
    {ι ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ι ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) (n : Nat) :
    PositiveTrace.IsTraceClassAlong sourceBasis
      (g8MetricCutoffSourceLeakageCrossOperator owner lambda family globalBasis sourceBasis n) := by
  exact g8MetricCutoffChannel_isTraceClassAlong owner lambda family globalBasis sourceBasis n
    (sourceInclusion lambda) (g8MetricLeakageCoframe lambda family)

/-- Exact four-channel expansion of the literal cutoff metric operator.
No channel has yet been identified with the finite prime-power scalar. -/
theorem g8PhysicalMetricCutoffOperator_eq_fourChannels
    {ι ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ι ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) (n : Nat) :
    g8PhysicalMetricCutoffOperator owner lambda family globalBasis sourceBasis n =
      g8MetricCutoffChannel owner lambda family globalBasis sourceBasis n
          (g8MetricSurvivorCoframe lambda family) (g8MetricSurvivorCoframe lambda family) +
        g8MetricCutoffChannel owner lambda family globalBasis sourceBasis n
          (g8MetricSurvivorCoframe lambda family)
          (g8MetricVisibleBoundaryCoframe lambda family) +
        g8MetricCutoffChannel owner lambda family globalBasis sourceBasis n
          (g8MetricVisibleBoundaryCoframe lambda family)
          (g8MetricSurvivorCoframe lambda family) +
        g8MetricCutoffChannel owner lambda family globalBasis sourceBasis n
          (g8MetricVisibleBoundaryCoframe lambda family)
          (g8MetricVisibleBoundaryCoframe lambda family) := by
  rw [g8PhysicalMetricCutoffOperator]
  rw [finiteEulerMetricCoframe_eq_g8MetricSurvivor_add_visibleBoundary]
  apply ContinuousLinearMap.ext
  intro x
  simp only [g8MetricCutoffChannel, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.adjoint.map_add, map_add]
  abel

/-- The four-channel identity remains valid after taking the ordinary trace on
the named source basis. -/
theorem ordinaryTraceAlong_g8PhysicalMetricCutoffOperator_eq_fourChannels
    {ι ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ι ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) (n : Nat) :
    ordinaryTraceAlong sourceBasis
        (g8PhysicalMetricCutoffOperator owner lambda family globalBasis sourceBasis n) =
      ordinaryTraceAlong sourceBasis
        (g8MetricCutoffChannel owner lambda family globalBasis sourceBasis n
          (g8MetricSurvivorCoframe lambda family) (g8MetricSurvivorCoframe lambda family)) +
        ordinaryTraceAlong sourceBasis
          (g8MetricCutoffChannel owner lambda family globalBasis sourceBasis n
            (g8MetricSurvivorCoframe lambda family)
            (g8MetricVisibleBoundaryCoframe lambda family)) +
        ordinaryTraceAlong sourceBasis
          (g8MetricCutoffChannel owner lambda family globalBasis sourceBasis n
            (g8MetricVisibleBoundaryCoframe lambda family)
            (g8MetricSurvivorCoframe lambda family)) +
        ordinaryTraceAlong sourceBasis
          (g8MetricCutoffChannel owner lambda family globalBasis sourceBasis n
            (g8MetricVisibleBoundaryCoframe lambda family)
            (g8MetricVisibleBoundaryCoframe lambda family)) := by
  have hSS := g8MetricCutoffChannel_isTraceClassAlong owner lambda family
    globalBasis sourceBasis n (g8MetricSurvivorCoframe lambda family)
      (g8MetricSurvivorCoframe lambda family)
  have hSB := g8MetricCutoffChannel_isTraceClassAlong owner lambda family
    globalBasis sourceBasis n (g8MetricSurvivorCoframe lambda family)
      (g8MetricVisibleBoundaryCoframe lambda family)
  have hBS := g8MetricCutoffChannel_isTraceClassAlong owner lambda family
    globalBasis sourceBasis n (g8MetricVisibleBoundaryCoframe lambda family)
      (g8MetricSurvivorCoframe lambda family)
  have hBB := g8MetricCutoffChannel_isTraceClassAlong owner lambda family
    globalBasis sourceBasis n (g8MetricVisibleBoundaryCoframe lambda family)
      (g8MetricVisibleBoundaryCoframe lambda family)
  have hSSSB := isTraceClassAlong_add sourceBasis _ _ hSS hSB
  have hSSSBS := isTraceClassAlong_add sourceBasis _ _ hSSSB hBS
  have hall := isTraceClassAlong_add sourceBasis _ _ hSSSBS hBB
  rw [g8PhysicalMetricCutoffOperator_eq_fourChannels]
  rw [ordinaryTraceAlong_add sourceBasis _ _ hSSSBS hBB]
  rw [ordinaryTraceAlong_add sourceBasis _ _ hSSSB hBS]
  rw [ordinaryTraceAlong_add sourceBasis _ _ hSS hSB]

theorem g8PhysicalMetricCutoffOperator_isTraceClassAlong
    {ι ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ι ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) (n : Nat) :
    PositiveTrace.IsTraceClassAlong sourceBasis
      (g8PhysicalMetricCutoffOperator owner lambda family globalBasis sourceBasis n) := by
  rw [g8PhysicalMetricCutoffOperator_eq_fourChannels]
  have hSS := g8MetricCutoffChannel_isTraceClassAlong owner lambda family
    globalBasis sourceBasis n (g8MetricSurvivorCoframe lambda family)
      (g8MetricSurvivorCoframe lambda family)
  have hSB := g8MetricCutoffChannel_isTraceClassAlong owner lambda family
    globalBasis sourceBasis n (g8MetricSurvivorCoframe lambda family)
      (g8MetricVisibleBoundaryCoframe lambda family)
  have hBS := g8MetricCutoffChannel_isTraceClassAlong owner lambda family
    globalBasis sourceBasis n (g8MetricVisibleBoundaryCoframe lambda family)
      (g8MetricSurvivorCoframe lambda family)
  have hBB := g8MetricCutoffChannel_isTraceClassAlong owner lambda family
    globalBasis sourceBasis n (g8MetricVisibleBoundaryCoframe lambda family)
      (g8MetricVisibleBoundaryCoframe lambda family)
  have hSSSB := isTraceClassAlong_add sourceBasis _ _ hSS hSB
  have hSSSBS := isTraceClassAlong_add sourceBasis _ _ hSSSB hBS
  exact isTraceClassAlong_add sourceBasis _ _ hSSSBS hBB

set_option maxHeartbeats 1000000 in
end
end C1G8P1MetricChannels
end Source
end ConnesWeilRH
