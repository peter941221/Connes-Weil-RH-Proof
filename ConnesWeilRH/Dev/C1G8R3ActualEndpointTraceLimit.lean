/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8AdjointShearGram
import ConnesWeilRH.Dev.C1G8R3InternalProlateGapEnergy
import ConnesWeilRH.Dev.C1G8R3PhysicalCutoffStrongLimit
import ConnesWeilRH.Dev.C1G8R3SurvivorCoframeBridge
import ConnesWeilRH.Dev.C1PositiveTraceTraceContinuity
import ConnesWeilRH.Source.CCM25Concrete.SelectedCrossingOperatorBridge

/-!
# Actual endpoint channel trace limit (the R2 remainder ρ4)

The G8 same-owner readback consumes the source-basis trace of
`g8SourceCutoffPairData … n`, that is `J† ∘L Wₙ† ∘L G ∘L Wₙ ∘L J` with the
fixed adjoint-shear Gram `G`, the expanding physical window `Wₙ`, and the
source inclusion `J`.  This file proves that this trace converges to the
named limit trace at the global root convolution as soon as ONE square-sum
holds: the root-convolution column energy of the source inclusion along the
named basis.  The proof cycles the diagonal to the source basis and
exchanges limit and sum by dominated convergence; the domination uses the
committed window factorization `Wₙ = projection ∘L C` with the projection
of operator norm at most one, so the summable majorant is `‖G‖` times the
gate square-sum.

Together with the record-1497 leakage square-sum and the exact Sonin split,
that one square-sum is exactly the in-Sonin survivor core: the endpoint
channel limit and the survivor energy are gated by the same column
square-sum family.  No unconditional estimate is claimed for the gate, and
RH is not touched.
-/

namespace ConnesWeilRH
namespace Dev

open Filter
open MeasureTheory
open Source.CC20Concrete
open Source.CC20Concrete.CompactRootHalfLinePair
open Source.CC20Concrete.PositiveTrace
open Source.CCM25Concrete
open Source.CCM25Concrete.CCM24FiniteSProjectionTrace
open Source.CCM25Concrete.CCM24FiniteSGramResponse
open Source.CCM25Concrete.CCM24FiniteSBandTrace
open Source.CCM25Concrete.CCM24FiniteSParameterizedEulerProduct
open Source.CCM25Concrete.SelectedCrossingOperatorBridge
open Source.Dev.C1PositiveTraceCutoffAdapter
open Source.Dev.C1PositiveTraceWindowProducer
open Source.Dev.C1PositiveTraceTraceContinuity
open Source.C1G8AdjointShearGram
open scoped InnerProduct InnerProductSpace Topology

noncomputable local instance endpointSourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

private theorem norm_kernelIntervalProjection_le_one
    (a c b : ℝ) : ‖kernelIntervalProjection a c b‖ ≤ (1 : ℝ) := by
  let E := kernelIntervalL2ZeroExtension a c b
  have hE : ‖E‖ ≤ (1 : ℝ) := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro u
    simpa only [E, one_mul] using (norm_kernelIntervalL2ZeroExtension a c b u).le
  have hEadj : ‖E.adjoint‖ ≤ (1 : ℝ) := by
    calc
      ‖E.adjoint‖ = ‖E‖ := ContinuousLinearMap.adjoint.norm_map E
      _ ≤ 1 := hE
  calc
    ‖kernelIntervalProjection a c b‖ = ‖E ∘L E.adjoint‖ := by
      simp [E, kernelIntervalProjection]
    _ ≤ ‖E‖ * ‖E.adjoint‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * 1 := mul_le_mul hE hEadj (norm_nonneg _) (by norm_num)
    _ = 1 := by norm_num

/-- The expanding physical window factor never enlarges root-convolution
images: `Wₙ = projection ∘L C` with a norm-one projection. -/
private theorem norm_g8EndpointWindowFactor_le
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) (n : ℕ)
    (u : finiteSCarrier) :
    ‖fullBoundaryPositiveOperator owner.sourceTest
        (cutoffLower owner.sourceTest n) (cutoffUpper owner.sourceTest n) u‖
      ≤ ‖rootConvolution owner u‖ := by
  have hC : cc20GlobalLogConvolution owner.sourceTest.involution.test =
      rootConvolution owner := rfl
  have hproj : ‖kernelIntervalProjection
      (-(cutoffUpper owner.sourceTest n)) (-(cutoffLower owner.sourceTest n)) 0‖
      ≤ (1 : ℝ) := norm_kernelIntervalProjection_le_one _ _ _
  rw [fullBoundaryPositiveOperator_cutoff_eq_projection_comp_globalConvolution, hC]
  calc
    ‖(kernelIntervalProjection (-(cutoffUpper owner.sourceTest n))
        (-(cutoffLower owner.sourceTest n)) 0) (rootConvolution owner u)‖
        ≤ ‖kernelIntervalProjection (-(cutoffUpper owner.sourceTest n))
            (-(cutoffLower owner.sourceTest n)) 0‖ * ‖rootConvolution owner u‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖rootConvolution owner u‖ :=
      mul_le_mul_of_nonneg_right hproj (norm_nonneg _)
    _ = ‖rootConvolution owner u‖ := one_mul _

/-- The actual endpoint channel operator at stage `n`: the source inclusion,
the adjoint expanding window, the fixed adjoint-shear Gram, the expanding
window, and the source inclusion. -/
noncomputable def g8EndpointSourceCutoffOperator
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) (n : ℕ) :
    sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
  (sourceInclusion lambda).adjoint ∘L
    (fullBoundaryPositiveOperator owner.sourceTest
        (cutoffLower owner.sourceTest n)
        (cutoffUpper owner.sourceTest n)).adjoint ∘L
      g8AdjointShearGram owner lambda family ∘L
        fullBoundaryPositiveOperator owner.sourceTest
          (cutoffLower owner.sourceTest n)
          (cutoffUpper owner.sourceTest n) ∘L sourceInclusion lambda

/-- The limit endpoint channel operator: the same composition with the
expanding window replaced by the global root convolution. -/
noncomputable def g8EndpointSourceCutoffLimitOperator
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
  (sourceInclusion lambda).adjoint ∘L (rootConvolution owner).adjoint ∘L
    g8AdjointShearGram owner lambda family ∘L rootConvolution owner ∘L
      sourceInclusion lambda

/-- The readback trace product is the endpoint channel operator: the pair
legs are the window factor and the middle is the fixed adjoint-shear Gram. -/
theorem g8EndpointSourceCutoffPairData_traceProduct_eq
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    {ν ρ : Type*}
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) (n : ℕ) :
    (g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n).traceProduct =
      g8EndpointSourceCutoffOperator owner lambda family n := by
  unfold g8EndpointSourceCutoffOperator
  rw [g8SourceCutoffPairData_traceProduct_eq, g8CutoffPairData_traceProduct_eq]
  rfl

/-- Diagonal matrix entry of the endpoint channel operator: the window
factor applied to the included vector, read against the fixed Gram. -/
theorem g8EndpointSourceCutoffOperator_inner_apply
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) (n : ℕ)
    (u : sourceSoninCarrier lambda) :
    ⟪u, g8EndpointSourceCutoffOperator owner lambda family n u⟫_ℂ
      = ⟪fullBoundaryPositiveOperator owner.sourceTest
            (cutoffLower owner.sourceTest n)
            (cutoffUpper owner.sourceTest n) (sourceInclusion lambda u),
          g8AdjointShearGram owner lambda family
            (fullBoundaryPositiveOperator owner.sourceTest
              (cutoffLower owner.sourceTest n)
              (cutoffUpper owner.sourceTest n) (sourceInclusion lambda u))⟫_ℂ := by
  simp only [g8EndpointSourceCutoffOperator, ContinuousLinearMap.comp_apply]
  rw [ContinuousLinearMap.adjoint_inner_right,
    ContinuousLinearMap.adjoint_inner_right]

/-- Diagonal matrix entry of the limit endpoint channel operator. -/
theorem g8EndpointSourceCutoffLimitOperator_inner_apply
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (u : sourceSoninCarrier lambda) :
    ⟪u, g8EndpointSourceCutoffLimitOperator owner lambda family u⟫_ℂ
      = ⟪rootConvolution owner (sourceInclusion lambda u),
          g8AdjointShearGram owner lambda family
            (rootConvolution owner (sourceInclusion lambda u))⟫_ℂ := by
  simp only [g8EndpointSourceCutoffLimitOperator, ContinuousLinearMap.comp_apply]
  rw [ContinuousLinearMap.adjoint_inner_right,
    ContinuousLinearMap.adjoint_inner_right]

/-- General short-type engine: if a vector sequence converges strongly,
the paired quadratic inner products against a fixed operator converge. -/
private theorem tendsto_inner_of_tendsto_apply
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : H →L[ℂ] H) {v : ℕ → H} {v₀ : H} (hv : Tendsto v atTop (𝓝 v₀)) :
    Tendsto (fun n : ℕ => ⟪v n, T (v n)⟫_ℂ) atTop (𝓝 (⟪v₀, T v₀⟫_ℂ)) := by
  have hpair : Tendsto (fun n : ℕ => (v n, T (v n))) atTop (𝓝 (v₀, T v₀)) := by
    rw [nhds_prod_eq]
    exact hv.prodMk ((T.continuous.tendsto _).comp hv)
  exact ((continuous_inner (𝕜 := ℂ)).tendsto (v₀, T v₀)).comp hpair

/- The endpoint channel diagonal entries converge, by the committed strong
limit of the expanding window and continuity of the Gram. -/
theorem tendsto_g8EndpointSourceCutoffOperator_inner_apply
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (u : sourceSoninCarrier lambda) :
    Tendsto
      (fun n : ℕ => ⟪u, g8EndpointSourceCutoffOperator owner lambda family n u⟫_ℂ)
      atTop
      (𝓝 (⟪u, g8EndpointSourceCutoffLimitOperator owner lambda family u⟫_ℂ)) := by
  have hstrong : Tendsto
      (fun n : ℕ =>
        fullBoundaryPositiveOperator owner.sourceTest
          (cutoffLower owner.sourceTest n)
          (cutoffUpper owner.sourceTest n) (sourceInclusion lambda u))
      atTop
      (𝓝 (rootConvolution owner (sourceInclusion lambda u))) := by
    simpa only [rootConvolution] using
      tendsto_fullBoundaryPositiveOperator_cutoff_apply owner.sourceTest
        (sourceInclusion lambda u)
  have hWG := tendsto_inner_of_tendsto_apply
    (g8AdjointShearGram owner lambda family)
    (v := fun n : ℕ =>
      fullBoundaryPositiveOperator owner.sourceTest
        (cutoffLower owner.sourceTest n)
        (cutoffUpper owner.sourceTest n) (sourceInclusion lambda u))
    (v₀ := rootConvolution owner (sourceInclusion lambda u)) hstrong
  refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
  have hconst : Tendsto
      (fun _ : ℕ => ⟪u, g8EndpointSourceCutoffLimitOperator owner lambda family u⟫_ℂ)
      atTop
      (𝓝 (⟪u, g8EndpointSourceCutoffLimitOperator owner lambda family u⟫_ℂ)) :=
    tendsto_const_nhds
  have hlimEq := g8EndpointSourceCutoffLimitOperator_inner_apply owner lambda family u
  have hnorm : Tendsto
      (fun e : ℕ =>
        ‖⟪fullBoundaryPositiveOperator owner.sourceTest
              (cutoffLower owner.sourceTest e)
              (cutoffUpper owner.sourceTest e) (sourceInclusion lambda u),
            g8AdjointShearGram owner lambda family
              (fullBoundaryPositiveOperator owner.sourceTest
                (cutoffLower owner.sourceTest e)
                (cutoffUpper owner.sourceTest e) (sourceInclusion lambda u))⟫_ℂ -
          ⟪u, g8EndpointSourceCutoffLimitOperator owner lambda family u⟫_ℂ‖)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [← hlimEq, sub_self, norm_zero] using (hWG.sub hconst).norm
  have hfunEq :
      (fun e : ℕ =>
        ‖⟪u, g8EndpointSourceCutoffOperator owner lambda family e u⟫_ℂ -
          ⟪u, g8EndpointSourceCutoffLimitOperator owner lambda family u⟫_ℂ‖) =
      (fun e : ℕ =>
        ‖⟪fullBoundaryPositiveOperator owner.sourceTest
              (cutoffLower owner.sourceTest e)
              (cutoffUpper owner.sourceTest e) (sourceInclusion lambda u),
            g8AdjointShearGram owner lambda family
              (fullBoundaryPositiveOperator owner.sourceTest
                (cutoffLower owner.sourceTest e)
                (cutoffUpper owner.sourceTest e) (sourceInclusion lambda u))⟫_ℂ -
          ⟪u, g8EndpointSourceCutoffLimitOperator owner lambda family u⟫_ℂ‖) :=
    funext fun n => by
      rw [g8EndpointSourceCutoffOperator_inner_apply owner lambda family n u]
  rw [hfunEq]
  exact hnorm

/-- The endpoint channel diagonal entries are dominated by `‖G‖` times the
root-convolution column energy of the included vector. -/
theorem g8EndpointSourceCutoffOperator_inner_norm_le
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) (n : ℕ)
    (u : sourceSoninCarrier lambda) :
    ‖⟪u, g8EndpointSourceCutoffOperator owner lambda family n u⟫_ℂ‖
      ≤ ‖g8AdjointShearGram owner lambda family‖ *
        ‖rootConvolution owner (sourceInclusion lambda u)‖ ^ 2 := by
  rw [g8EndpointSourceCutoffOperator_inner_apply]
  calc
    ‖⟪fullBoundaryPositiveOperator owner.sourceTest
          (cutoffLower owner.sourceTest n)
          (cutoffUpper owner.sourceTest n) (sourceInclusion lambda u),
        g8AdjointShearGram owner lambda family
          (fullBoundaryPositiveOperator owner.sourceTest
            (cutoffLower owner.sourceTest n)
            (cutoffUpper owner.sourceTest n) (sourceInclusion lambda u))⟫_ℂ‖
        ≤ ‖fullBoundaryPositiveOperator owner.sourceTest
            (cutoffLower owner.sourceTest n)
            (cutoffUpper owner.sourceTest n) (sourceInclusion lambda u)‖ *
          ‖g8AdjointShearGram owner lambda family
            (fullBoundaryPositiveOperator owner.sourceTest
              (cutoffLower owner.sourceTest n)
              (cutoffUpper owner.sourceTest n) (sourceInclusion lambda u))‖ :=
      norm_inner_le_norm _ _
    _ ≤ ‖fullBoundaryPositiveOperator owner.sourceTest
          (cutoffLower owner.sourceTest n)
          (cutoffUpper owner.sourceTest n) (sourceInclusion lambda u)‖ *
        (‖g8AdjointShearGram owner lambda family‖ *
          ‖fullBoundaryPositiveOperator owner.sourceTest
            (cutoffLower owner.sourceTest n)
            (cutoffUpper owner.sourceTest n) (sourceInclusion lambda u)‖) :=
      mul_le_mul_of_nonneg_left
        ((g8AdjointShearGram owner lambda family).le_opNorm _) (norm_nonneg _)
    _ = ‖g8AdjointShearGram owner lambda family‖ *
        ‖fullBoundaryPositiveOperator owner.sourceTest
          (cutoffLower owner.sourceTest n)
          (cutoffUpper owner.sourceTest n) (sourceInclusion lambda u)‖ ^ 2 := by
      ring
    _ ≤ ‖g8AdjointShearGram owner lambda family‖ *
        ‖rootConvolution owner (sourceInclusion lambda u)‖ ^ 2 :=
      mul_le_mul_of_nonneg_left
        ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2
          (norm_g8EndpointWindowFactor_le owner n (sourceInclusion lambda u)))
        (norm_nonneg _)

/-- The actual G8 endpoint channel trace converges to the named limit trace
under exactly one square-sum gate: the root-convolution column energy of the
source inclusion along the named source basis.  This discharges the ρ4
remainder of the R2 readback identity conditionally on that gate. -/
theorem tendsto_g8EndpointSourceCutoffPairData_trace
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    {ν ρ : Type*}
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda))
    (hgate : Summable fun i : ρ =>
      ‖rootConvolution owner ((sourceInclusion lambda) (sourceBasis i))‖ ^ 2) :
    Tendsto
      (fun n => ordinaryTraceAlong sourceBasis
        (g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n).traceProduct)
      atTop
      (𝓝 (ordinaryTraceAlong sourceBasis
        (g8EndpointSourceCutoffLimitOperator owner lambda family))) := by
  have hseq : (fun n => ordinaryTraceAlong sourceBasis
      (g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n).traceProduct) =
      (fun n => ordinaryTraceAlong sourceBasis
        (g8EndpointSourceCutoffOperator owner lambda family n)) := by
    funext n
    rw [g8EndpointSourceCutoffPairData_traceProduct_eq]
  rw [hseq]
  exact tendsto_ordinaryTraceAlong_of_dominated_diagonal sourceBasis
    (fun n => g8EndpointSourceCutoffOperator owner lambda family n)
    (g8EndpointSourceCutoffLimitOperator owner lambda family)
    (fun i => ‖g8AdjointShearGram owner lambda family‖ *
      ‖rootConvolution owner ((sourceInclusion lambda) (sourceBasis i))‖ ^ 2)
    (hgate.mul_left ‖g8AdjointShearGram owner lambda family‖)
    (fun i =>
      tendsto_g8EndpointSourceCutoffOperator_inner_apply owner lambda family
        (sourceBasis i))
    (fun n i =>
      g8EndpointSourceCutoffOperator_inner_norm_le owner lambda family n
        (sourceBasis i))

/-- The endpoint gate is exactly the in-Sonin survivor core.  By the exact
Sonin split the ambient root column energy is the in-Sonin core plus the
leakage band, and the leakage band is unconditionally square-summable by
record 1497; hence the gate holds if and only if the in-Sonin core does. -/
theorem g8EndpointGate_iff_survivorCore
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    {ρ : Type*} (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) :
    (Summable fun i : ρ =>
      ‖rootConvolution owner ((sourceInclusion lambda) (sourceBasis i))‖ ^ 2) ↔
    Summable fun i : ρ =>
      ‖((sourceInclusion lambda).adjoint ∘L rootConvolution owner ∘L
        sourceInclusion lambda) (sourceBasis i)‖ ^ 2 := by
  constructor
  · intro hgate
    refine Summable.of_nonneg_of_le (fun i => sq_nonneg _) (fun i => ?_) hgate
    have key := g8BridgeSoninCarrier_normSq_split lambda
      (rootConvolution owner ((sourceInclusion lambda) (sourceBasis i)))
    simp only [ContinuousLinearMap.comp_apply] at key ⊢
    have h2 : 0 ≤ ‖(ContinuousLinearMap.id ℂ finiteSCarrier -
        sourceSoninProjection lambda)
        (rootConvolution owner ((sourceInclusion lambda) (sourceBasis i)))‖ ^ 2 :=
      sq_nonneg _
    linarith
  · intro hcore
    have hout := selectedRoot_sourceSoninLeakage_sourceBasis_normSq_summable
      owner lambda sourceBasis
    refine Summable.of_nonneg_of_le (fun i => sq_nonneg _) (fun i => ?_)
      (hcore.add hout)
    have key := g8BridgeSoninCarrier_normSq_split lambda
      (rootConvolution owner ((sourceInclusion lambda) (sourceBasis i)))
    simp only [ContinuousLinearMap.comp_apply] at key ⊢
    linarith

/-- The endpoint channel trace converges under the in-Sonin survivor core
alone: the gate of the main theorem is discharged by the exact Sonin split
plus the record-1497 leakage square-sum. -/
theorem tendsto_g8EndpointSourceCutoffPairData_trace_of_survivorCore
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    {ν ρ : Type*}
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda))
    (hcore : Summable fun i : ρ =>
      ‖((sourceInclusion lambda).adjoint ∘L rootConvolution owner ∘L
        sourceInclusion lambda) (sourceBasis i)‖ ^ 2) :
    Tendsto
      (fun n => ordinaryTraceAlong sourceBasis
        (g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n).traceProduct)
      atTop
      (𝓝 (ordinaryTraceAlong sourceBasis
        (g8EndpointSourceCutoffLimitOperator owner lambda family))) :=
  tendsto_g8EndpointSourceCutoffPairData_trace owner lambda family globalBasis
    sourceBasis ((g8EndpointGate_iff_survivorCore owner lambda sourceBasis).mpr hcore)

end Dev
end ConnesWeilRH
