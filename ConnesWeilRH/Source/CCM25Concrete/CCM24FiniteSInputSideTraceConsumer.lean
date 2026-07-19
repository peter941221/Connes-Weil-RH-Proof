/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCommonBoundaryPair
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSJuliaCausal
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSJuliaSchur
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSNormalizedCoframe
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSNormalizedPhysicalResponse

-- These diagonal trace consumers normalize several nested Hilbert--Schmidt
-- bounds; keep enough heartbeat budget for the elaborator to close them.
set_option maxHeartbeats 1000000

/-!
# Input-side common-root trace consumer

The physical boundary owner has two different source-side inputs.  This is
strictly more general than the postcomposition-only `CommonRootS2Producer`:
the left and right Hilbert--Schmidt columns may see different projections of
the same source basis.

The consumer below keeps those two root energies separate and uses the actual
Julia range energy on the right.  It proves the estimate from the pair data
itself; no Douglas factorization, prefix bound, or Gate 3U premise is stored.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSInputSideTraceConsumer

open MeasureTheory
open CC20Concrete
open scoped InnerProduct InnerProductSpace
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSJuliaBessel
open CCM24FiniteSJuliaCausal
open CCM24FiniteSJuliaSchur
open CCM24FiniteSProjectionTrace
open CCM24FiniteSGramResponse
open CCM24FiniteSInverseMetric
open CCM24FiniteSCoframeResponse
open CCM24FiniteSBandTrace
open CCM24FiniteSTwoSidedRootRecombination
open CCM24FiniteSNormalizedCoframe
open CC20Concrete.CompactRootHalfLinePair
open CC20Concrete.CompactConvolutionSupport
open CCM24SourceProlateTrace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

theorem inputSideRootS2Producer_ordinaryTrace_norm_le
    {ι H K G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ H}
    (producer : InputSideRootS2Producer (K := K) (G := G) sourceBasis) :
    ‖CC20Concrete.PositiveTrace.ordinaryTraceAlong sourceBasis
        producer.response‖ ≤
      (1 / 2 : ℝ) *
        (‖producer.leftFactor‖ ^ 2 *
            (∑' i, ‖producer.root
              (producer.leftInput (sourceBasis i))‖ ^ 2) +
          ∑' i, ‖producer.root
            (producer.rightInput (sourceBasis i))‖ ^ 2) := by
  let data := inputSideRootS2PairData producer
  have hresponse : data.traceProduct = producer.response :=
    inputSideRootS2PairData_traceProduct_eq_response producer
  have htrace : CC20Concrete.PositiveTrace.IsTraceClassAlong sourceBasis
      producer.response := by
    rw [← hresponse]
    exact data.traceProduct_isTraceClassAlong
  have hdiag := htrace.norm
  have hleft : Summable (fun i =>
      ‖producer.root (producer.leftInput (sourceBasis i))‖ ^ 2) :=
    producer.leftRoot_summable_normSq
  have hright : Summable (fun i =>
      ‖producer.root (producer.rightInput (sourceBasis i))‖ ^ 2) :=
    producer.rightRoot_summable_normSq
  have hrange : Summable (fun i =>
      juliaRangeEnergy producer.steps
        (producer.root (producer.rightInput (sourceBasis i)))) :=
    summable_juliaRangeEnergy_comp sourceBasis producer.steps
      (producer.root ∘L producer.rightInput) producer.rightRoot_summable_normSq
  have hmajorant : Summable (fun i =>
      (1 / 2 : ℝ) *
        (‖producer.leftFactor‖ ^ 2 *
            ‖producer.root
              (producer.leftInput (sourceBasis i))‖ ^ 2 +
          juliaRangeEnergy producer.steps
            (producer.root (producer.rightInput (sourceBasis i))))) := by
    have hleft' : Summable (fun i =>
        (1 / 2 : ℝ) * (‖producer.leftFactor‖ ^ 2 *
          ‖producer.root (producer.leftInput (sourceBasis i))‖ ^ 2)) := by
      apply (hleft.mul_left ((1 / 2 : ℝ) * ‖producer.leftFactor‖ ^ 2)).congr
      intro i
      ring
    have hright' : Summable (fun i =>
        (1 / 2 : ℝ) * juliaRangeEnergy producer.steps
          (producer.root (producer.rightInput (sourceBasis i)))) :=
      hrange.mul_left (1 / 2 : ℝ)
    apply (hleft'.add hright').congr
    intro i
    ring
  have hpoint : ∀ i, (‖⟪sourceBasis i,
      producer.response (sourceBasis i)⟫_ℂ‖) ≤
      (1 / 2 : ℝ) *
        (‖producer.leftFactor‖ ^ 2 *
            ‖producer.root
              (producer.leftInput (sourceBasis i))‖ ^ 2 +
          juliaRangeEnergy producer.steps
            (producer.root (producer.rightInput (sourceBasis i)))) := by
    intro i
    have hdiagonal :
        ⟪sourceBasis i, producer.response (sourceBasis i)⟫_ℂ =
          ⟪data.left (sourceBasis i), data.right (sourceBasis i)⟫_ℂ := by
      rw [← hresponse]
      exact data.traceProduct_diagonal i
    rw [hdiagonal]
    have hleftPoint : ‖data.left (sourceBasis i)‖ ^ 2 ≤
        ‖producer.leftFactor‖ ^ 2 *
          ‖producer.root
            (producer.leftInput (sourceBasis i))‖ ^ 2 := by
      change ‖producer.leftFactor
          (producer.root (producer.leftInput (sourceBasis i)))‖ ^ 2 ≤ _
      calc
        ‖producer.leftFactor
            (producer.root (producer.leftInput (sourceBasis i)))‖ ^ 2 ≤
            (‖producer.leftFactor‖ *
              ‖producer.root (producer.leftInput (sourceBasis i))‖) ^ 2 := by
          gcongr
          exact producer.leftFactor.le_opNorm _
        _ = ‖producer.leftFactor‖ ^ 2 *
            ‖producer.root
              (producer.leftInput (sourceBasis i))‖ ^ 2 := by ring
    have hrightPoint : ‖data.right (sourceBasis i)‖ ^ 2 ≤
        juliaRangeEnergy producer.steps
          (producer.root (producer.rightInput (sourceBasis i))) := by
      change ‖producer.rightFactor
          (producer.root (producer.rightInput (sourceBasis i)))‖ ^ 2 ≤ _
      exact producer.right_energy_le i
    have hsum : ‖data.left (sourceBasis i)‖ ^ 2 +
        ‖data.right (sourceBasis i)‖ ^ 2 ≤
        ‖producer.leftFactor‖ ^ 2 *
            ‖producer.root
              (producer.leftInput (sourceBasis i))‖ ^ 2 +
          juliaRangeEnergy producer.steps
            (producer.root (producer.rightInput (sourceBasis i))) :=
      add_le_add hleftPoint hrightPoint
    calc
      ‖⟪data.left (sourceBasis i), data.right (sourceBasis i)⟫_ℂ‖ ≤
          ‖data.left (sourceBasis i)‖ * ‖data.right (sourceBasis i)‖ :=
        norm_inner_le_norm _ _
      _ ≤ (1 / 2 : ℝ) *
          (‖data.left (sourceBasis i)‖ ^ 2 +
            ‖data.right (sourceBasis i)‖ ^ 2) := by
        nlinarith [sq_nonneg
          (‖data.left (sourceBasis i)‖ -
            ‖data.right (sourceBasis i)‖)]
      _ ≤ (1 / 2 : ℝ) *
          (‖producer.leftFactor‖ ^ 2 *
              ‖producer.root
                (producer.leftInput (sourceBasis i))‖ ^ 2 +
            juliaRangeEnergy producer.steps
              (producer.root (producer.rightInput (sourceBasis i)))) := by
        exact mul_le_mul_of_nonneg_left hsum (by norm_num)
  have hraw :
      ‖CC20Concrete.PositiveTrace.ordinaryTraceAlong sourceBasis
          producer.response‖ ≤
        (1 / 2 : ℝ) *
          (‖producer.leftFactor‖ ^ 2 *
              (∑' i, ‖producer.root
                (producer.leftInput (sourceBasis i))‖ ^ 2) +
            ∑' i, juliaRangeEnergy producer.steps
              (producer.root (producer.rightInput (sourceBasis i)))) := by
    rw [CC20Concrete.PositiveTrace.ordinaryTraceAlong]
    calc
      ‖∑' i, ⟪sourceBasis i,
          producer.response (sourceBasis i)⟫_ℂ‖ ≤
          ∑' i, ‖⟪sourceBasis i,
            producer.response (sourceBasis i)⟫_ℂ‖ :=
        norm_tsum_le_tsum_norm hdiag
      _ ≤ ∑' i, (1 / 2 : ℝ) *
          (‖producer.leftFactor‖ ^ 2 *
              ‖producer.root
                (producer.leftInput (sourceBasis i))‖ ^ 2 +
            juliaRangeEnergy producer.steps
              (producer.root (producer.rightInput (sourceBasis i)))) :=
        hdiag.tsum_le_tsum hpoint hmajorant
      _ = (1 / 2 : ℝ) *
        (‖producer.leftFactor‖ ^ 2 *
            (∑' i, ‖producer.root
              (producer.leftInput (sourceBasis i))‖ ^ 2) +
          ∑' i, juliaRangeEnergy producer.steps
              (producer.root (producer.rightInput (sourceBasis i)))) := by
        rw [tsum_mul_left,
          (hleft.mul_left (‖producer.leftFactor‖ ^ 2)).tsum_add hrange,
          tsum_mul_left]
  have hrange_le :
      (∑' i, juliaRangeEnergy producer.steps
        (producer.root (producer.rightInput (sourceBasis i)))) ≤
        ∑' i, ‖producer.root
          (producer.rightInput (sourceBasis i))‖ ^ 2 :=
    tsum_juliaRangeEnergy_le producer.steps
      (fun i => producer.root (producer.rightInput (sourceBasis i))) hright
  exact hraw.trans (by
    gcongr)

/-!
The Douglas-aligned owner needs a right majorant different from the raw Julia
energy: the factor norm can be a polynomial source constant.  This helper
keeps that majorant abstract, so the actual Julia column is used only to prove
the source-specific pointwise inequality before the trace is summed.
-/
theorem inputSideRootS2Producer_ordinaryTrace_norm_le_of_right_majorant
    {ι H K G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ H}
    (producer : InputSideRootS2Producer (K := K) (G := G) sourceBasis)
    (rightMajorant : ι → ℝ)
    (hrightMajorant_nonneg : ∀ i, 0 ≤ rightMajorant i)
    (hrightMajorant_summable : Summable rightMajorant)
    (hrightPoint : ∀ i,
      ‖producer.rightFactor
          (producer.root (producer.rightInput (sourceBasis i)))‖ ^ 2 ≤
        rightMajorant i) :
    ‖CC20Concrete.PositiveTrace.ordinaryTraceAlong sourceBasis
        producer.response‖ ≤
      (1 / 2 : ℝ) *
        (‖producer.leftFactor‖ ^ 2 *
            (∑' i, ‖producer.root
              (producer.leftInput (sourceBasis i))‖ ^ 2) +
          ∑' i, rightMajorant i) := by
  let data := inputSideRootS2PairData producer
  have hresponse : data.traceProduct = producer.response :=
    inputSideRootS2PairData_traceProduct_eq_response producer
  have htrace : CC20Concrete.PositiveTrace.IsTraceClassAlong sourceBasis
      producer.response := by
    rw [← hresponse]
    exact data.traceProduct_isTraceClassAlong
  have hdiag := htrace.norm
  have hleft : Summable (fun i =>
      ‖producer.root (producer.leftInput (sourceBasis i))‖ ^ 2) :=
    producer.leftRoot_summable_normSq
  have hmajorant : Summable (fun i =>
      (1 / 2 : ℝ) *
        (‖producer.leftFactor‖ ^ 2 *
            ‖producer.root (producer.leftInput (sourceBasis i))‖ ^ 2 +
          rightMajorant i)) := by
    have hleft' : Summable (fun i =>
        (1 / 2 : ℝ) * (‖producer.leftFactor‖ ^ 2 *
          ‖producer.root (producer.leftInput (sourceBasis i))‖ ^ 2)) := by
      apply (hleft.mul_left ((1 / 2 : ℝ) * ‖producer.leftFactor‖ ^ 2)).congr
      intro i
      ring
    have hright' : Summable (fun i =>
        (1 / 2 : ℝ) * rightMajorant i) :=
      hrightMajorant_summable.mul_left (1 / 2 : ℝ)
    apply (hleft'.add hright').congr
    intro i
    ring
  have hpoint : ∀ i, (‖⟪sourceBasis i,
      producer.response (sourceBasis i)⟫_ℂ‖) ≤
      (1 / 2 : ℝ) *
        (‖producer.leftFactor‖ ^ 2 *
            ‖producer.root (producer.leftInput (sourceBasis i))‖ ^ 2 +
          rightMajorant i) := by
    intro i
    have hdiagonal :
        ⟪sourceBasis i, producer.response (sourceBasis i)⟫_ℂ =
          ⟪data.left (sourceBasis i), data.right (sourceBasis i)⟫_ℂ := by
      rw [← hresponse]
      exact data.traceProduct_diagonal i
    rw [hdiagonal]
    have hleftPoint : ‖data.left (sourceBasis i)‖ ^ 2 ≤
        ‖producer.leftFactor‖ ^ 2 *
          ‖producer.root (producer.leftInput (sourceBasis i))‖ ^ 2 := by
      change ‖producer.leftFactor
          (producer.root (producer.leftInput (sourceBasis i)))‖ ^ 2 ≤ _
      calc
        ‖producer.leftFactor
            (producer.root (producer.leftInput (sourceBasis i)))‖ ^ 2 ≤
            (‖producer.leftFactor‖ *
              ‖producer.root (producer.leftInput (sourceBasis i))‖) ^ 2 := by
          gcongr
          exact producer.leftFactor.le_opNorm _
        _ = ‖producer.leftFactor‖ ^ 2 *
            ‖producer.root (producer.leftInput (sourceBasis i))‖ ^ 2 := by
          ring
    have hrightPoint_i : ‖data.right (sourceBasis i)‖ ^ 2 ≤
        rightMajorant i := by
      change ‖producer.rightFactor
          (producer.root (producer.rightInput (sourceBasis i)))‖ ^ 2 ≤ _
      exact hrightPoint i
    have hsum : ‖data.left (sourceBasis i)‖ ^ 2 +
        ‖data.right (sourceBasis i)‖ ^ 2 ≤
        ‖producer.leftFactor‖ ^ 2 *
            ‖producer.root (producer.leftInput (sourceBasis i))‖ ^ 2 +
          rightMajorant i :=
      add_le_add hleftPoint hrightPoint_i
    calc
      ‖⟪data.left (sourceBasis i), data.right (sourceBasis i)⟫_ℂ‖ ≤
          ‖data.left (sourceBasis i)‖ * ‖data.right (sourceBasis i)‖ :=
        norm_inner_le_norm _ _
      _ ≤ (1 / 2 : ℝ) *
          (‖data.left (sourceBasis i)‖ ^ 2 +
            ‖data.right (sourceBasis i)‖ ^ 2) := by
        nlinarith [sq_nonneg
          (‖data.left (sourceBasis i)‖ -
            ‖data.right (sourceBasis i)‖)]
      _ ≤ (1 / 2 : ℝ) *
          (‖producer.leftFactor‖ ^ 2 *
              ‖producer.root (producer.leftInput (sourceBasis i))‖ ^ 2 +
            rightMajorant i) := by
        exact mul_le_mul_of_nonneg_left hsum (by norm_num)
  rw [CC20Concrete.PositiveTrace.ordinaryTraceAlong]
  calc
    ‖∑' i, ⟪sourceBasis i,
        producer.response (sourceBasis i)⟫_ℂ‖ ≤
        ∑' i, ‖⟪sourceBasis i,
          producer.response (sourceBasis i)⟫_ℂ‖ :=
      norm_tsum_le_tsum_norm hdiag
    _ ≤ ∑' i, (1 / 2 : ℝ) *
        (‖producer.leftFactor‖ ^ 2 *
            ‖producer.root (producer.leftInput (sourceBasis i))‖ ^ 2 +
          rightMajorant i) :=
      hdiag.tsum_le_tsum hpoint hmajorant
    _ = (1 / 2 : ℝ) *
        (‖producer.leftFactor‖ ^ 2 *
            (∑' i, ‖producer.root
              (producer.leftInput (sourceBasis i))‖ ^ 2) +
          ∑' i, rightMajorant i) := by
      rw [tsum_mul_left,
        (hleft.mul_left (‖producer.leftFactor‖ ^ 2)).tsum_add
          hrightMajorant_summable,
        tsum_mul_left]

/-!
The signed physical ledger may have a left column controlled by a genuine
co-defect column whose input carrier is different from the Hilbert--Schmidt
root carrier.  In that situation the theorem above is too specialized: its
left majorant is forced to be `‖leftFactor‖² * ‖root‖²`.  This version keeps
both diagonal majorants explicit, so a source proof can transport the
co-defect energy without identifying unrelated carriers.
-/
theorem inputSideRootS2Producer_ordinaryTrace_norm_le_of_two_majorants
    {ι H K G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ H}
    (producer : InputSideRootS2Producer (K := K) (G := G) sourceBasis)
    (leftMajorant rightMajorant : ι → ℝ)
    (hleftMajorant_nonneg : ∀ i, 0 ≤ leftMajorant i)
    (hrightMajorant_nonneg : ∀ i, 0 ≤ rightMajorant i)
    (hleftMajorant_summable : Summable leftMajorant)
    (hrightMajorant_summable : Summable rightMajorant)
    (hleftPoint : ∀ i,
      ‖producer.leftFactor
          (producer.root (producer.leftInput (sourceBasis i)))‖ ^ 2 ≤
        leftMajorant i)
    (hrightPoint : ∀ i,
      ‖producer.rightFactor
          (producer.root (producer.rightInput (sourceBasis i)))‖ ^ 2 ≤
        rightMajorant i) :
    ‖CC20Concrete.PositiveTrace.ordinaryTraceAlong sourceBasis
        producer.response‖ ≤
      (1 / 2 : ℝ) *
        ((∑' i, leftMajorant i) + ∑' i, rightMajorant i) := by
  let data := inputSideRootS2PairData producer
  have hresponse : data.traceProduct = producer.response :=
    inputSideRootS2PairData_traceProduct_eq_response producer
  have htrace : CC20Concrete.PositiveTrace.IsTraceClassAlong sourceBasis
      producer.response := by
    rw [← hresponse]
    exact data.traceProduct_isTraceClassAlong
  have hdiag := htrace.norm
  have hmajorant : Summable (fun i =>
      (1 / 2 : ℝ) * (leftMajorant i + rightMajorant i)) := by
    have hleft := hleftMajorant_summable.mul_left (1 / 2 : ℝ)
    have hright := hrightMajorant_summable.mul_left (1 / 2 : ℝ)
    apply (hleft.add hright).congr
    intro i
    ring
  have hpoint : ∀ i, (‖⟪sourceBasis i,
      producer.response (sourceBasis i)⟫_ℂ‖) ≤
      (1 / 2 : ℝ) * (leftMajorant i + rightMajorant i) := by
    intro i
    have hdiagonal :
        ⟪sourceBasis i, producer.response (sourceBasis i)⟫_ℂ =
          ⟪data.left (sourceBasis i), data.right (sourceBasis i)⟫_ℂ := by
      rw [← hresponse]
      exact data.traceProduct_diagonal i
    rw [hdiagonal]
    have hsum : ‖data.left (sourceBasis i)‖ ^ 2 +
        ‖data.right (sourceBasis i)‖ ^ 2 ≤
        leftMajorant i + rightMajorant i := by
      exact add_le_add (by
        change ‖producer.leftFactor
            (producer.root (producer.leftInput (sourceBasis i)))‖ ^ 2 ≤ _
        exact hleftPoint i) (by
        change ‖producer.rightFactor
            (producer.root (producer.rightInput (sourceBasis i)))‖ ^ 2 ≤ _
        exact hrightPoint i)
    calc
      ‖⟪data.left (sourceBasis i), data.right (sourceBasis i)⟫_ℂ‖ ≤
          ‖data.left (sourceBasis i)‖ * ‖data.right (sourceBasis i)‖ :=
        norm_inner_le_norm _ _
      _ ≤ (1 / 2 : ℝ) *
          (‖data.left (sourceBasis i)‖ ^ 2 +
            ‖data.right (sourceBasis i)‖ ^ 2) := by
        nlinarith [sq_nonneg (‖data.left (sourceBasis i)‖ -
          ‖data.right (sourceBasis i)‖)]
      _ ≤ (1 / 2 : ℝ) * (leftMajorant i + rightMajorant i) := by
        exact mul_le_mul_of_nonneg_left hsum (by norm_num)
  rw [CC20Concrete.PositiveTrace.ordinaryTraceAlong]
  calc
    ‖∑' i, ⟪sourceBasis i,
        producer.response (sourceBasis i)⟫_ℂ‖ ≤
      ∑' i, ‖⟪sourceBasis i,
          producer.response (sourceBasis i)⟫_ℂ‖ :=
      norm_tsum_le_tsum_norm hdiag
    _ ≤ ∑' i, (1 / 2 : ℝ) * (leftMajorant i + rightMajorant i) :=
      hdiag.tsum_le_tsum hpoint hmajorant
    _ = (1 / 2 : ℝ) *
        ((∑' i, leftMajorant i) + ∑' i, rightMajorant i) := by
      rw [tsum_mul_left,
        hleftMajorant_summable.tsum_add hrightMajorant_summable]

/-! The actual input-side Douglas owner now consumes the genuine Julia column. -/
theorem douglasAlignedInputSideRootS2Producer_ordinaryTrace_norm_le
    {ι H K G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ H}
    (producer : DouglasAlignedInputSideRootS2Producer (K := K) (G := G) sourceBasis) :
    ‖CC20Concrete.PositiveTrace.ordinaryTraceAlong sourceBasis
        producer.base.response‖ ≤
      (1 / 2 : ℝ) *
        (‖producer.base.leftFactor‖ ^ 2 *
            (∑' i, ‖producer.base.root
              (producer.base.leftInput (sourceBasis i))‖ ^ 2) +
          producer.factorBound ^ 2 *
            (∑' i, ‖producer.base.root
              (producer.base.rightInput (sourceBasis i))‖ ^ 2)) := by
  have hfactorSq_nonneg : 0 ≤ producer.factorBound ^ 2 := sq_nonneg _
  have hmajorant : Summable (fun i =>
      producer.factorBound ^ 2 *
        ‖producer.base.root
          (producer.base.rightInput (sourceBasis i))‖ ^ 2) :=
    producer.base.rightRoot_summable_normSq.mul_left
      (producer.factorBound ^ 2)
  have hpoint : ∀ i,
      0 ≤ producer.factorBound ^ 2 *
        ‖producer.base.root
          (producer.base.rightInput (sourceBasis i))‖ ^ 2 := by
    intro i
    exact mul_nonneg hfactorSq_nonneg (sq_nonneg _)
  have hrightPoint : ∀ i,
      ‖producer.base.rightFactor
          (producer.base.root
            (producer.base.rightInput (sourceBasis i)))‖ ^ 2 ≤
        producer.factorBound ^ 2 *
          ‖producer.base.root
            (producer.base.rightInput (sourceBasis i))‖ ^ 2 := by
    intro i
    exact producer.rightColumn_normSq_le
      (sourceBasis i)
  have hbound := inputSideRootS2Producer_ordinaryTrace_norm_le_of_right_majorant
    producer.base
    (fun i => producer.factorBound ^ 2 *
      ‖producer.base.root
        (producer.base.rightInput (sourceBasis i))‖ ^ 2)
    hpoint hmajorant hrightPoint
  calc
    ‖CC20Concrete.PositiveTrace.ordinaryTraceAlong sourceBasis
        producer.base.response‖ ≤
        (1 / 2 : ℝ) *
          (‖producer.base.leftFactor‖ ^ 2 *
              (∑' i, ‖producer.base.root
                (producer.base.leftInput (sourceBasis i))‖ ^ 2) +
            ∑' i, producer.factorBound ^ 2 *
              ‖producer.base.root
                (producer.base.rightInput (sourceBasis i))‖ ^ 2) := hbound
    _ = (1 / 2 : ℝ) *
        (‖producer.base.leftFactor‖ ^ 2 *
            (∑' i, ‖producer.base.root
              (producer.base.leftInput (sourceBasis i))‖ ^ 2) +
          producer.factorBound ^ 2 *
            (∑' i, ‖producer.base.root
              (producer.base.rightInput (sourceBasis i))‖ ^ 2)) := by
      rw [tsum_mul_left]

/-!
This adapter is the only route from a current-range cascade into the
input-side Douglas consumer.  Its `steps` are generated from the actual
compressed transfers and ambient range-sines; the old base owner's
bookkeeping `steps` cannot be used here.
-/
noncomputable def douglasAlignedInputSideRootS2ProducerOfCurrentRangeJulia
    {ι H K G Kambient : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    [NormedAddCommGroup Kambient] [InnerProductSpace ℂ Kambient]
    [CompleteSpace Kambient]
    {sourceBasis : HilbertBasis ι ℂ H}
    (base : InputSideRootS2Producer (K := K) (G := G) sourceBasis)
    (causalSteps : List (CurrentRangeJuliaStepData K Kambient G))
    (factor : PiLp 2
      (fun _ : Fin (currentRangeJuliaSteps causalSteps).length => G) →L[ℂ] G)
    (factorBound : ℝ) (factorBound_nonneg : 0 ≤ factorBound)
    (factor_norm_le : ‖factor‖ ≤ factorBound)
    (factorization :
      base.rightFactor ∘L base.root ∘L base.rightInput =
        factor ∘L (juliaRangeColumn (currentRangeJuliaSteps causalSteps) ∘L
          base.root ∘L base.rightInput)) :
    DouglasAlignedInputSideRootS2Producer (K := K) (G := G) sourceBasis :=
  douglasAlignedInputSideRootS2ProducerOfJuliaRangeColumn base
    (currentRangeJuliaSteps causalSteps) factor factorBound
    factorBound_nonneg factor_norm_le factorization

@[simp]
theorem douglasAlignedInputSideRootS2ProducerOfCurrentRangeJulia_rangeColumn
    {ι H K G Kambient : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    [NormedAddCommGroup Kambient] [InnerProductSpace ℂ Kambient]
    [CompleteSpace Kambient]
    {sourceBasis : HilbertBasis ι ℂ H}
    (base : InputSideRootS2Producer (K := K) (G := G) sourceBasis)
    (causalSteps : List (CurrentRangeJuliaStepData K Kambient G))
    (factor : PiLp 2
      (fun _ : Fin (currentRangeJuliaSteps causalSteps).length => G) →L[ℂ] G)
    (factorBound : ℝ) (factorBound_nonneg : 0 ≤ factorBound)
    (factor_norm_le : ‖factor‖ ≤ factorBound)
    (factorization :
      base.rightFactor ∘L base.root ∘L base.rightInput =
        factor ∘L (juliaRangeColumn (currentRangeJuliaSteps causalSteps) ∘L
          base.root ∘L base.rightInput)) :
    (douglasAlignedInputSideRootS2ProducerOfCurrentRangeJulia base
      causalSteps factor factorBound factorBound_nonneg factor_norm_le
      factorization).rangeColumn =
      juliaRangeColumn (currentRangeJuliaSteps causalSteps) ∘L
        base.root ∘L base.rightInput := by
  rfl

/-!
The Douglas map can be exposed as a finite coordinate readout instead of an
opaque operator witness.  This is the useful form for the physical boundary
owner: every coordinate is a genuine Julia range output, and the factor norm
is paid for by the sum of the coordinate readout norms.

The equality in `physicalColumn_eq_readout` is still source-specific.  It is
the exact finite cascade identity that must be proved for the boundary
column; no range or factorization equality is inferred from a scalar energy
bound.
-/
noncomputable def inputSidePiLpReadoutSum
    {n : ℕ} {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (readout : Fin n → G →L[ℂ] G) :
    PiLp 2 (fun _ : Fin n => G) →L[ℂ] G :=
  ∑ i, readout i ∘L
    PiLp.proj (p := 2) (β := fun _ : Fin n => G) i

@[simp]
theorem inputSidePiLpReadoutSum_apply
    {n : ℕ} {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (readout : Fin n → G →L[ℂ] G)
    (x : PiLp 2 (fun _ : Fin n => G)) :
    inputSidePiLpReadoutSum readout x = ∑ i, readout i (x i) := by
  simp [inputSidePiLpReadoutSum]

theorem norm_inputSidePiLpReadoutSum_le
    {n : ℕ} {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (readout : Fin n → G →L[ℂ] G) :
    ‖inputSidePiLpReadoutSum readout‖ ≤ ∑ i, ‖readout i‖ := by
  classical
  apply ContinuousLinearMap.opNorm_le_bound _
    (Finset.sum_nonneg fun i _ => norm_nonneg (readout i))
  intro x
  calc
    ‖inputSidePiLpReadoutSum readout x‖ =
        ‖∑ i, readout i (x i)‖ := by
      rw [inputSidePiLpReadoutSum_apply]
    _ ≤ ∑ i, ‖readout i (x i)‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖readout i‖ * ‖x‖ := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        ‖readout i (x i)‖ ≤ ‖readout i‖ * ‖x i‖ :=
          readout i |>.le_opNorm (x i)
        _ ≤ ‖readout i‖ * ‖x‖ := by
          exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le x i)
            (norm_nonneg _)
    _ = (∑ i, ‖readout i‖) * ‖x‖ := by
      rw [Finset.sum_mul]

structure InputSideJuliaCoordinateReadoutData
    {ι H K G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (sourceBasis : HilbertBasis ι ℂ H) where
  base : InputSideRootS2Producer (K := K) (G := G) sourceBasis
  steps : List (JuliaDefectStep K G)
  readout : Fin steps.length → G →L[ℂ] G
  physicalColumn_eq_readout :
    base.rightFactor ∘L base.root ∘L base.rightInput =
      inputSidePiLpReadoutSum readout ∘L
        (juliaRangeColumn steps ∘L base.root ∘L base.rightInput)

noncomputable def InputSideJuliaCoordinateReadoutData.toDouglas
    {ι H K G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ H}
    (data : InputSideJuliaCoordinateReadoutData (K := K) (G := G) sourceBasis) :
    DouglasAlignedInputSideRootS2Producer (K := K) (G := G) sourceBasis :=
  douglasAlignedInputSideRootS2ProducerOfJuliaRangeColumn data.base
    data.steps (inputSidePiLpReadoutSum data.readout)
    (∑ i, ‖data.readout i‖)
    (Finset.sum_nonneg fun i _ => norm_nonneg (data.readout i))
    (norm_inputSidePiLpReadoutSum_le data.readout)
    data.physicalColumn_eq_readout

@[simp]
theorem InputSideJuliaCoordinateReadoutData.toDouglas_factorBound
    {ι H K G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ H}
    (data : InputSideJuliaCoordinateReadoutData (K := K) (G := G) sourceBasis) :
    data.toDouglas.factorBound = ∑ i, ‖data.readout i‖ :=
  rfl

theorem InputSideJuliaCoordinateReadoutData.toDouglas_factor_norm_le
    {ι H K G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ H}
    (data : InputSideJuliaCoordinateReadoutData (K := K) (G := G) sourceBasis) :
    ‖data.toDouglas.factor‖ ≤ ∑ i, ‖data.readout i‖ :=
  norm_inputSidePiLpReadoutSum_le data.readout

/-!
These two constructors bind the coordinate readout to the exact current-range
schedule.  The only remaining source equation is now the physical cascade
readback on the displayed `juliaRangeColumn`; the old base-owner step list is
never consulted.
-/
noncomputable def douglasAlignedInputSideRootS2ProducerOfCurrentRangeJuliaReadout
    {ι H K Kambient G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup Kambient] [InnerProductSpace ℂ Kambient]
    [CompleteSpace Kambient]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ H}
    (base : InputSideRootS2Producer (K := K) (G := G) sourceBasis)
    (causalSteps : List (CurrentRangeJuliaStepData K Kambient G))
    (readout : Fin (currentRangeJuliaSteps causalSteps).length → G →L[ℂ] G)
    (physicalColumn_eq_readout :
      base.rightFactor ∘L base.root ∘L base.rightInput =
        inputSidePiLpReadoutSum readout ∘L
          (juliaRangeColumn (currentRangeJuliaSteps causalSteps) ∘L
            base.root ∘L base.rightInput)) :
    DouglasAlignedInputSideRootS2Producer (K := K) (G := G) sourceBasis :=
  InputSideJuliaCoordinateReadoutData.toDouglas
    { base := base
      steps := currentRangeJuliaSteps causalSteps
      readout := readout
      physicalColumn_eq_readout := physicalColumn_eq_readout }

noncomputable def douglasAlignedInputSideRootS2ProducerOfFactorizedCurrentRangeJuliaReadout
    {ι H K Kambient G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup Kambient] [InnerProductSpace ℂ Kambient]
    [CompleteSpace Kambient]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ H}
    (base : InputSideRootS2Producer (K := K) (G := G) sourceBasis)
    (causalSteps : List (FactorizedCurrentRangeJuliaStepData
      K Kambient G))
    (readout : Fin (factorizedCurrentRangeJuliaSteps causalSteps).length →
      G →L[ℂ] G)
    (physicalColumn_eq_readout :
      base.rightFactor ∘L base.root ∘L base.rightInput =
        inputSidePiLpReadoutSum readout ∘L
          (juliaRangeColumn (factorizedCurrentRangeJuliaSteps causalSteps) ∘L
            base.root ∘L base.rightInput)) :
    DouglasAlignedInputSideRootS2Producer (K := K) (G := G) sourceBasis :=
  InputSideJuliaCoordinateReadoutData.toDouglas
    { base := base
      steps := factorizedCurrentRangeJuliaSteps causalSteps
      readout := readout
      physicalColumn_eq_readout := physicalColumn_eq_readout }

theorem inputSideJuliaCoordinateReadout_ordinaryTrace_norm_le
    {ι H K G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ H}
    (data : InputSideJuliaCoordinateReadoutData (K := K) (G := G) sourceBasis) :
    ‖CC20Concrete.PositiveTrace.ordinaryTraceAlong sourceBasis
        data.base.response‖ ≤
      (1 / 2 : ℝ) *
        (‖data.base.leftFactor‖ ^ 2 *
            (∑' i, ‖data.base.root
              (data.base.leftInput (sourceBasis i))‖ ^ 2) +
          (∑ i, ‖data.readout i‖) ^ 2 *
            (∑' i, ‖data.base.root
              (data.base.rightInput (sourceBasis i))‖ ^ 2)) := by
  have hbound :=
    douglasAlignedInputSideRootS2Producer_ordinaryTrace_norm_le data.toDouglas
  simpa only [InputSideJuliaCoordinateReadoutData.toDouglas_factorBound] using
    hbound

/-!
The factorized current-range adapter is the preferred source entry point.
Every step already carries the defect-factor realization of its weighted
range sine, so this route cannot be instantiated with the old identity row.
-/
noncomputable def douglasAlignedInputSideRootS2ProducerOfFactorizedCurrentRangeJulia
    {ι H K G Kambient : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    [NormedAddCommGroup Kambient] [InnerProductSpace ℂ Kambient]
    [CompleteSpace Kambient]
    {sourceBasis : HilbertBasis ι ℂ H}
    (base : InputSideRootS2Producer (K := K) (G := G) sourceBasis)
    (causalSteps : List (FactorizedCurrentRangeJuliaStepData K Kambient G))
    (factor : PiLp 2
      (fun _ : Fin (factorizedCurrentRangeJuliaSteps causalSteps).length => G) →L[ℂ] G)
    (factorBound : ℝ) (factorBound_nonneg : 0 ≤ factorBound)
    (factor_norm_le : ‖factor‖ ≤ factorBound)
    (factorization :
      base.rightFactor ∘L base.root ∘L base.rightInput =
        factor ∘L (juliaRangeColumn (factorizedCurrentRangeJuliaSteps causalSteps) ∘L
          base.root ∘L base.rightInput)) :
    DouglasAlignedInputSideRootS2Producer (K := K) (G := G) sourceBasis :=
  douglasAlignedInputSideRootS2ProducerOfJuliaRangeColumn base
    (factorizedCurrentRangeJuliaSteps causalSteps) factor factorBound
    factorBound_nonneg factor_norm_le factorization

/-!
The operator-domination entry point removes the last opaque factor from the
current-range adapter.  The caller still has to prove the source-wide
physical estimate; the factor itself is generated by the closed-range
Douglas construction.
-/
noncomputable def douglasAlignedInputSideRootS2ProducerOfFactorizedCurrentRangeJuliaOperatorDomination
    {ι H K Kambient G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    [NormedAddCommGroup Kambient] [InnerProductSpace ℂ Kambient]
    [CompleteSpace Kambient]
    {sourceBasis : HilbertBasis ι ℂ H}
    (base : InputSideRootS2Producer (K := K) (G := G) sourceBasis)
    (causalSteps : List (FactorizedCurrentRangeJuliaStepData K Kambient G))
    (factorBound : ℝ) (factorBound_nonneg : 0 ≤ factorBound)
    (hdom : ∀ x : H,
      ‖base.rightFactor (base.root (base.rightInput x))‖ ≤
        factorBound *
          ‖juliaRangeColumn (factorizedCurrentRangeJuliaSteps causalSteps)
            (base.root (base.rightInput x))‖) :
    DouglasAlignedInputSideRootS2Producer (K := K) (G := G) sourceBasis :=
  douglasAlignedInputSideRootS2ProducerOfOperatorDomination base
    (factorizedCurrentRangeJuliaSteps causalSteps) factorBound
    factorBound_nonneg hdom

/-! The same route entry in the squared-norm form used by a positive operator
inequality. -/
noncomputable def douglasAlignedInputSideRootS2ProducerOfFactorizedCurrentRangeJuliaOperatorNormSqDomination
    {ι H K Kambient G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    [NormedAddCommGroup Kambient] [InnerProductSpace ℂ Kambient]
    [CompleteSpace Kambient]
    {sourceBasis : HilbertBasis ι ℂ H}
    (base : InputSideRootS2Producer (K := K) (G := G) sourceBasis)
    (causalSteps : List (FactorizedCurrentRangeJuliaStepData K Kambient G))
    (factorBound : ℝ) (factorBound_nonneg : 0 ≤ factorBound)
    (hdom : ∀ x : H,
      ‖base.rightFactor (base.root (base.rightInput x))‖ ^ 2 ≤
        factorBound ^ 2 *
          ‖juliaRangeColumn (factorizedCurrentRangeJuliaSteps causalSteps)
            (base.root (base.rightInput x))‖ ^ 2) :
    DouglasAlignedInputSideRootS2Producer (K := K) (G := G) sourceBasis :=
  douglasAlignedInputSideRootS2ProducerOfOperatorNormSqDomination base
    (factorizedCurrentRangeJuliaSteps causalSteps) factorBound
    factorBound_nonneg hdom

/-!
This is the source-owned Schur entry point.  The list consumed by the
Douglas owner is generated from the actual four-corner colligations and their
Schur transfers; a caller cannot silently substitute the old identity row or
an unrelated normalized inverse prefix.
-/
noncomputable def douglasAlignedInputSideRootS2ProducerOfSchurJulia
    {ι H K G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ H}
    (base : InputSideRootS2Producer (K := K) (G := G) sourceBasis)
    (schurSteps : List (SchurJuliaRangeStepData K G))
    (factor : PiLp 2
      (fun _ : Fin (schurJuliaSteps schurSteps).length => G) →L[ℂ] G)
    (factorBound : ℝ) (factorBound_nonneg : 0 ≤ factorBound)
    (factor_norm_le : ‖factor‖ ≤ factorBound)
    (factorization :
      base.rightFactor ∘L base.root ∘L base.rightInput =
        factor ∘L (juliaRangeColumn (schurJuliaSteps schurSteps) ∘L
          base.root ∘L base.rightInput)) :
    DouglasAlignedInputSideRootS2Producer (K := K) (G := G) sourceBasis :=
  douglasAlignedInputSideRootS2ProducerOfJuliaRangeColumn base
    (schurJuliaSteps schurSteps) factor factorBound factorBound_nonneg
    factor_norm_le factorization

theorem douglasAlignedInputSideRootS2ProducerOfSchurJulia_rangeColumn
    {ι H K G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ H}
    (base : InputSideRootS2Producer (K := K) (G := G) sourceBasis)
    (schurSteps : List (SchurJuliaRangeStepData K G))
    (factor : PiLp 2
      (fun _ : Fin (schurJuliaSteps schurSteps).length => G) →L[ℂ] G)
    (factorBound : ℝ) (factorBound_nonneg : 0 ≤ factorBound)
    (factor_norm_le : ‖factor‖ ≤ factorBound)
    (factorization :
      base.rightFactor ∘L base.root ∘L base.rightInput =
        factor ∘L (juliaRangeColumn (schurJuliaSteps schurSteps) ∘L
          base.root ∘L base.rightInput)) :
    (douglasAlignedInputSideRootS2ProducerOfSchurJulia base schurSteps
      factor factorBound factorBound_nonneg factor_norm_le factorization).rangeColumn =
      juliaRangeColumn (schurJuliaSteps schurSteps) ∘L
        base.root ∘L base.rightInput := by
  rfl

/-!
The physical Schur adapter uses the normalized frame column.  It is separate
from `douglasAlignedInputSideRootS2ProducerOfSchurJulia`: that older adapter
consumes the bare transfer `Phi`, which is a Julia coordinate and not the
Proof 390 source frame.
-/
noncomputable def douglasAlignedInputSideRootS2ProducerOfSchurFrameJulia
    {ι H K G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ H}
    (base : InputSideRootS2Producer (K := K) (G := G) sourceBasis)
    (schurSteps : List (SchurFrameJuliaRangeStepData K G))
    (factor : PiLp 2
      (fun _ : Fin (schurFrameJuliaSteps schurSteps).length => G) →L[ℂ] G)
    (factorBound : ℝ) (factorBound_nonneg : 0 ≤ factorBound)
    (factor_norm_le : ‖factor‖ ≤ factorBound)
    (factorization :
      base.rightFactor ∘L base.root ∘L base.rightInput =
        factor ∘L (juliaRangeColumn (schurFrameJuliaSteps schurSteps) ∘L
          base.root ∘L base.rightInput)) :
    DouglasAlignedInputSideRootS2Producer (K := K) (G := G) sourceBasis :=
  douglasAlignedInputSideRootS2ProducerOfJuliaRangeColumn base
    (schurFrameJuliaSteps schurSteps) factor factorBound factorBound_nonneg
    factor_norm_le factorization

theorem douglasAlignedInputSideRootS2ProducerOfSchurFrameJulia_rangeColumn
    {ι H K G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ H}
    (base : InputSideRootS2Producer (K := K) (G := G) sourceBasis)
    (schurSteps : List (SchurFrameJuliaRangeStepData K G))
    (factor : PiLp 2
      (fun _ : Fin (schurFrameJuliaSteps schurSteps).length => G) →L[ℂ] G)
    (factorBound : ℝ) (factorBound_nonneg : 0 ≤ factorBound)
    (factor_norm_le : ‖factor‖ ≤ factorBound)
    (factorization :
      base.rightFactor ∘L base.root ∘L base.rightInput =
        factor ∘L (juliaRangeColumn (schurFrameJuliaSteps schurSteps) ∘L
          base.root ∘L base.rightInput)) :
    (douglasAlignedInputSideRootS2ProducerOfSchurFrameJulia base schurSteps
      factor factorBound factorBound_nonneg factor_norm_le factorization).rangeColumn =
      juliaRangeColumn (schurFrameJuliaSteps schurSteps) ∘L
        base.root ∘L base.rightInput := by
  rfl

theorem inputSideFactorizedCurrentRangeDouglas_ordinaryTrace_norm_le_of_response
    {ι H K G Kambient : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    [NormedAddCommGroup Kambient] [InnerProductSpace ℂ Kambient]
    [CompleteSpace Kambient]
    {sourceBasis : HilbertBasis ι ℂ H}
    (base : InputSideRootS2Producer (K := K) (G := G) sourceBasis)
    (corner : H →L[ℂ] H)
    (hresponse : base.response = corner)
    (causalSteps : List (FactorizedCurrentRangeJuliaStepData K Kambient G))
    (factor : PiLp 2
      (fun _ : Fin (factorizedCurrentRangeJuliaSteps causalSteps).length => G) →L[ℂ] G)
    (factorBound : ℝ) (factorBound_nonneg : 0 ≤ factorBound)
    (factor_norm_le : ‖factor‖ ≤ factorBound)
    (factorization :
      base.rightFactor ∘L base.root ∘L base.rightInput =
        factor ∘L (juliaRangeColumn (factorizedCurrentRangeJuliaSteps causalSteps) ∘L
          base.root ∘L base.rightInput)) :
    ‖CC20Concrete.PositiveTrace.ordinaryTraceAlong sourceBasis corner‖ ≤
      (1 / 2 : ℝ) *
        (‖base.leftFactor‖ ^ 2 *
            (∑' i, ‖base.root (base.leftInput (sourceBasis i))‖ ^ 2) +
          factorBound ^ 2 *
            (∑' i, ‖base.root (base.rightInput (sourceBasis i))‖ ^ 2)) := by
  let producer :=
    douglasAlignedInputSideRootS2ProducerOfFactorizedCurrentRangeJulia base
      causalSteps factor factorBound factorBound_nonneg factor_norm_le
      factorization
  rw [← hresponse]
  exact douglasAlignedInputSideRootS2Producer_ordinaryTrace_norm_le producer

/-!
This is the response-level consumer for a genuine current-range Douglas
factorization.  The `corner` can be the signed fixed-quotient two-branch
operator, so the estimate is applied only after that operator identity has
been established.
-/
theorem inputSideCurrentRangeDouglas_ordinaryTrace_norm_le_of_response
    {ι H K G Kambient : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    [NormedAddCommGroup Kambient] [InnerProductSpace ℂ Kambient]
    [CompleteSpace Kambient]
    {sourceBasis : HilbertBasis ι ℂ H}
    (base : InputSideRootS2Producer (K := K) (G := G) sourceBasis)
    (corner : H →L[ℂ] H)
    (hresponse : base.response = corner)
    (causalSteps : List (CurrentRangeJuliaStepData K Kambient G))
    (factor : PiLp 2
      (fun _ : Fin (currentRangeJuliaSteps causalSteps).length => G) →L[ℂ] G)
    (factorBound : ℝ) (factorBound_nonneg : 0 ≤ factorBound)
    (factor_norm_le : ‖factor‖ ≤ factorBound)
    (factorization :
      base.rightFactor ∘L base.root ∘L base.rightInput =
        factor ∘L (juliaRangeColumn (currentRangeJuliaSteps causalSteps) ∘L
          base.root ∘L base.rightInput)) :
    ‖CC20Concrete.PositiveTrace.ordinaryTraceAlong sourceBasis corner‖ ≤
      (1 / 2 : ℝ) *
        (‖base.leftFactor‖ ^ 2 *
            (∑' i, ‖base.root
              (base.leftInput (sourceBasis i))‖ ^ 2) +
          factorBound ^ 2 *
            (∑' i, ‖base.root
              (base.rightInput (sourceBasis i))‖ ^ 2)) := by
  let producer := douglasAlignedInputSideRootS2ProducerOfCurrentRangeJulia
    base causalSteps factor factorBound factorBound_nonneg factor_norm_le
    factorization
  rw [← hresponse]
  exact douglasAlignedInputSideRootS2Producer_ordinaryTrace_norm_le producer

/-!
The route-facing package keeps the physical response equality and the
current-range Douglas factorization together.  A caller must provide the
actual physical base, not merely a pair with the same two root energies.
-/
structure SourceBandGramCurrentRangeDouglasData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    {ι K G Kambient : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    [NormedAddCommGroup Kambient] [InnerProductSpace ℂ Kambient]
    [CompleteSpace Kambient]
    (sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda)) where
  base : InputSideRootS2Producer (K := K) (G := G) sourceBasis
  base_response_eq : base.response = sourceBandGramResponse owner lambda family
  causalSteps : List (CurrentRangeJuliaStepData K Kambient G)
  factor : PiLp 2
      (fun _ : Fin (currentRangeJuliaSteps causalSteps).length => G) →L[ℂ] G
  factorBound : ℝ
  factorBound_nonneg : 0 ≤ factorBound
  factor_norm_le : ‖factor‖ ≤ factorBound
  factorization :
    base.rightFactor ∘L base.root ∘L base.rightInput =
      factor ∘L (juliaRangeColumn (currentRangeJuliaSteps causalSteps) ∘L
        base.root ∘L base.rightInput)

noncomputable def SourceBandGramCurrentRangeDouglasData.toProducer
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {family : FinitePrimePowerFamily}
    {ι K G Kambient : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    [NormedAddCommGroup Kambient] [InnerProductSpace ℂ Kambient]
    [CompleteSpace Kambient]
    {sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda)}
    (data : SourceBandGramCurrentRangeDouglasData
      (K := K) (G := G) (Kambient := Kambient) owner lambda family
      sourceBasis) :
    DouglasAlignedInputSideRootS2Producer (K := K) (G := G) sourceBasis :=
  douglasAlignedInputSideRootS2ProducerOfCurrentRangeJulia data.base
    data.causalSteps data.factor data.factorBound data.factorBound_nonneg
    data.factor_norm_le data.factorization

theorem SourceBandGramCurrentRangeDouglasData.toProducer_response_eq
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {family : FinitePrimePowerFamily}
    {ι K G Kambient : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    [NormedAddCommGroup Kambient] [InnerProductSpace ℂ Kambient]
    [CompleteSpace Kambient]
    {sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda)}
    (data : SourceBandGramCurrentRangeDouglasData
      (K := K) (G := G) (Kambient := Kambient) owner lambda family
      sourceBasis) :
    data.toProducer.base.response = sourceBandGramResponse owner lambda family := by
  simpa only [SourceBandGramCurrentRangeDouglasData.toProducer] using
    data.base_response_eq

theorem sourceBandGramResponse_ordinaryTrace_norm_le_of_currentRangeDouglas
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    {ι K G Kambient : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    [NormedAddCommGroup Kambient] [InnerProductSpace ℂ Kambient]
    [CompleteSpace Kambient]
    {sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda)}
    (data : SourceBandGramCurrentRangeDouglasData
      (K := K) (G := G) (Kambient := Kambient) owner lambda family
      sourceBasis) :
    ‖CC20Concrete.PositiveTrace.ordinaryTraceAlong sourceBasis
        (sourceBandGramResponse owner lambda family)‖ ≤
      (1 / 2 : ℝ) *
      (‖data.toProducer.base.leftFactor‖ ^ 2 *
            (∑' i, ‖data.toProducer.base.root
              (data.toProducer.base.leftInput (sourceBasis i))‖ ^ 2) +
          data.toProducer.factorBound ^ 2 *
            (∑' i, ‖data.toProducer.base.root
              (data.toProducer.base.rightInput (sourceBasis i))‖ ^ 2)) := by
  rw [← data.toProducer_response_eq]
  exact douglasAlignedInputSideRootS2Producer_ordinaryTrace_norm_le
    data.toProducer

/-!
This is the route-facing interface.  It can only be instantiated after the
corrected physical response has been identified with the base owner and the
actual Julia/Douglas factorization has been supplied.
-/
theorem sourceBandGramResponse_ordinaryTrace_norm_le_of_douglasAlignedInputSide
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    {ι K G : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda)}
    (producer : DouglasAlignedInputSideRootS2Producer (K := K) (G := G) sourceBasis)
    (hresponse : producer.base.response =
      sourceBandGramResponse owner lambda family) :
    ‖CC20Concrete.PositiveTrace.ordinaryTraceAlong sourceBasis
        (sourceBandGramResponse owner lambda family)‖ ≤
      (1 / 2 : ℝ) *
        (‖producer.base.leftFactor‖ ^ 2 *
            (∑' i, ‖producer.base.root
              (producer.base.leftInput (sourceBasis i))‖ ^ 2) +
          producer.factorBound ^ 2 *
            (∑' i, ‖producer.base.root
              (producer.base.rightInput (sourceBasis i))‖ ^ 2)) := by
  rw [← hresponse]
  exact douglasAlignedInputSideRootS2Producer_ordinaryTrace_norm_le producer

/-!
Legacy Phi-only route package.  It keeps the old algebraic interface available
for existing experiments, but it is not the Gate 3U source owner: its transfer
is `graphTransfer = Phi`, not the normalized physical Schur frame.  New route
work must use `SourceBandGramSchurFrameJuliaDouglasData` below.
-/
structure SourceBandGramSchurJuliaDouglasData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    {ι K G : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda)) where
  base : InputSideRootS2Producer (K := K) (G := G) sourceBasis
  base_response_eq : base.response = sourceBandGramResponse owner lambda family
  schurSteps : List (SchurJuliaRangeStepData K G)
  factor : PiLp 2
      (fun _ : Fin (schurJuliaSteps schurSteps).length => G) →L[ℂ] G
  factorBound : ℝ
  factorBound_nonneg : 0 ≤ factorBound
  factor_norm_le : ‖factor‖ ≤ factorBound
  factorization :
    base.rightFactor ∘L base.root ∘L base.rightInput =
      factor ∘L (juliaRangeColumn (schurJuliaSteps schurSteps) ∘L
        base.root ∘L base.rightInput)

noncomputable def SourceBandGramSchurJuliaDouglasData.toProducer
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {family : FinitePrimePowerFamily}
    {ι K G : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda)}
    (data : SourceBandGramSchurJuliaDouglasData (K := K) (G := G)
      owner lambda family
      sourceBasis) :
    DouglasAlignedInputSideRootS2Producer (K := K) (G := G) sourceBasis :=
  douglasAlignedInputSideRootS2ProducerOfSchurJulia data.base data.schurSteps
    data.factor data.factorBound data.factorBound_nonneg data.factor_norm_le
    data.factorization

theorem SourceBandGramSchurJuliaDouglasData.toProducer_response_eq
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {family : FinitePrimePowerFamily}
    {ι K G : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda)}
    (data : SourceBandGramSchurJuliaDouglasData (K := K) (G := G)
      owner lambda family
      sourceBasis) :
    data.toProducer.base.response = sourceBandGramResponse owner lambda family := by
  simpa only [SourceBandGramSchurJuliaDouglasData.toProducer] using
    data.base_response_eq

theorem sourceBandGramResponse_ordinaryTrace_norm_le_of_schurJuliaDouglas
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    {ι K G : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda)}
    (data : SourceBandGramSchurJuliaDouglasData (K := K) (G := G)
      owner lambda family
      sourceBasis) :
    ‖CC20Concrete.PositiveTrace.ordinaryTraceAlong sourceBasis
        (sourceBandGramResponse owner lambda family)‖ ≤
      (1 / 2 : ℝ) *
        (‖data.toProducer.base.leftFactor‖ ^ 2 *
            (∑' i, ‖data.toProducer.base.root
              (data.toProducer.base.leftInput (sourceBasis i))‖ ^ 2) +
          data.toProducer.factorBound ^ 2 *
            (∑' i, ‖data.toProducer.base.root
              (data.toProducer.base.rightInput (sourceBasis i))‖ ^ 2)) := by
  exact sourceBandGramResponse_ordinaryTrace_norm_le_of_douglasAlignedInputSide
    owner lambda family data.toProducer data.toProducer_response_eq

/-!
This is the route-facing package for the corrected source coordinate.  The
right factorization is through the physical Schur-frame column, so the
remaining missing theorem is exactly the source Douglas estimate for the
completed corrected bracket.
-/
structure SourceBandGramSchurFrameJuliaDouglasData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    {ι K G : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda)) where
  base : InputSideRootS2Producer (K := K) (G := G) sourceBasis
  base_response_eq : base.response = sourceBandGramResponse owner lambda family
  schurSteps : List (SchurFrameJuliaRangeStepData K G)
  factor : PiLp 2
      (fun _ : Fin (schurFrameJuliaSteps schurSteps).length => G) →L[ℂ] G
  factorBound : ℝ
  factorBound_nonneg : 0 ≤ factorBound
  factor_norm_le : ‖factor‖ ≤ factorBound
  factorization :
    base.rightFactor ∘L base.root ∘L base.rightInput =
      factor ∘L (juliaRangeColumn (schurFrameJuliaSteps schurSteps) ∘L
        base.root ∘L base.rightInput)

noncomputable def SourceBandGramSchurFrameJuliaDouglasData.toProducer
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {family : FinitePrimePowerFamily}
    {ι K G : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda)}
    (data : SourceBandGramSchurFrameJuliaDouglasData (K := K) (G := G)
      owner lambda family
      sourceBasis) :
    DouglasAlignedInputSideRootS2Producer (K := K) (G := G) sourceBasis :=
  douglasAlignedInputSideRootS2ProducerOfSchurFrameJulia data.base
    data.schurSteps data.factor data.factorBound data.factorBound_nonneg
    data.factor_norm_le data.factorization

theorem SourceBandGramSchurFrameJuliaDouglasData.toProducer_response_eq
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {family : FinitePrimePowerFamily}
    {ι K G : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda)}
    (data : SourceBandGramSchurFrameJuliaDouglasData (K := K) (G := G)
      owner lambda family
      sourceBasis) :
    data.toProducer.base.response = sourceBandGramResponse owner lambda family := by
  simpa only [SourceBandGramSchurFrameJuliaDouglasData.toProducer] using
    data.base_response_eq

theorem sourceBandGramResponse_ordinaryTrace_norm_le_of_schurFrameJuliaDouglas
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    {ι K G : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda)}
    (data : SourceBandGramSchurFrameJuliaDouglasData (K := K) (G := G)
      owner lambda family
      sourceBasis) :
    ‖CC20Concrete.PositiveTrace.ordinaryTraceAlong sourceBasis
        (sourceBandGramResponse owner lambda family)‖ ≤
      (1 / 2 : ℝ) *
        (‖data.toProducer.base.leftFactor‖ ^ 2 *
            (∑' i, ‖data.toProducer.base.root
              (data.toProducer.base.leftInput (sourceBasis i))‖ ^ 2) +
          data.toProducer.factorBound ^ 2 *
            (∑' i, ‖data.toProducer.base.root
              (data.toProducer.base.rightInput (sourceBasis i))‖ ^ 2)) := by
  exact sourceBandGramResponse_ordinaryTrace_norm_le_of_douglasAlignedInputSide
    owner lambda family data.toProducer data.toProducer_response_eq

/-! A direct wrapper for the already assembled corrected physical bracket. -/
theorem correctedPhysicalBracket_ordinaryTrace_norm_le_of_douglasAlignedInputSide
    {ι K G : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (sourceBasis : HilbertBasis ι ℂ finiteSCarrier)
    (producer : DouglasAlignedInputSideRootS2Producer
      (H := finiteSCarrier) (K := K) (G := G) sourceBasis)
    (support secondSupport prolate detector transport :
      finiteSCarrier →L[ℂ] finiteSCarrier)
    (hresponse : producer.base.response =
      correctedPhysicalBracket support secondSupport prolate detector transport) :
    ‖CC20Concrete.PositiveTrace.ordinaryTraceAlong sourceBasis
        (correctedPhysicalBracket support secondSupport prolate detector transport)‖ ≤
      (1 / 2 : ℝ) *
        (‖producer.base.leftFactor‖ ^ 2 *
            (∑' i, ‖producer.base.root
              (producer.base.leftInput (sourceBasis i))‖ ^ 2) +
          producer.factorBound ^ 2 *
            (∑' i, ‖producer.base.root
              (producer.base.rightInput (sourceBasis i))‖ ^ 2)) := by
  rw [← hresponse]
  exact douglasAlignedInputSideRootS2Producer_ordinaryTrace_norm_le producer

/-!
A bounded source-side dressing should be attached before the common-root
packing, not estimated after the two legs have been separated.  This owner
does exactly that.  The `-1` is kept in the right leg, so the response remains
the signed physical response while the two input maps stay visible to the
energy consumer.
-/
noncomputable def inputSideRootS2ProducerOfBoundedPrecomp
    {ι κ μ H K G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ H}
    (targetBasis : HilbertBasis κ ℂ G)
    (newSourceBasis : HilbertBasis μ ℂ K)
    (data : CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := G) sourceBasis)
    (leftBounded rightBounded : K →L[ℂ] H) :
    InputSideRootS2Producer
      (K := WithLp 2 (G × G)) (G := WithLp 2 (G × G)) newSourceBasis :=
  inputSideRootS2ProducerOfPairData (G := G)
    ((CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.boundedPrecomp
      targetBasis newSourceBasis data leftBounded rightBounded).smulRight (-1))

theorem inputSideRootS2ProducerOfBoundedPrecomp_response_eq
    {ι κ μ H K G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ H}
    (targetBasis : HilbertBasis κ ℂ G)
    (newSourceBasis : HilbertBasis μ ℂ K)
    (data : CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := G) sourceBasis)
    (leftBounded rightBounded : K →L[ℂ] H) :
    (inputSideRootS2ProducerOfBoundedPrecomp targetBasis newSourceBasis data
      leftBounded rightBounded).response =
      -(leftBounded† ∘L data.traceProduct ∘L rightBounded) := by
  unfold inputSideRootS2ProducerOfBoundedPrecomp
  rw [inputSideRootS2ProducerOfPairData_response_eq,
    CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.smulRight_traceProduct_eq,
    CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.boundedPrecomp_traceProduct_eq]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.smul_apply, neg_one_smul,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply]

theorem inputSideRootS2ProducerOfBoundedPrecomp_root_energy_le
    {ι κ μ H K G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ H}
    (targetBasis : HilbertBasis κ ℂ G)
    (newSourceBasis : HilbertBasis μ ℂ K)
    (data : CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := G) sourceBasis)
    (leftBounded rightBounded : K →L[ℂ] H) :
    ∑' i, ‖(inputSideRootS2ProducerOfBoundedPrecomp targetBasis
        newSourceBasis data leftBounded rightBounded).root
        (newSourceBasis i)‖ ^ 2 ≤
      ‖leftBounded‖ ^ 2 *
          (∑' i, ‖data.left (sourceBasis i)‖ ^ 2) +
        ‖rightBounded‖ ^ 2 *
          (∑' i, ‖data.right (sourceBasis i)‖ ^ 2) := by
  let precomp :=
    CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.boundedPrecomp
      targetBasis newSourceBasis data leftBounded rightBounded
  let signed := precomp.smulRight (-1)
  have henergy := inputSideRootS2ProducerOfPairData_root_energy_eq signed
  have hleft := CC20Concrete.PositiveTrace.tsum_normSq_precomp_le
    sourceBasis targetBasis newSourceBasis data.left leftBounded
      data.left_summable_normSq
  have hright := CC20Concrete.PositiveTrace.tsum_normSq_precomp_le
    sourceBasis targetBasis newSourceBasis data.right rightBounded
      data.right_summable_normSq
  dsimp [inputSideRootS2ProducerOfBoundedPrecomp]
  change ∑' i, ‖(inputSideRootS2ProducerOfPairData signed).root
      (newSourceBasis i)‖ ^ 2 ≤ _
  rw [henergy]
  have hsigned : ∀ i,
      ‖signed.left (newSourceBasis i)‖ ^ 2 +
          ‖signed.right (newSourceBasis i)‖ ^ 2 =
        ‖precomp.left (newSourceBasis i)‖ ^ 2 +
          ‖precomp.right (newSourceBasis i)‖ ^ 2 := by
    intro i
    simp [signed,
      CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.smulRight]
  calc
    ∑' i, (‖signed.left (newSourceBasis i)‖ ^ 2 +
        ‖signed.right (newSourceBasis i)‖ ^ 2) =
        ∑' i, (‖precomp.left (newSourceBasis i)‖ ^ 2 +
          ‖precomp.right (newSourceBasis i)‖ ^ 2) := by
      apply tsum_congr
      exact hsigned
    _ ≤ ‖leftBounded‖ ^ 2 *
          (∑' i, ‖data.left (sourceBasis i)‖ ^ 2) +
        ‖rightBounded‖ ^ 2 *
          (∑' i, ‖data.right (sourceBasis i)‖ ^ 2) := by
      rw [precomp.left_summable_normSq.tsum_add
        precomp.right_summable_normSq]
      apply add_le_add
      · dsimp [precomp,
          CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.boundedPrecomp]
        exact hleft
      · dsimp [precomp,
          CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.boundedPrecomp]
        exact hright

theorem inputSideRootS2ProducerOfBoundedPrecomp_root_energy_le_of_contractions
    {ι κ μ H K G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ H}
    (targetBasis : HilbertBasis κ ℂ G)
    (newSourceBasis : HilbertBasis μ ℂ K)
    (data : CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := G) sourceBasis)
    (leftBounded rightBounded : K →L[ℂ] H)
    (hleft : ‖leftBounded‖ ≤ 1) (hright : ‖rightBounded‖ ≤ 1) :
    ∑' i, ‖(inputSideRootS2ProducerOfBoundedPrecomp targetBasis
        newSourceBasis data leftBounded rightBounded).root
        (newSourceBasis i)‖ ^ 2 ≤
      (∑' i, ‖data.left (sourceBasis i)‖ ^ 2) +
        ∑' i, ‖data.right (sourceBasis i)‖ ^ 2 := by
  have henergy := inputSideRootS2ProducerOfBoundedPrecomp_root_energy_le
    targetBasis newSourceBasis data leftBounded rightBounded
  have hleftSq : ‖leftBounded‖ ^ 2 ≤ (1 : ℝ) := by
    nlinarith [sq_nonneg (‖leftBounded‖ - 1), norm_nonneg leftBounded]
  have hrightSq : ‖rightBounded‖ ^ 2 ≤ (1 : ℝ) := by
    nlinarith [sq_nonneg (‖rightBounded‖ - 1), norm_nonneg rightBounded]
  have hleftEnergy : 0 ≤ ∑' i, ‖data.left (sourceBasis i)‖ ^ 2 :=
    tsum_nonneg fun i => sq_nonneg _
  have hrightEnergy : 0 ≤ ∑' i, ‖data.right (sourceBasis i)‖ ^ 2 :=
    tsum_nonneg fun i => sq_nonneg _
  calc
    _ ≤ ‖leftBounded‖ ^ 2 *
          (∑' i, ‖data.left (sourceBasis i)‖ ^ 2) +
        ‖rightBounded‖ ^ 2 *
          (∑' i, ‖data.right (sourceBasis i)‖ ^ 2) := henergy
    _ ≤ (∑' i, ‖data.left (sourceBasis i)‖ ^ 2) +
        ∑' i, ‖data.right (sourceBasis i)‖ ^ 2 := by
      apply add_le_add
      · calc
          ‖leftBounded‖ ^ 2 *
              (∑' i, ‖data.left (sourceBasis i)‖ ^ 2) ≤
            1 * (∑' i, ‖data.left (sourceBasis i)‖ ^ 2) :=
              mul_le_mul_of_nonneg_right hleftSq hleftEnergy
          _ = ∑' i, ‖data.left (sourceBasis i)‖ ^ 2 := one_mul _
      · calc
          ‖rightBounded‖ ^ 2 *
              (∑' i, ‖data.right (sourceBasis i)‖ ^ 2) ≤
            1 * (∑' i, ‖data.right (sourceBasis i)‖ ^ 2) :=
              mul_le_mul_of_nonneg_right hrightSq hrightEnergy
          _ = ∑' i, ‖data.right (sourceBasis i)‖ ^ 2 := one_mul _

theorem inputSideRootS2ProducerOfBoundedPrecomp_ordinaryTrace_norm_le
    {ι κ μ H K G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ H}
    (targetBasis : HilbertBasis κ ℂ G)
    (newSourceBasis : HilbertBasis μ ℂ K)
    (data : CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := G) sourceBasis)
    (leftBounded rightBounded : K →L[ℂ] H) :
    ‖CC20Concrete.PositiveTrace.ordinaryTraceAlong newSourceBasis
        (inputSideRootS2ProducerOfBoundedPrecomp targetBasis newSourceBasis
          data leftBounded rightBounded).response‖ ≤
      (1 / 2 : ℝ) *
        (‖leftBounded‖ ^ 2 *
            (∑' i, ‖data.left (sourceBasis i)‖ ^ 2) +
          ‖rightBounded‖ ^ 2 *
            (∑' i, ‖data.right (sourceBasis i)‖ ^ 2)) := by
  let precomp :=
    CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.boundedPrecomp
      targetBasis newSourceBasis data leftBounded rightBounded
  let signed := precomp.smulRight (-1)
  let producer := inputSideRootS2ProducerOfPairData signed
  have hresponse : producer.response =
      (inputSideRootS2ProducerOfBoundedPrecomp targetBasis newSourceBasis
        data leftBounded rightBounded).response := by
    exact inputSideRootS2ProducerOfPairData_response_eq signed
  have hproducerResponse : producer.response = signed.traceProduct := by
    exact inputSideRootS2ProducerOfPairData_response_eq signed
  have htrace : CC20Concrete.PositiveTrace.IsTraceClassAlong newSourceBasis
      producer.response := by
    rw [hproducerResponse]
    exact signed.traceProduct_isTraceClassAlong
  have hdiag := htrace.norm
  have hleft : Summable (fun i =>
      ‖signed.left (newSourceBasis i)‖ ^ 2) :=
    signed.left_summable_normSq
  have hright : Summable (fun i =>
      ‖signed.right (newSourceBasis i)‖ ^ 2) :=
    signed.right_summable_normSq
  have hmajorant : Summable (fun i =>
      (1 / 2 : ℝ) *
        (‖signed.left (newSourceBasis i)‖ ^ 2 +
          ‖signed.right (newSourceBasis i)‖ ^ 2)) := by
    simpa only [mul_add] using
      (hleft.add hright).mul_left (1 / 2 : ℝ)
  have hpoint : ∀ i, (‖⟪newSourceBasis i,
      producer.response (newSourceBasis i)⟫_ℂ‖) ≤
      (1 / 2 : ℝ) *
        (‖signed.left (newSourceBasis i)‖ ^ 2 +
          ‖signed.right (newSourceBasis i)‖ ^ 2) := by
    intro i
    have hdiagonal :
        ⟪newSourceBasis i, producer.response (newSourceBasis i)⟫_ℂ =
          ⟪signed.left (newSourceBasis i),
            signed.right (newSourceBasis i)⟫_ℂ := by
      rw [hproducerResponse]
      exact signed.traceProduct_diagonal i
    rw [hdiagonal]
    calc
      ‖⟪signed.left (newSourceBasis i),
          signed.right (newSourceBasis i)⟫_ℂ‖ ≤
          ‖signed.left (newSourceBasis i)‖ *
            ‖signed.right (newSourceBasis i)‖ :=
        norm_inner_le_norm _ _
      _ ≤ (1 / 2 : ℝ) *
          (‖signed.left (newSourceBasis i)‖ ^ 2 +
            ‖signed.right (newSourceBasis i)‖ ^ 2) := by
        nlinarith [sq_nonneg
          (‖signed.left (newSourceBasis i)‖ -
            ‖signed.right (newSourceBasis i)‖)]
  have hraw :
      ‖CC20Concrete.PositiveTrace.ordinaryTraceAlong newSourceBasis
          producer.response‖ ≤
        (1 / 2 : ℝ) *
          (∑' i, ‖signed.left (newSourceBasis i)‖ ^ 2 +
            ∑' i, ‖signed.right (newSourceBasis i)‖ ^ 2) := by
    rw [CC20Concrete.PositiveTrace.ordinaryTraceAlong]
    calc
      ‖∑' i, ⟪newSourceBasis i,
          producer.response (newSourceBasis i)⟫_ℂ‖ ≤
          ∑' i, ‖⟪newSourceBasis i,
            producer.response (newSourceBasis i)⟫_ℂ‖ :=
        norm_tsum_le_tsum_norm hdiag
      _ ≤ ∑' i, (1 / 2 : ℝ) *
          (‖signed.left (newSourceBasis i)‖ ^ 2 +
            ‖signed.right (newSourceBasis i)‖ ^ 2) :=
        hdiag.tsum_le_tsum hpoint hmajorant
      _ = (1 / 2 : ℝ) *
          (∑' i, ‖signed.left (newSourceBasis i)‖ ^ 2 +
            ∑' i, ‖signed.right (newSourceBasis i)‖ ^ 2) := by
        rw [tsum_mul_left, hleft.tsum_add hright]
  have hleftEnergy :=
    CC20Concrete.PositiveTrace.tsum_normSq_precomp_le
      sourceBasis targetBasis newSourceBasis data.left leftBounded
        data.left_summable_normSq
  have hrightEnergy :=
    CC20Concrete.PositiveTrace.tsum_normSq_precomp_le
      sourceBasis targetBasis newSourceBasis data.right rightBounded
        data.right_summable_normSq
  have hsignedEnergy :
      (∑' i, ‖signed.left (newSourceBasis i)‖ ^ 2) +
          ∑' i, ‖signed.right (newSourceBasis i)‖ ^ 2 ≤
        ‖leftBounded‖ ^ 2 *
            (∑' i, ‖data.left (sourceBasis i)‖ ^ 2) +
          ‖rightBounded‖ ^ 2 *
            (∑' i, ‖data.right (sourceBasis i)‖ ^ 2) := by
    have hleftSigned :
        ∑' i, ‖signed.left (newSourceBasis i)‖ ^ 2 ≤
          ‖leftBounded‖ ^ 2 *
            (∑' i, ‖data.left (sourceBasis i)‖ ^ 2) := by
      dsimp [signed, precomp,
        CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.smulRight,
        CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.boundedPrecomp]
      exact hleftEnergy
    have hrightSigned :
        ∑' i, ‖signed.right (newSourceBasis i)‖ ^ 2 ≤
          ‖rightBounded‖ ^ 2 *
            (∑' i, ‖data.right (sourceBasis i)‖ ^ 2) := by
      dsimp [signed, precomp,
        CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.smulRight,
        CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.boundedPrecomp]
      simpa using hrightEnergy
    exact add_le_add hleftSigned hrightSigned
  rw [← hresponse]
  exact hraw.trans (by
    exact mul_le_mul_of_nonneg_left hsignedEnergy (by norm_num))

theorem inputSideRootS2ProducerOfBoundedPrecomp_ordinaryTrace_norm_le_of_contractions
    {ι κ μ H K G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ H}
    (targetBasis : HilbertBasis κ ℂ G)
    (newSourceBasis : HilbertBasis μ ℂ K)
    (data : CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := G) sourceBasis)
    (leftBounded rightBounded : K →L[ℂ] H)
    (hleft : ‖leftBounded‖ ≤ 1) (hright : ‖rightBounded‖ ≤ 1) :
    ‖CC20Concrete.PositiveTrace.ordinaryTraceAlong newSourceBasis
        (inputSideRootS2ProducerOfBoundedPrecomp targetBasis newSourceBasis
          data leftBounded rightBounded).response‖ ≤
      (1 / 2 : ℝ) *
        ((∑' i, ‖data.left (sourceBasis i)‖ ^ 2) +
          ∑' i, ‖data.right (sourceBasis i)‖ ^ 2) := by
  have htrace := inputSideRootS2ProducerOfBoundedPrecomp_ordinaryTrace_norm_le
    targetBasis newSourceBasis data leftBounded rightBounded
  have hleftSq : ‖leftBounded‖ ^ 2 ≤ (1 : ℝ) := by
    nlinarith [sq_nonneg (‖leftBounded‖ - 1), norm_nonneg leftBounded]
  have hrightSq : ‖rightBounded‖ ^ 2 ≤ (1 : ℝ) := by
    nlinarith [sq_nonneg (‖rightBounded‖ - 1), norm_nonneg rightBounded]
  have hleftEnergy : 0 ≤ ∑' i, ‖data.left (sourceBasis i)‖ ^ 2 :=
    tsum_nonneg fun i => sq_nonneg _
  have hrightEnergy : 0 ≤ ∑' i, ‖data.right (sourceBasis i)‖ ^ 2 :=
    tsum_nonneg fun i => sq_nonneg _
  have hsum :
      ‖leftBounded‖ ^ 2 * (∑' i, ‖data.left (sourceBasis i)‖ ^ 2) +
          ‖rightBounded‖ ^ 2 * (∑' i, ‖data.right (sourceBasis i)‖ ^ 2) ≤
        (∑' i, ‖data.left (sourceBasis i)‖ ^ 2) +
          ∑' i, ‖data.right (sourceBasis i)‖ ^ 2 := by
    apply add_le_add
    · exact (mul_le_mul_of_nonneg_right hleftSq hleftEnergy).trans_eq
        (one_mul _)
    · exact (mul_le_mul_of_nonneg_right hrightSq hrightEnergy).trans_eq
        (one_mul _)
  exact htrace.trans (mul_le_mul_of_nonneg_left hsum (by norm_num))

theorem inputSideRootS2Producer_ordinaryTrace_norm_le_of_bounds
    {ι H K G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ H}
    (producer : InputSideRootS2Producer (K := K) (G := G) sourceBasis)
    (leftRootBound rightRootBound leftFactorBound : ℝ)
    (hleftRoot : (∑' i, ‖producer.root
      (producer.leftInput (sourceBasis i))‖ ^ 2) ≤ leftRootBound)
    (hrightRoot : (∑' i, ‖producer.root
      (producer.rightInput (sourceBasis i))‖ ^ 2) ≤ rightRootBound)
    (hleftRoot_nonneg : 0 ≤ leftRootBound)
    (hrightRoot_nonneg : 0 ≤ rightRootBound)
    (hleftFactor : ‖producer.leftFactor‖ ≤ leftFactorBound)
    (hleftFactor_nonneg : 0 ≤ leftFactorBound) :
    ‖CC20Concrete.PositiveTrace.ordinaryTraceAlong sourceBasis
        producer.response‖ ≤
      (1 / 2 : ℝ) *
        (leftFactorBound ^ 2 * leftRootBound + rightRootBound) := by
  have hfactor : ‖producer.leftFactor‖ ^ 2 ≤
      leftFactorBound ^ 2 := by
    have hprod : 0 ≤ (leftFactorBound - ‖producer.leftFactor‖) *
        (leftFactorBound + ‖producer.leftFactor‖) :=
      mul_nonneg (sub_nonneg.mpr hleftFactor)
        (add_nonneg hleftFactor_nonneg (norm_nonneg _))
    nlinarith
  have hleftProduct : ‖producer.leftFactor‖ ^ 2 *
      (∑' i, ‖producer.root
        (producer.leftInput (sourceBasis i))‖ ^ 2) ≤
      leftFactorBound ^ 2 * leftRootBound := by
    exact mul_le_mul hfactor hleftRoot
      (tsum_nonneg fun i => sq_nonneg _) (by positivity)
  have hsum : ‖producer.leftFactor‖ ^ 2 *
      (∑' i, ‖producer.root
        (producer.leftInput (sourceBasis i))‖ ^ 2) +
      ∑' i, ‖producer.root
        (producer.rightInput (sourceBasis i))‖ ^ 2 ≤
      leftFactorBound ^ 2 * leftRootBound + rightRootBound :=
    add_le_add hleftProduct hrightRoot
  calc
    ‖CC20Concrete.PositiveTrace.ordinaryTraceAlong sourceBasis
        producer.response‖ ≤
      (1 / 2 : ℝ) *
        (‖producer.leftFactor‖ ^ 2 *
          (∑' i, ‖producer.root
            (producer.leftInput (sourceBasis i))‖ ^ 2) +
          ∑' i, ‖producer.root
            (producer.rightInput (sourceBasis i))‖ ^ 2) :=
      inputSideRootS2Producer_ordinaryTrace_norm_le producer
    _ ≤ (1 / 2 : ℝ) *
        (leftFactorBound ^ 2 * leftRootBound + rightRootBound) := by
      exact mul_le_mul_of_nonneg_left hsum (by norm_num)

theorem correctedPhysicalBracket_ordinaryTrace_norm_le_of_inputSideRoot
    {ι K G : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (sourceBasis : HilbertBasis ι ℂ finiteSCarrier)
    (producer : InputSideRootS2Producer
      (H := finiteSCarrier) (K := K) (G := G) sourceBasis)
    (support secondSupport prolate detector transport :
      finiteSCarrier →L[ℂ] finiteSCarrier)
    (hresponse : producer.response =
      correctedPhysicalBracket support secondSupport prolate detector transport) :
    ‖CC20Concrete.PositiveTrace.ordinaryTraceAlong sourceBasis
        (correctedPhysicalBracket support secondSupport prolate detector transport)‖ ≤
      (1 / 2 : ℝ) *
        (‖producer.leftFactor‖ ^ 2 *
            (∑' i, ‖producer.root
              (producer.leftInput (sourceBasis i))‖ ^ 2) +
          ∑' i, ‖producer.root
            (producer.rightInput (sourceBasis i))‖ ^ 2) := by
  rw [← hresponse]
  exact inputSideRootS2Producer_ordinaryTrace_norm_le producer

theorem sourceBandGramResponse_ordinaryTrace_norm_le_of_inputSideRoot
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    {ι K G : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda))
    (producer : InputSideRootS2Producer
      (H := sourceSoninCarrier lambda) (K := K) (G := G) sourceBasis)
    (hresponse : producer.response =
      sourceBandGramResponse owner lambda family) :
    ‖CC20Concrete.PositiveTrace.ordinaryTraceAlong sourceBasis
        (sourceBandGramResponse owner lambda family)‖ ≤
      (1 / 2 : ℝ) *
        (‖producer.leftFactor‖ ^ 2 *
            (∑' i, ‖producer.root
              (producer.leftInput (sourceBasis i))‖ ^ 2) +
          ∑' i, ‖producer.root
            (producer.rightInput (sourceBasis i))‖ ^ 2) := by
  rw [← hresponse]
  exact inputSideRootS2Producer_ordinaryTrace_norm_le producer

/-!
The actual source-side producer, with the finite-S coframe kept literal.

`sourceThreeBranchSourcePairData` already owns the complete physical ledger
and precomposes both Hilbert--Schmidt legs by the actual
`finiteEulerAmbientGram * sourceInclusion * finiteEulerGramInv`.  The
input-side wrapper below does not replace that coframe by an identity row: it
only packages the two resulting legs into the common-root interface consumed
above.  Its inherited `steps` field is still the old bookkeeping row; it is a
physical owner only and must not be passed to the Julia-aligned theorem.  The
Gate 3U producer must wrap this base with an independent actual cascade using
`DouglasAlignedInputSideRootS2Producer`.
-/
noncomputable def sourceBandGramResponseInputSideProducer
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

theorem sourceBandGramResponseInputSideProducer_response_eq
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
    (sourceBandGramResponseInputSideProducer owner lambda family a c hac hsupp
      negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
      sourceBasis hfactor).response =
      sourceBandGramResponse owner lambda family := by
  rw [sourceBandGramResponseInputSideProducer,
    inputSideRootS2ProducerOfPairData_response_eq]
  exact sourceThreeBranchSourcePairData_traceProduct_eq owner lambda family
    a c hac hsupp negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
    sourceBasis hfactor

/-! The root energy is the exact two-leg energy of the source-side physical
owner.  Keeping this equality explicit prevents a normalized contraction from
being mistaken for the unnormalised Gate 3U estimate. -/
theorem sourceBandGramResponseInputSideProducer_root_energy_eq
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
    ∑' i, ‖(sourceBandGramResponseInputSideProducer owner lambda family
        a c hac hsupp negativeBasis positiveBasis outputBasis
        reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
        globalBasis boundaryBasis sourceBasis hfactor).root (sourceBasis i)‖ ^ 2 =
      ∑' i, (‖(sourceThreeBranchSourcePairData owner lambda family a c hac
        hsupp negativeBasis positiveBasis outputBasis reflectedNegativeBasis
        reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
        sourceBasis hfactor).left (sourceBasis i)‖ ^ 2 +
        ‖(sourceThreeBranchSourcePairData owner lambda family a c hac hsupp
        negativeBasis positiveBasis outputBasis reflectedNegativeBasis
        reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
        sourceBasis hfactor).right (sourceBasis i)‖ ^ 2) := by
  exact inputSideRootS2ProducerOfPairData_root_energy_eq
    (sourceThreeBranchSourcePairData owner lambda family a c hac hsupp
      negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
      sourceBasis hfactor)

/-!
This is the same source ledger with the normalized metric coframe attached on
the right.  The left source inclusion is contractive and the normalized
coframe is contractive independently of the visible finite set.  The pair is
therefore the correct energy owner for the normalized physical response.
-/
noncomputable def normalizedSourceBandGramResponseInputSideProducer
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
  inputSideRootS2ProducerOfBoundedPrecomp boundaryBasis sourceBasis
    (sourceThreeBranchPairData owner lambda a c hac hsupp negativeBasis
      positiveBasis outputBasis reflectedNegativeBasis reflectedPositiveBasis
      reflectedOutputBasis globalBasis hfactor)
    (sourceInclusion lambda)
    (normalizedFiniteEulerMetricCoframe lambda family)

theorem normalizedSourceBandGramResponseInputSideProducer_response_eq
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
    (normalizedSourceBandGramResponseInputSideProducer owner lambda family
      a c hac hsupp negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
      sourceBasis hfactor).response =
      CCM24FiniteSNormalizedPhysicalResponse.normalizedSourceBandGramResponse
        owner lambda family := by
  rw [normalizedSourceBandGramResponseInputSideProducer,
    inputSideRootS2ProducerOfBoundedPrecomp_response_eq,
    sourceThreeBranchPairData_traceProduct_eq owner lambda a c hac hsupp
      negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor,
    CCM24FiniteSNormalizedPhysicalResponse.normalizedSourceBandGramResponse,
    sourceBandGramResponse_eq_neg_threeBranch owner lambda family]
  apply ContinuousLinearMap.ext
  intro u
  have hcoframe :
      finiteEulerMetricCoframe lambda family u =
        finiteEulerAmbientGram family
          (sourceInclusion lambda (finiteEulerGramInv lambda family u)) := by
    rfl
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.smul_apply, map_smul]
  unfold normalizedFiniteEulerMetricCoframe
  simp only [ContinuousLinearMap.smul_apply]
  rw [hcoframe]
  simp only [map_smul, neg_smul, smul_neg]

theorem normalizedSourceBandGramResponseInputSideProducer_root_energy_le
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
    ∑' i, ‖(normalizedSourceBandGramResponseInputSideProducer owner lambda
        family a c hac hsupp negativeBasis positiveBasis outputBasis
        reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
        globalBasis boundaryBasis sourceBasis hfactor).root
        (sourceBasis i)‖ ^ 2 ≤
      ∑' i, ‖(sourceThreeBranchPairData owner lambda a c hac hsupp
        negativeBasis positiveBasis outputBasis reflectedNegativeBasis
        reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor).left
        (globalBasis i)‖ ^ 2 +
      ∑' i, ‖(sourceThreeBranchPairData owner lambda a c hac hsupp
        negativeBasis positiveBasis outputBasis reflectedNegativeBasis
        reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor).right
        (globalBasis i)‖ ^ 2 := by
  apply inputSideRootS2ProducerOfBoundedPrecomp_root_energy_le_of_contractions
    boundaryBasis sourceBasis
    (sourceThreeBranchPairData owner lambda a c hac hsupp negativeBasis
      positiveBasis outputBasis reflectedNegativeBasis reflectedPositiveBasis
      reflectedOutputBasis globalBasis hfactor)
    (sourceInclusion lambda) (normalizedFiniteEulerMetricCoframe lambda family)
  · exact Submodule.norm_subtypeL_le _
  · exact norm_normalizedFiniteEulerMetricCoframe_le_one lambda family

theorem normalizedSourceBandGramResponseInputSideProducer_ordinaryTrace_norm_le
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
    ‖CC20Concrete.PositiveTrace.ordinaryTraceAlong sourceBasis
        (CCM24FiniteSNormalizedPhysicalResponse.normalizedSourceBandGramResponse
          owner lambda family)‖ ≤
      (1 / 2 : ℝ) *
        (∑' i, ‖(sourceThreeBranchPairData owner lambda a c hac hsupp
          negativeBasis positiveBasis outputBasis reflectedNegativeBasis
          reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor).left
          (globalBasis i)‖ ^ 2 +
          ∑' i, ‖(sourceThreeBranchPairData owner lambda a c hac hsupp
          negativeBasis positiveBasis outputBasis reflectedNegativeBasis
          reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor).right
          (globalBasis i)‖ ^ 2) := by
  rw [← normalizedSourceBandGramResponseInputSideProducer_response_eq owner
    lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis sourceBasis hfactor]
  exact inputSideRootS2ProducerOfBoundedPrecomp_ordinaryTrace_norm_le_of_contractions
    boundaryBasis sourceBasis
    (sourceThreeBranchPairData owner lambda a c hac hsupp negativeBasis
      positiveBasis outputBasis reflectedNegativeBasis reflectedPositiveBasis
      reflectedOutputBasis globalBasis hfactor)
    (sourceInclusion lambda) (normalizedFiniteEulerMetricCoframe lambda family)
    (Submodule.norm_subtypeL_le _)
    (norm_normalizedFiniteEulerMetricCoframe_le_one lambda family)

theorem inputSideRootS2ProducerOfPairData_ordinaryTrace_norm_le
    {ι H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ H}
    (data : CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := G) sourceBasis) :
    ‖CC20Concrete.PositiveTrace.ordinaryTraceAlong sourceBasis
        (inputSideRootS2ProducerOfPairData data).response‖ ≤
      (1 / 2 : ℝ) *
        ((∑' i, ‖data.left (sourceBasis i)‖ ^ 2) +
          ∑' i, ‖data.right (sourceBasis i)‖ ^ 2) := by
  have hresponse :
      (inputSideRootS2ProducerOfPairData data).response = data.traceProduct :=
    inputSideRootS2ProducerOfPairData_response_eq data
  have hdiag := data.summable_traceProduct_diagonal
  have hmajorant : Summable (fun i =>
      (1 / 2 : ℝ) *
        (‖data.left (sourceBasis i)‖ ^ 2 +
          ‖data.right (sourceBasis i)‖ ^ 2)) := by
    exact (data.left_summable_normSq.add data.right_summable_normSq).mul_left
      (1 / 2 : ℝ)
  rw [hresponse, CC20Concrete.PositiveTrace.ordinaryTraceAlong]
  calc
    ‖∑' i, ⟪sourceBasis i, data.traceProduct (sourceBasis i)⟫_ℂ‖ ≤
        ∑' i, ‖⟪sourceBasis i, data.traceProduct (sourceBasis i)⟫_ℂ‖ :=
      norm_tsum_le_tsum_norm hdiag.norm
    _ ≤ ∑' i, (1 / 2 : ℝ) *
        (‖data.left (sourceBasis i)‖ ^ 2 +
          ‖data.right (sourceBasis i)‖ ^ 2) := by
      apply hdiag.norm.tsum_le_tsum
      · intro i
        rw [data.traceProduct_diagonal]
        calc
          ‖⟪data.left (sourceBasis i), data.right (sourceBasis i)⟫_ℂ‖ ≤
              ‖data.left (sourceBasis i)‖ * ‖data.right (sourceBasis i)‖ :=
            norm_inner_le_norm _ _
          _ ≤ (1 / 2 : ℝ) *
              (‖data.left (sourceBasis i)‖ ^ 2 +
                ‖data.right (sourceBasis i)‖ ^ 2) := by
            nlinarith [sq_nonneg
              (‖data.left (sourceBasis i)‖ -
                ‖data.right (sourceBasis i)‖)]
      · exact hmajorant
    _ = (1 / 2 : ℝ) *
        ((∑' i, ‖data.left (sourceBasis i)‖ ^ 2) +
          ∑' i, ‖data.right (sourceBasis i)‖ ^ 2) := by
      rw [tsum_mul_left,
        data.left_summable_normSq.tsum_add data.right_summable_normSq]

/-!
This physical-owner estimate is retained for fixed-S bookkeeping only.  It
inherits the legacy identity Julia row and therefore is deliberately separate
from `sourceBandGramResponse_ordinaryTrace_norm_le_of_douglasAlignedInputSide`.
-/
theorem sourceBandGramResponse_ordinaryTrace_norm_le_of_physicalInputSideProducer
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
    ‖CC20Concrete.PositiveTrace.ordinaryTraceAlong sourceBasis
        (sourceBandGramResponse owner lambda family)‖ ≤
      (1 / 2 : ℝ) *
        (∑' i, ‖(sourceThreeBranchSourcePairData owner lambda family a c hac
          hsupp negativeBasis positiveBasis outputBasis reflectedNegativeBasis
          reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
          sourceBasis hfactor).left (sourceBasis i)‖ ^ 2 +
        ∑' i, ‖(sourceThreeBranchSourcePairData owner lambda family a c hac
          hsupp negativeBasis positiveBasis outputBasis reflectedNegativeBasis
          reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
          sourceBasis hfactor).right (sourceBasis i)‖ ^ 2) := by
  rw [← sourceBandGramResponseInputSideProducer_response_eq owner lambda
    family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis sourceBasis hfactor]
  exact inputSideRootS2ProducerOfPairData_ordinaryTrace_norm_le
    (sourceThreeBranchSourcePairData owner lambda family a c hac hsupp
      negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
      sourceBasis hfactor)

/-!
The fixed-quotient first jet now has a source-side owner with the same
composition order as the two surviving Proof 405 branches.  This is a
transport of the already assembled `A†B` pair; it does not introduce a new
trace cycle or split the signed branches before the response is identified.
-/
noncomputable def sourceFixedQuotientFirstJetInputSideProducer
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
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
    (transport : finiteSCarrier →L[ℂ] finiteSCarrier) :
    InputSideRootS2Producer
      (K := WithLp 2 (commonBoundaryCarrier a c × commonBoundaryCarrier a c))
      (G := WithLp 2 (commonBoundaryCarrier a c × commonBoundaryCarrier a c))
      sourceBasis :=
  inputSideRootS2ProducerOfPairData
    (CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.boundedPrecomp
      boundaryBasis sourceBasis
      (sourceFixedQuotientFirstJetPairData owner lambda a c hac hsupp
        negativeBasis positiveBasis outputBasis reflectedNegativeBasis
        reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
        hfactor transport)
      (sourceInclusion lambda) (sourceInclusion lambda))

theorem sourceFixedQuotientFirstJetInputSideProducer_response_eq_corner
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
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
    (transport : finiteSCarrier →L[ℂ] finiteSCarrier) :
    (sourceFixedQuotientFirstJetInputSideProducer owner lambda a c hac hsupp
      negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
      sourceBasis hfactor transport).response =
      (sourceInclusion lambda)† ∘L sourceBandProjection lambda ∘L
        commutator (compressedDetector (radialSupportProjection lambda)
          (detectorOperator owner))
          (sourceCompression (radialSupportProjection lambda)
            (sourceFourierSupportProjection lambda)
            (sourceProlateRemainder lambda)) ∘L
    sourceCompression (radialSupportProjection lambda)
      (sourceFourierSupportProjection lambda)
      (sourceProlateRemainder lambda) ∘L transport ∘L
    sourceBandProjection lambda ∘L sourceInclusion lambda := by
  rw [sourceFixedQuotientFirstJetInputSideProducer,
    inputSideRootS2ProducerOfPairData_response_eq,
    CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.boundedPrecomp_traceProduct_eq,
    sourceFixedQuotientFirstJetPairData_traceProduct_eq_corner owner lambda
      a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis hfactor transport]
  apply ContinuousLinearMap.ext
  intro u
  rfl

theorem sourceFixedQuotientFirstJetInputSideProducer_response_eq_twoBranch
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
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
    (transport : finiteSCarrier →L[ℂ] finiteSCarrier) :
    (sourceFixedQuotientFirstJetInputSideProducer owner lambda a c hac hsupp
      negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
      sourceBasis hfactor transport).response =
      (sourceInclusion lambda)† ∘L
        (sourceBandProjection lambda ∘L sourceFourierSupportProjection lambda ∘L
          compressedDetector (radialSupportProjection lambda)
            (detectorOperator owner) ∘L
          sourceCompression (radialSupportProjection lambda)
            (sourceFourierSupportProjection lambda)
            (sourceProlateRemainder lambda) ∘L transport ∘L
          sourceBandProjection lambda) ∘L sourceInclusion lambda +
        (sourceInclusion lambda)† ∘L sourceBandProjection lambda ∘L
          (ContinuousLinearMap.id ℂ finiteSCarrier -
            sourceFourierSupportProjection lambda) ∘L
          commutator (compressedDetector (radialSupportProjection lambda)
            (detectorOperator owner)) (sourceFourierSupportProjection lambda) ∘L
          sourceCompression (radialSupportProjection lambda)
            (sourceFourierSupportProjection lambda)
            (sourceProlateRemainder lambda) ∘L transport ∘L
          sourceBandProjection lambda ∘L sourceInclusion lambda := by
  rw [sourceFixedQuotientFirstJetInputSideProducer_response_eq_corner owner
    lambda a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis sourceBasis hfactor transport]
  have hcompression :
      sourceCompression (radialSupportProjection lambda)
          (sourceFourierSupportProjection lambda)
          (sourceProlateRemainder lambda) = sourceSoninProjection lambda := by
    simpa only [ContinuousLinearMap.mul_def] using
      (sourceSoninProjection_eq_compression_sub_prolate lambda).symm
  rw [hcompression]
  apply ContinuousLinearMap.ext
  intro u
  have h := DFunLike.congr_fun
    (sourceFixedQuotientCorner_eq_secondSupport_twoBranch owner lambda transport)
    (sourceInclusion lambda u)
  have h' := congrArg ((sourceInclusion lambda)†) h
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    map_add] using h'

/-! The normalized finite-`S` causal inverse is the concrete transport
specialization of the source fixed-quotient owner. -/
noncomputable def sourceFiniteEulerFixedQuotientFirstJetInputSideProducer
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
  sourceFixedQuotientFirstJetInputSideProducer owner lambda a c hac hsupp
    negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
    sourceBasis hfactor
    (radialSupportProjection lambda ∘L normalizedFiniteEulerInverse family ∘L
      radialSupportProjection lambda)

theorem sourceFiniteEulerFixedQuotientFirstJetInputSideProducer_response_eq_twoBranch
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
    (sourceFiniteEulerFixedQuotientFirstJetInputSideProducer owner lambda
      family a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis sourceBasis hfactor).response =
      (sourceInclusion lambda)† ∘L
        (sourceBandProjection lambda ∘L sourceFourierSupportProjection lambda ∘L
          compressedDetector (radialSupportProjection lambda)
            (detectorOperator owner) ∘L
          sourceCompression (radialSupportProjection lambda)
            (sourceFourierSupportProjection lambda)
            (sourceProlateRemainder lambda) ∘L
          (radialSupportProjection lambda ∘L
            normalizedFiniteEulerInverse family ∘L radialSupportProjection lambda) ∘L
          sourceBandProjection lambda) ∘L sourceInclusion lambda +
        (sourceInclusion lambda)† ∘L sourceBandProjection lambda ∘L
          (ContinuousLinearMap.id ℂ finiteSCarrier -
            sourceFourierSupportProjection lambda) ∘L
          commutator (compressedDetector (radialSupportProjection lambda)
            (detectorOperator owner)) (sourceFourierSupportProjection lambda) ∘L
          sourceCompression (radialSupportProjection lambda)
            (sourceFourierSupportProjection lambda)
            (sourceProlateRemainder lambda) ∘L
          (radialSupportProjection lambda ∘L
            normalizedFiniteEulerInverse family ∘L radialSupportProjection lambda) ∘L
          sourceBandProjection lambda ∘L sourceInclusion lambda := by
  exact sourceFixedQuotientFirstJetInputSideProducer_response_eq_twoBranch
    owner lambda a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis sourceBasis hfactor
    (radialSupportProjection lambda ∘L normalizedFiniteEulerInverse family ∘L
      radialSupportProjection lambda)

/-!
The fixed-quotient first jet now enters the actual current-range Douglas
consumer.  The carrier is the same boundary product used by the physical
`A†B` owner; the ambient carrier is the global finite-S logarithmic space.
This is the route-facing bridge for Proof 405.  The equality `hbase` is
deliberately explicit: a caller cannot replace the physical first-jet owner
with a bookkeeping pair that has the same energy.
-/
noncomputable abbrev fixedQuotientFirstJetBoundaryCarrier (a c : ℝ) :=
  WithLp 2 (commonBoundaryCarrier a c × commonBoundaryCarrier a c)

theorem sourceFiniteEulerFixedQuotientFirstJet_ordinaryTrace_norm_le_of_currentRangeDouglas
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
    (base : InputSideRootS2Producer
      (K := fixedQuotientFirstJetBoundaryCarrier a c)
      (G := fixedQuotientFirstJetBoundaryCarrier a c) sourceBasis)
    (hbase : base =
      sourceFiniteEulerFixedQuotientFirstJetInputSideProducer owner lambda
        family a c hac hsupp negativeBasis positiveBasis outputBasis
        reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
        globalBasis boundaryBasis sourceBasis hfactor)
    (causalSteps : List (FactorizedCurrentRangeJuliaStepData
      (fixedQuotientFirstJetBoundaryCarrier a c) finiteSCarrier
      (fixedQuotientFirstJetBoundaryCarrier a c)))
    (factor : PiLp 2
      (fun _ : Fin (factorizedCurrentRangeJuliaSteps causalSteps).length =>
        fixedQuotientFirstJetBoundaryCarrier a c) →L[ℂ]
      fixedQuotientFirstJetBoundaryCarrier a c)
    (factorBound : ℝ) (factorBound_nonneg : 0 ≤ factorBound)
    (factor_norm_le : ‖factor‖ ≤ factorBound)
    (factorization :
      base.rightFactor ∘L base.root ∘L base.rightInput =
        factor ∘L (juliaRangeColumn
          (factorizedCurrentRangeJuliaSteps causalSteps) ∘L
          base.root ∘L base.rightInput)) :
    ‖CC20Concrete.PositiveTrace.ordinaryTraceAlong sourceBasis
        (sourceFiniteEulerFixedQuotientFirstJetInputSideProducer owner lambda
          family a c hac hsupp negativeBasis positiveBasis outputBasis
          reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
          globalBasis boundaryBasis sourceBasis hfactor).response‖ ≤
      (1 / 2 : ℝ) *
        (‖base.leftFactor‖ ^ 2 *
            (∑' i, ‖base.root
              (base.leftInput (sourceBasis i))‖ ^ 2) +
          factorBound ^ 2 *
            (∑' i, ‖base.root
              (base.rightInput (sourceBasis i))‖ ^ 2)) := by
  have hresponse : base.response =
      (sourceFiniteEulerFixedQuotientFirstJetInputSideProducer owner lambda
        family a c hac hsupp negativeBasis positiveBasis outputBasis
        reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
        globalBasis boundaryBasis sourceBasis hfactor).response := by
    rw [hbase]
  exact inputSideFactorizedCurrentRangeDouglas_ordinaryTrace_norm_le_of_response
    base _ hresponse causalSteps factor factorBound factorBound_nonneg
    factor_norm_le factorization

/-!
Proof 405 route-facing form with the Douglas factor generated from finite
coordinate readouts.  This removes the arbitrary factor and factor-bound
fields from the caller.  The remaining hypothesis is the literal physical
readback of the corrected boundary column through the actual factorized
current-range Julia column.
-/
theorem sourceFiniteEulerFixedQuotientFirstJet_ordinaryTrace_norm_le_of_currentRangeReadout
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
    (base : InputSideRootS2Producer
      (K := fixedQuotientFirstJetBoundaryCarrier a c)
      (G := fixedQuotientFirstJetBoundaryCarrier a c) sourceBasis)
    (hbase : base =
      sourceFiniteEulerFixedQuotientFirstJetInputSideProducer owner lambda
        family a c hac hsupp negativeBasis positiveBasis outputBasis
        reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
        globalBasis boundaryBasis sourceBasis hfactor)
    (causalSteps : List (FactorizedCurrentRangeJuliaStepData
      (fixedQuotientFirstJetBoundaryCarrier a c) finiteSCarrier
      (fixedQuotientFirstJetBoundaryCarrier a c)))
    (readout : Fin (factorizedCurrentRangeJuliaSteps causalSteps).length →
      fixedQuotientFirstJetBoundaryCarrier a c →L[ℂ]
        fixedQuotientFirstJetBoundaryCarrier a c)
    (physicalColumn_eq_readout :
      base.rightFactor ∘L base.root ∘L base.rightInput =
        inputSidePiLpReadoutSum readout ∘L
          (juliaRangeColumn (factorizedCurrentRangeJuliaSteps causalSteps) ∘L
            base.root ∘L base.rightInput)) :
    ‖CC20Concrete.PositiveTrace.ordinaryTraceAlong sourceBasis
        (sourceFiniteEulerFixedQuotientFirstJetInputSideProducer owner lambda
          family a c hac hsupp negativeBasis positiveBasis outputBasis
          reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
          globalBasis boundaryBasis sourceBasis hfactor).response‖ ≤
      (1 / 2 : ℝ) *
        (‖base.leftFactor‖ ^ 2 *
            (∑' i, ‖base.root
              (base.leftInput (sourceBasis i))‖ ^ 2) +
          (∑ i, ‖readout i‖) ^ 2 *
            (∑' i, ‖base.root
              (base.rightInput (sourceBasis i))‖ ^ 2)) := by
  exact sourceFiniteEulerFixedQuotientFirstJet_ordinaryTrace_norm_le_of_currentRangeDouglas
    owner lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis sourceBasis hfactor base hbase causalSteps
    (inputSidePiLpReadoutSum readout) (∑ i, ‖readout i‖)
    (Finset.sum_nonneg fun i _ => norm_nonneg (readout i))
    (norm_inputSidePiLpReadoutSum_le readout) physicalColumn_eq_readout

/-!
This is the source-facing operator form.  It asks for domination of the
complete physical right column on every vector of the fixed source carrier;
the Douglas factor is then produced, rather than supplied as a hidden field.
The signed first-jet response remains the single object passed to the
consumer, so no branchwise absolute value is introduced here.
-/
theorem sourceFiniteEulerFixedQuotientFirstJet_ordinaryTrace_norm_le_of_currentRangeOperatorDomination
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
    (base : InputSideRootS2Producer
      (K := fixedQuotientFirstJetBoundaryCarrier a c)
      (G := fixedQuotientFirstJetBoundaryCarrier a c) sourceBasis)
    (hbase : base =
      sourceFiniteEulerFixedQuotientFirstJetInputSideProducer owner lambda
        family a c hac hsupp negativeBasis positiveBasis outputBasis
        reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
        globalBasis boundaryBasis sourceBasis hfactor)
    (causalSteps : List (FactorizedCurrentRangeJuliaStepData
      (fixedQuotientFirstJetBoundaryCarrier a c) finiteSCarrier
      (fixedQuotientFirstJetBoundaryCarrier a c)))
    (factorBound : ℝ) (factorBound_nonneg : 0 ≤ factorBound)
    (hdom : ∀ x : sourceSoninCarrier lambda,
      ‖base.rightFactor (base.root (base.rightInput x))‖ ≤
        factorBound *
          ‖juliaRangeColumn (factorizedCurrentRangeJuliaSteps causalSteps)
            (base.root (base.rightInput x))‖) :
    ‖CC20Concrete.PositiveTrace.ordinaryTraceAlong sourceBasis
        (sourceFiniteEulerFixedQuotientFirstJetInputSideProducer owner lambda
          family a c hac hsupp negativeBasis positiveBasis outputBasis
          reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
          globalBasis boundaryBasis sourceBasis hfactor).response‖ ≤
      (1 / 2 : ℝ) *
        (‖base.leftFactor‖ ^ 2 *
            (∑' i, ‖base.root
              (base.leftInput (sourceBasis i))‖ ^ 2) +
          factorBound ^ 2 *
            (∑' i, ‖base.root
              (base.rightInput (sourceBasis i))‖ ^ 2)) := by
  let producer :=
    douglasAlignedInputSideRootS2ProducerOfFactorizedCurrentRangeJuliaOperatorDomination
      base causalSteps factorBound factorBound_nonneg hdom
  have hfactorization :
      base.rightFactor ∘L base.root ∘L base.rightInput =
        producer.factor ∘L
          (juliaRangeColumn (factorizedCurrentRangeJuliaSteps causalSteps) ∘L
            base.root ∘L base.rightInput) := by
    exact producer.factorization
  exact sourceFiniteEulerFixedQuotientFirstJet_ordinaryTrace_norm_le_of_currentRangeDouglas
    owner lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis sourceBasis hfactor base hbase causalSteps
    producer.factor producer.factorBound producer.factorBound_nonneg
    producer.factor_norm_le hfactorization

/-!
This is the same fixed-quotient consumer for the quadratic form that appears
in a positive-operator Douglas proof.  The physical response and all signed
boundary corrections remain those of the preceding theorem.
-/
theorem sourceFiniteEulerFixedQuotientFirstJet_ordinaryTrace_norm_le_of_currentRangeOperatorNormSqDomination
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
    (base : InputSideRootS2Producer
      (K := fixedQuotientFirstJetBoundaryCarrier a c)
      (G := fixedQuotientFirstJetBoundaryCarrier a c) sourceBasis)
    (hbase : base =
      sourceFiniteEulerFixedQuotientFirstJetInputSideProducer owner lambda
        family a c hac hsupp negativeBasis positiveBasis outputBasis
        reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
        globalBasis boundaryBasis sourceBasis hfactor)
    (causalSteps : List (FactorizedCurrentRangeJuliaStepData
      (fixedQuotientFirstJetBoundaryCarrier a c) finiteSCarrier
      (fixedQuotientFirstJetBoundaryCarrier a c)))
    (factorBound : ℝ) (factorBound_nonneg : 0 ≤ factorBound)
    (hdom : ∀ x : sourceSoninCarrier lambda,
      ‖base.rightFactor (base.root (base.rightInput x))‖ ^ 2 ≤
        factorBound ^ 2 *
          ‖juliaRangeColumn (factorizedCurrentRangeJuliaSteps causalSteps)
            (base.root (base.rightInput x))‖ ^ 2) :
    ‖CC20Concrete.PositiveTrace.ordinaryTraceAlong sourceBasis
        (sourceFiniteEulerFixedQuotientFirstJetInputSideProducer owner lambda
          family a c hac hsupp negativeBasis positiveBasis outputBasis
          reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
          globalBasis boundaryBasis sourceBasis hfactor).response‖ ≤
      (1 / 2 : ℝ) *
        (‖base.leftFactor‖ ^ 2 *
            (∑' i, ‖base.root
              (base.leftInput (sourceBasis i))‖ ^ 2) +
          factorBound ^ 2 *
            (∑' i, ‖base.root
              (base.rightInput (sourceBasis i))‖ ^ 2)) := by
  let producer :=
    douglasAlignedInputSideRootS2ProducerOfFactorizedCurrentRangeJuliaOperatorNormSqDomination
      base causalSteps factorBound factorBound_nonneg hdom
  have hfactorization :
      base.rightFactor ∘L base.root ∘L base.rightInput =
        producer.factor ∘L
          (juliaRangeColumn (factorizedCurrentRangeJuliaSteps causalSteps) ∘L
            base.root ∘L base.rightInput) := by
    exact producer.factorization
  exact sourceFiniteEulerFixedQuotientFirstJet_ordinaryTrace_norm_le_of_currentRangeDouglas
    owner lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis sourceBasis hfactor base hbase causalSteps
    producer.factor producer.factorBound producer.factorBound_nonneg
    producer.factor_norm_le hfactorization

end CCM24FiniteSInputSideTraceConsumer
end CCM25Concrete
end Source
end ConnesWeilRH
