/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSInputSideTraceConsumer
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSDouglasFactor
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSFixedSourcePolar

/-!
# Co-defect-side common-root consumer

The Julia range column is the natural right-side Bessel row, but Proof 388
shows that the physical right column need not be visible to it.  Proof 392
provides a different exact owner: the Schur co-defect is the left row of the
intertwining telescope.  This module packages that orientation.

The source-specific field is now a left-column factorization through the
genuine `juliaDefectColumn`.  The opposite physical leg is controlled by its
ordinary Hilbert--Schmidt root energy.  No range-column visibility or
branchwise splitting is inferred here.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCoDefectConsumer

open MeasureTheory
open CC20Concrete
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSInputSideTraceConsumer
open CCM24FiniteSBandTrace
open CCM24FiniteSProjectionTrace
open CCM24FiniteSJuliaBessel
open CCM24FiniteSFixedSourcePolar
open CCM24FiniteSGramResponse

open scoped InnerProduct InnerProductSpace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

structure CoDefectAlignedInputSideRootS2Producer
    {ι H K D G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup D] [InnerProductSpace ℂ D] [CompleteSpace D]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (sourceBasis : HilbertBasis ι ℂ H) where
  root : H →L[ℂ] K
  leftInput : H →L[ℂ] H
  rightInput : H →L[ℂ] H
  leftFactor : K →L[ℂ] G
  rightFactor : K →L[ℂ] G
  leftRoot_summable_normSq : Summable fun i =>
    ‖root (leftInput (sourceBasis i))‖ ^ 2
  rightRoot_summable_normSq : Summable fun i =>
    ‖root (rightInput (sourceBasis i))‖ ^ 2
  defectSteps : List (JuliaDefectStep K D)
  defectFactor : PiLp 2
      (fun _ : Fin defectSteps.length => K) →L[ℂ] G
  defectFactorBound : ℝ
  defectFactorBound_nonneg : 0 ≤ defectFactorBound
  defectFactor_norm_le : ‖defectFactor‖ ≤ defectFactorBound
  left_factorization :
    leftFactor ∘L root ∘L leftInput =
      defectFactor ∘L
        (juliaDefectColumn defectSteps ∘L root ∘L leftInput)
  response : H →L[ℂ] H
  response_eq :
    (leftFactor ∘L root ∘L leftInput).adjoint ∘L
        (rightFactor ∘L root ∘L rightInput) = response

/-!
The Douglas constructor is deliberately stated on the full source carrier.
Checking the inequality only on the Hilbert basis would not define a bounded
readout on the closure of the defect column range.
-/
noncomputable def CoDefectAlignedInputSideRootS2Producer.ofNormDomination
    {ι H K D G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup D] [InnerProductSpace ℂ D] [CompleteSpace D]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ H}
    (base : InputSideRootS2Producer (K := K) (G := G) sourceBasis)
    (defectSteps : List (JuliaDefectStep K D))
    (defectFactorBound : ℝ) (defectFactorBound_nonneg : 0 ≤ defectFactorBound)
    (hdom : ∀ x : H,
      ‖base.leftFactor (base.root (base.leftInput x))‖ ≤
        defectFactorBound *
          ‖juliaDefectColumn defectSteps
            (base.root (base.leftInput x))‖) :
    CoDefectAlignedInputSideRootS2Producer
      (H := H) (K := K) (D := D) (G := G) sourceBasis := by
  let physicalColumn : H →L[ℂ] G :=
    base.leftFactor ∘L base.root ∘L base.leftInput
  let defectColumn : H →L[ℂ]
      PiLp 2 (fun _ : Fin defectSteps.length => K) :=
    juliaDefectColumn defectSteps ∘L base.root ∘L base.leftInput
  let factorWitness :=
    CCM24FiniteSDouglasFactor.exists_factor_of_norm_le
      physicalColumn defectColumn defectFactorBound
      defectFactorBound_nonneg (by
        intro x
        exact hdom x)
  let defectFactor := Classical.choose factorWitness
  have factorSpec := Classical.choose_spec factorWitness
  refine
    { root := base.root
      leftInput := base.leftInput
      rightInput := base.rightInput
      leftFactor := base.leftFactor
      rightFactor := base.rightFactor
      leftRoot_summable_normSq := base.leftRoot_summable_normSq
      rightRoot_summable_normSq := base.rightRoot_summable_normSq
      defectSteps := defectSteps
      defectFactor := defectFactor
      defectFactorBound := defectFactorBound
      defectFactorBound_nonneg := defectFactorBound_nonneg
      defectFactor_norm_le := factorSpec.1
      left_factorization := by
        simpa only [physicalColumn, defectColumn] using
          factorSpec.2.symm
      response := base.response
      response_eq := base.response_eq }

theorem CoDefectAlignedInputSideRootS2Producer.leftColumn_normSq_le
    {ι H K D G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup D] [InnerProductSpace ℂ D] [CompleteSpace D]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ H}
    (producer : CoDefectAlignedInputSideRootS2Producer
      (H := H) (K := K) (D := D) (G := G) sourceBasis)
    (i : ι) :
    ‖producer.leftFactor
        (producer.root (producer.leftInput (sourceBasis i)))‖ ^ 2 ≤
      producer.defectFactorBound ^ 2 *
        ‖juliaDefectColumn producer.defectSteps
          (producer.root (producer.leftInput (sourceBasis i)))‖ ^ 2 := by
  have hfactorization := congrArg
    (fun T : H →L[ℂ] G => T (sourceBasis i))
    producer.left_factorization
  have hfactor_sq : ‖producer.defectFactor‖ ^ 2 ≤
      producer.defectFactorBound ^ 2 := by
    have hprod : 0 ≤ (producer.defectFactorBound -
        ‖producer.defectFactor‖) *
        (producer.defectFactorBound + ‖producer.defectFactor‖) :=
      mul_nonneg (sub_nonneg.mpr producer.defectFactor_norm_le)
        (add_nonneg producer.defectFactorBound_nonneg (norm_nonneg _))
    nlinarith
  rw [show producer.leftFactor
      (producer.root (producer.leftInput (sourceBasis i))) =
        producer.defectFactor
          (juliaDefectColumn producer.defectSteps
            (producer.root (producer.leftInput (sourceBasis i)))) by
        simpa only [ContinuousLinearMap.comp_apply] using hfactorization]
  calc
    ‖producer.defectFactor
        (juliaDefectColumn producer.defectSteps
          (producer.root (producer.leftInput (sourceBasis i))))‖ ^ 2 ≤
        (‖producer.defectFactor‖ *
          ‖juliaDefectColumn producer.defectSteps
            (producer.root (producer.leftInput (sourceBasis i)))‖) ^ 2 := by
      gcongr
      exact producer.defectFactor.le_opNorm _
    _ = ‖producer.defectFactor‖ ^ 2 *
        ‖juliaDefectColumn producer.defectSteps
          (producer.root (producer.leftInput (sourceBasis i)))‖ ^ 2 := by
      ring
    _ ≤ producer.defectFactorBound ^ 2 *
        ‖juliaDefectColumn producer.defectSteps
          (producer.root (producer.leftInput (sourceBasis i)))‖ ^ 2 := by
      exact mul_le_mul_of_nonneg_right hfactor_sq (sq_nonneg _)

theorem CoDefectAlignedInputSideRootS2Producer.leftColumn_summable_normSq
    {ι H K D G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup D] [InnerProductSpace ℂ D] [CompleteSpace D]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ H}
    (producer : CoDefectAlignedInputSideRootS2Producer
      (H := H) (K := K) (D := D) (G := G) sourceBasis) :
    Summable fun i => ‖producer.leftFactor
      (producer.root (producer.leftInput (sourceBasis i)))‖ ^ 2 := by
  have hcolumn : Summable (fun i =>
      ‖juliaDefectColumn producer.defectSteps
        (producer.root (producer.leftInput (sourceBasis i)))‖ ^ 2) :=
    Summable.of_nonneg_of_le
      (fun i => sq_nonneg _)
      (fun i => juliaDefectColumn_normSq_le_normSq producer.defectSteps
        (producer.root (producer.leftInput (sourceBasis i))))
      producer.leftRoot_summable_normSq
  have hmajorant := hcolumn.mul_left (producer.defectFactorBound ^ 2)
  exact Summable.of_nonneg_of_le
    (fun i => sq_nonneg _)
    (fun i => producer.leftColumn_normSq_le i)
    hmajorant

theorem CoDefectAlignedInputSideRootS2Producer.rightColumn_summable_normSq
    {ι H K D G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup D] [InnerProductSpace ℂ D] [CompleteSpace D]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ H}
    (producer : CoDefectAlignedInputSideRootS2Producer
      (H := H) (K := K) (D := D) (G := G) sourceBasis) :
    Summable fun i => ‖producer.rightFactor
      (producer.root (producer.rightInput (sourceBasis i)))‖ ^ 2 := by
  have hmajorant := producer.rightRoot_summable_normSq.mul_left
    (‖producer.rightFactor‖ ^ 2)
  apply Summable.of_nonneg_of_le
    (fun i => sq_nonneg _)
    (fun i => ?_)
    hmajorant
  calc
    ‖producer.rightFactor
        (producer.root (producer.rightInput (sourceBasis i)))‖ ^ 2 ≤
      (‖producer.rightFactor‖ *
        ‖producer.root (producer.rightInput (sourceBasis i))‖) ^ 2 := by
      gcongr
      exact producer.rightFactor.le_opNorm _
    _ = ‖producer.rightFactor‖ ^ 2 *
        ‖producer.root (producer.rightInput (sourceBasis i))‖ ^ 2 := by
      ring

theorem coDefectAlignedInputSideRootS2Producer_ordinaryTrace_norm_le
    {ι H K D G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup D] [InnerProductSpace ℂ D] [CompleteSpace D]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ H}
    (producer : CoDefectAlignedInputSideRootS2Producer
      (H := H) (K := K) (D := D) (G := G) sourceBasis) :
    ‖CC20Concrete.PositiveTrace.ordinaryTraceAlong sourceBasis
        producer.response‖ ≤
      (1 / 2 : ℝ) *
        (producer.defectFactorBound ^ 2 *
            (∑' i, ‖producer.root
              (producer.leftInput (sourceBasis i))‖ ^ 2) +
          ‖producer.rightFactor‖ ^ 2 *
            (∑' i, ‖producer.root
              (producer.rightInput (sourceBasis i))‖ ^ 2)) := by
  let data :=
    CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.mk
      (producer.leftFactor ∘L producer.root ∘L producer.leftInput)
      (producer.rightFactor ∘L producer.root ∘L producer.rightInput)
      producer.leftColumn_summable_normSq
      producer.rightColumn_summable_normSq
  have hresponse : data.traceProduct = producer.response := by
    change (producer.leftFactor ∘L producer.root ∘L producer.leftInput).adjoint ∘L
        (producer.rightFactor ∘L producer.root ∘L producer.rightInput) =
      producer.response
    exact producer.response_eq
  have htrace : CC20Concrete.PositiveTrace.IsTraceClassAlong sourceBasis
      producer.response := by
    rw [← hresponse]
    exact data.traceProduct_isTraceClassAlong
  have hdiag : Summable (fun i =>
      ‖⟪sourceBasis i, producer.response (sourceBasis i)⟫_ℂ‖) :=
    htrace.norm
  have hleftMajorant : Summable (fun i =>
      (1 / 2 : ℝ) *
        (producer.defectFactorBound ^ 2 *
            ‖producer.root (producer.leftInput (sourceBasis i))‖ ^ 2 +
          ‖producer.rightFactor‖ ^ 2 *
            ‖producer.root (producer.rightInput (sourceBasis i))‖ ^ 2)) := by
    have hleft := producer.leftRoot_summable_normSq.mul_left
      ((1 / 2 : ℝ) * producer.defectFactorBound ^ 2)
    have hright := producer.rightRoot_summable_normSq.mul_left
      ((1 / 2 : ℝ) * ‖producer.rightFactor‖ ^ 2)
    apply (hleft.add hright).congr
    intro i
    ring
  have hpoint : ∀ i, ‖⟪sourceBasis i,
      producer.response (sourceBasis i)⟫_ℂ‖ ≤
      (1 / 2 : ℝ) *
        (producer.defectFactorBound ^ 2 *
            ‖producer.root (producer.leftInput (sourceBasis i))‖ ^ 2 +
          ‖producer.rightFactor‖ ^ 2 *
            ‖producer.root (producer.rightInput (sourceBasis i))‖ ^ 2) := by
    intro i
    have hdiagonal :
        ⟪sourceBasis i, producer.response (sourceBasis i)⟫_ℂ =
      ⟪data.left (sourceBasis i), data.right (sourceBasis i)⟫_ℂ := by
      rw [← hresponse]
      exact data.traceProduct_diagonal i
    rw [hdiagonal]
    have hsum : ‖data.left (sourceBasis i)‖ ^ 2 +
        ‖data.right (sourceBasis i)‖ ^ 2 ≤
      producer.defectFactorBound ^ 2 *
          ‖producer.root (producer.leftInput (sourceBasis i))‖ ^ 2 +
        ‖producer.rightFactor‖ ^ 2 *
          ‖producer.root (producer.rightInput (sourceBasis i))‖ ^ 2 := by
      apply add_le_add
      · change ‖producer.leftFactor
          (producer.root (producer.leftInput (sourceBasis i)))‖ ^ 2 ≤
          producer.defectFactorBound ^ 2 *
            ‖producer.root (producer.leftInput (sourceBasis i))‖ ^ 2
        calc
          ‖producer.leftFactor
              (producer.root (producer.leftInput (sourceBasis i)))‖ ^ 2 ≤
              producer.defectFactorBound ^ 2 *
                ‖juliaDefectColumn producer.defectSteps
                  (producer.root (producer.leftInput (sourceBasis i)))‖ ^ 2 :=
            producer.leftColumn_normSq_le i
          _ ≤ producer.defectFactorBound ^ 2 *
              ‖producer.root (producer.leftInput (sourceBasis i))‖ ^ 2 := by
            exact mul_le_mul_of_nonneg_left
              (juliaDefectColumn_normSq_le_normSq producer.defectSteps
                (producer.root (producer.leftInput (sourceBasis i))))
              (sq_nonneg _)
      · calc
          ‖producer.rightFactor
              (producer.root (producer.rightInput (sourceBasis i)))‖ ^ 2 ≤
              (‖producer.rightFactor‖ *
                ‖producer.root (producer.rightInput (sourceBasis i))‖) ^ 2 := by
            gcongr
            exact producer.rightFactor.le_opNorm _
          _ = ‖producer.rightFactor‖ ^ 2 *
              ‖producer.root (producer.rightInput (sourceBasis i))‖ ^ 2 := by
            ring
    calc
      ‖⟪data.left (sourceBasis i), data.right (sourceBasis i)⟫_ℂ‖ ≤
          ‖data.left (sourceBasis i)‖ * ‖data.right (sourceBasis i)‖ :=
        norm_inner_le_norm _ _
      _ ≤ (1 / 2 : ℝ) *
          (‖data.left (sourceBasis i)‖ ^ 2 +
            ‖data.right (sourceBasis i)‖ ^ 2) := by
        nlinarith [sq_nonneg (‖data.left (sourceBasis i)‖ -
          ‖data.right (sourceBasis i)‖)]
      _ ≤ (1 / 2 : ℝ) *
          (producer.defectFactorBound ^ 2 *
              ‖producer.root (producer.leftInput (sourceBasis i))‖ ^ 2 +
            ‖producer.rightFactor‖ ^ 2 *
              ‖producer.root (producer.rightInput (sourceBasis i))‖ ^ 2) := by
        exact mul_le_mul_of_nonneg_left hsum (by norm_num)
  rw [CC20Concrete.PositiveTrace.ordinaryTraceAlong]
  calc
    ‖∑' i, ⟪sourceBasis i,
        producer.response (sourceBasis i)⟫_ℂ‖ ≤
      ∑' i, ‖⟪sourceBasis i,
          producer.response (sourceBasis i)⟫_ℂ‖ :=
      norm_tsum_le_tsum_norm hdiag
    _ ≤ ∑' i, (1 / 2 : ℝ) *
        (producer.defectFactorBound ^ 2 *
            ‖producer.root (producer.leftInput (sourceBasis i))‖ ^ 2 +
          ‖producer.rightFactor‖ ^ 2 *
            ‖producer.root (producer.rightInput (sourceBasis i))‖ ^ 2) :=
      hdiag.tsum_le_tsum hpoint hleftMajorant
    _ = (1 / 2 : ℝ) *
        (producer.defectFactorBound ^ 2 *
            (∑' i, ‖producer.root
              (producer.leftInput (sourceBasis i))‖ ^ 2) +
          ‖producer.rightFactor‖ ^ 2 *
            (∑' i, ‖producer.root
              (producer.rightInput (sourceBasis i))‖ ^ 2)) := by
      rw [tsum_mul_left,
        (producer.leftRoot_summable_normSq.mul_left
          (producer.defectFactorBound ^ 2)).tsum_add
        (producer.rightRoot_summable_normSq.mul_left
          (‖producer.rightFactor‖ ^ 2)),
        tsum_mul_left,
        tsum_mul_left]

/-!
This is the source-facing Gate 3U entry point.  The theorem does not hide the
remaining producer obligation: callers must identify the actual finite-S
physical left column with the co-defect column and provide bounds for the two
root energies.  In particular, a normalized operator contraction alone cannot
be substituted for `left_factorization`.
-/
theorem sourceBandGramResponse_ordinaryTrace_norm_le_of_coDefectAlignedInputSide
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    {ι K D G : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup D] [InnerProductSpace ℂ D] [CompleteSpace D]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda)}
    (producer : CoDefectAlignedInputSideRootS2Producer
      (H := sourceSoninCarrier lambda) (K := K) (D := D) (G := G)
        sourceBasis)
    (hresponse : producer.response =
      sourceBandGramResponse owner lambda family) :
    ‖CC20Concrete.PositiveTrace.ordinaryTraceAlong sourceBasis
        (sourceBandGramResponse owner lambda family)‖ ≤
      (1 / 2 : ℝ) *
        (producer.defectFactorBound ^ 2 *
            (∑' i, ‖producer.root
              (producer.leftInput (sourceBasis i))‖ ^ 2) +
          ‖producer.rightFactor‖ ^ 2 *
            (∑' i, ‖producer.root
              (producer.rightInput (sourceBasis i))‖ ^ 2)) := by
  rw [← hresponse]
  exact coDefectAlignedInputSideRootS2Producer_ordinaryTrace_norm_le producer

end CCM24FiniteSCoDefectConsumer
end CCM25Concrete
end Source
end ConnesWeilRH
