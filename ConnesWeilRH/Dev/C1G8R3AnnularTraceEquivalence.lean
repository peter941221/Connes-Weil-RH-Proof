/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3SourceRootFiniteWindowCriterion
import ConnesWeilRH.Dev.C1G8R3AnnularTraceConsumer
import ConnesWeilRH.Dev.C1G8R3ActualEndpointTraceLimit

/-!
# The uniform annular trace bound is exactly the survivor core

The single remaining front-A object — a uniform bound
`Re tr Gram(N,n) <= B` for `n >= N` — is often called *sufficient* for the
survivor core (the consumer chain 1659-1676).  This module formalizes the
CONVERSE direction and packages both as an iff, so the estimate's exact
strength is on the record:

* (`_of_ambientColumnEnergy`) if the ambient root column energy is
  square-summable along the carrier basis, then `B := 4 * SUM' || C J e_i ||^2`
  is a uniform annular trace bound.  Proof: the two interval projections are
  norm-one, so the annular output column is at most `2 * || C J e_i ||`;
  `tsum_le_tsum` and the exact column-energy identity do the rest.
* (`uniformAnnularTraceBound_iff_survivorCore`) the iff: by 1659
  (`g8EndpointGate_iff_survivorCore`) the ambient column energy is
  equivalent to the survivor core, and by 1676 the uniform bound implies
  the core.  Hence

  ```text
  (exists B uniform annular trace bound)  <->  survivor-core square-sum
  <->  ambient column energy  <->  endpoint gate  (1659).
  ```

No slack: proving the estimate is proving the gate content itself, and
refuting it (with the carrier nonempty) refutes the lane.  No estimate is
proved here and RH is not claimed.
-/

namespace ConnesWeilRH
namespace Dev

open Filter
open MeasureTheory
open Source.CC20Concrete
open Source.CC20Concrete.CompactRootHalfLinePair
open Source.CCM25Concrete.CCM24FiniteSGramResponse
open Source.CCM25Concrete.CCM24FiniteSProjectionTrace
open Source.CCM25Concrete.CCM24FiniteSBandTrace
open Source.CCM25Concrete.SelectedCrossingOperatorBridge
open Source.CCM25Concrete.SelectedWeilSquare
open scoped Topology

-- The kernel module's CompleteSpace instance on the carrier is `local`, so
-- every consumer module re-declares it (pattern: C1G8R3SourceCompressedRootKernel.lean).
noncomputable local instance annularTraceEquivalenceCarrierCompleteSpace
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

/-- A uniform annular trace bound follows from the ambient root column
energy alone: each annular output column is at most twice the unwindowed
column (difference of two norm-one projections), and the exact 1669
column-energy identity transports the `tsum` domination to the trace. -/
theorem uniformAnnularTraceBound_of_ambientColumnEnergy
    (owner : SelectedWeilSquareOwner) (lambda : CCM24SoninScale)
    {ι : Type*}
    (sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda))
    (N : ℕ) (hN : selectedRootSupportRadius owner ≤ (N : ℝ))
    (hgate : Summable fun i =>
      ‖rootConvolution owner (sourceInclusion lambda
        (sourceBasis i))‖ ^ 2) :
    ∃ B : ℝ, ∀ n, N ≤ n →
      (Source.CC20Concrete.PositiveTrace.ordinaryTraceAlong sourceBasis
        (sourceRootAnnularGram owner lambda N n)).re ≤ B := by
  have hB : Summable fun i => (4 : ℝ) * ‖rootConvolution owner
      (sourceInclusion lambda (sourceBasis i))‖ ^ 2 :=
    Summable.mul_left (4 : ℝ) hgate
  refine ⟨∑' i, (4 : ℝ) * ‖rootConvolution owner
    (sourceInclusion lambda (sourceBasis i))‖ ^ 2, fun n hn => ?_⟩
  have hnN : selectedRootSupportRadius owner ≤ (n : ℝ) :=
    le_trans hN (Nat.cast_le.mpr hn)
  have hsumAnn := sourceRootAnnularOutputWindow_sourceBasis_normSq_summable
    owner lambda N n hN hnN sourceBasis
  have hle : (∑' i, ‖sourceRootAnnularOutputWindow owner lambda N n
      (sourceBasis i)‖ ^ 2) ≤
      (∑' i, (4 : ℝ) * ‖rootConvolution owner
        (sourceInclusion lambda (sourceBasis i))‖ ^ 2) := by
    refine hsumAnn.tsum_le_tsum (fun i => ?_) hB
    have h2 : ‖sourceRootAnnularOutputWindow owner lambda N n
        (sourceBasis i)‖ ≤
        2 * ‖rootConvolution owner (sourceInclusion lambda
          (sourceBasis i))‖ := by
      have hcN : ‖kernelIntervalProjection (-(n : ℝ)) (n : ℝ) 0 (rootConvolution
          owner (sourceInclusion lambda (sourceBasis i)))‖
          ≤ ‖rootConvolution owner (sourceInclusion lambda
            (sourceBasis i))‖ := by
        calc
          _ ≤ ‖kernelIntervalProjection (-(n : ℝ)) (n : ℝ) 0‖ *
              ‖rootConvolution owner (sourceInclusion lambda
                (sourceBasis i))‖ :=
            ContinuousLinearMap.le_opNorm _ _
          _ ≤ 1 * ‖rootConvolution owner (sourceInclusion lambda
              (sourceBasis i))‖ :=
            mul_le_mul_of_nonneg_right (norm_kernelIntervalProjection_le_one
              (-(n : ℝ)) (n : ℝ) 0) (norm_nonneg _)
          _ = ‖rootConvolution owner (sourceInclusion lambda
              (sourceBasis i))‖ := by norm_num
      have hcN' : ‖kernelIntervalProjection (-(N : ℝ)) (N : ℝ) 0
          (rootConvolution owner (sourceInclusion lambda
            (sourceBasis i)))‖
          ≤ ‖rootConvolution owner (sourceInclusion lambda
            (sourceBasis i))‖ := by
        calc
          _ ≤ ‖kernelIntervalProjection (-(N : ℝ)) (N : ℝ) 0‖ *
              ‖rootConvolution owner (sourceInclusion lambda
                (sourceBasis i))‖ :=
            ContinuousLinearMap.le_opNorm _ _
          _ ≤ 1 * ‖rootConvolution owner (sourceInclusion lambda
              (sourceBasis i))‖ :=
            mul_le_mul_of_nonneg_right (norm_kernelIntervalProjection_le_one
              (-(N : ℝ)) (N : ℝ) 0) (norm_nonneg _)
          _ = ‖rootConvolution owner (sourceInclusion lambda
              (sourceBasis i))‖ := by norm_num
      calc
        ‖sourceRootAnnularOutputWindow owner lambda N n (sourceBasis i)‖
            = ‖kernelIntervalProjection (-(n : ℝ)) (n : ℝ) 0
                (rootConvolution owner (sourceInclusion lambda
                  (sourceBasis i)))
              - kernelIntervalProjection (-(N : ℝ)) (N : ℝ) 0
                (rootConvolution owner (sourceInclusion lambda
                  (sourceBasis i)))‖ := by
          rw [sourceRootAnnularOutputWindow]
          simp only [ContinuousLinearMap.comp_apply,
            ContinuousLinearMap.sub_apply]
        _ ≤ ‖kernelIntervalProjection (-(n : ℝ)) (n : ℝ) 0
              (rootConvolution owner (sourceInclusion lambda
                (sourceBasis i)))‖
              + ‖kernelIntervalProjection (-(N : ℝ)) (N : ℝ) 0
                (rootConvolution owner (sourceInclusion lambda
                  (sourceBasis i)))‖ := norm_sub_le _ _
        _ ≤ ‖rootConvolution owner (sourceInclusion lambda
              (sourceBasis i))‖ + ‖rootConvolution owner
              (sourceInclusion lambda (sourceBasis i))‖ :=
            add_le_add hcN hcN'
        _ = 2 * ‖rootConvolution owner (sourceInclusion lambda
              (sourceBasis i))‖ := by ring
    calc
      ‖sourceRootAnnularOutputWindow owner lambda N n
          (sourceBasis i)‖ ^ 2 ≤
          (2 * ‖rootConvolution owner (sourceInclusion lambda
            (sourceBasis i))‖) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _)
          (mul_nonneg zero_le_two (norm_nonneg _))).mpr h2
      _ = (4 : ℝ) * ‖rootConvolution owner (sourceInclusion lambda
            (sourceBasis i))‖ ^ 2 := by
        rw [two_mul]; ring
  have hcast : (∑' i, ((‖sourceRootAnnularOutputWindow owner lambda N n
        (sourceBasis i)‖ ^ 2 : ℝ) : ℂ)) =
      ((∑' i, ‖sourceRootAnnularOutputWindow owner lambda N n
        (sourceBasis i)‖ ^ 2 : ℝ) : ℂ) :=
    (Complex.ofRealCLM.map_tsum hsumAnn).symm
  rw [sourceRootAnnularGram_trace_eq_column_energy owner lambda N n sourceBasis,
    hcast, Complex.ofReal_re]
  exact hle

/-- **The uniform annular trace bound is exactly the survivor core.**
Forward by the 1676 trace-form consumer; backward through the 1659 ambient
equivalence and the norm-one projection domination above.  Together with
1659 the estimate is the gate content itself — there is no slack between
"proving the estimate" and "proving the endpoint face". -/
theorem uniformAnnularTraceBound_iff_survivorCore
    (owner : SelectedWeilSquareOwner) (lambda : CCM24SoninScale)
    {ι : Type*}
    (sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda))
    (N : ℕ) (hN : selectedRootSupportRadius owner ≤ (N : ℝ)) :
    (∃ B : ℝ, ∀ n, N ≤ n →
      (Source.CC20Concrete.PositiveTrace.ordinaryTraceAlong sourceBasis
        (sourceRootAnnularGram owner lambda N n)).re ≤ B) ↔
    Summable fun i => ‖sourceCompressedRoot owner lambda
      (sourceBasis i)‖ ^ 2 := by
  constructor
  · intro h
    obtain ⟨B, hB⟩ := h
    exact sourceCompressedRoot_squareSum_of_eventual_ambient_annular_trace_bound
      owner lambda sourceBasis N hN hB
  · intro hcore
    have hamb : Summable fun i => ‖rootConvolution owner
        (sourceInclusion lambda (sourceBasis i))‖ ^ 2 :=
      (g8EndpointGate_iff_survivorCore owner lambda sourceBasis).mpr
        (show Summable fun i => ‖((sourceInclusion lambda).adjoint ∘L
            rootConvolution owner ∘L sourceInclusion lambda)
            (sourceBasis i)‖ ^ 2 from hcore)
    exact uniformAnnularTraceBound_of_ambientColumnEnergy owner lambda
      sourceBasis N hN hamb

end Dev
end ConnesWeilRH
