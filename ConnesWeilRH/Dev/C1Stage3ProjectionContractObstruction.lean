/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1Stage3ProjectionDefectBounds
import ConnesWeilRH.Dev.C1Stage3ProjectionOperatorFamily

/-!
# Conditional obstruction for the fixed-response projection contract

The projection-window operator is positive and trace class at every cutoff.
This leaf isolates the remaining owner mismatch: if the insertion defect has
vanishing real trace and the response is fixed, the projection cutoff trace
contract is impossible because the window bulk is unbounded.  Thus any live
projection producer must retain a divergent counterterm in the insertion
trace, or use a genuinely moving/renormalized response.
-/

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace C1Stage3ProjectionContractObstruction

open Filter
open scoped Topology
open CC20Concrete
open CC20Concrete.PositiveTrace
open C1PositiveTraceCutoffAdapter
open C1Stage3ProjectionDefectBounds
open C1Stage3ProjectionOperatorFamily
open C1Stage3ProjectionResponseBridge
open CCM25Concrete.SelectedWeilSquare
open CCM25Concrete.CompactLogConvolution

noncomputable section

theorem not_projectionCutoffLimitContracts_of_fixedResponse_and_traceDefect_vanishing
    (owner : SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime)
    {nu : Type*} (globalBasis : HilbertBasis nu ℂ
      C1Stage3ProjectionOperatorFamily.projectionCarrier)
    (hresponse : IsTraceClassAlong globalBasis
      (C1Stage3ProjectionTraceLedger.projectionResponse owner lambda S))
    (contracts : ProjectionCutoffLimitContracts owner.sourceTest lambda S
      globalBasis)
    (hD1 : Tendsto
      (fun n => (ordinaryTraceAlong globalBasis
        (cutoffKernelInsertionSandwich owner.sourceTest lambda S n)).re)
      atTop (𝓝 (0 : Real)))
    (hg : owner.sourceTest.test ≠ 0) : False := by
  have hfull : Tendsto
      (fun n => (ordinaryTraceAlong globalBasis
        (cutoffProjectionOperator owner.sourceTest lambda S globalBasis n)).re)
      atTop (𝓝 (C1SameOwnerWeil.qw owner.sourceTest)) := by
    have hsum := contracts.readback_tendsto_qw.add
      contracts.remainder_tendsto_zero
    simpa [sub_add_cancel] using hsum
  let responseValue : Real :=
    (ordinaryTraceAlong globalBasis
      (C1Stage3ProjectionTraceLedger.projectionResponse owner lambda S)).re
  have hfullEventually : ∀ᶠ n in atTop,
    (ordinaryTraceAlong globalBasis
        (cutoffProjectionOperator owner.sourceTest lambda S globalBasis n)).re <
        C1SameOwnerWeil.qw owner.sourceTest + 1 :=
    hfull.eventually (show Set.Iio (C1SameOwnerWeil.qw owner.sourceTest + 1) ∈
      𝓝 (C1SameOwnerWeil.qw owner.sourceTest) from
      Iio_mem_nhds (by linarith))
  have hD1Eventually : ∀ᶠ n in atTop,
      -1 < (ordinaryTraceAlong globalBasis
        (cutoffKernelInsertionSandwich owner.sourceTest lambda S n)).re :=
    hD1.eventually (show Set.Ioi (-1 : Real) ∈ 𝓝 (0 : Real) from
      Ioi_mem_nhds (by norm_num))
  obtain ⟨Nfull, hNfull⟩ := eventually_atTop.mp hfullEventually
  obtain ⟨ND1, hND1⟩ := eventually_atTop.mp hD1Eventually
  let N : Nat := max Nfull ND1
  obtain ⟨n, hnN, hlarge⟩ :=
    cutoffWindowToMovingResponseDefect_trace_re_cofinal_unbounded_of_sourceTest_ne_zero
      owner (fun _ : Nat =>
        C1Stage3ProjectionTraceLedger.projectionResponse owner lambda S) globalBasis
      (fun _ => hresponse) ⟨responseValue, fun _ => le_rfl⟩ hg N
      (C1SameOwnerWeil.qw owner.sourceTest + 1 - responseValue + 1)
  have hlarge' :
      C1SameOwnerWeil.qw owner.sourceTest + 1 - responseValue + 1 <
        (ordinaryTraceAlong globalBasis
          (cutoffWindowToResponseDefect owner lambda S n)).re := by
    simpa [cutoffWindowToMovingResponseDefect,
      cutoffWindowToResponseDefect, windowToResponseDefect] using hlarge
  have hdecomp :=
      ordinaryTraceAlong_cutoffProjectionOperator_eq_projectionResponse_add_defects
      owner lambda S globalBasis hresponse n
  have hdecompRe := congrArg Complex.re hdecomp
  have hdecompRe' :
      (ordinaryTraceAlong globalBasis
        (cutoffProjectionOperator owner.sourceTest lambda S globalBasis n)).re =
        (ordinaryTraceAlong globalBasis
          (C1Stage3ProjectionTraceLedger.projectionResponse owner lambda S)).re +
          (ordinaryTraceAlong globalBasis
            (cutoffKernelInsertionSandwich owner.sourceTest lambda S n)).re +
          (ordinaryTraceAlong globalBasis
            (cutoffWindowToResponseDefect owner lambda S n)).re := by
    simpa only [Complex.add_re, cutoffKernelInsertionSandwich,
      cutoffWindowToResponseDefect] using hdecompRe
  have hupper := hNfull n (le_trans (le_max_left _ _) hnN)
  have hlower := hND1 n (le_trans (le_max_right _ _) hnN)
  have hupper' :
      (ordinaryTraceAlong globalBasis
        (cutoffWindowToResponseDefect owner lambda S n)).re <
        C1SameOwnerWeil.qw owner.sourceTest + 1 - responseValue + 1 := by
    dsimp only [responseValue] at hupper hlower ⊢
    linarith [hdecompRe']
  exact (not_lt_of_ge (le_of_lt hupper')) hlarge'

end
end C1Stage3ProjectionContractObstruction
end Dev
end Source
end ConnesWeilRH
