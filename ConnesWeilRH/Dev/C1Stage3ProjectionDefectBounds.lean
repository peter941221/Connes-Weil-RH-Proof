/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1Stage3ProjectionResponseBridge
import ConnesWeilRH.Dev.C1PositiveTraceCutoffGrowth
import ConnesWeilRH.Dev.C1PositiveTraceCutoffVerdict

/-!
# C1 Stage-3 projection defect bounds and cutoff obstruction

This file keeps the two operator mismatches from
`C1Stage3ProjectionResponseBridge` quantitative.

For a bounded root factor `F`, output compression `Z† K Z`, and response `R`,
the two defects are

```text
D₁ = F† (Z† K Z - I) F
D₂ = windowedDetector - R.
```

The first theorem gives the honest operator-norm estimate for `D₁`; the second
gives the triangle estimate for `D₂`.  These estimates do not manufacture a
cutoff rate.  The canonical symmetric cutoff is then used to prove a stronger
negative result for `D₂`: its real trace is unbounded for every nonzero test,
because the windowed detector has the exact linear bulk trace while `R` is a
fixed operator.  Thus the frequently requested statement
`D₂,n -> 0` is false for the current owner.

The remaining `D₁` limit is deliberately not asserted: the finite-stage
zero-iff identifies the exact sandwich that must vanish, while a separate
compressed-kernel estimate is still needed to force any cutoff rate.  No such
estimate is silently assumed here.
-/

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace C1Stage3ProjectionDefectBounds

open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open CC20Concrete.PositiveTrace
open C1PositiveTraceCutoffAdapter
open C1PositiveTraceCutoffGrowth
open C1PositiveTraceCutoffVerdict
open C1Stage3ProjectionResponseBridge
open C1Stage3ProjectionTraceLedger
open CCM25Concrete.SelectedWeilSquare
open MeasureTheory
open Filter
open scoped Topology

noncomputable section

abbrev projectionCarrier := cc20GlobalLogCrossingL2

/-! ## Unconditional quantitative bounds -/

/-- The insertion defect has the expected three-factor operator-norm bound.
This is the only bound available without a rate for the compressed kernel. -/
theorem norm_kernelInsertionSandwich_le
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest)
    (a c : ℝ) (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    ‖kernelInsertionSandwich g a c lambda S‖ ≤
      ‖fullBoundaryRootFactor g a c‖ ^ 2 *
        ‖kernelInsertionDefect a c lambda S‖ := by
  unfold kernelInsertionSandwich
  calc
    ‖(fullBoundaryRootFactor g a c).adjoint ∘L
        kernelInsertionDefect a c lambda S ∘L
          fullBoundaryRootFactor g a c‖ ≤
      ‖(fullBoundaryRootFactor g a c).adjoint‖ *
        ‖kernelInsertionDefect a c lambda S ∘L
          fullBoundaryRootFactor g a c‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖(fullBoundaryRootFactor g a c).adjoint‖ *
        (‖kernelInsertionDefect a c lambda S‖ *
          ‖fullBoundaryRootFactor g a c‖) := by
      gcongr
      exact ContinuousLinearMap.opNorm_comp_le _ _
    _ = ‖fullBoundaryRootFactor g a c‖ ^ 2 *
        ‖kernelInsertionDefect a c lambda S‖ := by
      rw [ContinuousLinearMap.adjoint.norm_map]
      ring

/-- The second defect is bounded by the sum of the two owner norms. -/
theorem norm_windowToResponseDefect_le
    (owner : SelectedWeilSquareOwner) (a c : ℝ)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    ‖windowToResponseDefect owner a c lambda S‖ ≤
      ‖windowedBoundaryDetector owner.sourceTest a c‖ +
        ‖projectionResponse owner lambda S‖ := by
  unfold windowToResponseDefect
  exact norm_sub_le _ _

/-- A zero insertion defect is equivalent to the compressed kernel acting as
the identity after sandwiching by the same root factor. -/
theorem kernelInsertionSandwich_eq_zero_iff
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest)
    (a c : ℝ) (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    kernelInsertionSandwich g a c lambda S = 0 ↔
      (fullBoundaryRootFactor g a c).adjoint ∘L
          (outputCompressedStage3Kernel a c lambda S -
            ContinuousLinearMap.id ℂ
              (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c)))) ∘L
        fullBoundaryRootFactor g a c = 0 := by
  rfl

/-- The response defect is zero exactly when the finite-window detector and
the active projection response are the same owner. -/
theorem windowToResponseDefect_eq_zero_iff
    (owner : SelectedWeilSquareOwner) (a c : ℝ)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    windowToResponseDefect owner a c lambda S = 0 ↔
      windowedBoundaryDetector owner.sourceTest a c =
        projectionResponse owner lambda S := by
  simpa [windowToResponseDefect] using
    (sub_eq_zero :
      windowedBoundaryDetector owner.sourceTest a c -
          projectionResponse owner lambda S = 0 ↔
        windowedBoundaryDetector owner.sourceTest a c =
          projectionResponse owner lambda S)

/-! ## The canonical cutoff sequence -/

/-- `D₁` specialized to the existing symmetric cutoff, transported back to the
fixed whole-line carrier. -/
noncomputable def cutoffKernelInsertionSandwich
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) (n : Nat) :
    projectionCarrier →L[ℂ] projectionCarrier :=
  kernelInsertionSandwich g (cutoffLower g n) (cutoffUpper g n) lambda S

/-- `D₂` specialized to the same cutoff and fixed whole-line carrier. -/
noncomputable def cutoffWindowToResponseDefect
    (owner : SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) (n : Nat) :
    projectionCarrier →L[ℂ] projectionCarrier :=
  windowToResponseDefect owner
    (cutoffLower owner.sourceTest n) (cutoffUpper owner.sourceTest n)
    lambda S

theorem norm_cutoffKernelInsertionSandwich_le
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) (n : Nat) :
    ‖cutoffKernelInsertionSandwich g lambda S n‖ ≤
      ‖fullBoundaryRootFactor g (cutoffLower g n) (cutoffUpper g n)‖ ^ 2 *
        ‖kernelInsertionDefect (cutoffLower g n) (cutoffUpper g n)
          lambda S‖ := by
  exact norm_kernelInsertionSandwich_le g (cutoffLower g n)
    (cutoffUpper g n) lambda S

theorem norm_cutoffWindowToResponseDefect_le
    (owner : SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) (n : Nat) :
    ‖cutoffWindowToResponseDefect owner lambda S n‖ ≤
      ‖windowedBoundaryDetector owner.sourceTest
          (cutoffLower owner.sourceTest n) (cutoffUpper owner.sourceTest n)‖ +
        ‖projectionResponse owner lambda S‖ := by
  exact norm_windowToResponseDefect_le owner
    (cutoffLower owner.sourceTest n) (cutoffUpper owner.sourceTest n)
    lambda S

/-! ## Trace identity and the hard obstruction for `D₂` -/

theorem ordinaryTraceAlong_cutoffWindowToResponseDefect_eq_sub
    (owner : SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime)
    {nu : Type*} (globalBasis : HilbertBasis nu ℂ projectionCarrier)
    (hresponse : IsTraceClassAlong globalBasis
      (projectionResponse owner lambda S)) (n : Nat) :
    ordinaryTraceAlong globalBasis (cutoffWindowToResponseDefect owner lambda S n) =
      ordinaryTraceAlong globalBasis
          (windowedBoundaryDetector owner.sourceTest
            (cutoffLower owner.sourceTest n) (cutoffUpper owner.sourceTest n)) -
        ordinaryTraceAlong globalBasis (projectionResponse owner lambda S) := by
  unfold cutoffWindowToResponseDefect windowToResponseDefect
  exact ordinaryTraceAlong_sub globalBasis _ _
    (windowedBoundaryDetector_isTraceClassAlong
      owner.sourceTest (cutoffLower owner.sourceTest n)
        (cutoffUpper owner.sourceTest n)
        (cutoffFullBasis owner.sourceTest n)
        (cutoffOutputBasis owner.sourceTest n) globalBasis)
    hresponse

theorem cutoffWindowToResponseDefect_trace_re_eq_sub
    (owner : SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime)
    {nu : Type*} (globalBasis : HilbertBasis nu ℂ projectionCarrier)
    (hresponse : IsTraceClassAlong globalBasis
      (projectionResponse owner lambda S)) (n : Nat) :
    (ordinaryTraceAlong globalBasis
      (cutoffWindowToResponseDefect owner lambda S n)).re =
      (ordinaryTraceAlong globalBasis
        (windowedBoundaryDetector owner.sourceTest
          (cutoffLower owner.sourceTest n) (cutoffUpper owner.sourceTest n))).re -
        (ordinaryTraceAlong globalBasis (projectionResponse owner lambda S)).re := by
  have htrace := ordinaryTraceAlong_cutoffWindowToResponseDefect_eq_sub
    owner lambda S globalBasis hresponse n
  exact congrArg Complex.re htrace

/-- The real trace of `D₂,n` is unbounded on the canonical cutoff for every
nonzero source test.  This is the decisive kill-test for an independent
`D₂,n → 0` claim. -/
theorem cutoffWindowToResponseDefect_trace_re_unbounded_of_sourceTest_ne_zero
    (owner : SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime)
    {nu : Type*} (globalBasis : HilbertBasis nu ℂ projectionCarrier)
    (hresponse : IsTraceClassAlong globalBasis
      (projectionResponse owner lambda S))
    (hg : owner.sourceTest.test ≠ 0) :
    ∀ boundValue : ℝ, ∃ n,
      boundValue <
        (ordinaryTraceAlong globalBasis
          (cutoffWindowToResponseDefect owner lambda S n)).re := by
  intro boundValue
  let responseValue : ℝ :=
    (ordinaryTraceAlong globalBasis (projectionResponse owner lambda S)).re
  obtain ⟨n, hn⟩ :=
    cutoffPositiveBasisData_trace_re_unbounded_of_test_ne_zero
      owner.sourceTest globalBasis hg (boundValue + responseValue)
  have hdet := cutoffPositiveBasisData_trace_eq_detector
    owner.sourceTest globalBasis n
  have hdetRe := congrArg Complex.re hdet
  have hdetValue :
      boundValue + responseValue <
        (ordinaryTraceAlong globalBasis
          (windowedBoundaryDetector owner.sourceTest
            (cutoffLower owner.sourceTest n) (cutoffUpper owner.sourceTest n))).re := by
    calc
      boundValue + responseValue <
          (ordinaryTraceAlong globalBasis
            (cutoffPositiveBasisData owner.sourceTest globalBasis n).positiveComposition).re := hn
      _ = (ordinaryTraceAlong globalBasis
          (windowedBoundaryDetector owner.sourceTest
            (cutoffLower owner.sourceTest n) (cutoffUpper owner.sourceTest n))).re := hdetRe
  refine ⟨n, ?_⟩
  rw [cutoffWindowToResponseDefect_trace_re_eq_sub
    owner lambda S globalBasis hresponse n]
  dsimp only [responseValue] at hdetValue ⊢
  linarith

/-- Consequently the second defect cannot converge to zero even at the scalar
real-trace level. -/
theorem not_tendsto_zero_cutoffWindowToResponseDefect_trace_re_of_sourceTest_ne_zero
    (owner : SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime)
    {nu : Type*} (globalBasis : HilbertBasis nu ℂ projectionCarrier)
    (hresponse : IsTraceClassAlong globalBasis
      (projectionResponse owner lambda S))
    (hg : owner.sourceTest.test ≠ 0) :
    ¬ Tendsto
      (fun n =>
        (ordinaryTraceAlong globalBasis
          (cutoffWindowToResponseDefect owner lambda S n)).re)
      atTop (𝓝 (0 : ℝ)) := by
  intro hzero
  have hbounded : ∀ᶠ n : Nat in atTop,
      (ordinaryTraceAlong globalBasis
        (cutoffWindowToResponseDefect owner lambda S n)).re < 1 :=
    hzero.eventually (gt_mem_nhds (by norm_num))
  obtain ⟨N, hN⟩ := eventually_atTop.mp hbounded
  obtain ⟨n, hn⟩ :=
    cutoffWindowToResponseDefect_trace_re_unbounded_of_sourceTest_ne_zero
      owner lambda S globalBasis hresponse hg 1
  by_cases hNn : N ≤ n
  · exact (not_lt_of_ge (le_of_lt (hN n hNn))) hn
  · have hnN : n ≤ N := Nat.le_of_lt (Nat.lt_of_not_ge hNn)
    have hdetMono := cutoffPositiveBasisData_trace_re_monotone
      owner.sourceTest globalBasis hnN
    have hdetN := cutoffPositiveBasisData_trace_eq_detector
      owner.sourceTest globalBasis N
    have hdetn := cutoffPositiveBasisData_trace_eq_detector
      owner.sourceTest globalBasis n
    have hdetNRe := congrArg Complex.re hdetN
    have hdetnRe := congrArg Complex.re hdetn
    have hdetMono' :
        (ordinaryTraceAlong globalBasis
          (windowedBoundaryDetector owner.sourceTest
            (cutoffLower owner.sourceTest n) (cutoffUpper owner.sourceTest n))).re ≤
        (ordinaryTraceAlong globalBasis
          (windowedBoundaryDetector owner.sourceTest
            (cutoffLower owner.sourceTest N) (cutoffUpper owner.sourceTest N))).re := by
      rw [← hdetnRe, ← hdetNRe]
      exact hdetMono
    have hdefN := cutoffWindowToResponseDefect_trace_re_eq_sub
      owner lambda S globalBasis hresponse N
    have hdefn := cutoffWindowToResponseDefect_trace_re_eq_sub
      owner lambda S globalBasis hresponse n
    have hlargeN :
        1 < (ordinaryTraceAlong globalBasis
          (cutoffWindowToResponseDefect owner lambda S N)).re := by
      rw [hdefN]
      have : 1 <
          (ordinaryTraceAlong globalBasis
            (windowedBoundaryDetector owner.sourceTest
              (cutoffLower owner.sourceTest N) (cutoffUpper owner.sourceTest N))).re -
          (ordinaryTraceAlong globalBasis (projectionResponse owner lambda S)).re := by
        rw [hdefn] at hn
        linarith [hdetMono']
      exact this
    exact (not_lt_of_ge (le_of_lt (hN N (le_rfl)))) hlargeN

end
end C1Stage3ProjectionDefectBounds
end Dev
end Source
end ConnesWeilRH
