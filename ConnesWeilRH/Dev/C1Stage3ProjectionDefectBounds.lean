/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1Stage3ProjectionResponseBridge
import ConnesWeilRH.Dev.C1PositiveTraceCutoffGrowth
import ConnesWeilRH.Dev.C1PositiveTraceCutoffVerdict
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompactRootEnergy

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
open C1PositiveTraceWindowProducer
open C1Stage3ProjectionKernel
open C1Stage3ProjectionResponseBridge
open C1Stage3ProjectionTraceLedger
open CCM25Concrete.SelectedWeilSquare
open CCM25Concrete.SelectedCrossingOperatorBridge
open CCM25Concrete.CCM24FiniteSCompactRootEnergy
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

/-! ## The D₁ compressed-kernel reduction

The insertion defect is not an independent object: it is exactly the output-
compression, by the same zero-extension `Z`, of the fixed global operator
`K_S - id`.  Because the compressed kernel deviates from the identity only
through this single cutoff-independent operator, no decay of `D₁,n -> 0` can be
manufactured from the windowing alone; it requires a genuine estimate on how
that fixed operator compresses to expanding output windows. -/

/-- The insertion defect equals the output-compression of the Stage-3 kernel's
deviation from the identity global operator.  Since `Z = fullBoundaryOutputZeroExtension a c`
satisfies `Z.adjoint ∘L Z = id`, we have `Z.adjoint K_S Z - I = Z.adjoint (K_S - id) Z`. -/
theorem kernelInsertionDefect_eq_compressedKernelDifference
    (a c : ℝ) (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    kernelInsertionDefect a c lambda S =
      (fullBoundaryOutputZeroExtension a c).adjoint ∘L
        (stage3ProjectionKernel lambda S - ContinuousLinearMap.id ℂ cc20GlobalLogCrossingL2) ∘L
          fullBoundaryOutputZeroExtension a c := by
  apply ContinuousLinearMap.ext
  intro u
  unfold kernelInsertionDefect outputCompressedStage3Kernel
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply]
  have hId : (fullBoundaryOutputZeroExtension a c).adjoint ((fullBoundaryOutputZeroExtension a c) u) = u := by
    rw [← ContinuousLinearMap.comp_apply, fullBoundaryOutputZeroExtension_adjoint_comp,
      ContinuousLinearMap.id_apply]
  rw [map_sub, hId]

/-- The insertion defect is bounded uniformly in the window (hence also along any
cutoff sequence) by the norm of the fixed global operator `K_S - id`: both the
zero-extension and its adjoint are contractions. -/
theorem norm_kernelInsertionDefect_le_kernelDifference
    (a c : ℝ) (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    ‖kernelInsertionDefect a c lambda S‖ ≤
      ‖stage3ProjectionKernel lambda S - ContinuousLinearMap.id ℂ cc20GlobalLogCrossingL2‖ := by
  let Z := fullBoundaryOutputZeroExtension a c
  let Kdiff : cc20GlobalLogCrossingL2 →L[ℂ] cc20GlobalLogCrossingL2 :=
    stage3ProjectionKernel lambda S - ContinuousLinearMap.id ℂ cc20GlobalLogCrossingL2
  have hZ : ‖Z‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro u
    simpa only [Z, fullBoundaryOutputZeroExtension, one_mul] using
      (norm_kernelIntervalL2ZeroExtension (-c) (-a) 0 u).le
  have hZadj : ‖Z.adjoint‖ ≤ 1 := by
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact hZ
  calc
    ‖kernelInsertionDefect a c lambda S‖ =
        ‖(fullBoundaryOutputZeroExtension a c).adjoint ∘L Kdiff ∘L fullBoundaryOutputZeroExtension a c‖ := by
      rw [kernelInsertionDefect_eq_compressedKernelDifference]
    _ ≤ ‖Z.adjoint‖ * ‖Kdiff ∘L Z‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖Z.adjoint‖ * (‖Kdiff‖ * ‖Z‖) := by
      exact mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le Kdiff Z) (norm_nonneg _)
    _ ≤ 1 * (‖Kdiff‖ * ‖Z‖) := by
      apply mul_le_mul_of_nonneg_right hZadj
      exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
    _ = ‖Kdiff‖ * ‖Z‖ := one_mul _
    _ ≤ ‖Kdiff‖ * 1 := by
      exact mul_le_mul_of_nonneg_left hZ (norm_nonneg _)
    _ = ‖Kdiff‖ := mul_one _

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

/-! ## The honest `D₁` sufficient condition -/

/-- The root factor on a canonical cutoff is uniformly bounded by the
whole-line convolution norm.  The only cutoff-dependent map in the
factorization is the interval restriction, whose norm is at most one. -/
theorem norm_cutoffFullBoundaryRootFactor_le_globalConvolution
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest) (n : Nat) :
    ‖fullBoundaryRootFactor g (cutoffLower g n) (cutoffUpper g n)‖ ≤
      ‖cc20GlobalLogConvolution g.involution.test‖ := by
  rw [fullBoundaryRootFactor_eq_globalConvolution
    g (cutoffLower g n) (cutoffUpper g n)
    (support_subset_cutoffWindow g n)]
  calc
    ‖globalL2ToKernelInterval (-cutoffUpper g n) (-cutoffLower g n) 0 ∘L
        cc20GlobalLogConvolution g.involution.test‖ ≤
        ‖globalL2ToKernelInterval (-cutoffUpper g n) (-cutoffLower g n) 0‖ *
          ‖cc20GlobalLogConvolution g.involution.test‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * ‖cc20GlobalLogConvolution g.involution.test‖ := by
      exact mul_le_mul_of_nonneg_right
        (norm_globalL2ToKernelInterval_le_one
          (-cutoffUpper g n) (-cutoffLower g n) 0)
        (norm_nonneg _)
    _ = ‖cc20GlobalLogConvolution g.involution.test‖ := one_mul _

/-- If the compressed output defect has norm tending to zero, the root-factor
sandwich defect `D₁,n` tends to zero in operator norm.  The theorem exposes
exactly the missing analytic input: no decay of `Zₙ† Kₙ Zₙ - I` is inferred
from trace-class or positivity alone. -/
theorem tendsto_norm_cutoffKernelInsertionSandwich_zero_of_compressedDefect
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime)
    (hdefect :
      Tendsto
        (fun n => ‖kernelInsertionDefect
          (cutoffLower g n) (cutoffUpper g n) lambda S‖)
        atTop (𝓝 (0 : ℝ))) :
    Tendsto
      (fun n => ‖cutoffKernelInsertionSandwich g lambda S n‖)
      atTop (𝓝 (0 : ℝ)) := by
  let boundValue : ℝ := ‖cc20GlobalLogConvolution g.involution.test‖
  have hbound : ∀ n,
      ‖cutoffKernelInsertionSandwich g lambda S n‖ ≤
        boundValue ^ 2 *
          ‖kernelInsertionDefect
            (cutoffLower g n) (cutoffUpper g n) lambda S‖ := by
    intro n
    calc
      ‖cutoffKernelInsertionSandwich g lambda S n‖ ≤
          ‖fullBoundaryRootFactor g (cutoffLower g n)
            (cutoffUpper g n)‖ ^ 2 *
            ‖kernelInsertionDefect
              (cutoffLower g n) (cutoffUpper g n) lambda S‖ :=
        norm_cutoffKernelInsertionSandwich_le g lambda S n
      _ ≤ boundValue ^ 2 *
          ‖kernelInsertionDefect
            (cutoffLower g n) (cutoffUpper g n) lambda S‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        apply pow_le_pow_left₀ (norm_nonneg _) _ 2
        exact norm_cutoffFullBoundaryRootFactor_le_globalConvolution g n
  have hupper : Tendsto
      (fun n => boundValue ^ 2 *
        ‖kernelInsertionDefect
          (cutoffLower g n) (cutoffUpper g n) lambda S‖)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul hdefect :
        Tendsto
          (fun n => boundValue ^ 2 *
            ‖kernelInsertionDefect
              (cutoffLower g n) (cutoffUpper g n) lambda S‖)
          atTop (𝓝 (boundValue ^ 2 * 0)))
  exact squeeze_zero (fun n => norm_nonneg _) hbound hupper

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

/-! ## Moving-response obstruction

The fixed-response obstruction is not an artifact of holding the response
operator constant.  If a moving response has a uniformly bounded real trace,
it still cannot absorb the canonical window bulk.  Any surviving response
owner must therefore carry an equally divergent trace, which is precisely the
renormalized/finite-part choice left open by the route audit.
-/

noncomputable def cutoffWindowToMovingResponseDefect
    (owner : SelectedWeilSquareOwner)
    (response : Nat → projectionCarrier →L[ℂ] projectionCarrier) (n : Nat) :
    projectionCarrier →L[ℂ] projectionCarrier :=
  windowedBoundaryDetector owner.sourceTest
      (cutoffLower owner.sourceTest n) (cutoffUpper owner.sourceTest n) -
    response n

theorem ordinaryTraceAlong_cutoffWindowToMovingResponseDefect_eq_sub
    (owner : SelectedWeilSquareOwner)
    (response : Nat → projectionCarrier →L[ℂ] projectionCarrier)
    {nu : Type*} (globalBasis : HilbertBasis nu ℂ projectionCarrier)
    (hresponse : ∀ n, IsTraceClassAlong globalBasis (response n)) (n : Nat) :
    ordinaryTraceAlong globalBasis
        (cutoffWindowToMovingResponseDefect owner response n) =
      ordinaryTraceAlong globalBasis
        (windowedBoundaryDetector owner.sourceTest
          (cutoffLower owner.sourceTest n) (cutoffUpper owner.sourceTest n)) -
        ordinaryTraceAlong globalBasis (response n) := by
  unfold cutoffWindowToMovingResponseDefect
  exact ordinaryTraceAlong_sub globalBasis _ _
    (windowedBoundaryDetector_isTraceClassAlong
      owner.sourceTest (cutoffLower owner.sourceTest n)
        (cutoffUpper owner.sourceTest n)
        (cutoffFullBasis owner.sourceTest n)
        (cutoffOutputBasis owner.sourceTest n) globalBasis)
    (hresponse n)

theorem cutoffWindowToMovingResponseDefect_trace_re_cofinal_unbounded_of_sourceTest_ne_zero
    (owner : SelectedWeilSquareOwner)
    (response : Nat → projectionCarrier →L[ℂ] projectionCarrier)
    {nu : Type*} (globalBasis : HilbertBasis nu ℂ projectionCarrier)
    (hresponse : ∀ n, IsTraceClassAlong globalBasis (response n))
    (hresponse_upper : ∃ upperBound : ℝ, ∀ n,
      (ordinaryTraceAlong globalBasis (response n)).re ≤ upperBound)
    (hg : owner.sourceTest.test ≠ 0) :
    ∀ start : Nat, ∀ boundValue : ℝ, ∃ n,
      start ≤ n ∧ boundValue <
        (ordinaryTraceAlong globalBasis
          (cutoffWindowToMovingResponseDefect owner response n)).re := by
  obtain ⟨upperBound, hupper⟩ := hresponse_upper
  intro start boundValue
  obtain ⟨m, hm⟩ :=
    cutoffPositiveBasisData_trace_re_unbounded_of_test_ne_zero
      owner.sourceTest globalBasis hg (boundValue + upperBound)
  let n : Nat := max start m
  have hstart : start ≤ n := le_max_left _ _
  have hmle : m ≤ n := le_max_right _ _
  have hmono := cutoffPositiveBasisData_trace_re_monotone
    owner.sourceTest globalBasis hmle
  have hdetm := cutoffPositiveBasisData_trace_eq_detector
    owner.sourceTest globalBasis m
  have hdetn := cutoffPositiveBasisData_trace_eq_detector
    owner.sourceTest globalBasis n
  have hdetmRe := congrArg Complex.re hdetm
  have hdetnRe := congrArg Complex.re hdetn
  have hdetMono :
      (ordinaryTraceAlong globalBasis
        (windowedBoundaryDetector owner.sourceTest
          (cutoffLower owner.sourceTest m) (cutoffUpper owner.sourceTest m))).re ≤
      (ordinaryTraceAlong globalBasis
        (windowedBoundaryDetector owner.sourceTest
          (cutoffLower owner.sourceTest n) (cutoffUpper owner.sourceTest n))).re := by
    rw [← hdetmRe, ← hdetnRe]
    exact hmono
  have hdetmLarge :
      boundValue + upperBound <
        (ordinaryTraceAlong globalBasis
          (windowedBoundaryDetector owner.sourceTest
            (cutoffLower owner.sourceTest m) (cutoffUpper owner.sourceTest m))).re := by
    calc
      boundValue + upperBound <
          (ordinaryTraceAlong globalBasis
            (cutoffPositiveBasisData owner.sourceTest globalBasis m).positiveComposition).re := hm
      _ = (ordinaryTraceAlong globalBasis
          (windowedBoundaryDetector owner.sourceTest
            (cutoffLower owner.sourceTest m) (cutoffUpper owner.sourceTest m))).re := hdetmRe
  have hdetnLarge :
      boundValue + upperBound <
        (ordinaryTraceAlong globalBasis
          (windowedBoundaryDetector owner.sourceTest
            (cutoffLower owner.sourceTest n) (cutoffUpper owner.sourceTest n))).re :=
    lt_of_lt_of_le hdetmLarge hdetMono
  refine ⟨n, hstart, ?_⟩
  have htrace := ordinaryTraceAlong_cutoffWindowToMovingResponseDefect_eq_sub
    owner response globalBasis hresponse n
  have htraceRe := congrArg Complex.re htrace
  have htraceRe' :
      (ordinaryTraceAlong globalBasis
        (cutoffWindowToMovingResponseDefect owner response n)).re =
        (ordinaryTraceAlong globalBasis
          (windowedBoundaryDetector owner.sourceTest
            (cutoffLower owner.sourceTest n) (cutoffUpper owner.sourceTest n))).re -
          (ordinaryTraceAlong globalBasis (response n)).re := by
    simpa only [Complex.sub_re] using htraceRe
  rw [htraceRe']
  have hresp := hupper n
  linarith

theorem not_tendsto_zero_cutoffWindowToMovingResponseDefect_trace_re_of_sourceTest_ne_zero
    (owner : SelectedWeilSquareOwner)
    (response : Nat → projectionCarrier →L[ℂ] projectionCarrier)
    {nu : Type*} (globalBasis : HilbertBasis nu ℂ projectionCarrier)
    (hresponse : ∀ n, IsTraceClassAlong globalBasis (response n))
    (hresponse_upper : ∃ upperBound : ℝ, ∀ n,
      (ordinaryTraceAlong globalBasis (response n)).re ≤ upperBound)
    (hg : owner.sourceTest.test ≠ 0) :
    ¬ Tendsto
      (fun n =>
        (ordinaryTraceAlong globalBasis
          (cutoffWindowToMovingResponseDefect owner response n)).re)
      atTop (𝓝 (0 : ℝ)) := by
  intro hzero
  have hbounded : ∀ᶠ n : Nat in atTop,
      (ordinaryTraceAlong globalBasis
        (cutoffWindowToMovingResponseDefect owner response n)).re < 1 :=
    hzero.eventually (gt_mem_nhds (by norm_num))
  obtain ⟨N, hN⟩ := eventually_atTop.mp hbounded
  obtain ⟨n, hnN, hn⟩ :=
    cutoffWindowToMovingResponseDefect_trace_re_cofinal_unbounded_of_sourceTest_ne_zero
      owner response globalBasis hresponse hresponse_upper hg N 1
  exact (not_lt_of_ge (le_of_lt (hN n hnN))) hn

end
end C1Stage3ProjectionDefectBounds
end Dev
end Source
end ConnesWeilRH
