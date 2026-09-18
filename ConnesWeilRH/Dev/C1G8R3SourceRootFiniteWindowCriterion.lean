/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3FiniteWindowEnergyCriterion
import ConnesWeilRH.Dev.C1G8R3SourceCompressedRootKernel
import ConnesWeilRH.Dev.C1G8R3CompactRootWindowEnergy

/-!
# Finite-window criterion specialized to the source-compressed root

The finite approximation is the literal operator
`J† ∘L P_n ∘L C ∘L J`; it is not obtained by applying an output window to
the already compressed operator.  This distinction is essential because the
source projection need not commute with the expanding output projection.
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

noncomputable local instance sourceRootFiniteWindowCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

noncomputable def sourceCompressedRootFiniteWindow
    (owner : SelectedWeilSquareOwner) (lambda : CCM24SoninScale) (n : ℕ) :
    sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
  (sourceInclusion lambda).adjoint ∘L
    kernelIntervalProjection (-(n : ℝ)) (n : ℝ) 0 ∘L
    rootConvolution owner ∘L sourceInclusion lambda

noncomputable def sourceCompressedRootAnnularWindow
    (owner : SelectedWeilSquareOwner) (lambda : CCM24SoninScale)
    (N n : ℕ) : sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
  (sourceInclusion lambda).adjoint ∘L
    (kernelIntervalProjection (-(n : ℝ)) (n : ℝ) 0 -
      kernelIntervalProjection (-(N : ℝ)) (N : ℝ) 0) ∘L
    rootConvolution owner ∘L sourceInclusion lambda

theorem sourceCompressedRootFiniteWindow_sub_eq_annularWindow
    (owner : SelectedWeilSquareOwner) (lambda : CCM24SoninScale)
    (N n : ℕ) :
    sourceCompressedRootFiniteWindow owner lambda n -
        sourceCompressedRootFiniteWindow owner lambda N =
      sourceCompressedRootAnnularWindow owner lambda N n := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [sourceCompressedRootFiniteWindow,
    sourceCompressedRootAnnularWindow, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.comp_apply]
  exact ((sourceInclusion lambda).adjoint.map_sub _ _).symm

set_option maxHeartbeats 1000000 in
theorem sourceCompressedRootFiniteWindow_sourceBasis_normSq_summable
    (owner : SelectedWeilSquareOwner) (lambda : CCM24SoninScale)
    (n : ℕ) (hn : selectedRootSupportRadius owner ≤ (n : ℝ))
    {ι : Type*}
    (sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda)) :
    Summable fun i =>
      ‖sourceCompressedRootFiniteWindow owner lambda n (sourceBasis i)‖ ^ 2 := by
  obtain ⟨κ, inputBasis, _⟩ :=
    exists_hilbertBasis (𝕜 := ℂ)
      (E := Lp ℂ 2 (volume : Measure
        (BoundaryFullInputInterval (-(n : ℝ)) (n : ℝ))))
  obtain ⟨τ, outputBasis, _⟩ :=
    exists_hilbertBasis (𝕜 := ℂ)
      (E := Lp ℂ 2 (volume : Measure
        (BoundaryOutputInterval (-(n : ℝ)) (n : ℝ))))
  let F := fullBoundaryRootFactor owner.sourceTest (-(n : ℝ)) (n : ℝ)
  let FJ := F ∘L sourceInclusion lambda
  have hsupp : Function.support owner.sourceTest.test ⊆
      Set.Icc (-(n : ℝ)) (n : ℝ) := by
    intro x hx
    have hroot := selectedRoot_sourceTest_support_subset owner hx
    constructor <;> linarith [hn, hroot.1, hroot.2]
  have hF : Summable fun i =>
      ‖F (sourceInclusion lambda (sourceBasis i))‖ ^ 2 := by
    exact selectedRoot_fullWindowFactor_sourceBasis_normSq_summable
      owner lambda (-(n : ℝ)) (n : ℝ) inputBasis outputBasis sourceBasis
  have hFJ : Summable fun i => ‖FJ (sourceBasis i)‖ ^ 2 := by
    simpa only [FJ, ContinuousLinearMap.comp_apply] using hF
  let Z := kernelIntervalL2ZeroExtension (-(n : ℝ))
    (-(-(n : ℝ))) 0
  have hZF : Summable fun i =>
      ‖Z (FJ (sourceBasis i))‖ ^ 2 := by
    exact PositiveTrace.summable_normSq_postcomp sourceBasis FJ Z hFJ
  have hZFp : Summable fun i =>
      ‖(sourceInclusion lambda).adjoint
        (Z (FJ (sourceBasis i)))‖ ^ 2 := by
    exact PositiveTrace.summable_normSq_postcomp sourceBasis (Z ∘L FJ)
      (sourceInclusion lambda).adjoint hZF
  refine hZFp.congr (fun i => ?_)
  have hfactor : Z ∘L FJ =
      kernelIntervalProjection (-(n : ℝ)) (-(-(n : ℝ))) 0 ∘L
        rootConvolution owner ∘L sourceInclusion lambda := by
    dsimp [Z, FJ, F, rootConvolution]
    rw [fullBoundaryRootFactor_eq_globalConvolution owner.sourceTest
      (-(n : ℝ)) (n : ℝ) hsupp]
    unfold kernelIntervalProjection
    simp only [kernelIntervalL2ZeroExtension_eq_adjoint_globalL2ToKernelInterval,
      ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.comp_assoc]
  have hi : (Z ∘L FJ) (sourceBasis i) =
      (kernelIntervalProjection (-(n : ℝ)) (-(-(n : ℝ))) 0 ∘L
        rootConvolution owner ∘L sourceInclusion lambda) (sourceBasis i) :=
    congrArg (fun A : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier =>
      A (sourceBasis i)) hfactor
  have hi' := congrArg (fun z : finiteSCarrier =>
      (sourceInclusion lambda).adjoint z) hi
  simpa only [sourceCompressedRootFiniteWindow, neg_neg,
    ContinuousLinearMap.comp_apply] using congrArg (fun z : sourceSoninCarrier lambda =>
    ‖z‖ ^ 2) hi'

theorem sourceCompressedRootAnnularWindow_sourceBasis_normSq_summable
    (owner : SelectedWeilSquareOwner) (lambda : CCM24SoninScale)
    (N n : ℕ) (hN : selectedRootSupportRadius owner ≤ (N : ℝ))
    (hn : selectedRootSupportRadius owner ≤ (n : ℝ))
    {ι : Type*}
    (sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda)) :
    Summable fun i =>
      ‖sourceCompressedRootAnnularWindow owner lambda N n
        (sourceBasis i)‖ ^ 2 := by
  have hN' := sourceCompressedRootFiniteWindow_sourceBasis_normSq_summable
    owner lambda N hN sourceBasis
  have hn' := sourceCompressedRootFiniteWindow_sourceBasis_normSq_summable
    owner lambda n hn sourceBasis
  have hneg : Summable fun i =>
      ‖(-sourceCompressedRootFiniteWindow owner lambda N)
        (sourceBasis i)‖ ^ 2 := by
    simpa only [ContinuousLinearMap.neg_apply, norm_neg] using hN'
  have hsum := PositiveTrace.summable_normSq_add sourceBasis
    (sourceCompressedRootFiniteWindow owner lambda n)
    (-sourceCompressedRootFiniteWindow owner lambda N) hn' hneg
  refine hsum.congr (fun i => ?_)
  have hi := congrArg (fun T : sourceSoninCarrier lambda →L[ℂ]
      sourceSoninCarrier lambda => T (sourceBasis i))
    (sourceCompressedRootFiniteWindow_sub_eq_annularWindow owner lambda N n)
  simpa only [ContinuousLinearMap.add_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.sub_apply, sub_eq_add_neg,
    sourceCompressedRootAnnularWindow] using
    congrArg (fun z : sourceSoninCarrier lambda => ‖z‖ ^ 2) hi

theorem sourceCompressedRoot_squareSum_of_uniform_finite_window_energy
    (owner : SelectedWeilSquareOwner) (lambda : CCM24SoninScale)
    {ι : Type*}
    (sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda))
    {B : ℝ}
    (hbound : ∀ n (s : Finset ι),
      ∑ i ∈ s, ‖sourceCompressedRootFiniteWindow owner lambda n
        (sourceBasis i)‖ ^ 2 ≤ B) :
    Summable fun i => ‖sourceCompressedRoot owner lambda (sourceBasis i)‖ ^ 2 := by
  apply summable_normSq_of_uniform_finite_window_energy sourceBasis
    (sourceCompressedRoot owner lambda)
    (sourceCompressedRootFiniteWindow owner lambda)
  · intro u
    have hproj := tendsto_kernelIntervalProjection_symmetric_apply
      (rootConvolution owner (sourceInclusion lambda u))
    have hpost := ((sourceInclusion lambda).adjoint.continuous.tendsto _).comp hproj
    simpa only [sourceCompressedRootFiniteWindow, sourceCompressedRoot,
      ContinuousLinearMap.comp_apply] using hpost
  · exact hbound

theorem sourceCompressedRoot_squareSum_of_eventual_uniform_finite_window_energy
    (owner : SelectedWeilSquareOwner) (lambda : CCM24SoninScale)
    {ι : Type*}
    (sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda))
    {B : ℝ} (N : ℕ)
    (hbound : ∀ n, N ≤ n → ∀ s : Finset ι,
      ∑ i ∈ s, ‖sourceCompressedRootFiniteWindow owner lambda n
        (sourceBasis i)‖ ^ 2 ≤ B) :
    Summable fun i => ‖sourceCompressedRoot owner lambda (sourceBasis i)‖ ^ 2 := by
  refine summable_normSq_of_eventual_uniform_finite_window_energy
    (B := B) sourceBasis (sourceCompressedRoot owner lambda)
    (sourceCompressedRootFiniteWindow owner lambda) ?_ N hbound
  · intro u
    have hproj := tendsto_kernelIntervalProjection_symmetric_apply
      (rootConvolution owner (sourceInclusion lambda u))
    have hpost := ((sourceInclusion lambda).adjoint.continuous.tendsto _).comp hproj
    simpa only [sourceCompressedRootFiniteWindow, sourceCompressedRoot,
      ContinuousLinearMap.comp_apply] using hpost

theorem sourceCompressedRoot_squareSum_of_eventual_annular_energy
    (owner : SelectedWeilSquareOwner) (lambda : CCM24SoninScale)
    {ι : Type*}
    (sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda))
    (N : ℕ) (hN : selectedRootSupportRadius owner ≤ (N : ℝ))
    {B : ℝ}
    (hannular : ∀ n, N ≤ n → ∀ s : Finset ι,
      ∑ i ∈ s, ‖sourceCompressedRootAnnularWindow owner lambda N n
        (sourceBasis i)‖ ^ 2 ≤ B) :
    Summable fun i => ‖sourceCompressedRoot owner lambda (sourceBasis i)‖ ^ 2 := by
  let head := sourceCompressedRootFiniteWindow owner lambda N
  let tail := fun n : ℕ =>
    sourceCompressedRootFiniteWindow owner lambda n - head
  have hhead : Summable fun i => ‖head (sourceBasis i)‖ ^ 2 := by
    simpa only [head] using
      sourceCompressedRootFiniteWindow_sourceBasis_normSq_summable
        owner lambda N hN sourceBasis
  have htail : ∀ n, N ≤ n → ∀ s : Finset ι,
      ∑ i ∈ s, ‖tail n (sourceBasis i)‖ ^ 2 ≤ B := by
    intro n hn s
    have h := hannular n hn s
    rw [← sourceCompressedRootFiniteWindow_sub_eq_annularWindow
      owner lambda N n] at h
    simpa only [tail, head] using h
  have hwindow := eventual_uniform_finite_window_energy_of_fixed_plus_tail
    sourceBasis head tail hhead N htail
  have hsum : ∀ n, N ≤ n → ∀ s : Finset ι,
      ∑ i ∈ s, ‖sourceCompressedRootFiniteWindow owner lambda n
        (sourceBasis i)‖ ^ 2 ≤
        2 * ((∑' i, ‖head (sourceBasis i)‖ ^ 2) + B) := by
    intro n hn s
    have hop : head + tail n =
        sourceCompressedRootFiniteWindow owner lambda n := by
      apply ContinuousLinearMap.ext
      intro u
      simp only [head, tail, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.sub_apply]
      abel
    have h := hwindow n hn s
    rw [hop] at h
    exact h
  refine sourceCompressedRoot_squareSum_of_eventual_uniform_finite_window_energy
    owner lambda sourceBasis N hsum

theorem sourceCompressedRoot_squareSum_of_eventual_annular_tsum_energy
    (owner : SelectedWeilSquareOwner) (lambda : CCM24SoninScale)
    {ι : Type*}
    (sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda))
    (N : ℕ) (hN : selectedRootSupportRadius owner ≤ (N : ℝ))
    {B : ℝ}
    (hannular : ∀ n, N ≤ n →
      ∑' i, ‖sourceCompressedRootAnnularWindow owner lambda N n
        (sourceBasis i)‖ ^ 2 ≤ B) :
    Summable fun i => ‖sourceCompressedRoot owner lambda
      (sourceBasis i)‖ ^ 2 := by
  apply sourceCompressedRoot_squareSum_of_eventual_annular_energy
    owner lambda sourceBasis N hN
  intro n hn s
  have hsummable := sourceCompressedRootAnnularWindow_sourceBasis_normSq_summable
    owner lambda N n hN (le_trans hN (Nat.cast_le.mpr hn)) sourceBasis
  have hle := hsummable.sum_le_tsum s (fun i _ => sq_nonneg _)
  exact hle.trans (hannular n hn)
end Dev
end ConnesWeilRH
