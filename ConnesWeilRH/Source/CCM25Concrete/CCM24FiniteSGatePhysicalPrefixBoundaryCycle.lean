/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSGatePhysicalBoundaryCycle
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSGatePhysicalPrefixRootPairing
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSRectangularTailFactorization

/-!
# Common-boundary cycle for the finite physical Gate prefix

Proof 737 exposes each ordered Gate prefix as a finite pairing after the
genuine compact convolution root.  This file inserts the literal source-basis
prefix projection into the existing Hilbert--Schmidt pair data and cycles the
finite prefix onto the common physical boundary carrier.

The resulting middle operator keeps the endpoint and reverse-forward
coordinates inside one subtraction.  No infinite trace cycle, branchwise
trace norm, uniform family estimate, finite-S sign, or RH conclusion is used.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSGatePhysicalPrefixBoundaryCycle

open MeasureTheory
open scoped BigOperators InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open CC20Concrete.PositiveTrace
open CCM24FiniteSActualBandSourceRemainder
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSGatePhysicalBoundaryCycle
open CCM24FiniteSGatePhysicalBoundaryDifference
open CCM24FiniteSGatePhysicalPrefixCompression
open CCM24FiniteSGatePhysicalPrefixRootPairing
open CCM24FiniteSGramResponse
open CCM24FiniteSMovingBandPrefixCompression
open CCM24FiniteSProjectionTrace
open CCM24FiniteSRawCompletedGaugeOwner
open CCM24FiniteSRawRemainderCommonPair
open CCM24FiniteSRectangularTailFactorization
open CCM24SourceProlateTrace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- The finite-rank prefix projection retains exactly the first `N` vectors
of its defining natural Hilbert basis. -/
theorem basisPrefixProjection_apply_basis
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (basis : HilbertBasis ℕ ℂ H) (N i : ℕ) :
    basisPrefixProjection basis N (basis i) =
      if i < N then basis i else 0 := by
  classical
  rw [basisPrefixProjection_apply]
  simp only [orthonormal_iff_ite.mp basis.orthonormal]
  simp only [ite_smul, one_smul, zero_smul]
  let sequence : ℕ → H := fun n => if n = i then basis n else 0
  change (∑ x : Fin N, sequence (x : ℕ)) = _
  rw [Fin.sum_univ_eq_sum_range sequence N]
  dsimp only [sequence]
  by_cases hi : i < N
  · simp [hi]
  · simp [hi]

/-- Right composition by the prefix projection turns the ordinary diagonal
trace into the ordered finite diagonal sum, without a summability premise. -/
theorem ordinaryTraceAlong_comp_basisPrefixProjection_eq_rangeDiagonal
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (basis : HilbertBasis ℕ ℂ H) (N : ℕ)
    (operator : H →L[ℂ] H) :
    ordinaryTraceAlong basis
        (operator ∘L basisPrefixProjection basis N) =
      ∑ i ∈ Finset.range N, ⟪basis i, operator (basis i)⟫_ℂ := by
  rw [ordinaryTraceAlong]
  calc
    (∑' i, ⟪basis i,
        (operator ∘L basisPrefixProjection basis N) (basis i)⟫_ℂ) =
        ∑ i ∈ Finset.range N, ⟪basis i,
          (operator ∘L basisPrefixProjection basis N) (basis i)⟫_ℂ := by
      apply tsum_eq_sum
      intro i hi
      have hi' : ¬ i < N := by
        simpa only [Finset.mem_range] using hi
      rw [ContinuousLinearMap.comp_apply,
        basisPrefixProjection_apply_basis]
      simp only [if_neg hi', map_zero, inner_zero_right]
    _ = ∑ i ∈ Finset.range N, ⟪basis i, operator (basis i)⟫_ℂ := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi' : i < N := Finset.mem_range.mp hi
      rw [ContinuousLinearMap.comp_apply,
        basisPrefixProjection_apply_basis]
      simp only [if_pos hi']

/-- The same finite-support identity stated as the literal `Fin N` matrix
trace used by Proof 735. -/
theorem ordinaryTraceAlong_comp_basisPrefixProjection_eq_prefixMatrixTrace
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (basis : HilbertBasis ℕ ℂ H) (N : ℕ)
    (operator : H →L[ℂ] H) :
    ordinaryTraceAlong basis
        (operator ∘L basisPrefixProjection basis N) =
      Matrix.trace (basisPrefixMatrix basis N operator) := by
  rw [ordinaryTraceAlong_comp_basisPrefixProjection_eq_rangeDiagonal,
    trace_basisPrefixMatrix_eq_rangeDiagonal]

private theorem cyclicProduct_isTraceClassAlong
    {ι κ H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (sourceBasis : HilbertBasis ι ℂ H) (targetBasis : HilbertBasis κ ℂ G)
    (data : BasisHilbertSchmidtPairData (G := G) sourceBasis) :
    IsTraceClassAlong targetBasis (data.right ∘L data.left†) := by
  let cycled : BasisHilbertSchmidtPairData (G := H) targetBasis :=
    { left := data.right†
      right := data.left†
      left_summable_normSq :=
        BasisHilbertSchmidtPairData.summable_adjoint_normSq
          sourceBasis targetBasis data.right data.right_summable_normSq
      right_summable_normSq :=
        BasisHilbertSchmidtPairData.summable_adjoint_normSq
          sourceBasis targetBasis data.left data.left_summable_normSq }
  have hcycled := cycled.traceProduct_isTraceClassAlong
  have hproduct : cycled.traceProduct = data.right ∘L data.left† := by
    dsimp only [cycled, BasisHilbertSchmidtPairData.traceProduct]
    rw [ContinuousLinearMap.adjoint_adjoint]
  rw [hproduct] at hcycled
  exact hcycled

/-- Cycle a difference of two Hilbert--Schmidt trace products after the same
bounded right cutoff, then recombine it on the common target carrier. -/
theorem ordinaryTraceAlong_pairDifference_comp_eq_cycledPrefixDifference
    {ι κ H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (sourceBasis : HilbertBasis ι ℂ H) (targetBasis : HilbertBasis κ ℂ G)
    (first second : BasisHilbertSchmidtPairData (G := G) sourceBasis)
    (cutoff : H →L[ℂ] H) :
    ordinaryTraceAlong sourceBasis
        ((first.traceProduct - second.traceProduct) ∘L cutoff) =
      ordinaryTraceAlong targetBasis
        ((first.right ∘L cutoff ∘L first.left†) -
          (second.right ∘L cutoff ∘L second.left†)) := by
  let firstPrefix := first.boundedPrecomp targetBasis sourceBasis
    (ContinuousLinearMap.id ℂ H) cutoff
  let secondPrefix := second.boundedPrecomp targetBasis sourceBasis
    (ContinuousLinearMap.id ℂ H) cutoff
  have hfirstSource : firstPrefix.traceProduct =
      first.traceProduct ∘L cutoff := by
    dsimp only [firstPrefix]
    rw [BasisHilbertSchmidtPairData.boundedPrecomp_traceProduct_eq,
      ContinuousLinearMap.adjoint_id]
    apply ContinuousLinearMap.ext
    intro x
    rfl
  have hsecondSource : secondPrefix.traceProduct =
      second.traceProduct ∘L cutoff := by
    dsimp only [secondPrefix]
    rw [BasisHilbertSchmidtPairData.boundedPrecomp_traceProduct_eq,
      ContinuousLinearMap.adjoint_id]
    apply ContinuousLinearMap.ext
    intro x
    rfl
  have hsource :
      (first.traceProduct - second.traceProduct) ∘L cutoff =
        firstPrefix.traceProduct - secondPrefix.traceProduct := by
    rw [hfirstSource, hsecondSource]
    apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.sub_apply]
  have hfirstTarget : firstPrefix.right ∘L firstPrefix.left† =
      first.right ∘L cutoff ∘L first.left† := by
    dsimp only [firstPrefix, BasisHilbertSchmidtPairData.boundedPrecomp]
    rw [ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_id]
    apply ContinuousLinearMap.ext
    intro x
    rfl
  have hsecondTarget : secondPrefix.right ∘L secondPrefix.left† =
      second.right ∘L cutoff ∘L second.left† := by
    dsimp only [secondPrefix, BasisHilbertSchmidtPairData.boundedPrecomp]
    rw [ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_id]
    apply ContinuousLinearMap.ext
    intro x
    rfl
  have hfirstBoundary :=
    cyclicProduct_isTraceClassAlong sourceBasis targetBasis firstPrefix
  have hsecondBoundary :=
    cyclicProduct_isTraceClassAlong sourceBasis targetBasis secondPrefix
  calc
    ordinaryTraceAlong sourceBasis
        ((first.traceProduct - second.traceProduct) ∘L cutoff) =
        ordinaryTraceAlong sourceBasis
          (firstPrefix.traceProduct - secondPrefix.traceProduct) :=
      congrArg (ordinaryTraceAlong sourceBasis) hsource
    _ = ordinaryTraceAlong sourceBasis firstPrefix.traceProduct -
        ordinaryTraceAlong sourceBasis secondPrefix.traceProduct :=
      ordinaryTraceAlong_sub sourceBasis _ _
        firstPrefix.traceProduct_isTraceClassAlong
        secondPrefix.traceProduct_isTraceClassAlong
    _ = ordinaryTraceAlong targetBasis
          (firstPrefix.right ∘L firstPrefix.left†) -
        ordinaryTraceAlong targetBasis
          (secondPrefix.right ∘L secondPrefix.left†) :=
      congrArg₂ (fun left right : ℂ => left - right)
        (firstPrefix.ordinaryTraceAlong_traceProduct_eq_cyclic targetBasis)
        (secondPrefix.ordinaryTraceAlong_traceProduct_eq_cyclic targetBasis)
    _ = ordinaryTraceAlong targetBasis
          ((firstPrefix.right ∘L firstPrefix.left†) -
            (secondPrefix.right ∘L secondPrefix.left†)) :=
      (ordinaryTraceAlong_sub targetBasis _ _ hfirstBoundary
        hsecondBoundary).symm
    _ = ordinaryTraceAlong targetBasis
          ((first.right ∘L cutoff ∘L first.left†) -
            (second.right ∘L cutoff ∘L second.left†)) := by
      rw [hfirstTarget, hsecondTarget]

private theorem pairCycledPrefixDifference_factor
    {ι κ H K G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {baseBasis : HilbertBasis ι ℂ H}
    {sourceBasis : HilbertBasis κ ℂ K}
    (base : BasisHilbertSchmidtPairData (G := G) baseBasis)
    (first second : BasisHilbertSchmidtPairData (G := G) sourceBasis)
    (endpoint inclusion forward : K →L[ℂ] H) (cutoff : K →L[ℂ] K)
    (hfirstLeft : first.left = base.left ∘L inclusion)
    (hfirstRight : first.right = base.right ∘L endpoint)
    (hsecondLeft : second.left = base.left ∘L forward)
    (hsecondRight : second.right = base.right ∘L inclusion) :
    (first.right ∘L cutoff ∘L first.left†) -
        (second.right ∘L cutoff ∘L second.left†) =
      base.right ∘L
        (endpoint ∘L cutoff ∘L inclusion† -
          inclusion ∘L cutoff ∘L forward†) ∘L base.left† := by
  rw [hfirstLeft, hfirstRight, hsecondLeft, hsecondRight,
    ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_comp]
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, map_sub]

private theorem cycledSandwich_isTraceClassAlong
    {ι κ H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (sourceBasis : HilbertBasis ι ℂ H) (targetBasis : HilbertBasis κ ℂ G)
    (data : BasisHilbertSchmidtPairData (G := G) sourceBasis)
    (middle : H →L[ℂ] H) :
    IsTraceClassAlong targetBasis
      (data.right ∘L middle ∘L data.left†) := by
  let cycled : BasisHilbertSchmidtPairData (G := H) targetBasis :=
    { left := data.right†
      right := middle ∘L data.left†
      left_summable_normSq :=
        BasisHilbertSchmidtPairData.summable_adjoint_normSq
          sourceBasis targetBasis data.right data.right_summable_normSq
      right_summable_normSq :=
        summable_normSq_postcomp targetBasis (data.left†) middle
          (BasisHilbertSchmidtPairData.summable_adjoint_normSq
            sourceBasis targetBasis data.left data.left_summable_normSq) }
  have hcycled := cycled.traceProduct_isTraceClassAlong
  have hproduct : cycled.traceProduct =
      data.right ∘L middle ∘L data.left† := by
    dsimp only [cycled, BasisHilbertSchmidtPairData.traceProduct]
    rw [ContinuousLinearMap.adjoint_adjoint]
  rw [hproduct] at hcycled
  exact hcycled

/-- The complete ambient coframe difference with the finite source prefix
inserted before both source adjoint legs. -/
noncomputable def sourceGatePhysicalPrefixCoframeDifference
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (sourceBasis : HilbertBasis ℕ ℂ (sourceSoninCarrier lambda))
    (N : ℕ) : finiteSCarrier →L[ℂ] finiteSCarrier :=
  sourceActualBandForwardEndpointCoframe lambda family ∘L
      basisPrefixProjection sourceBasis N ∘L (sourceInclusion lambda)† -
    sourceInclusion lambda ∘L basisPrefixProjection sourceBasis N ∘L
      (sourceActualBandForwardCoframe lambda family)†

/-- The finite Gate prefix after both legal Hilbert--Schmidt cycles have been
recombined on the one common physical boundary carrier. -/
noncomputable def sourceGatePhysicalPrefixBoundaryCycleResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ιr κr τr ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis ιr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis κr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis τr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ℕ ℂ (sourceSoninCarrier lambda))
    (N : ℕ)
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    commonBoundaryCarrier a c →L[ℂ] commonBoundaryCarrier a c :=
  let base := sourceThreeBranchPairData owner lambda a c hac hsupp
    negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor
  base.right ∘L
    sourceGatePhysicalPrefixCoframeDifference lambda family sourceBasis N ∘L
      base.left†

/-- The finite boundary-side cycle is trace legal in the same common boundary
basis, for every fixed prefix length. -/
theorem sourceGatePhysicalPrefixBoundaryCycleResponse_isTraceClassAlong
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ιr κr τr ν μ : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis ιr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis κr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis τr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis μ ℂ (commonBoundaryCarrier a c))
    (sourceBasis : HilbertBasis ℕ ℂ (sourceSoninCarrier lambda))
    (N : ℕ)
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    IsTraceClassAlong boundaryBasis
      (sourceGatePhysicalPrefixBoundaryCycleResponse
        owner lambda family a c hac hsupp negativeBasis positiveBasis
        outputBasis reflectedNegativeBasis reflectedPositiveBasis
        reflectedOutputBasis globalBasis sourceBasis N hfactor) := by
  let base := sourceThreeBranchPairData owner lambda a c hac hsupp
    negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor
  change IsTraceClassAlong boundaryBasis
    (base.right ∘L
      sourceGatePhysicalPrefixCoframeDifference
        lambda family sourceBasis N ∘L base.left†)
  exact cycledSandwich_isTraceClassAlong globalBasis boundaryBasis base
    (sourceGatePhysicalPrefixCoframeDifference
      lambda family sourceBasis N)

/-- The literal finite Gate compression trace is exactly the ordinary trace
of the recombined finite-prefix owner on the common boundary carrier. -/
theorem sourceGatePhysicalPrefixCompressionTrace_eq_boundaryCycle
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ιr κr τr ν μ : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis ιr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis κr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis τr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis μ ℂ (commonBoundaryCarrier a c))
    (sourceBasis : HilbertBasis ℕ ℂ (sourceSoninCarrier lambda))
    (N : ℕ)
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    sourceGatePhysicalPrefixCompressionTrace
        owner lambda family sourceBasis N =
      ordinaryTraceAlong boundaryBasis
        (sourceGatePhysicalPrefixBoundaryCycleResponse
          owner lambda family a c hac hsupp negativeBasis positiveBasis
          outputBasis reflectedNegativeBasis reflectedPositiveBasis
          reflectedOutputBasis globalBasis sourceBasis N hfactor) := by
  let cutoff := basisPrefixProjection sourceBasis N
  let first := sourceActualBandForwardEndpointPairData owner lambda family
    a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis sourceBasis hfactor
  let second := sourceActualBandReverseForwardPairData owner lambda family
    a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis sourceBasis hfactor
  let base := sourceThreeBranchPairData owner lambda a c hac hsupp
    negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor
  have hprefix :
      sourceGatePhysicalPrefixCompressionTrace
          owner lambda family sourceBasis N =
        ordinaryTraceAlong sourceBasis
          (lowerFactorGaugedActualBandCompletedRelativeResponse
            owner lambda family ∘L cutoff) := by
    rw [sourceGatePhysicalPrefixCompressionTrace]
    dsimp only [cutoff]
    exact
      (ordinaryTraceAlong_comp_basisPrefixProjection_eq_prefixMatrixTrace
        sourceBasis N
          (lowerFactorGaugedActualBandCompletedRelativeResponse
            owner lambda family)).symm
  have hgate :
      lowerFactorGaugedActualBandCompletedRelativeResponse
          owner lambda family =
        first.traceProduct - second.traceProduct := by
    dsimp only [first, second]
    rw [sourceActualBandForwardEndpointPairData_traceProduct_eq
        owner lambda family a c hac hsupp negativeBasis positiveBasis
        outputBasis reflectedNegativeBasis reflectedPositiveBasis
        reflectedOutputBasis globalBasis boundaryBasis sourceBasis hfactor,
      sourceActualBandReverseForwardPairData_traceProduct_eq
        owner lambda family a c hac hsupp negativeBasis positiveBasis
        outputBasis reflectedNegativeBasis reflectedPositiveBasis
        reflectedOutputBasis globalBasis boundaryBasis sourceBasis hfactor]
    exact lowerFactorGaugedResponse_eq_completePhysicalBoundaryDifference
      owner lambda family
  have hfirstLeft : first.left = base.left ∘L sourceInclusion lambda := by
    dsimp only [first, sourceActualBandForwardEndpointPairData, base]
    exact boundedPrecompAddRight_left_eq boundaryBasis sourceBasis _ _ _ _
  have hfirstRight : first.right =
      base.right ∘L
        sourceActualBandForwardEndpointCoframe lambda family := by
    dsimp only [first, sourceActualBandForwardEndpointPairData, base]
    rw [boundedPrecompAddRight_right_eq]
    rfl
  have hsecondLeft : second.left =
      base.left ∘L sourceActualBandForwardCoframe lambda family := by
    rfl
  have hsecondRight : second.right =
      base.right ∘L sourceInclusion lambda := by
    rfl
  have hboundaryOperator :
      (first.right ∘L cutoff ∘L first.left†) -
          (second.right ∘L cutoff ∘L second.left†) =
        base.right ∘L
          sourceGatePhysicalPrefixCoframeDifference
            lambda family sourceBasis N ∘L base.left† := by
    rw [sourceGatePhysicalPrefixCoframeDifference]
    exact pairCycledPrefixDifference_factor base first second
      (sourceActualBandForwardEndpointCoframe lambda family)
      (sourceInclusion lambda) (sourceActualBandForwardCoframe lambda family)
      cutoff hfirstLeft hfirstRight hsecondLeft hsecondRight
  calc
    sourceGatePhysicalPrefixCompressionTrace
        owner lambda family sourceBasis N =
        ordinaryTraceAlong sourceBasis
          (lowerFactorGaugedActualBandCompletedRelativeResponse
            owner lambda family ∘L cutoff) := hprefix
    _ = ordinaryTraceAlong sourceBasis
          ((first.traceProduct - second.traceProduct) ∘L cutoff) :=
      congrArg
        (fun operator => ordinaryTraceAlong sourceBasis (operator ∘L cutoff))
        hgate
    _ = ordinaryTraceAlong boundaryBasis
          ((first.right ∘L cutoff ∘L first.left†) -
            (second.right ∘L cutoff ∘L second.left†)) :=
      ordinaryTraceAlong_pairDifference_comp_eq_cycledPrefixDifference
        sourceBasis boundaryBasis first second cutoff
    _ = ordinaryTraceAlong boundaryBasis
          (base.right ∘L
            sourceGatePhysicalPrefixCoframeDifference
              lambda family sourceBasis N ∘L base.left†) :=
      congrArg (ordinaryTraceAlong boundaryBasis) hboundaryOperator
    _ = ordinaryTraceAlong boundaryBasis
          (sourceGatePhysicalPrefixBoundaryCycleResponse
            owner lambda family a c hac hsupp negativeBasis positiveBasis
            outputBasis reflectedNegativeBasis reflectedPositiveBasis
            reflectedOutputBasis globalBasis sourceBasis N hfactor) := by
      rfl

/-- Proof 737's genuine compact-root finite pairing is the same finite
common-boundary trace. -/
theorem sourceGatePhysicalPrefixRootPairing_eq_boundaryCycle
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ιr κr τr ν μ : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis ιr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis κr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis τr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis μ ℂ (commonBoundaryCarrier a c))
    (sourceBasis : HilbertBasis ℕ ℂ (sourceSoninCarrier lambda))
    (N : ℕ)
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    sourceGatePhysicalPrefixRootPairing
        owner lambda family sourceBasis N =
      ordinaryTraceAlong boundaryBasis
        (sourceGatePhysicalPrefixBoundaryCycleResponse
          owner lambda family a c hac hsupp negativeBasis positiveBasis
          outputBasis reflectedNegativeBasis reflectedPositiveBasis
          reflectedOutputBasis globalBasis sourceBasis N hfactor) := by
  rw [← sourceGatePhysicalPrefixCompressionTrace_eq_rootPairing]
  exact sourceGatePhysicalPrefixCompressionTrace_eq_boundaryCycle
    owner lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis sourceBasis N hfactor

/-- A bound for every finite common-boundary prefix controls the ordinary Gate
trace after the existing fixed-family pair data discharges trace legality. -/
theorem lowerFactorGaugedResponse_trace_norm_le_of_pairData_prefixBoundaryCycleBound
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ιr κr τr ν μ σ : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis ιr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis κr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis τr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis μ ℂ (commonBoundaryCarrier a c))
    (pairedBoundaryBasis : HilbertBasis σ ℂ (actualBandPairCarrier a c))
    (sourceBasis : HilbertBasis ℕ ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    (bound : ℝ)
    (hbound : ∀ N : ℕ,
      ‖ordinaryTraceAlong boundaryBasis
        (sourceGatePhysicalPrefixBoundaryCycleResponse
          owner lambda family a c hac hsupp negativeBasis positiveBasis
          outputBasis reflectedNegativeBasis reflectedPositiveBasis
          reflectedOutputBasis globalBasis sourceBasis N hfactor)‖ ≤ bound) :
    ‖ordinaryTraceAlong sourceBasis
      (lowerFactorGaugedActualBandCompletedRelativeResponse
        owner lambda family)‖ ≤ bound := by
  apply
    lowerFactorGaugedResponse_trace_norm_le_of_pairData_prefixRootPairingBound
      owner lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis pairedBoundaryBasis sourceBasis hfactor bound
  intro N
  rw [sourceGatePhysicalPrefixRootPairing_eq_boundaryCycle
    owner lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis sourceBasis N hfactor]
  exact hbound N

end CCM24FiniteSGatePhysicalPrefixBoundaryCycle
end CCM25Concrete
end Source
end ConnesWeilRH
