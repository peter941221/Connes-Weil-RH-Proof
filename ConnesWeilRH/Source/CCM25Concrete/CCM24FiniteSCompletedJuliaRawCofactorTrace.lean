/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawLocalCofactor

/-!
# Trace transfer through the raw local cofactor

Proof 556 gives an exact cofactor identity for the raw adjacent row.  This
module feeds the existing Hilbert--Schmidt owner of the local raw defect
through the bounded transition and then solves the nonzero scalar cofactor.

The result is a fixed-suffix trace-class transfer.  It is deliberately not a
uniform estimate: no family-independent bound is inferred from trace-class
legality.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedJuliaRawCofactorTrace

open scoped ComplexConjugate InnerProduct InnerProductSpace

open MeasureTheory
open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open CC20Concrete.PositiveTrace
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSGramResponse
open CCM24FiniteSProjectionTrace
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSCompletedJuliaRawPhysicalFactorization
open CCM24FiniteSCompletedJuliaRawLocalCofactor
open CCM24FiniteSRawLocalTraceFactorization
open CCM24FiniteSRawCompletedSchurCocycle
open CCM24SourceProlateTrace
open CCM24FiniteSSchurMarkovPairing

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace
      (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

noncomputable local instance commonBoundaryTwoCopyTopologicalSpace
    (a c : ℝ) : TopologicalSpace
      (WithLp 2
        (WithLp 2 (commonBoundaryCarrier a c × commonBoundaryCarrier a c) ×
          WithLp 2 (commonBoundaryCarrier a c × commonBoundaryCarrier a c))) :=
  WithLp.instProdTopologicalSpace 2 _ _

private noncomputable def chooseTraceTargetHilbertBasisIndex
    (G : Type*) [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G] : Set G :=
  Classical.choose (exists_hilbertBasis ℂ G)

private noncomputable def chooseTraceTargetHilbertBasis
    (G : Type*) [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G] : HilbertBasis (chooseTraceTargetHilbertBasisIndex G) ℂ G :=
  Classical.choose (Classical.choose_spec (exists_hilbertBasis ℂ G))

/-! ## Fixed-suffix row trace legality -/

theorem suffixActualBandRawPhysicalFourTermRow_isTraceClassAlong_of_localPairOwner
    {ι κ G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime)
    (sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda))
    (targetBasis : HilbertBasis κ ℂ G)
    (data : BasisHilbertSchmidtPairData (G := G) sourceBasis)
    (hdata : data.traceProduct =
      suffixActualBandLocalRawDefect owner lambda p S) :
    IsTraceClassAlong sourceBasis
      (suffixActualBandRawPhysicalFourTermRow owner lambda p S) := by
  have hcofactor := data.boundedSandwich_isTraceClassAlong targetBasis
    (ContinuousLinearMap.id ℂ (sourceSoninCarrier lambda))
    (suffixEulerFrameTransition lambda p S)
  have hcofactor' : IsTraceClassAlong sourceBasis
      (suffixActualBandLocalRawDefect owner lambda p S ∘L
        suffixEulerFrameTransition lambda p S) := by
    rw [← hdata]
    simpa only [ContinuousLinearMap.id_comp] using hcofactor
  have hscalar : (primeSchurMarkovScalar p : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr
      (ne_of_gt (primeSchurMarkovScalar_pos p))
  have hrowAdjEq :
      (suffixActualBandRawPhysicalFourTermRow owner lambda p S)† =
        (-(primeSchurMarkovScalar p : ℂ)⁻¹) •
          (suffixActualBandLocalRawDefect owner lambda p S ∘L
            suffixEulerFrameTransition lambda p S) := by
    apply ContinuousLinearMap.ext
    intro x
    have hcofactorPoint := congrArg
      (fun operator : sourceSoninCarrier lambda →L[ℂ]
          sourceSoninCarrier lambda => operator x)
      (suffixActualBandLocalRawDefect_comp_transition_eq_neg_scalar_rawPhysicalRow_adjoint
        owner lambda p S)
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply]
      at hcofactorPoint
    calc
      (ContinuousLinearMap.adjoint
          (suffixActualBandRawPhysicalFourTermRow owner lambda p S)) x =
          (-((primeSchurMarkovScalar p : ℂ)⁻¹)) •
            (-((primeSchurMarkovScalar p : ℂ) •
              (ContinuousLinearMap.adjoint
                (suffixActualBandRawPhysicalFourTermRow owner lambda p S)) x)) := by
        simp only [smul_neg, neg_smul, neg_neg]
        rw [smul_smul]
        simp [hscalar]
      _ = (-((primeSchurMarkovScalar p : ℂ)⁻¹)) •
          (suffixActualBandLocalRawDefect owner lambda p S)
            (suffixEulerFrameTransition lambda p S x) := by
        rw [hcofactorPoint]
  have hrowAdj : IsTraceClassAlong sourceBasis
      (ContinuousLinearMap.adjoint
        (suffixActualBandRawPhysicalFourTermRow owner lambda p S)) := by
    rw [hrowAdjEq]
    exact isTraceClassAlong_smul sourceBasis _ _ hcofactor'
  exact by
      simpa only [ContinuousLinearMap.adjoint_adjoint] using
      isTraceClassAlong_adjoint sourceBasis
        (ContinuousLinearMap.adjoint
          (suffixActualBandRawPhysicalFourTermRow owner lambda p S)) hrowAdj

/-! ## The actual finite-window owner -/

theorem suffixActualBandRawPhysicalFourTermRow_isTraceClassAlong
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {iota kappa tau iotaR kappaR tauR nu mu rho sigma : Type*}
    (negativeBasis : HilbertBasis iota ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis kappa ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis tau ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis iotaR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis kappaR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis tauR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis mu ℂ (commonBoundaryCarrier a c))
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (pairedBoundaryBasis : HilbertBasis sigma ℂ
      (WithLp 2 (commonBoundaryCarrier a c × commonBoundaryCarrier a c)))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    IsTraceClassAlong sourceBasis
      (suffixActualBandRawPhysicalFourTermRow owner lambda p S) := by
  let targetBasis := chooseTraceTargetHilbertBasis (WithLp 2
    (WithLp 2 (commonBoundaryCarrier a c × commonBoundaryCarrier a c) ×
      WithLp 2 (commonBoundaryCarrier a c × commonBoundaryCarrier a c)))
  let data := suffixActualBandLocalRawDefectPairData owner lambda p S a c hac
    hsupp negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
    sourceBasis pairedBoundaryBasis hfactor
  exact suffixActualBandRawPhysicalFourTermRow_isTraceClassAlong_of_localPairOwner
    owner lambda p S sourceBasis targetBasis data
    (suffixActualBandLocalRawDefectPairData_traceProduct_eq owner lambda p S
      a c hac hsupp negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
      sourceBasis pairedBoundaryBasis hfactor)

/-! ## The exact fixed-suffix trace readback -/

theorem ordinaryTraceAlong_suffixActualBandRawPhysicalFourTermRow_eq_star_neg_inv_localCofactorTrace
    {ι κ G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime)
    (sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda))
    (targetBasis : HilbertBasis κ ℂ G)
    (data : BasisHilbertSchmidtPairData (G := G) sourceBasis)
    (hdata : data.traceProduct =
      suffixActualBandLocalRawDefect owner lambda p S) :
    ordinaryTraceAlong sourceBasis
        (suffixActualBandRawPhysicalFourTermRow owner lambda p S) =
      star ((-(primeSchurMarkovScalar p : ℂ)⁻¹) *
        ordinaryTraceAlong sourceBasis
          (suffixActualBandLocalRawDefect owner lambda p S ∘L
            suffixEulerFrameTransition lambda p S)) := by
  have hcofactor := data.boundedSandwich_isTraceClassAlong targetBasis
    (ContinuousLinearMap.id ℂ (sourceSoninCarrier lambda))
    (suffixEulerFrameTransition lambda p S)
  have hcofactor' : IsTraceClassAlong sourceBasis
      (suffixActualBandLocalRawDefect owner lambda p S ∘L
        suffixEulerFrameTransition lambda p S) := by
    rw [← hdata]
    simpa only [ContinuousLinearMap.id_comp] using hcofactor
  have hrowAdjEq :
      (suffixActualBandRawPhysicalFourTermRow owner lambda p S)† =
        (-(primeSchurMarkovScalar p : ℂ)⁻¹) •
          (suffixActualBandLocalRawDefect owner lambda p S ∘L
            suffixEulerFrameTransition lambda p S) := by
    apply ContinuousLinearMap.ext
    intro x
    have hcofactorPoint := congrArg
      (fun operator : sourceSoninCarrier lambda →L[ℂ]
          sourceSoninCarrier lambda => operator x)
      (suffixActualBandLocalRawDefect_comp_transition_eq_neg_scalar_rawPhysicalRow_adjoint
        owner lambda p S)
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply]
      at hcofactorPoint
    calc
      (ContinuousLinearMap.adjoint
          (suffixActualBandRawPhysicalFourTermRow owner lambda p S)) x =
          (-((primeSchurMarkovScalar p : ℂ)⁻¹)) •
            (-((primeSchurMarkovScalar p : ℂ) •
              (ContinuousLinearMap.adjoint
                (suffixActualBandRawPhysicalFourTermRow owner lambda p S)) x)) := by
        simp only [smul_neg, neg_smul, neg_neg]
        rw [smul_smul]
        simp [Complex.ofReal_ne_zero.mpr
          (ne_of_gt (primeSchurMarkovScalar_pos p))]
      _ = (-((primeSchurMarkovScalar p : ℂ)⁻¹)) •
          (suffixActualBandLocalRawDefect owner lambda p S)
            (suffixEulerFrameTransition lambda p S x) := by
        rw [hcofactorPoint]
  have htraceAdj := ordinaryTraceAlong_smul sourceBasis
    (-(primeSchurMarkovScalar p : ℂ)⁻¹)
    (suffixActualBandLocalRawDefect owner lambda p S ∘L
      suffixEulerFrameTransition lambda p S) hcofactor'
  calc
    ordinaryTraceAlong sourceBasis
        (suffixActualBandRawPhysicalFourTermRow owner lambda p S) =
      star (star (ordinaryTraceAlong sourceBasis
        (suffixActualBandRawPhysicalFourTermRow owner lambda p S))) := by
          simp
    _ = star (ordinaryTraceAlong sourceBasis
        (ContinuousLinearMap.adjoint
          (suffixActualBandRawPhysicalFourTermRow owner lambda p S))) := by
          rw [ordinaryTraceAlong_adjoint]
    _ = star ((-(primeSchurMarkovScalar p : ℂ)⁻¹) *
        ordinaryTraceAlong sourceBasis
          (suffixActualBandLocalRawDefect owner lambda p S ∘L
            suffixEulerFrameTransition lambda p S)) := by
          rw [hrowAdjEq, htraceAdj]

/-! ## Legal target-side trace readback -/

theorem ordinaryTraceAlong_suffixActualBandRawPhysicalFourTermRow_eq_star_neg_inv_targetTrace
    {ι κ G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime)
    (sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda))
    (targetBasis : HilbertBasis κ ℂ G)
    (data : BasisHilbertSchmidtPairData (G := G) sourceBasis)
    (hdata : data.traceProduct =
      suffixActualBandLocalRawDefect owner lambda p S) :
    ordinaryTraceAlong sourceBasis
        (suffixActualBandRawPhysicalFourTermRow owner lambda p S) =
      star ((-(primeSchurMarkovScalar p : ℂ)⁻¹) *
        ordinaryTraceAlong targetBasis
          ((data.right ∘L suffixEulerFrameTransition lambda p S) ∘L
            data.left.adjoint)) := by
  have hright : Summable fun i =>
      ‖(data.right ∘L suffixEulerFrameTransition lambda p S)
        (sourceBasis i)‖ ^ 2 := by
    exact summable_normSq_precomp sourceBasis targetBasis sourceBasis
      data.right (suffixEulerFrameTransition lambda p S)
      data.right_summable_normSq
  have hcycle := BasisHilbertSchmidtPairData.ordinaryTraceAlong_adjoint_comp_eq_comp_adjoint
    sourceBasis targetBasis data.left
      (data.right ∘L suffixEulerFrameTransition lambda p S)
      data.left_summable_normSq hright
  have htraceProduct :
      data.traceProduct ∘L suffixEulerFrameTransition lambda p S =
        data.left.adjoint ∘L
          (data.right ∘L suffixEulerFrameTransition lambda p S) := by
    apply ContinuousLinearMap.ext
    intro x
    rfl
  calc
    ordinaryTraceAlong sourceBasis
        (suffixActualBandRawPhysicalFourTermRow owner lambda p S) =
      star ((-(primeSchurMarkovScalar p : ℂ)⁻¹) *
        ordinaryTraceAlong sourceBasis
          (suffixActualBandLocalRawDefect owner lambda p S ∘L
            suffixEulerFrameTransition lambda p S)) :=
      ordinaryTraceAlong_suffixActualBandRawPhysicalFourTermRow_eq_star_neg_inv_localCofactorTrace
        owner lambda p S sourceBasis targetBasis data hdata
    _ = star ((-(primeSchurMarkovScalar p : ℂ)⁻¹) *
        ordinaryTraceAlong sourceBasis
          (data.traceProduct ∘L suffixEulerFrameTransition lambda p S)) := by
      rw [hdata]
    _ = star ((-(primeSchurMarkovScalar p : ℂ)⁻¹) *
        ordinaryTraceAlong targetBasis
          ((data.right ∘L suffixEulerFrameTransition lambda p S) ∘L
            data.left.adjoint)) := by
      rw [htraceProduct, hcycle]

theorem ordinaryTraceAlong_l2Sum_targetTrace_eq_add
    {ι κ μ ν H G K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (sourceBasis : HilbertBasis ι ℂ H)
    (targetGBasis : HilbertBasis κ ℂ G)
    (targetKBasis : HilbertBasis μ ℂ K)
    (targetBasis : HilbertBasis ν ℂ (WithLp 2 (G × K)))
    (first : BasisHilbertSchmidtPairData (G := G) sourceBasis)
    (second : BasisHilbertSchmidtPairData (G := K) sourceBasis)
    (bounded : H →L[ℂ] H) :
    ordinaryTraceAlong targetBasis
        (((BasisHilbertSchmidtPairData.l2Sum first second).right ∘L bounded) ∘L
          (BasisHilbertSchmidtPairData.l2Sum first second).left.adjoint) =
      ordinaryTraceAlong targetGBasis
          ((first.right ∘L bounded) ∘L first.left.adjoint) +
        ordinaryTraceAlong targetKBasis
          ((second.right ∘L bounded) ∘L second.left.adjoint) := by
  let combined := BasisHilbertSchmidtPairData.l2Sum first second
  have hrightFirst : Summable fun i =>
      ‖(first.right ∘L bounded) (sourceBasis i)‖ ^ 2 := by
    exact summable_normSq_precomp sourceBasis targetGBasis sourceBasis
      first.right bounded first.right_summable_normSq
  have hrightSecond : Summable fun i =>
      ‖(second.right ∘L bounded) (sourceBasis i)‖ ^ 2 := by
    exact summable_normSq_precomp sourceBasis targetKBasis sourceBasis
      second.right bounded second.right_summable_normSq
  have hrightCombined : Summable fun i =>
      ‖(combined.right ∘L bounded) (sourceBasis i)‖ ^ 2 := by
    exact summable_normSq_precomp sourceBasis targetBasis sourceBasis
      combined.right bounded combined.right_summable_normSq
  have hcycleFirst := BasisHilbertSchmidtPairData.ordinaryTraceAlong_adjoint_comp_eq_comp_adjoint
    sourceBasis targetGBasis first.left (first.right ∘L bounded)
      first.left_summable_normSq hrightFirst
  have hcycleSecond := BasisHilbertSchmidtPairData.ordinaryTraceAlong_adjoint_comp_eq_comp_adjoint
    sourceBasis targetKBasis second.left (second.right ∘L bounded)
      second.left_summable_normSq hrightSecond
  have hcycleCombined := BasisHilbertSchmidtPairData.ordinaryTraceAlong_adjoint_comp_eq_comp_adjoint
    sourceBasis targetBasis combined.left (combined.right ∘L bounded)
      combined.left_summable_normSq hrightCombined
  have hfirstOperator :
      first.traceProduct ∘L bounded =
        first.left.adjoint ∘L (first.right ∘L bounded) := by
    apply ContinuousLinearMap.ext
    intro x
    rfl
  have hsecondOperator :
      second.traceProduct ∘L bounded =
        second.left.adjoint ∘L (second.right ∘L bounded) := by
    apply ContinuousLinearMap.ext
    intro x
    rfl
  have hcombinedOperator :
      combined.traceProduct ∘L bounded =
        combined.left.adjoint ∘L (combined.right ∘L bounded) := by
    apply ContinuousLinearMap.ext
    intro x
    rfl
  have hsourceOperator :
      combined.left.adjoint ∘L (combined.right ∘L bounded) =
        first.traceProduct ∘L bounded + second.traceProduct ∘L bounded := by
    rw [← hcombinedOperator]
    rw [show combined.traceProduct = first.traceProduct + second.traceProduct by
      exact BasisHilbertSchmidtPairData.l2Sum_traceProduct_eq_add first second]
    apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply]
  have hfirstClass : IsTraceClassAlong sourceBasis
      (first.traceProduct ∘L bounded) := by
    simpa only [ContinuousLinearMap.id_comp] using
      first.boundedSandwich_isTraceClassAlong targetGBasis
        (ContinuousLinearMap.id ℂ H) bounded
  have hsecondClass : IsTraceClassAlong sourceBasis
      (second.traceProduct ∘L bounded) := by
    simpa only [ContinuousLinearMap.id_comp] using
      second.boundedSandwich_isTraceClassAlong targetKBasis
        (ContinuousLinearMap.id ℂ H) bounded
  have hfirstTrace : ordinaryTraceAlong sourceBasis
      (first.traceProduct ∘L bounded) =
        ordinaryTraceAlong targetGBasis
          ((first.right ∘L bounded) ∘L first.left.adjoint) := by
    rw [hfirstOperator]
    exact hcycleFirst
  have hsecondTrace : ordinaryTraceAlong sourceBasis
      (second.traceProduct ∘L bounded) =
        ordinaryTraceAlong targetKBasis
          ((second.right ∘L bounded) ∘L second.left.adjoint) := by
    rw [hsecondOperator]
    exact hcycleSecond
  change ordinaryTraceAlong targetBasis
      ((combined.right ∘L bounded) ∘L combined.left.adjoint) = _
  calc
    ordinaryTraceAlong targetBasis
        ((combined.right ∘L bounded) ∘L combined.left.adjoint) =
      ordinaryTraceAlong sourceBasis
        (combined.left.adjoint ∘L (combined.right ∘L bounded)) :=
      hcycleCombined.symm
    _ = ordinaryTraceAlong sourceBasis
        (first.traceProduct ∘L bounded + second.traceProduct ∘L bounded) := by
      rw [hsourceOperator]
    _ = ordinaryTraceAlong sourceBasis (first.traceProduct ∘L bounded) +
          ordinaryTraceAlong sourceBasis (second.traceProduct ∘L bounded) :=
      ordinaryTraceAlong_add sourceBasis _ _ hfirstClass hsecondClass
    _ = _ := by rw [hfirstTrace, hsecondTrace]

theorem ordinaryTraceAlong_l2Sum_boundedTargetTrace_eq_scalar_orderedDifference
    {ι κ ν H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (sourceBasis : HilbertBasis ι ℂ H)
    (targetBasis : HilbertBasis κ ℂ G)
    (combinedBasis : HilbertBasis ν ℂ (WithLp 2 (G × G)))
    (newData oldData : BasisHilbertSchmidtPairData (G := G) sourceBasis)
    (forward reverse : H →L[ℂ] H) (scalar : ℂ)
    (combined : BasisHilbertSchmidtPairData
      (G := WithLp 2 (G × G)) sourceBasis)
    (hpair : reverse ∘L forward =
      scalar • ContinuousLinearMap.id ℂ H)
    (hcombined : combined =
      BasisHilbertSchmidtPairData.l2Sum
        (newData.smulRight scalar)
        ((oldData.boundedSandwich targetBasis forward reverse).smulRight (-1))) :
    ordinaryTraceAlong combinedBasis
        ((combined.right ∘L forward) ∘L combined.left.adjoint) =
      scalar *
        (ordinaryTraceAlong sourceBasis (newData.traceProduct ∘L forward) -
          ordinaryTraceAlong sourceBasis (forward ∘L oldData.traceProduct)) := by
  let first := newData.smulRight scalar
  let second :=
    (oldData.boundedSandwich targetBasis forward reverse).smulRight (-1)
  have hcombined' : combined =
      BasisHilbertSchmidtPairData.l2Sum first second := by
    simpa only [first, second] using hcombined
  have hnewClass : IsTraceClassAlong sourceBasis
      (newData.traceProduct ∘L forward) := by
    simpa only [ContinuousLinearMap.id_comp] using
      newData.boundedSandwich_isTraceClassAlong targetBasis
        (ContinuousLinearMap.id ℂ H) forward
  have holdClass : IsTraceClassAlong sourceBasis
      (forward ∘L oldData.traceProduct) := by
    have hclass := oldData.boundedSandwich_isTraceClassAlong targetBasis
      forward (ContinuousLinearMap.id ℂ H)
    simpa only [ContinuousLinearMap.comp_id] using hclass
  have hrightFirst : Summable fun i =>
      ‖(first.right ∘L forward) (sourceBasis i)‖ ^ 2 := by
    exact summable_normSq_precomp sourceBasis targetBasis sourceBasis
      first.right forward first.right_summable_normSq
  have hrightSecond : Summable fun i =>
      ‖(second.right ∘L forward) (sourceBasis i)‖ ^ 2 := by
    exact summable_normSq_precomp sourceBasis targetBasis sourceBasis
      second.right forward second.right_summable_normSq
  have hcycleFirst := BasisHilbertSchmidtPairData.ordinaryTraceAlong_adjoint_comp_eq_comp_adjoint
    sourceBasis targetBasis first.left (first.right ∘L forward)
      first.left_summable_normSq hrightFirst
  have hcycleSecond := BasisHilbertSchmidtPairData.ordinaryTraceAlong_adjoint_comp_eq_comp_adjoint
    sourceBasis targetBasis second.left (second.right ∘L forward)
      second.left_summable_normSq hrightSecond
  have hfirstAssoc :
      first.left.adjoint ∘L (first.right ∘L forward) =
        first.traceProduct ∘L forward := by
    apply ContinuousLinearMap.ext
    intro x
    rfl
  have hsecondAssoc :
      second.left.adjoint ∘L (second.right ∘L forward) =
        second.traceProduct ∘L forward := by
    apply ContinuousLinearMap.ext
    intro x
    rfl
  have hfirstProduct :
      first.traceProduct ∘L forward =
        scalar • (newData.traceProduct ∘L forward) := by
    rw [BasisHilbertSchmidtPairData.smulRight_traceProduct_eq]
    apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      map_smul]
  have hsecondProduct :
      second.traceProduct ∘L forward =
        (-scalar) • (forward ∘L oldData.traceProduct) := by
    have hsecondTraceProduct :
        second.traceProduct =
          (-1 : ℂ) •
            (forward ∘L oldData.traceProduct ∘L reverse) := by
      dsimp only [second]
      rw [BasisHilbertSchmidtPairData.smulRight_traceProduct_eq,
        BasisHilbertSchmidtPairData.boundedSandwich_traceProduct_eq]
    rw [hsecondTraceProduct]
    apply ContinuousLinearMap.ext
    intro x
    have hpairPoint := congrArg
      (fun operator : H →L[ℂ] H => operator x) hpair
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply] at hpairPoint ⊢
    rw [hpairPoint]
    simp only [map_smul]
    module
  have hfirstTrace :
      ordinaryTraceAlong targetBasis
          ((first.right ∘L forward) ∘L first.left.adjoint) =
        scalar * ordinaryTraceAlong sourceBasis
          (newData.traceProduct ∘L forward) := by
    calc
      ordinaryTraceAlong targetBasis
          ((first.right ∘L forward) ∘L first.left.adjoint) =
          ordinaryTraceAlong sourceBasis
            (first.left.adjoint ∘L (first.right ∘L forward)) :=
        hcycleFirst.symm
      _ = ordinaryTraceAlong sourceBasis (first.traceProduct ∘L forward) := by
        rw [hfirstAssoc]
      _ = ordinaryTraceAlong sourceBasis
          (scalar • (newData.traceProduct ∘L forward)) := by
        rw [hfirstProduct]
      _ = scalar * ordinaryTraceAlong sourceBasis
          (newData.traceProduct ∘L forward) :=
        ordinaryTraceAlong_smul sourceBasis scalar _ hnewClass
  have hsecondTrace :
      ordinaryTraceAlong targetBasis
          ((second.right ∘L forward) ∘L second.left.adjoint) =
        (-scalar) * ordinaryTraceAlong sourceBasis
          (forward ∘L oldData.traceProduct) := by
    calc
      ordinaryTraceAlong targetBasis
          ((second.right ∘L forward) ∘L second.left.adjoint) =
          ordinaryTraceAlong sourceBasis
            (second.left.adjoint ∘L (second.right ∘L forward)) :=
        hcycleSecond.symm
      _ = ordinaryTraceAlong sourceBasis (second.traceProduct ∘L forward) := by
        rw [hsecondAssoc]
      _ = ordinaryTraceAlong sourceBasis
          ((-scalar) • (forward ∘L oldData.traceProduct)) := by
        rw [hsecondProduct]
      _ = (-scalar) * ordinaryTraceAlong sourceBasis
          (forward ∘L oldData.traceProduct) :=
        ordinaryTraceAlong_smul sourceBasis (-scalar) _ holdClass
  rw [hcombined']
  calc
    ordinaryTraceAlong combinedBasis
        (((BasisHilbertSchmidtPairData.l2Sum first second).right ∘L forward) ∘L
          (BasisHilbertSchmidtPairData.l2Sum first second).left.adjoint) =
      ordinaryTraceAlong targetBasis
          ((first.right ∘L forward) ∘L first.left.adjoint) +
        ordinaryTraceAlong targetBasis
          ((second.right ∘L forward) ∘L second.left.adjoint) :=
      ordinaryTraceAlong_l2Sum_targetTrace_eq_add sourceBasis targetBasis
        targetBasis combinedBasis first second forward
    _ = scalar * ordinaryTraceAlong sourceBasis
          (newData.traceProduct ∘L forward) +
        (-scalar) * ordinaryTraceAlong sourceBasis
          (forward ∘L oldData.traceProduct) := by
      rw [hfirstTrace, hsecondTrace]
    _ = scalar *
        (ordinaryTraceAlong sourceBasis (newData.traceProduct ∘L forward) -
          ordinaryTraceAlong sourceBasis (forward ∘L oldData.traceProduct)) := by
      ring

theorem ordinaryTraceAlong_suffixActualBandRawPhysicalFourTermRow_targetTrace_eq_orderedDifference
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {iota kappa tau iotaR kappaR tauR nu mu rho sigma targetIndex : Type*}
    (negativeBasis : HilbertBasis iota ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis kappa ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis tau ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis iotaR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis kappaR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis tauR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis mu ℂ (commonBoundaryCarrier a c))
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (pairedBoundaryBasis : HilbertBasis sigma ℂ
      (WithLp 2 (commonBoundaryCarrier a c × commonBoundaryCarrier a c)))
    (targetBasis : HilbertBasis targetIndex ℂ
      (WithLp 2
        (WithLp 2 (commonBoundaryCarrier a c × commonBoundaryCarrier a c) ×
          WithLp 2 (commonBoundaryCarrier a c × commonBoundaryCarrier a c))))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    ordinaryTraceAlong targetBasis
        (((suffixActualBandLocalRawDefectPairData owner lambda p S a c hac
          hsupp negativeBasis positiveBasis outputBasis reflectedNegativeBasis
          reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
          sourceBasis pairedBoundaryBasis hfactor).right ∘L
            suffixEulerFrameTransition lambda p S) ∘L
          (suffixActualBandLocalRawDefectPairData owner lambda p S a c hac
            hsupp negativeBasis positiveBasis outputBasis reflectedNegativeBasis
            reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
            sourceBasis pairedBoundaryBasis hfactor).left.adjoint) =
      (primeSchurMarkovScalar p : ℂ) *
        (ordinaryTraceAlong sourceBasis
            (suffixActualBandRawQuadraticCycledResponse owner lambda (p :: S) ∘L
              suffixEulerFrameTransition lambda p S) -
          ordinaryTraceAlong sourceBasis
            (suffixEulerFrameTransition lambda p S ∘L
              suffixActualBandRawQuadraticCycledResponse owner lambda S)) := by
  let newData := suffixActualBandRawCommonPairData owner lambda (p :: S) a c hac
    hsupp negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
    sourceBasis hfactor
  let oldData := suffixActualBandRawCommonPairData owner lambda S a c hac hsupp
    negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
    sourceBasis hfactor
  let combined := suffixActualBandLocalRawDefectPairData owner lambda p S a c hac
    hsupp negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
    sourceBasis pairedBoundaryBasis hfactor
  have hcombined : combined =
      BasisHilbertSchmidtPairData.l2Sum
        (newData.smulRight (primeSchurMarkovScalar p : ℂ))
        ((oldData.boundedSandwich pairedBoundaryBasis
          (suffixEulerFrameTransition lambda p S)
          (suffixEulerFrameReverseTransition lambda p S)).smulRight (-1)) := by
    rfl
  have hordered :=
    ordinaryTraceAlong_l2Sum_boundedTargetTrace_eq_scalar_orderedDifference
      sourceBasis pairedBoundaryBasis targetBasis newData oldData
      (suffixEulerFrameTransition lambda p S)
      (suffixEulerFrameReverseTransition lambda p S)
      (primeSchurMarkovScalar p : ℂ) combined
      (suffixEulerFrameReverse_comp_transition lambda p S) hcombined
  have hnew : newData.traceProduct =
      suffixActualBandRawQuadraticCycledResponse owner lambda (p :: S) := by
    exact suffixActualBandRawCommonPairData_traceProduct_eq_raw owner lambda
      (p :: S) a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis sourceBasis hfactor
  have hold : oldData.traceProduct =
      suffixActualBandRawQuadraticCycledResponse owner lambda S := by
    exact suffixActualBandRawCommonPairData_traceProduct_eq_raw owner lambda S
      a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis sourceBasis hfactor
  calc
    ordinaryTraceAlong targetBasis
        (((suffixActualBandLocalRawDefectPairData owner lambda p S a c hac
          hsupp negativeBasis positiveBasis outputBasis reflectedNegativeBasis
          reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
          sourceBasis pairedBoundaryBasis hfactor).right ∘L
            suffixEulerFrameTransition lambda p S) ∘L
          (suffixActualBandLocalRawDefectPairData owner lambda p S a c hac
            hsupp negativeBasis positiveBasis outputBasis reflectedNegativeBasis
            reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
            sourceBasis pairedBoundaryBasis hfactor).left.adjoint) =
      (primeSchurMarkovScalar p : ℂ) *
        (ordinaryTraceAlong sourceBasis
            (newData.traceProduct ∘L suffixEulerFrameTransition lambda p S) -
          ordinaryTraceAlong sourceBasis
            (suffixEulerFrameTransition lambda p S ∘L oldData.traceProduct)) := by
      simpa only [combined] using hordered
    _ = (primeSchurMarkovScalar p : ℂ) *
        (ordinaryTraceAlong sourceBasis
            (suffixActualBandRawQuadraticCycledResponse owner lambda (p :: S) ∘L
              suffixEulerFrameTransition lambda p S) -
          ordinaryTraceAlong sourceBasis
            (suffixEulerFrameTransition lambda p S ∘L
              suffixActualBandRawQuadraticCycledResponse owner lambda S)) := by
      rw [hnew, hold]

theorem ordinaryTraceAlong_suffixActualBandRawPhysicalFourTermRow_of_actual_owner
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {iota kappa tau iotaR kappaR tauR nu mu rho sigma : Type*}
    (negativeBasis : HilbertBasis iota ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis kappa ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis tau ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis iotaR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis kappaR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis tauR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis mu ℂ (commonBoundaryCarrier a c))
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (pairedBoundaryBasis : HilbertBasis sigma ℂ
      (WithLp 2 (commonBoundaryCarrier a c × commonBoundaryCarrier a c)))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    ordinaryTraceAlong sourceBasis
        (suffixActualBandRawPhysicalFourTermRow owner lambda p S) =
      star ((-(primeSchurMarkovScalar p : ℂ)⁻¹) *
        ordinaryTraceAlong sourceBasis
          (suffixActualBandLocalRawDefect owner lambda p S ∘L
            suffixEulerFrameTransition lambda p S)) := by
  let targetBasis := chooseTraceTargetHilbertBasis (WithLp 2
    (WithLp 2 (commonBoundaryCarrier a c × commonBoundaryCarrier a c) ×
      WithLp 2 (commonBoundaryCarrier a c × commonBoundaryCarrier a c)))
  let data := suffixActualBandLocalRawDefectPairData owner lambda p S a c hac
    hsupp negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
    sourceBasis pairedBoundaryBasis hfactor
  exact ordinaryTraceAlong_suffixActualBandRawPhysicalFourTermRow_eq_star_neg_inv_localCofactorTrace
    owner lambda p S sourceBasis targetBasis data
    (suffixActualBandLocalRawDefectPairData_traceProduct_eq owner lambda p S
      a c hac hsupp negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
      sourceBasis pairedBoundaryBasis hfactor)

theorem ordinaryTraceAlong_suffixActualBandRawPhysicalFourTermRow_targetTrace_actual
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {iota kappa tau iotaR kappaR tauR nu mu rho sigma targetIndex : Type*}
    (negativeBasis : HilbertBasis iota ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis kappa ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis tau ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis iotaR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis kappaR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis tauR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis mu ℂ (commonBoundaryCarrier a c))
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (pairedBoundaryBasis : HilbertBasis sigma ℂ
      (WithLp 2 (commonBoundaryCarrier a c × commonBoundaryCarrier a c)))
    (targetBasis : HilbertBasis targetIndex ℂ
      (WithLp 2
        (WithLp 2 (commonBoundaryCarrier a c × commonBoundaryCarrier a c) ×
          WithLp 2 (commonBoundaryCarrier a c × commonBoundaryCarrier a c))))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    ordinaryTraceAlong sourceBasis
        (suffixActualBandRawPhysicalFourTermRow owner lambda p S) =
      star ((-(primeSchurMarkovScalar p : ℂ)⁻¹) *
        ordinaryTraceAlong targetBasis
          (((suffixActualBandLocalRawDefectPairData owner lambda p S a c hac
            hsupp negativeBasis positiveBasis outputBasis reflectedNegativeBasis
            reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
            sourceBasis pairedBoundaryBasis hfactor).right ∘L
              suffixEulerFrameTransition lambda p S) ∘L
            (suffixActualBandLocalRawDefectPairData owner lambda p S a c hac
              hsupp negativeBasis positiveBasis outputBasis reflectedNegativeBasis
              reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
              sourceBasis pairedBoundaryBasis hfactor).left.adjoint)) := by
  let data := suffixActualBandLocalRawDefectPairData owner lambda p S a c hac
    hsupp negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
    sourceBasis pairedBoundaryBasis hfactor
  exact ordinaryTraceAlong_suffixActualBandRawPhysicalFourTermRow_eq_star_neg_inv_targetTrace
    owner lambda p S sourceBasis targetBasis data
    (suffixActualBandLocalRawDefectPairData_traceProduct_eq owner lambda p S
      a c hac hsupp negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
      sourceBasis pairedBoundaryBasis hfactor)

end CCM24FiniteSCompletedJuliaRawCofactorTrace
end CCM25Concrete
end Source
end ConnesWeilRH
