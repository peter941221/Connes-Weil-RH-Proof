/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1PositiveTraceTraceContinuity
import ConnesWeilRH.Source.CC20Concrete.HilbertSchmidtIdeal
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCommonBoundaryPair

/-!
# R3 trace transfer through a uniformly bounded strong sandwich

For a trace-class operator represented by two Hilbert--Schmidt legs, a
uniformly bounded strongly convergent cutoff sandwich has a convergent
ordinary trace.  The proof cycles to the target basis, where the summable
majorant is the product of the two fixed adjoint column energies.  This is a
sign-free trace-transfer tool for the P1 source-band channel; it does not
assert that the G8 cutoff family satisfies these strong-limit premises.
-/

namespace ConnesWeilRH
namespace Dev

open Filter
open Source.CC20Concrete.PositiveTrace
open Source.Dev.C1PositiveTraceTraceContinuity
open Source.CCM25Concrete
open Source.CCM25Concrete.CCM24FiniteSProjectionTrace
open Source.CCM25Concrete.CCM24FiniteSGramResponse
open Source.CCM25Concrete.CCM24FiniteSBandTrace
open Source.CCM25Concrete.CCM24FiniteSCommonBoundaryPair
open Source.CCM25Concrete.CCM24SourceProlateTrace
open Source.CCM25Concrete.CCM24RadialBoundaryPairTransport
open Source.CC20Concrete
open Source.CC20Concrete.CompactRootHalfLinePair
open MeasureTheory
open scoped InnerProduct InnerProductSpace Topology

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/- Tannery convergence for a same-owner Hilbert--Schmidt trace product
under a uniformly bounded strong sandwich.  The strong convergence is
required only for the doubled cutoff `Cₙ Cₙ†`, exactly the operator appearing
after cycling the trace to the target basis. -/
/- The basis change and dominated-sum elaboration need a larger heartbeat cap. -/
set_option maxHeartbeats 1000000 in
-- The basis-change and dominated-series proof needs this elaboration budget.
theorem tendsto_ordinaryTraceAlong_pairSandwich_of_strong
    {ι κ : Type*} {H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (sourceBasis : HilbertBasis ι ℂ H)
    (targetBasis : HilbertBasis κ ℂ G)
    (pair : BasisHilbertSchmidtPairData (G := G) sourceBasis)
    (cutoff : ℕ → H →L[ℂ] H)
    (limitCutoff : H →L[ℂ] H)
    (doubleBound : ℝ) (hdoubleBound_nonneg : 0 ≤ doubleBound)
    (hdouble_norm : ∀ n, ‖cutoff n ∘L (cutoff n).adjoint‖ ≤ doubleBound)
    (hdouble_tendsto : ∀ x,
      Tendsto (fun n => cutoff n ((cutoff n).adjoint x)) atTop
        (𝓝 (limitCutoff (limitCutoff.adjoint x)))) :
    Tendsto
      (fun n => ordinaryTraceAlong sourceBasis
        ((pair.boundedSandwich targetBasis (cutoff n).adjoint (cutoff n)).traceProduct))
      atTop
      (𝓝 (ordinaryTraceAlong sourceBasis
        ((pair.boundedSandwich targetBasis limitCutoff.adjoint limitCutoff).traceProduct))) := by
  let traceBound : κ → ℝ := fun j =>
    doubleBound * ‖pair.right.adjoint (targetBasis j)‖ *
      ‖pair.left.adjoint (targetBasis j)‖
  have htraceBound_nonneg : ∀ j, 0 ≤ traceBound j := by
    intro j
    dsimp [traceBound]
    positivity
  have hleftAdj : Summable fun j =>
      ‖pair.left.adjoint (targetBasis j)‖ ^ 2 :=
    BasisHilbertSchmidtPairData.summable_adjoint_normSq
      sourceBasis targetBasis pair.left pair.left_summable_normSq
  have hrightAdj : Summable fun j =>
      ‖pair.right.adjoint (targetBasis j)‖ ^ 2 :=
    BasisHilbertSchmidtPairData.summable_adjoint_normSq
      sourceBasis targetBasis pair.right pair.right_summable_normSq
  have hproduct : Summable fun j =>
      ‖pair.right.adjoint (targetBasis j)‖ *
        ‖pair.left.adjoint (targetBasis j)‖ := by
    apply Summable.of_nonneg_of_le
      (fun j => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (fun j => by
        nlinarith [sq_nonneg
          (‖pair.right.adjoint (targetBasis j)‖ -
            ‖pair.left.adjoint (targetBasis j)‖)])
      ((hrightAdj.add hleftAdj).mul_left (1 / 2 : ℝ))
  have htraceBound : Summable traceBound := by
    simpa only [traceBound, mul_assoc] using hproduct.mul_left doubleBound
  have hdiagonal : ∀ j,
      Tendsto
        (fun n => ⟪targetBasis j,
          (pair.right ∘L cutoff n ∘L (cutoff n).adjoint ∘L pair.left.adjoint)
            (targetBasis j)⟫_ℂ)
        atTop
        (𝓝 (⟪targetBasis j,
          (pair.right ∘L limitCutoff ∘L limitCutoff.adjoint ∘L pair.left.adjoint)
            (targetBasis j)⟫_ℂ)) := by
    intro j
    let v := targetBasis j
    have hvector := hdouble_tendsto (pair.left.adjoint v)
    have hfunctional :=
      ((innerSL ℂ (pair.right.adjoint v)).continuous.tendsto
        (limitCutoff (limitCutoff.adjoint (pair.left.adjoint v)))).comp hvector
    convert hfunctional using 1
    · funext n
      simp only [Function.comp_apply, innerSL_apply_apply,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left, v]
    · simp only [innerSL_apply_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.adjoint_inner_left, v]
  have hdominated : ∀ n j,
      ‖⟪targetBasis j,
        (pair.right ∘L cutoff n ∘L (cutoff n).adjoint ∘L pair.left.adjoint)
          (targetBasis j)⟫_ℂ‖ ≤ traceBound j := by
    intro n j
    let v := targetBasis j
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.adjoint_inner_left]
    calc
      ‖⟪pair.right.adjoint v,
          cutoff n ((cutoff n).adjoint (pair.left.adjoint v))⟫_ℂ‖ ≤
          ‖pair.right.adjoint v‖ *
            ‖cutoff n ((cutoff n).adjoint (pair.left.adjoint v))‖ :=
        norm_inner_le_norm _ _
      _ ≤ ‖pair.right.adjoint v‖ *
          (‖cutoff n ∘L (cutoff n).adjoint‖ *
            ‖pair.left.adjoint v‖) := by
        gcongr
        exact (cutoff n ∘L (cutoff n).adjoint).le_opNorm _
      _ ≤ doubleBound * ‖pair.right.adjoint v‖ *
          ‖pair.left.adjoint v‖ := by
        calc
          _ ≤ ‖pair.right.adjoint v‖ *
              (doubleBound * ‖pair.left.adjoint v‖) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right (hdouble_norm n) (norm_nonneg _))
              (norm_nonneg _)
          _ = doubleBound * ‖pair.right.adjoint v‖ *
              ‖pair.left.adjoint v‖ := by ring
      _ = traceBound j := by rfl
  have hcycled := tendsto_ordinaryTraceAlong_of_dominated_diagonal
    targetBasis
    (fun n => pair.right ∘L cutoff n ∘L (cutoff n).adjoint ∘L pair.left.adjoint)
    (pair.right ∘L limitCutoff ∘L limitCutoff.adjoint ∘L pair.left.adjoint)
    traceBound htraceBound hdiagonal hdominated
  have hcycle (n : ℕ) :
      ordinaryTraceAlong sourceBasis
          ((pair.boundedSandwich targetBasis (cutoff n).adjoint (cutoff n)).traceProduct) =
        ordinaryTraceAlong targetBasis
          (pair.right ∘L cutoff n ∘L (cutoff n).adjoint ∘L pair.left.adjoint) := by
    calc
      _ = ordinaryTraceAlong targetBasis
          (((pair.boundedSandwich targetBasis (cutoff n).adjoint
              (cutoff n)).right) ∘L
            (pair.boundedSandwich targetBasis (cutoff n).adjoint
              (cutoff n)).left.adjoint) :=
        (pair.boundedSandwich targetBasis (cutoff n).adjoint
          (cutoff n)).ordinaryTraceAlong_traceProduct_eq_cyclic targetBasis
      _ = _ := by
        simp only [BasisHilbertSchmidtPairData.boundedSandwich,
          ContinuousLinearMap.adjoint_comp,
          ContinuousLinearMap.adjoint_adjoint,
          ContinuousLinearMap.comp_assoc]
  have hcycleLimit :
      ordinaryTraceAlong sourceBasis
          ((pair.boundedSandwich targetBasis limitCutoff.adjoint limitCutoff).traceProduct) =
        ordinaryTraceAlong targetBasis
          (pair.right ∘L limitCutoff ∘L limitCutoff.adjoint ∘L pair.left.adjoint) := by
    calc
      _ = ordinaryTraceAlong targetBasis
          (((pair.boundedSandwich targetBasis limitCutoff.adjoint
              limitCutoff).right) ∘L
            (pair.boundedSandwich targetBasis limitCutoff.adjoint
              limitCutoff).left.adjoint) :=
        (pair.boundedSandwich targetBasis limitCutoff.adjoint
          limitCutoff).ordinaryTraceAlong_traceProduct_eq_cyclic targetBasis
      _ = _ := by
        simp only [BasisHilbertSchmidtPairData.boundedSandwich,
          ContinuousLinearMap.adjoint_comp,
          ContinuousLinearMap.adjoint_adjoint,
          ContinuousLinearMap.comp_assoc]
  rw [hcycleLimit]
  have hsequence :
      (fun n => ordinaryTraceAlong sourceBasis
        ((pair.boundedSandwich targetBasis (cutoff n).adjoint
          (cutoff n)).traceProduct)) =
        (fun n => ordinaryTraceAlong targetBasis
          (pair.right ∘L cutoff n ∘L (cutoff n).adjoint ∘L
            pair.left.adjoint)) := by
    funext n
    exact hcycle n
  rw [hsequence]
  exact hcycled

/-!
The generic transfer now has its concrete P1 consumer: the source-band
response is represented by the already-owned three-branch pair.  The caller
only has to establish the doubled-cutoff strong convergence for its chosen
source compression; the endpoint and trace pairing stay fixed.
-/
set_option maxHeartbeats 1000000 in
-- Instantiating the same-basis transfer through the three-branch owner needs it.
theorem tendsto_ordinaryTraceAlong_sourceBandGramResponse_sandwich
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ιr κr τr ν μ ρ : Type*}
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
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    (cutoff : ℕ → sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda)
    (limitCutoff : sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda)
    (doubleBound : ℝ) (hdoubleBound_nonneg : 0 ≤ doubleBound)
    (hdouble_norm : ∀ n,
      ‖cutoff n ∘L (cutoff n).adjoint‖ ≤ doubleBound)
    (hdouble_tendsto : ∀ x,
      Tendsto (fun n => cutoff n ((cutoff n).adjoint x)) atTop
        (𝓝 (limitCutoff (limitCutoff.adjoint x)))) :
    Tendsto
      (fun n => ordinaryTraceAlong sourceBasis
        ((cutoff n).adjoint ∘L sourceBandGramResponse owner lambda family ∘L cutoff n))
      atTop
      (𝓝 (ordinaryTraceAlong sourceBasis
        (limitCutoff.adjoint ∘L sourceBandGramResponse owner lambda family ∘L
          limitCutoff))) := by
  let pair := sourceThreeBranchSourcePairData owner lambda family a c hac hsupp
    negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
    sourceBasis hfactor
  have hpair : pair.traceProduct = sourceBandGramResponse owner lambda family := by
    exact sourceThreeBranchSourcePairData_traceProduct_eq owner lambda family
      a c hac hsupp negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
      sourceBasis hfactor
  have hgeneric := tendsto_ordinaryTraceAlong_pairSandwich_of_strong
    sourceBasis boundaryBasis pair cutoff limitCutoff doubleBound
    hdoubleBound_nonneg hdouble_norm hdouble_tendsto
  have hsequence :
      (fun n => ordinaryTraceAlong sourceBasis
        ((pair.boundedSandwich boundaryBasis (cutoff n).adjoint (cutoff n)).traceProduct)) =
      (fun n => ordinaryTraceAlong sourceBasis
        ((cutoff n).adjoint ∘L sourceBandGramResponse owner lambda family ∘L cutoff n)) := by
    funext n
    rw [pair.boundedSandwich_traceProduct_eq boundaryBasis
      (cutoff n).adjoint (cutoff n)]
    rw [hpair]
  have hlimit :
      ordinaryTraceAlong sourceBasis
        ((pair.boundedSandwich boundaryBasis limitCutoff.adjoint
          limitCutoff).traceProduct) =
      ordinaryTraceAlong sourceBasis
        (limitCutoff.adjoint ∘L sourceBandGramResponse owner lambda family ∘L
          limitCutoff) := by
    rw [pair.boundedSandwich_traceProduct_eq boundaryBasis
      limitCutoff.adjoint limitCutoff, hpair]
  rw [← hsequence, ← hlimit]
  exact hgeneric

end Dev
end ConnesWeilRH
