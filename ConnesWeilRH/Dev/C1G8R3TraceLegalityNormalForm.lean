/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24SourceProlateTrace

/-!
# R3 trace-legality normal form

The radial compact-root transport already discharges the two outer branches
of the source ledger.  This leaf records the converse as well as the forward
implication: trace legality of the complete three-branch commutator is
equivalent to trace legality of the coupled second-support/prolate remainder.

This is an analytic normal form for R3, not a sign theorem and not an RH
conclusion.  In particular, it does not assume `qw`, `SourceRH`, or any
healthy-detector proposition.
-/

namespace ConnesWeilRH
namespace Source
namespace C1G8R3TraceLegalityNormalForm

open MeasureTheory
open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open CCM25Concrete
open CCM25Concrete.CCM24FiniteSProjectionTrace
open CCM25Concrete.CCM24RadialBoundaryPairTransport
open CCM25Concrete.CCM24SourceProlateTrace

noncomputable section

theorem sourceThreeBranchCommutator_isTraceClassAlong_iff_remainder
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier) :
    PositiveTrace.IsTraceClassAlong globalBasis
        (cc20ThreeBranchCommutator (radialSupportProjection lambda)
          (sourceFourierSupportProjection lambda)
          (sourceProlateRemainder lambda) (detectorOperator owner)) ↔
      PositiveTrace.IsTraceClassAlong globalBasis
        (sourceSecondSupportProlateRemainder owner lambda) := by
  constructor
  · intro htotal
    have houter := sourceOuterCommutatorPair_isTraceClassAlong
      owner lambda a c hac hsupp negativeBasis positiveBasis outputBasis
        globalBasis
    have hdecomp := sourceThreeBranchCommutator_eq_outerPair_add_remainder
      owner lambda
    have hrewrite : sourceSecondSupportProlateRemainder owner lambda =
        cc20ThreeBranchCommutator (radialSupportProjection lambda)
            (sourceFourierSupportProjection lambda)
            (sourceProlateRemainder lambda) (detectorOperator owner) -
          (cc20OuterCommutatorBranch (radialSupportProjection lambda)
            (sourceFourierSupportProjection lambda) (detectorOperator owner) +
            cc20ReflectedOuterCommutatorBranch
              (radialSupportProjection lambda)
              (sourceFourierSupportProjection lambda)
              (detectorOperator owner)) := by
      rw [hdecomp]
      apply ContinuousLinearMap.ext
      intro u
      simp only [ContinuousLinearMap.add_apply,
        ContinuousLinearMap.sub_apply]
      abel
    rw [hrewrite]
    exact CCM24FiniteSProjectionTrace.PositiveTrace.isTraceClassAlong_sub
      globalBasis _ _ htotal houter
  · intro hrem
    exact sourceThreeBranchCommutator_isTraceClassAlong_of_remainder
      owner lambda a c hac hsupp negativeBasis positiveBasis outputBasis
        globalBasis hrem

end
end C1G8R3TraceLegalityNormalForm
end Source
end ConnesWeilRH
