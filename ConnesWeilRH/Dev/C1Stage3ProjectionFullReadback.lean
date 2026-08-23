/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1Stage3QwReadback
import ConnesWeilRH.Dev.C1Stage3ProjectionResponseBridge

/-!
# C1 Stage-3 projection full readback

The active `qw` readback already expresses the Weil value through the
projection-response trace.  The finite-window bridge expresses the same
response as the positive cutoff trace minus the two explicit window defects.
This module combines those two identities into one owner-preserving formula.

The result is deliberately an exact ledger only.  The arithmetic residual,
`D₁` insertion defect, and `D₂` window-to-response defect remain visible; no
defect limit, positivity shortcut, or RH conclusion is inferred.
-/

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace C1Stage3ProjectionFullReadback

open CC20Concrete
open CC20Concrete.PositiveTrace
open CCM25Concrete.CompactLogConvolution
open CCM25Concrete.SelectedWeilSquare
open C1CrossingCommonCarrier
open C1CrossingEulerLogReadback
open C1Stage3ProjectionResponseBridge
open C1Stage3ProjectionTraceLedger
open C1Stage3QwReadback
open MeasureTheory
open scoped InnerProduct InnerProductSpace BigOperators

noncomputable section

/-! ### Gate-2 exact finite-window owner ledger -/

/-- The same-owner Weil value reads back through the finite-window positive
trace, with every unresolved term retained explicitly:

```text
qw g = pole(g⋆g) − arch(g⋆g) − Re Tr(cutoff pair)
       + Re Tr(same-object residual)
       + Re Tr(D₁) + Re Tr(D₂).
```

This is the finite-window form of the Gate-2 ledger.  It is an algebraic
identity; the three displayed trace corrections still require separate
analysis before any limit can be taken. -/
theorem stage3ProjectionFullReadback_qw_eq_pole_sub_arch_sub_trace_add_defects
    (g : CompactLogTest)
    (a c : ℝ) (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime)
    (data : CrossingCommonCarrierData g.test g.test.continuous a c
      (canonicalCrossingLengthSet
        (SelectedWeilSquareOwner.ofCompactLogTest g)))
    (hsupp : Function.support g.test ⊆ Set.Icc a c)
    {iota kappa nu : Type*}
    (fullBasis : HilbertBasis iota ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryFullInputInterval a c))))
    (outputBasis : HilbertBasis kappa ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis nu ℂ cc20GlobalLogCrossingL2)
    (basisData : ∀ pm : {pm // pm ∈ canonicalPrimePowerTerms
        (SelectedWeilSquareOwner.ofCompactLogTest g)},
      GlobalPrimePowerTraceBasisData a c pm.1.1 pm.1.2)
    (hresponse : IsTraceClassAlong globalBasis
      (projectionResponse (SelectedWeilSquareOwner.ofCompactLogTest g)
        lambda S)) :
    C1SameOwnerWeil.qw g =
      (SelectedWeilSquareOwner.ofCompactLogTest g).poleTerm.re -
        (SelectedWeilSquareOwner.ofCompactLogTest g).archimedeanTerm.re -
        (ordinaryTraceAlong globalBasis
          (fullBoundaryProjectionPairData g a c lambda S
            fullBasis outputBasis globalBasis).traceProduct).re +
        (ordinaryTraceAlong globalBasis
          (sameObjectResidual
            (SelectedWeilSquareOwner.ofCompactLogTest g) lambda S
            (canonicalPrimePowerTerms
              (SelectedWeilSquareOwner.ofCompactLogTest g)))).re +
        (ordinaryTraceAlong globalBasis
          (kernelInsertionSandwich g a c lambda S)).re +
        (ordinaryTraceAlong globalBasis
          (windowToResponseDefect
            (SelectedWeilSquareOwner.ofCompactLogTest g) a c lambda S)).re := by
  have hqw := stage3QwReadback_qw_eq_pole_sub_arch_sub_response_add_residual
    g a c lambda S data hsupp globalBasis basisData hresponse
  have htrace :=
    ordinaryTraceAlong_fullBoundaryProjectionPairData_eq_projectionResponse_add_defects
      (SelectedWeilSquareOwner.ofCompactLogTest g) a c lambda S
      fullBasis outputBasis globalBasis hresponse
  have htraceReal := congrArg Complex.re htrace
  have htraceReal' :
      (ordinaryTraceAlong globalBasis
        (fullBoundaryProjectionPairData g a c lambda S
          fullBasis outputBasis globalBasis).traceProduct).re =
        (ordinaryTraceAlong globalBasis
          (projectionResponse (SelectedWeilSquareOwner.ofCompactLogTest g)
            lambda S)).re +
          (ordinaryTraceAlong globalBasis
            (kernelInsertionSandwich g a c lambda S)).re +
          (ordinaryTraceAlong globalBasis
            (windowToResponseDefect
              (SelectedWeilSquareOwner.ofCompactLogTest g) a c lambda S)).re := by
    simpa only [Complex.add_re] using htraceReal
  linarith [hqw, htraceReal']

/-! ### Axiom audit -/

#print axioms stage3ProjectionFullReadback_qw_eq_pole_sub_arch_sub_trace_add_defects

end
end C1Stage3ProjectionFullReadback
end Dev
end Source
end ConnesWeilRH
