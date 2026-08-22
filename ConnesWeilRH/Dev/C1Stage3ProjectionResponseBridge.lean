/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1Stage3ProjectionWindow
import ConnesWeilRH.Dev.C1Stage3ProjectionTraceLedger
import ConnesWeilRH.Dev.C1Stage3CarrierReadback

/-!
# C1 Stage-3 projection response bridge

The finite-window sandwich and the existing projection response are not
definitionally the same operator.  This module records the exact gap instead
of identifying them by their common carrier type.

For an output zero-extension `Z`, a root factor `F`, and the positive Stage-3
kernel `K_S`, the finite-window owner is

```text
  (Z F)† K_S (Z F) = F† (Z† K_S Z) F.
```

Splitting the compressed kernel as `I + (Z† K_S Z - I)` gives

```text
  (Z F)† K_S (Z F)
    = windowedDetector + kernelInsertionSandwich.
```

The active projection ledger uses a different response, so the remaining
window-to-response defect is kept as a second explicit term:

```text
  finiteWindowSandwich
    = projectionResponse + kernelInsertionSandwich + windowToResponseDefect.
```

These are exact operator and named-basis trace identities.  No defect is
declared to vanish, and no `qw` or RH conclusion is inferred.
-/

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace C1Stage3ProjectionResponseBridge

open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open CC20Concrete.PositiveTrace
open C1Stage3ProjectionKernel
open C1Stage3ProjectionTraceLedger
open C1Stage3ProjectionWindow
open C1Stage3CarrierReadback
open C1PositiveTraceWindowProducer
open C1CrossingCommonCarrier
open C1CrossingEulerLogReadback
open CCM25Concrete.SelectedCrossingOperatorBridge
open CCM25Concrete.SelectedWeilSquare
open MeasureTheory

noncomputable section

abbrev projectionCarrier := cc20GlobalLogCrossingL2

/-! ### The output-compressed kernel -/

/-- The Stage-3 kernel compressed to the finite output window. -/
noncomputable def outputCompressedStage3Kernel
    (a c : ℝ) (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c)) :=
  (fullBoundaryOutputZeroExtension a c).adjoint ∘L
      stage3ProjectionKernel lambda S ∘L
        fullBoundaryOutputZeroExtension a c

theorem outputCompressedStage3Kernel_isPositive
    (a c : ℝ) (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    (outputCompressedStage3Kernel a c lambda S).IsPositive := by
  exact ContinuousLinearMap.IsPositive.adjoint_conj
    (stage3ProjectionKernel_isPositive lambda S)
    (fullBoundaryOutputZeroExtension a c)

/-- The part left after removing the identity compression from the output
window.  It is a data-bearing defect, not an assumed small remainder. -/
noncomputable def kernelInsertionDefect
    (a c : ℝ) (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c)) :=
  outputCompressedStage3Kernel a c lambda S -
    ContinuousLinearMap.id ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c)))

/-- The root-factor sandwich of the output-compression defect. -/
noncomputable def kernelInsertionSandwich
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest)
    (a c : ℝ) (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    projectionCarrier →L[ℂ] projectionCarrier :=
  (fullBoundaryRootFactor g a c).adjoint ∘L
      kernelInsertionDefect a c lambda S ∘L
        fullBoundaryRootFactor g a c

/-! ### Exact finite-window identities -/

/-- The finite-window trace-product owner is exactly the root factor wrapped
around the output-compressed Stage-3 kernel. -/
theorem fullBoundaryProjectionPairData_traceProduct_eq_outputCompressed
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest) (a c : ℝ)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime)
    {iota kappa nu : Type*}
    (fullBasis : HilbertBasis iota ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryFullInputInterval a c))))
    (outputBasis : HilbertBasis kappa ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis nu ℂ projectionCarrier) :
    (fullBoundaryProjectionPairData g a c lambda S fullBasis outputBasis
        globalBasis).traceProduct =
      (fullBoundaryRootFactor g a c).adjoint ∘L
        outputCompressedStage3Kernel a c lambda S ∘L
          fullBoundaryRootFactor g a c := by
  rw [fullBoundaryProjectionPairData,
    kernelSandwichPairData_traceProduct_eq]
  unfold fullBoundaryPositiveOperator outputCompressedStage3Kernel
  rw [ContinuousLinearMap.adjoint_comp]
  simp only [ContinuousLinearMap.comp_assoc]

/-- Splitting the compressed kernel into identity plus its insertion defect
gives the exact detector-plus-defect decomposition. -/
theorem fullBoundaryProjectionPairData_traceProduct_eq_detector_add_kernelInsertion
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest) (a c : ℝ)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime)
    {iota kappa nu : Type*}
    (fullBasis : HilbertBasis iota ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryFullInputInterval a c))))
    (outputBasis : HilbertBasis kappa ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis nu ℂ projectionCarrier) :
    (fullBoundaryProjectionPairData g a c lambda S fullBasis outputBasis
        globalBasis).traceProduct =
      windowedBoundaryDetector g a c +
        kernelInsertionSandwich g a c lambda S := by
  rw [fullBoundaryProjectionPairData_traceProduct_eq_outputCompressed
    g a c lambda S fullBasis outputBasis globalBasis]
  unfold kernelInsertionSandwich kernelInsertionDefect
    windowedBoundaryDetector
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, map_sub]
  abel

/-! ### Trace-class consequences -/

theorem windowedBoundaryDetector_isTraceClassAlong
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest) (a c : ℝ)
    {iota kappa nu : Type*}
    (fullBasis : HilbertBasis iota ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryFullInputInterval a c))))
    (outputBasis : HilbertBasis kappa ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis nu ℂ projectionCarrier) :
    IsTraceClassAlong globalBasis (windowedBoundaryDetector g a c) := by
  rw [← fullBoundaryPositivePairData_traceProduct_eq_detector
    g a c fullBasis outputBasis globalBasis]
  exact fullBoundaryPositivePairData_traceProduct_isTraceClass
    g a c fullBasis outputBasis globalBasis

theorem kernelInsertionSandwich_isTraceClassAlong
    (g : CCM25Concrete.CompactLogConvolution.CompactLogTest) (a c : ℝ)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime)
    {iota kappa nu : Type*}
    (fullBasis : HilbertBasis iota ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryFullInputInterval a c))))
    (outputBasis : HilbertBasis kappa ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis nu ℂ projectionCarrier) :
    IsTraceClassAlong globalBasis (kernelInsertionSandwich g a c lambda S) := by
  have hdiff := isTraceClassAlong_sub globalBasis
    ((fullBoundaryProjectionPairData g a c lambda S fullBasis outputBasis
      globalBasis).traceProduct)
    (windowedBoundaryDetector g a c)
    (fullBoundaryProjectionPairData_traceProduct_isTraceClassAlong
      g a c lambda S fullBasis outputBasis globalBasis)
    (windowedBoundaryDetector_isTraceClassAlong
      g a c fullBasis outputBasis globalBasis)
  have hident :=
    fullBoundaryProjectionPairData_traceProduct_eq_detector_add_kernelInsertion
      g a c lambda S fullBasis outputBasis globalBasis
  rw [hident] at hdiff
  simpa only [add_sub_cancel_left] using hdiff

/-! ### The second, owner-preserving response defect -/

/-- Difference between the finite-window detector and the active projection
response for the same selected Weil-square owner. -/
noncomputable def windowToResponseDefect
    (owner : SelectedWeilSquareOwner) (a c : ℝ)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    projectionCarrier →L[ℂ] projectionCarrier :=
  windowedBoundaryDetector owner.sourceTest a c -
    projectionResponse owner lambda S

theorem windowToResponseDefect_isTraceClassAlong
    (owner : SelectedWeilSquareOwner) (a c : ℝ)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime)
    {iota kappa nu : Type*}
    (globalBasis : HilbertBasis nu ℂ projectionCarrier)
    (fullBasis : HilbertBasis iota ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryFullInputInterval a c))))
    (outputBasis : HilbertBasis kappa ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (hresponse : IsTraceClassAlong globalBasis
      (projectionResponse owner lambda S)) :
    IsTraceClassAlong globalBasis
      (windowToResponseDefect owner a c lambda S) := by
  unfold windowToResponseDefect
  exact isTraceClassAlong_sub globalBasis _ _
    (windowedBoundaryDetector_isTraceClassAlong
      owner.sourceTest a c fullBasis outputBasis globalBasis)
    hresponse

/-- Exact three-term operator bridge.  The two defects are retained as named
owners, so this theorem does not silently identify the window sandwich with
the projection response. -/
theorem fullBoundaryProjectionPairData_traceProduct_eq_projectionResponse_add_defects
    (owner : SelectedWeilSquareOwner) (a c : ℝ)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime)
    {iota kappa nu : Type*}
    (fullBasis : HilbertBasis iota ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryFullInputInterval a c))))
    (outputBasis : HilbertBasis kappa ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis nu ℂ projectionCarrier) :
    (fullBoundaryProjectionPairData owner.sourceTest a c lambda S
        fullBasis outputBasis globalBasis).traceProduct =
      projectionResponse owner lambda S +
        kernelInsertionSandwich owner.sourceTest a c lambda S +
        windowToResponseDefect owner a c lambda S := by
  rw [fullBoundaryProjectionPairData_traceProduct_eq_detector_add_kernelInsertion
    owner.sourceTest a c lambda S fullBasis outputBasis globalBasis]
  unfold windowToResponseDefect
  abel

/-- Named-basis trace ledger for the same three owners.  It is conditional only
on trace legality of the active projection response; no limit or sign premise
is consumed. -/
theorem ordinaryTraceAlong_fullBoundaryProjectionPairData_eq_projectionResponse_add_defects
    (owner : SelectedWeilSquareOwner) (a c : ℝ)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime)
    {iota kappa nu : Type*}
    (fullBasis : HilbertBasis iota ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryFullInputInterval a c))))
    (outputBasis : HilbertBasis kappa ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis nu ℂ projectionCarrier)
    (hresponse : IsTraceClassAlong globalBasis
      (projectionResponse owner lambda S)) :
    ordinaryTraceAlong globalBasis
        (fullBoundaryProjectionPairData owner.sourceTest a c lambda S
          fullBasis outputBasis globalBasis).traceProduct =
      ordinaryTraceAlong globalBasis (projectionResponse owner lambda S) +
        ordinaryTraceAlong globalBasis
          (kernelInsertionSandwich owner.sourceTest a c lambda S) +
        ordinaryTraceAlong globalBasis
          (windowToResponseDefect owner a c lambda S) := by
  rw [fullBoundaryProjectionPairData_traceProduct_eq_projectionResponse_add_defects
    owner a c lambda S fullBasis outputBasis globalBasis]
  have hinsertion := kernelInsertionSandwich_isTraceClassAlong
    owner.sourceTest a c lambda S fullBasis outputBasis globalBasis
  have hwindow := windowToResponseDefect_isTraceClassAlong
    owner a c lambda S globalBasis
    fullBasis outputBasis hresponse
  have hsum := isTraceClassAlong_add globalBasis
    (projectionResponse owner lambda S)
    (kernelInsertionSandwich owner.sourceTest a c lambda S)
    hresponse hinsertion
  rw [ordinaryTraceAlong_add globalBasis _ _ hsum hwindow]
  rw [ordinaryTraceAlong_add globalBasis _ _ hresponse hinsertion]

/-! ### Arithmetic readback with the two explicit bridge defects -/

/-- The active Stage-2 arithmetic readback can be attached to the finite-window
projection owner without erasing either operator defect.  This is the current
Gate-2 endpoint for this bridge: the selected finite arithmetic scalar is
isolated, while the same-object residual and both window defects remain
explicit real traces. -/
theorem realTrace_fullBoundaryProjectionPairData_eq_selectedArithmetic_add_defects
    (owner : SelectedWeilSquareOwner) (a c : ℝ)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime)
    (data : CrossingCommonCarrierData owner.sourceTest.test
      owner.sourceTest.test.continuous a c (canonicalCrossingLengthSet owner))
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {iota kappa nu : Type*}
    (fullBasis : HilbertBasis iota ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryFullInputInterval a c))))
    (outputBasis : HilbertBasis kappa ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis nu ℂ projectionCarrier)
    (basisData : ∀ pm : {pm // pm ∈ canonicalPrimePowerTerms owner},
      GlobalPrimePowerTraceBasisData a c pm.1.1 pm.1.2)
    (hresponse : IsTraceClassAlong globalBasis
      (projectionResponse owner lambda S)) :
    (ordinaryTraceAlong globalBasis
      (fullBoundaryProjectionPairData owner.sourceTest a c lambda S
        fullBasis outputBasis globalBasis).traceProduct).re =
      selectedArithmeticCarrierSum owner +
        (ordinaryTraceAlong globalBasis
          (sameObjectResidual owner lambda S
            (canonicalPrimePowerTerms owner))).re +
        (ordinaryTraceAlong globalBasis
          (kernelInsertionSandwich owner.sourceTest a c lambda S)).re +
        (ordinaryTraceAlong globalBasis
          (windowToResponseDefect owner a c lambda S)).re := by
  have htrace :=
    ordinaryTraceAlong_fullBoundaryProjectionPairData_eq_projectionResponse_add_defects
      owner a c lambda S fullBasis outputBasis globalBasis hresponse
  have hreal := congrArg Complex.re htrace
  have hreal' :
      (ordinaryTraceAlong globalBasis
        (fullBoundaryProjectionPairData owner.sourceTest a c lambda S
          fullBasis outputBasis globalBasis).traceProduct).re =
        (ordinaryTraceAlong globalBasis (projectionResponse owner lambda S)).re +
          (ordinaryTraceAlong globalBasis
            (kernelInsertionSandwich owner.sourceTest a c lambda S)).re +
          (ordinaryTraceAlong globalBasis
            (windowToResponseDefect owner a c lambda S)).re := by
    simpa only [Complex.add_re] using hreal
  rw [hreal']
  rw [stage3CarrierReadback_arithmetic_eq_selectedRealSum_residual
    owner a c lambda S data hsupp globalBasis basisData hresponse]

end
end C1Stage3ProjectionResponseBridge
end Dev
end Source
end ConnesWeilRH
