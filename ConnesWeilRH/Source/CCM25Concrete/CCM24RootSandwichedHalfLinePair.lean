/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.SelectedCrossingOperatorBridge
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSRootSandwichedMovingFlow
import ConnesWeilRH.Source.CC20Concrete.HilbertSchmidtIdeal

/-!
# A genuine root-sandwiched half-line crossing pair

The two global-to-compact source-window factors are Hilbert--Schmidt.  After
reflecting the compact test, their trace product is the literal operator
`C (I-E) U_b E C†`.  This is an operator identity, not only a cyclic trace
readback.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24RootSandwichedHalfLinePair

open MeasureTheory
open CC20Concrete
open SelectedCrossingKernel
open SelectedCrossingOperatorBridge
open CCM24FiniteSProjectionTrace
open CCM24FiniteSOrthogonalProjectionFlow
open CCM24FiniteSRootSandwichedMovingFlow
open _root_.ConnesWeilRH.CC20Concrete

local notation "H" => finiteSCarrier

/-- The two compact-source-window legs of the genuine root sandwich. -/
noncomputable def pairData
    (g : CompactLogConvolution.CompactLogTest)
    (a c b : ℝ)
    (hsupp : Function.support g.test ⊆ Set.Icc a c)
    {κ τ ν : Type*}
    (kernelBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (KernelInterval (-c) (-a) b))))
    (sourceBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (SourceInterval b))))
    (globalBasis : HilbertBasis ν ℂ H) :
    PositiveTrace.BasisHilbertSchmidtPairData
      (G := Lp ℂ 2 (volume : Measure (SourceInterval b))) globalBasis := by
  let reflected := g.involution
  let left := leftGlobalTranslatedConvolutionSourceOperator reflected b
  let right := rightGlobalConvolutionSourceOperator reflected b
  have hreflected : Function.support reflected.test ⊆ Set.Icc (-c) (-a) := by
    exact compactLogTest_involution_support_subset_reflected g a c hsupp
  have hleft : Summable fun j => ‖left (globalBasis j)‖ ^ 2 := by
    rw [show left = leftKernelGlobalRestrictionOperator
        reflected (-c) (-a) b by
      exact (leftKernelGlobalRestrictionOperator_eq_globalTranslatedConvolution
        reflected (-c) (-a) b hreflected).symm]
    exact PositiveTrace.summable_normSq_precomp
      kernelBasis sourceBasis globalBasis
      (ContinuousKernelHilbertSchmidt.operator
        (volume : Measure (KernelInterval (-c) (-a) b))
        (volume : Measure (SourceInterval b))
        (leftKernel reflected.test reflected.test.continuous
          (-c) (-a) b))
      (globalL2ToKernelInterval (-c) (-a) b)
      (ContinuousKernelHilbertSchmidt.basis_normSq_summable
        (volume : Measure (KernelInterval (-c) (-a) b))
        (volume : Measure (SourceInterval b))
        (leftKernel reflected.test reflected.test.continuous
          (-c) (-a) b) kernelBasis)
  have hright : Summable fun j => ‖right (globalBasis j)‖ ^ 2 := by
    rw [show right = rightKernelGlobalRestrictionOperator
        reflected (-c) (-a) b by
      exact (rightKernelGlobalRestrictionOperator_eq_globalConvolution
        reflected (-c) (-a) b hreflected).symm]
    exact PositiveTrace.summable_normSq_precomp
      kernelBasis sourceBasis globalBasis
      (ContinuousKernelHilbertSchmidt.operator
        (volume : Measure (KernelInterval (-c) (-a) b))
        (volume : Measure (SourceInterval b))
        (rightKernel reflected.test reflected.test.continuous
          (-c) (-a) b))
      (globalL2ToKernelInterval (-c) (-a) b)
      (ContinuousKernelHilbertSchmidt.basis_normSq_summable
        (volume : Measure (KernelInterval (-c) (-a) b))
        (volume : Measure (SourceInterval b))
        (rightKernel reflected.test reflected.test.continuous
          (-c) (-a) b) kernelBasis)
  exact
    { left := left
      right := right
      left_summable_normSq := hleft
      right_summable_normSq := hright }

theorem projectionLeftCrossing_positiveHalfLine_translation
    (b : ℝ) :
    projectionLeftCrossing cc20PositiveHalfLineProjection
        (cc20GlobalLogTranslation b).toContinuousLinearMap =
      cc20SingleCrossingOperator b := by
  rfl

/-- The compact pair owns the actual root-sandwiched crossing, with the roots
in the route order `C (...) C†`. -/
theorem pairData_traceProduct_eq_rootSandwichedCrossing
    (g : CompactLogConvolution.CompactLogTest)
    (a c b : ℝ)
    (hsupp : Function.support g.test ⊆ Set.Icc a c)
    (hb : 0 ≤ b)
    {κ τ ν : Type*}
    (kernelBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (KernelInterval (-c) (-a) b))))
    (sourceBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (SourceInterval b))))
    (globalBasis : HilbertBasis ν ℂ H) :
    (pairData g a c b hsupp kernelBasis sourceBasis globalBasis).traceProduct =
      rootSandwichedLeftCrossing
        (cc20GlobalLogConvolution g.involution.test)
        cc20PositiveHalfLineProjection
        (cc20GlobalLogTranslation b).toContinuousLinearMap := by
  dsimp only [pairData, PositiveTrace.BasisHilbertSchmidtPairData.traceProduct]
  rw [leftGlobalTranslatedConvolutionSourceOperator_eq]
  unfold rightGlobalConvolutionSourceOperator
  rw [ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_comp,
    cc20GlobalLogTranslation_neg_adjoint]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply]
  rw [compactLogTest_involution_involution_test]
  rw [← globalLogConvolution_involution_eq_adjoint g]
  have hsource := congrArg
    (fun T : H →L[ℂ] H =>
      T (cc20GlobalLogConvolution g.test u))
    (globalL2ToSourceInterval_adjoint_comp b)
  simp only [ContinuousLinearMap.comp_apply] at hsource
  rw [hsource]
  have hboundary := congrArg
    (fun T : H →L[ℂ] H =>
      T (cc20GlobalLogConvolution g.test u))
    (globalBoundaryTranslationProjection_eq_singleCrossingOperator b hb)
  simp only [globalBoundaryTranslationProjection_apply] at hboundary
  change cc20GlobalLogConvolution g.involution.test
      (cc20GlobalLogTranslation b
        (sourceWindowProjection b
          (cc20GlobalLogConvolution g.test u))) = _
  rw [hboundary]
  unfold rootSandwichedLeftCrossing
  rw [projectionLeftCrossing_positiveHalfLine_translation]
  rw [adjoint_globalLogConvolution_involution]
  simp only [ContinuousLinearMap.comp_apply]

theorem rootSandwichedHalfLineCrossing_isTraceClassAlong
    (g : CompactLogConvolution.CompactLogTest)
    (a c b : ℝ)
    (hsupp : Function.support g.test ⊆ Set.Icc a c)
    (hb : 0 ≤ b)
    {κ τ ν : Type*}
    (kernelBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (KernelInterval (-c) (-a) b))))
    (sourceBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (SourceInterval b))))
    (globalBasis : HilbertBasis ν ℂ H) :
    PositiveTrace.IsTraceClassAlong globalBasis
      (rootSandwichedLeftCrossing
        (cc20GlobalLogConvolution g.involution.test)
        cc20PositiveHalfLineProjection
        (cc20GlobalLogTranslation b).toContinuousLinearMap) := by
  rw [← pairData_traceProduct_eq_rootSandwichedCrossing g a c b hsupp hb
    kernelBasis sourceBasis globalBasis]
  exact (pairData g a c b hsupp kernelBasis sourceBasis globalBasis)
    |>.traceProduct_isTraceClassAlong

end CCM24RootSandwichedHalfLinePair
end CCM25Concrete
end Source
end ConnesWeilRH
