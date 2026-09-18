/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3RadialBoundarySupportIdentity

/-!
# Finite-window energy for the selected root

The source carrier has only a lower radial support condition; it is not a
compactly supported input space.  This leaf therefore records only the part
which genuinely follows from the continuous compact kernel: every finite
input/output window of the selected root is Hilbert--Schmidt, and this remains
true after precomposition with the actual source inclusion.  The missing
internal-gap estimate is the tail beyond these windows and is not hidden in
this statement.
-/

namespace ConnesWeilRH
namespace Dev

open MeasureTheory
open Source.CC20Concrete
open Source.CC20Concrete.CompactRootHalfLinePair
open Source.CC20Concrete.ContinuousKernelHilbertSchmidt
open Source.CC20Concrete.PositiveTrace
open Source.CCM25Concrete
open Source.CCM25Concrete.CCM24FiniteSGramResponse
open Source.CCM25Concrete.CCM24FiniteSProjectionTrace
open Source.CCM25Concrete.SelectedCrossingOperatorBridge
open Source.CCM25Concrete.SelectedWeilSquare
open scoped InnerProduct InnerProductSpace

noncomputable local instance compactRootWindowSourceCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- The complete compact-window root factor has square-summable columns on
any named basis of the ambient logarithmic carrier. -/
theorem selectedRoot_fullWindowFactor_basis_normSq_summable
    (owner : SelectedWeilSquareOwner) (a c : ℝ)
    {κ τ ν : Type*}
    (inputBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryFullInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier) :
    Summable fun i : ν =>
      ‖fullBoundaryRootFactor owner.sourceTest a c (globalBasis i)‖ ^ 2 := by
  let kernel := fullBoundaryRootKernel owner.sourceTest a c
  let kernelOperator := ContinuousKernelHilbertSchmidt.operator
    (volume : Measure (BoundaryFullInputInterval a c))
    (volume : Measure (BoundaryOutputInterval a c)) kernel
  have hkernel : Summable fun i : κ =>
      ‖kernelOperator (inputBasis i)‖ ^ 2 := by
    exact ContinuousKernelHilbertSchmidt.basis_normSq_summable
      (volume : Measure (BoundaryFullInputInterval a c))
      (volume : Measure (BoundaryOutputInterval a c)) kernel inputBasis
  let restrictedInput :=
    globalL2ToKernelInterval (a - c) (c - a) 0
      ∘L ContinuousLinearMap.id ℂ finiteSCarrier
  have hrestricted : Summable fun i : ν =>
      ‖(kernelOperator ∘L restrictedInput) (globalBasis i)‖ ^ 2 := by
    exact PositiveTrace.summable_normSq_precomp inputBasis outputBasis
      globalBasis kernelOperator restrictedInput hkernel
  simpa only [kernel, kernelOperator, restrictedInput, fullBoundaryRootFactor,
    ContinuousLinearMap.comp_assoc] using hrestricted

/-- The same finite-window estimate after inserting the actual source
inclusion.  This is the usable source-side form of the compact-kernel fact. -/
theorem selectedRoot_fullWindowFactor_sourceBasis_normSq_summable
    (owner : SelectedWeilSquareOwner) (lambda : CCM24SoninScale)
    (a c : ℝ) {κ τ ρ : Type*}
    (inputBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryFullInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) :
    Summable fun i : ρ =>
      ‖fullBoundaryRootFactor owner.sourceTest a c
        (sourceInclusion lambda (sourceBasis i))‖ ^ 2 := by
  let kernel := fullBoundaryRootKernel owner.sourceTest a c
  let kernelOperator := ContinuousKernelHilbertSchmidt.operator
    (volume : Measure (BoundaryFullInputInterval a c))
    (volume : Measure (BoundaryOutputInterval a c)) kernel
  have hkernel : Summable fun i : κ =>
      ‖kernelOperator (inputBasis i)‖ ^ 2 := by
    exact ContinuousKernelHilbertSchmidt.basis_normSq_summable
      (volume : Measure (BoundaryFullInputInterval a c))
      (volume : Measure (BoundaryOutputInterval a c)) kernel inputBasis
  let restrictedInput :=
    globalL2ToKernelInterval (a - c) (c - a) 0 ∘L
      sourceInclusion lambda
  have hrestricted : Summable fun i : ρ =>
      ‖(kernelOperator ∘L restrictedInput) (sourceBasis i)‖ ^ 2 := by
    exact PositiveTrace.summable_normSq_precomp inputBasis outputBasis
      sourceBasis kernelOperator restrictedInput hkernel
  simpa only [kernel, kernelOperator, restrictedInput, fullBoundaryRootFactor,
    ContinuousLinearMap.comp_assoc] using hrestricted

end Dev
end ConnesWeilRH
