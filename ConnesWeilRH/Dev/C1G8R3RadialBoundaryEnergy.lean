/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3RadialBoundarySupportIdentity
import ConnesWeilRH.Source.CC20Concrete.HilbertSchmidtIdeal

/-!
# Source-basis energy of the finite radial root boundary

The compact-output root factor is a continuous-kernel Hilbert--Schmidt
operator on its finite input and output windows. This file transfers that
square-summability through the actual source inclusion and radial translation.
-/

namespace ConnesWeilRH
namespace Dev

open MeasureTheory
open Source.CC20Concrete
open Source.CC20Concrete.CompactConvolutionSupport
open Source.CC20Concrete.ContinuousKernelHilbertSchmidt
open Source.CC20Concrete.PositiveTrace
open Source.CCM25Concrete
open Source.CCM25Concrete.CCM24FiniteSGramResponse
open Source.CCM25Concrete.CCM24FiniteSCommonBoundaryPair
open Source.CCM25Concrete.CCM24FiniteSProjectionTrace
open Source.CCM25Concrete.CCM24FiniteSBandTrace
open Source.CCM25Concrete.CCM24RadialBoundaryPairTransport
open Source.CCM25Concrete.SelectedCrossingOperatorBridge
open Source.CCM25Concrete.SelectedWeilSquare
open scoped InnerProduct InnerProductSpace

set_option maxHeartbeats 1000000

noncomputable local instance radialBoundaryEnergySoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- The finite-window zero-boundary crossing has square-summable columns on
any named basis of the ambient logarithmic carrier. -/
theorem selectedRootBoundaryWindowOperator_basis_normSq_summable
    (owner : SelectedWeilSquareOwner)
    {κ τ ν : Type*}
    (inputBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure
        (CompactInputInterval
          (-selectedRootSupportRadius owner)
          (selectedRootSupportRadius owner)
          (-selectedRootSupportRadius owner) 0))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure
        (CompactOutputInterval (-selectedRootSupportRadius owner) 0))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier) :
    Summable fun i : ν =>
      ‖selectedRootBoundaryWindowOperator owner (globalBasis i)‖ ^ 2 := by
  let radius := selectedRootSupportRadius owner
  let kernel := compactOutputRootKernel owner.sourceTest (-radius) radius
    (-radius) 0
  let kernelOperator := ContinuousKernelHilbertSchmidt.operator
    (volume : Measure (CompactInputInterval (-radius) radius (-radius) 0))
    (volume : Measure (CompactOutputInterval (-radius) 0)) kernel
  have hkernel : Summable fun i : κ =>
      ‖kernelOperator (inputBasis i)‖ ^ 2 := by
    exact ContinuousKernelHilbertSchmidt.basis_normSq_summable
      (volume : Measure (CompactInputInterval (-radius) radius (-radius) 0))
      (volume : Measure (CompactOutputInterval (-radius) 0)) kernel inputBasis
  let restrictedInput :=
    globalL2ToKernelInterval ((-radius) + (-radius)) (0 + radius) 0 ∘L
      cc20PositiveHalfLineProjection
  have hrestricted : Summable fun i : ν =>
      ‖(kernelOperator ∘L restrictedInput) (globalBasis i)‖ ^ 2 := by
    exact PositiveTrace.summable_normSq_precomp inputBasis outputBasis
      globalBasis kernelOperator restrictedInput hkernel
  have hextended : Summable fun i : ν =>
      ‖(kernelIntervalL2ZeroExtension (-radius) 0 0 ∘L
          (kernelOperator ∘L restrictedInput)) (globalBasis i)‖ ^ 2 := by
    exact PositiveTrace.summable_normSq_postcomp globalBasis
      (kernelOperator ∘L restrictedInput)
      (kernelIntervalL2ZeroExtension (-radius) 0 0) hrestricted
  simpa only [radius, kernel, kernelOperator, restrictedInput,
    selectedRootBoundaryWindowOperator,
    selectedRootBoundaryWindowFactor, compactOutputRootFactor,
    ContinuousLinearMap.comp_assoc] using hextended

/-- At every selected radial scale, the actual source-inclusion boundary
channel has square-summable columns on the named source basis. -/
theorem selectedRoot_radialBoundary_sourceBasis_normSq_summable
    (owner : SelectedWeilSquareOwner) (lambda : CCM24SoninScale)
    {ρ κ τ ν : Type*}
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda))
    (inputBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure
        (CompactInputInterval
          (-selectedRootSupportRadius owner)
          (selectedRootSupportRadius owner)
          (-selectedRootSupportRadius owner) 0))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure
        (CompactOutputInterval (-selectedRootSupportRadius owner) 0))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier) :
    Summable fun i : ρ =>
      ‖((ContinuousLinearMap.id ℂ finiteSCarrier -
          radialSupportProjection lambda) ∘L
          rootConvolution owner ∘L sourceInclusion lambda)
        (sourceBasis i)‖ ^ 2 := by
  let inputTranslation :=
    (cc20GlobalLogTranslation (Real.log lambda)).toContinuousLinearMap ∘L
      sourceInclusion lambda
  let window := selectedRootBoundaryWindowOperator owner
  have hwindow := selectedRootBoundaryWindowOperator_basis_normSq_summable
    owner inputBasis outputBasis globalBasis
  have hpre : Summable fun i : ρ =>
      ‖(window ∘L inputTranslation) (sourceBasis i)‖ ^ 2 :=
    PositiveTrace.summable_normSq_precomp globalBasis globalBasis sourceBasis
      window inputTranslation hwindow
  have hpost : Summable fun i : ρ =>
      ‖((cc20GlobalLogTranslation (-Real.log lambda)).toContinuousLinearMap ∘L
          (window ∘L inputTranslation)) (sourceBasis i)‖ ^ 2 :=
    PositiveTrace.summable_normSq_postcomp sourceBasis
      (window ∘L inputTranslation)
      (cc20GlobalLogTranslation (-Real.log lambda)).toContinuousLinearMap hpre
  rw [selectedRoot_radialSourceLeakage_eq_translatedFiniteWindow owner lambda]
  simpa only [inputTranslation, window, ContinuousLinearMap.comp_assoc]
    using hpost

end Dev
end ConnesWeilRH
