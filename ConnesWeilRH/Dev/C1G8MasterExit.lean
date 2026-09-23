/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.RHDefinition
import ConnesWeilRH.Source.CC20YoshidaNearZeros
import ConnesWeilRH.Dev.C1G8P4ReadbackSocketVacuity
import ConnesWeilRH.Dev.C1G8P3Contradiction
import ConnesWeilRH.Dev.C1G8R3SameOwnerGateNormalForm
import ConnesWeilRH.Dev.C1G8R3ActualEndpointTraceLimit
import ConnesWeilRH.Dev.C1G8AdjointShearGram
import ConnesWeilRH.Dev.C1G8R3AnnularMassConsumer
import ConnesWeilRH.Dev.C1G8R3SourceCompressedRootKernel
import ConnesWeilRH.Dev.C1HealthyYoshidaSpectralNegativity
import ConnesWeilRH.Dev.C1PinnedOrbitExit

/-!
# G8 Master Exit: Operator Trace & Annular Majorant to Mathlib RiemannHypothesis

This module formally connects the G8 noncommutative operator trace framework
and the S3 annular wing majorant directly to Mathlib's canonical `_root_.RiemannHypothesis`:

1. `sourceRH_of_right_g8SameOwnerReadbackData`:
   Exhibiting `G8SameOwnerReadbackData` for every hypothetical off-line zero directly
   implies `SourceRH`.
2. `riemannHypothesis_of_right_g8SameOwnerReadbackData`:
   Direct proof of Mathlib's `_root_.RiemannHypothesis` from `G8SameOwnerReadbackData`.
3. `riemannHypothesis_of_right_survivorCore_and_aggregateEq`:
   Reduces the exit to the survivor core square-sum (S3) and the endpoint trace equality (ρ5).
4. `riemannHypothesis_of_right_annular_wing_majorant_and_aggregateEq`:
   Reduces S3 to the two-sided annular wing majorant from the two-IBP / digamma page.

Axioms: strictly standard `[propext, Classical.choice, Quot.sound]`, zero `sorryAx`.
-/

set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace ConnesWeilRH
namespace Source
namespace C1G8MasterExit

open Filter
open MeasureTheory
open CC20Concrete
open CC20Concrete.PositiveTrace
open CC20Concrete.CompactRootHalfLinePair
open CC20YoshidaNearZeros
open CCM25Concrete
open CCM25Concrete.CCM24FiniteSBandTrace
open CCM25Concrete.CCM24FiniteSProjectionTrace
open CCM25Concrete.CCM24FiniteSGramResponse
open CCM25Concrete.SelectedWeilSquare
open C1G8AdjointShearGram
open C1G8P3Contradiction
open C1G8P4ReadbackSocketVacuity
open ConnesWeilRH.Dev
open C1HealthyYoshidaDetector
open C1HealthyYoshidaSpectralNegativity
open C1SameOwnerWeil

noncomputable local instance g8MasterExitCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- Master G8 Exit 1 (SourceRH): Exhibiting a valid `G8SameOwnerReadbackData` for every
    hypothetical right off-line zero proves `RHDefinitionBridge.standard.SourceRH`. -/
theorem sourceRH_of_right_g8SameOwnerReadbackData
    (hreadback : ∀ rho : sourceNontrivialZeroSet,
      (1 / 2 : Real) < rho.1.re →
        ∃ (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
          (lambda : CCM24SoninScale)
          (family : FinitePrimePowerFamily)
          (ν ρ : Type*)
          (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
          (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda))
          (_readback : G8SameOwnerReadbackData owner lambda family globalBasis sourceBasis),
          HealthyYoshidaDetectorData rho.1 owner.sourceTest) :
    RHDefinitionBridge.standard.SourceRH := by
  apply healthy_sourceRH_of_right_detector_specific_qw_nonneg
  intro rho hright
  obtain ⟨owner, lambda, family, ν, ρ_type, globalBasis, sourceBasis, readback, hdata⟩ :=
    hreadback rho hright
  refine ⟨owner.sourceTest, hdata, ?_⟩
  exact qw_nonnegative_of_g8SameOwnerReadbackData owner lambda family
    globalBasis sourceBasis readback

/-- Master G8 Exit 2 (Mathlib RH): Exhibiting a valid `G8SameOwnerReadbackData` for every
    hypothetical right off-line zero directly proves Mathlib's canonical `_root_.RiemannHypothesis`. -/
theorem riemannHypothesis_of_right_g8SameOwnerReadbackData
    (hreadback : ∀ rho : sourceNontrivialZeroSet,
      (1 / 2 : Real) < rho.1.re →
        ∃ (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
          (lambda : CCM24SoninScale)
          (family : FinitePrimePowerFamily)
          (ν ρ : Type*)
          (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
          (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda))
          (_readback : G8SameOwnerReadbackData owner lambda family globalBasis sourceBasis),
          HealthyYoshidaDetectorData rho.1 owner.sourceTest) :
    _root_.RiemannHypothesis := by
  exact RHDefinitionBridge.standard_source_rh_iff_mathlib.mp
    (sourceRH_of_right_g8SameOwnerReadbackData hreadback)

/-- Master G8 Exit 3 (Survivor Core & Aggregate Trace Equality):
    Deduces Mathlib's `_root_.RiemannHypothesis` from the S3 survivor core square-sum
    and the ρ5 aggregate endpoint trace equality. -/
theorem riemannHypothesis_of_right_survivorCore_and_aggregateEq
    (hcore : ∀ rho : sourceNontrivialZeroSet,
      (1 / 2 : Real) < rho.1.re →
        ∃ (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
          (lambda : CCM24SoninScale)
          (family : FinitePrimePowerFamily)
          (ν ρ : Type*)
          (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
          (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)),
          HealthyYoshidaDetectorData rho.1 owner.sourceTest ∧
          (Summable fun i : ρ =>
            ‖((sourceInclusion lambda).adjoint ∘L rootConvolution owner ∘L
              sourceInclusion lambda) (sourceBasis i)‖ ^ 2) ∧
          ((ordinaryTraceAlong sourceBasis
            (g8EndpointSourceCutoffLimitOperator owner lambda family)).re
            = C1SameOwnerWeil.qw owner.sourceTest)) :
    _root_.RiemannHypothesis := by
  apply riemannHypothesis_of_right_g8SameOwnerReadbackData
  intro rho hright
  obtain ⟨owner, lambda, family, ν, ρ_type, globalBasis, sourceBasis, hdata, hsum, heq⟩ :=
    hcore rho hright
  have readback := g8R5ZeroRemainderReadbackData owner lambda family globalBasis sourceBasis
    hsum heq
  exact ⟨owner, lambda, family, ν, ρ_type, globalBasis, sourceBasis, readback, hdata⟩

/-- Master G8 Exit 4 (Annular Wing Majorant & Aggregate Trace Equality):
    Deduces Mathlib's `_root_.RiemannHypothesis` from the two-sided annular wing majorant (S3)
    and the ρ5 aggregate endpoint trace equality. -/
theorem riemannHypothesis_of_right_annular_wing_majorant_and_aggregateEq
    (hwing : ∀ rho : sourceNontrivialZeroSet,
      (1 / 2 : Real) < rho.1.re →
        ∃ (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
          (lambda : CCM24SoninScale)
          (family : FinitePrimePowerFamily)
          (ν : Type*)
          (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
          (ι : Type*)
          (_hcount : Countable ι)
          (sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda))
          (N : ℕ) (hN : selectedRootSupportRadius owner ≤ (N : ℝ))
          (g : ℝ → ℝ) (B₁ B₂ : ℝ),
          HealthyYoshidaDetectorData rho.1 owner.sourceTest ∧
          Measurable g ∧ (∀ t, 0 ≤ g t) ∧ 0 ≤ B₁ ∧ 0 ≤ B₂ ∧
          0 < (N : ℝ) ∧ (∀ t, -(N : ℝ) ≤ t → t ≤ (N : ℝ) → g t = 0) ∧
          (∀ n, N ≤ n → ∀ t, ∑' i, ENNReal.ofReal
            (‖(sourceRootAnnularOutputWindow owner lambda N n
              (sourceBasis i) : ℝ → ℂ) t‖) ^ (2 : ℕ) ≤
            ENNReal.ofReal (g t)) ∧
          (∫⁻ t in Set.Iic (-(N : ℝ)), ENNReal.ofReal (g t) ≤ ENNReal.ofReal B₁) ∧
          (∫⁻ t in Set.Ici (N : ℝ), ENNReal.ofReal (g t) ≤ ENNReal.ofReal B₂) ∧
          ((ordinaryTraceAlong sourceBasis
            (g8EndpointSourceCutoffLimitOperator owner lambda family)).re
            = C1SameOwnerWeil.qw owner.sourceTest)) :
    _root_.RiemannHypothesis := by
  apply riemannHypothesis_of_right_survivorCore_and_aggregateEq
  intro rho hright
  obtain ⟨owner, lambda, family, ν, globalBasis, ι, hcount, sourceBasis, N, hN, g, B₁, B₂,
    hdata, hg, hgnonneg, hB₁, hB₂, hNpos, hzero, hpoint, hleft, hright_int, heq⟩ :=
    hwing rho hright
  haveI := hcount
  have hsummable : Summable (fun i : ι =>
      ‖((sourceInclusion lambda).adjoint ∘L rootConvolution owner ∘L
        sourceInclusion lambda) (sourceBasis i)‖ ^ 2) := by
    change Summable (fun i : ι => ‖sourceCompressedRoot owner lambda (sourceBasis i)‖ ^ 2)
    exact sourceCompressedRoot_squareSum_of_annular_wing_majorant owner lambda sourceBasis
      N hN hg hgnonneg hB₁ hB₂ hNpos hzero hpoint hleft hright_int
  exact ⟨owner, lambda, family, ν, ι, globalBasis, sourceBasis, hdata, hsummable, heq⟩

end C1G8MasterExit
end Source
end ConnesWeilRH
