/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSActualSchurCascade
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCoframeResponse

/-!
# Complete forward Schur--polar telescope

The unconditional rectangular steps in `suffixEulerFrameSchurSteps` are the
actual consecutive polar-frame steps.  This module composes their ambient and
source transitions in the only order compatible with the suffix frames and
proves the complete intertwining.  It then reads the raw metric coframe from
the terminal polar frame and the inverse-Gram square root.

No physical boundary readout or Gate 3U estimate is asserted here.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSSchurPolarTelescoping

open scoped InnerProduct

open CC20Concrete
open _root_.ConnesWeilRH.CC20Concrete
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCausalSupport
open CCM24FiniteSCoframeResponse
open CCM24FiniteSFixedSourcePolar
open CCM24FiniteSGramInverseCalculus
open CCM24FiniteSGramResponse
open CCM24FiniteSInverseMetric
open CCM24FiniteSJuliaBessel
open CCM24FiniteSJuliaCoDefect
open CCM24FiniteSParameterizedEulerEquiv
open CCM24FiniteSParameterizedEulerProduct
open CCM24FiniteSProjectionTrace
open CCM24FiniteSTransportBounds

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace
      (CCM24FiniteSFrameGramCalculus.sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! ## Ordered complete products -/

/-- The normalized ambient Euler factors in forward suffix order. -/
noncomputable def suffixEulerAmbientProduct :
    List CCM24VisiblePrime -> finiteSCarrier →L[ℂ] finiteSCarrier
  | [] => ContinuousLinearMap.id ℂ finiteSCarrier
  | p :: S => normalizedPrimeEulerFrameTransport p ∘L
      suffixEulerAmbientProduct S

/-- The compressed source transitions in the same forward suffix order. -/
noncomputable def suffixEulerTransitionProduct
    (lambda : CCM24SoninScale) :
    List CCM24VisiblePrime ->
      sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda
  | [] => ContinuousLinearMap.id ℂ (sourceSoninCarrier lambda)
  | p :: S => suffixEulerFrameTransition lambda p S ∘L
      suffixEulerTransitionProduct lambda S

/-- The terminal Julia survivor for the genuine rectangular steps is exactly
the adjoint of the ordered source transition product. -/
theorem juliaSurvivor_suffixEulerFrameCoDefectSteps
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    juliaSurvivor (suffixEulerFrameCoDefectSteps lambda S) =
      (suffixEulerTransitionProduct lambda S)† := by
  induction S with
  | nil =>
      simp [suffixEulerFrameCoDefectSteps, suffixEulerFrameSchurSteps,
        suffixEulerTransitionProduct, juliaSurvivor]
  | cons p S ih =>
      simp only [suffixEulerFrameCoDefectSteps,
        suffixEulerFrameSchurSteps, List.map_cons, juliaSurvivor,
        suffixEulerTransitionProduct, ContinuousLinearMap.adjoint_comp,
        RectangularSchurCoDefectStepData.toAdjointCoDefectJuliaStep_transfer,
        suffixEulerFrameSchurStep]
      rw [show juliaSurvivor
          ((suffixEulerFrameSchurSteps lambda S).map
            RectangularSchurCoDefectStepData.toAdjointCoDefectJuliaStep) =
          (suffixEulerTransitionProduct lambda S)† by
        simpa only [suffixEulerFrameCoDefectSteps] using ih]

/-- The complete normalized ambient Euler product intertwines the empty
polar frame with the terminal finite-S polar frame through the ordered source
transition product. -/
theorem suffixEulerAmbientProduct_comp_emptyPolarFrame
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    suffixEulerAmbientProduct S ∘L newSuffixFrame lambda [] =
      newSuffixFrame lambda S ∘L suffixEulerTransitionProduct lambda S := by
  induction S with
  | nil =>
      apply ContinuousLinearMap.ext
      intro x
      rfl
  | cons p S ih =>
      let step := suffixEulerFrameSchurStep lambda p S
      have hstep : normalizedPrimeEulerFrameTransport p ∘L
            newSuffixFrame lambda S =
          oldSuffixFrame lambda p S ∘L
            suffixEulerFrameTransition lambda p S := by
        simpa only [step, suffixEulerFrameSchurStep] using
          step.transport_intertwining
      calc
        suffixEulerAmbientProduct (p :: S) ∘L
              newSuffixFrame lambda [] =
            normalizedPrimeEulerFrameTransport p ∘L
              (suffixEulerAmbientProduct S ∘L
                newSuffixFrame lambda []) := by
          apply ContinuousLinearMap.ext
          intro x
          rfl
        _ = normalizedPrimeEulerFrameTransport p ∘L
              (newSuffixFrame lambda S ∘L
                suffixEulerTransitionProduct lambda S) := by rw [ih]
        _ = (normalizedPrimeEulerFrameTransport p ∘L
              newSuffixFrame lambda S) ∘L
                suffixEulerTransitionProduct lambda S := by
          apply ContinuousLinearMap.ext
          intro x
          rfl
        _ = (oldSuffixFrame lambda p S ∘L
              suffixEulerFrameTransition lambda p S) ∘L
                suffixEulerTransitionProduct lambda S := by rw [hstep]
        _ = newSuffixFrame lambda (p :: S) ∘L
              suffixEulerTransitionProduct lambda (p :: S) := by
          apply ContinuousLinearMap.ext
          intro x
          rfl

/-- Restoring the product of the upper scalar normalizations gives the
literal complete Euler transport. -/
theorem upperFactor_smul_suffixEulerAmbientProduct
    (S : List CCM24VisiblePrime) :
    (finiteEulerUpperFactor S : ℂ) • suffixEulerAmbientProduct S =
      (ccm24FiniteEulerTransportEquiv S).toContinuousLinearMap := by
  induction S with
  | nil =>
      apply ContinuousLinearMap.ext
      intro x
      simp [finiteEulerUpperFactor, suffixEulerAmbientProduct,
        ccm24FiniteEulerTransportEquiv_nil]
  | cons p S ih =>
      have hp : (1 + (ccm24PrimeEulerCoefficient p : ℂ)) ≠ 0 :=
        by
          exact_mod_cast ne_of_gt (primeEulerUpperFactor_pos p)
      apply ContinuousLinearMap.ext
      intro x
      change (((1 + ccm24PrimeEulerCoefficient p) *
          finiteEulerUpperFactor S : ℝ) : ℂ) •
          normalizedPrimeEulerFrameTransport p
            (suffixEulerAmbientProduct S x) =
        ccm24FiniteEulerTransportEquiv (p :: S) x
      rw [ccm24FiniteEulerTransportEquiv_cons_apply]
      have ihx := congrArg
        (fun operator : finiteSCarrier →L[ℂ] finiteSCarrier => operator x) ih
      change (finiteEulerUpperFactor S : ℂ) •
          suffixEulerAmbientProduct S x =
        ccm24FiniteEulerTransportEquiv S x at ihx
      rw [← ihx]
      simp only [normalizedPrimeEulerFrameTransport,
        ContinuousLinearMap.smul_apply, map_smul, smul_smul]
      rw [show ((((1 + ccm24PrimeEulerCoefficient p) *
            finiteEulerUpperFactor S : ℝ) : ℂ) *
          (1 + (ccm24PrimeEulerCoefficient p : ℂ))⁻¹) =
          (finiteEulerUpperFactor S : ℂ) by
        push_cast
        field_simp]
      rfl

/-- Adjointing the normalized product identity preserves the real upper
factor. -/
theorem upperFactor_smul_suffixEulerAmbientProduct_adjoint
    (S : List CCM24VisiblePrime) :
    (finiteEulerUpperFactor S : ℂ) •
        (suffixEulerAmbientProduct S)† =
      ((ccm24FiniteEulerTransportEquiv S).toContinuousLinearMap)† := by
  have h := congrArg ContinuousLinearMap.adjoint
    (upperFactor_smul_suffixEulerAmbientProduct S)
  simpa only [map_smulₛₗ, RCLike.star_def, Complex.conj_ofReal] using h

/-! ## Boundary expansion of the complete adjoint product -/

/-- One rectangular Schur step decomposes the ambient adjoint applied to the
old frame into its new-frame source coordinate and its genuine orthogonal
boundary dagger. -/
theorem transportAdjoint_comp_oldFrame_eq_newFrame_add_boundaryDagger
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (step : CCM24FiniteSJuliaCoDefect.RectangularSchurCoDefectStepData H K) :
    step.transport† ∘L step.oldFrame =
      step.newFrame ∘L step.transition† + step.boundaryDagger := by
  have hadjoint := congrArg ContinuousLinearMap.adjoint
    step.transport_intertwining
  have hadjoint' : step.newFrame† ∘L step.transport† =
      step.transition† ∘L step.oldFrame† := by
    simpa only [ContinuousLinearMap.adjoint_comp] using hadjoint
  have hcoordinate : step.newFrame† ∘L step.transport† ∘L step.oldFrame =
      step.transition† := by
    calc
      step.newFrame† ∘L step.transport† ∘L step.oldFrame =
          (step.transition† ∘L step.oldFrame†) ∘L step.oldFrame := by
        apply ContinuousLinearMap.ext
        intro x
        have hpoint := congrArg
          (fun operator : K →L[ℂ] H => operator (step.oldFrame x)) hadjoint'
        simpa only [ContinuousLinearMap.comp_apply] using hpoint
      _ = step.transition† ∘L (step.oldFrame† ∘L step.oldFrame) := by
        apply ContinuousLinearMap.ext
        intro x
        rfl
      _ = step.transition† := by
        rw [step.oldFrame_isometry, ContinuousLinearMap.comp_id]
  apply ContinuousLinearMap.ext
  intro x
  have hpoint := congrArg
    (fun operator : H →L[ℂ] H => operator x) hcoordinate
  simp only [ContinuousLinearMap.comp_apply] at hpoint
  simp only [CCM24FiniteSJuliaCoDefect.RectangularSchurCoDefectStepData.boundaryDagger,
    CCM24FiniteSJuliaCoDefect.rectangularBoundaryCompressionDagger,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]
  rw [hpoint]
  abel

/-- Every boundary dagger after its remaining ambient adjoint suffix and its
preceding source-adjoint prefix.  The list order agrees with the chronological
forward Schur steps. -/
noncomputable def suffixEulerBoundaryOutputMaps
    (lambda : CCM24SoninScale) :
    List CCM24VisiblePrime ->
      List (sourceSoninCarrier lambda →L[ℂ] finiteSCarrier)
  | [] => []
  | p :: S =>
      ((suffixEulerAmbientProduct S)† ∘L
          (suffixEulerFrameSchurStep lambda p S).boundaryDagger) ::
        (suffixEulerBoundaryOutputMaps lambda S).map
          (fun output => output ∘L
            (suffixEulerFrameTransition lambda p S)†)

theorem suffixEulerBoundaryOutputMaps_length
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    (suffixEulerBoundaryOutputMaps lambda S).length = S.length := by
  induction S with
  | nil => rfl
  | cons p S ih => simp [suffixEulerBoundaryOutputMaps, ih]

theorem sum_map_comp_apply
    {H K : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup K] [NormedSpace ℂ K]
    (maps : List (H →L[ℂ] K)) (right : H →L[ℂ] H) (x : H) :
    (maps.map (fun output => output ∘L right)).sum x =
      maps.sum (right x) := by
  induction maps with
  | nil => simp
  | cons output maps ih =>
      simp only [List.map_cons, List.sum_cons,
        ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, ih]

/-- Full Schur--polar adjoint telescope.  The complete normalized ambient
adjoint acting on the terminal polar frame is the terminal source survivor
plus the ordered sum of all actual rectangular boundary daggers. -/
theorem suffixEulerAmbientProduct_adjoint_comp_terminalPolarFrame
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    (suffixEulerAmbientProduct S)† ∘L newSuffixFrame lambda S =
      newSuffixFrame lambda [] ∘L
          (suffixEulerTransitionProduct lambda S)† +
        (suffixEulerBoundaryOutputMaps lambda S).sum := by
  induction S with
  | nil =>
      apply ContinuousLinearMap.ext
      intro x
      simp [suffixEulerAmbientProduct, suffixEulerTransitionProduct,
        suffixEulerBoundaryOutputMaps]
  | cons p S ih =>
      let step := suffixEulerFrameSchurStep lambda p S
      have hone :=
        transportAdjoint_comp_oldFrame_eq_newFrame_add_boundaryDagger step
      have hone' :
          (normalizedPrimeEulerFrameTransport p)† ∘L
              newSuffixFrame lambda (p :: S) =
            newSuffixFrame lambda S ∘L
                (suffixEulerFrameTransition lambda p S)† +
              step.boundaryDagger := by
        simpa only [step, suffixEulerFrameSchurStep, oldSuffixFrame,
          newSuffixFrame] using hone
      apply ContinuousLinearMap.ext
      intro x
      have ihPoint := congrArg
        (fun operator : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier =>
          operator (((suffixEulerFrameTransition lambda p S)†) x)) ih
      have honePoint := congrArg
        (fun operator : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier =>
          operator x) hone'
      simp only [ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.add_apply] at ihPoint honePoint ⊢
      simp only [suffixEulerAmbientProduct,
        ContinuousLinearMap.adjoint_comp,
        ContinuousLinearMap.comp_apply] at ⊢
      rw [honePoint, map_add, ihPoint]
      simp only [suffixEulerTransitionProduct, suffixEulerBoundaryOutputMaps,
        ContinuousLinearMap.adjoint_comp, List.sum_cons,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply]
      rw [sum_map_comp_apply]
      dsimp only [step]
      abel

/-! ## Raw metric-coframe readback -/

/-- At `alpha = 1`, the parameterized restricted frame is the finite Euler
frame on the same visible-prime list. -/
theorem parameterizedSoninFrame_one_eq_finiteEulerFrame
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    CCM24FiniteSFrameGramCalculus.parameterizedSoninFrame
        lambda 1 family.visiblePrimes =
      finiteEulerFrame lambda family := by
  apply ContinuousLinearMap.ext
  intro x
  rw [parameterizedSoninFrame_eq_restrictedClosedTransport
    lambda 1 family.visiblePrimes (by norm_num [abs_of_nonneg])]
  change parameterizedFiniteEulerEquiv 1 family.visiblePrimes (by norm_num) x =
    ccm24FiniteEulerTransportEquiv family.visiblePrimes x
  rw [parameterizedFiniteEulerEquiv_one]

/-- The parameterized inverse Gram at `alpha = 1` is the actual finite-S
inverse Gram. -/
theorem parameterizedSoninGramInv_one_eq_finiteEulerGramInv
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    parameterizedSoninGramInv lambda 1 family.visiblePrimes (by norm_num) =
      finiteEulerGramInv lambda family := by
  unfold parameterizedSoninGramInv finiteEulerGramInv
  rw [parameterizedFiniteEulerEquiv_one]

/-- The raw metric coframe is the transport adjoint applied to the terminal
polar frame and one further inverse-Gram square root.  This is the exact
Schur--polar endpoint which the completed physical history must read out. -/
theorem finiteEulerMetricCoframe_eq_transportAdjoint_polar_sqrt
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteEulerMetricCoframe lambda family =
      (finiteEulerTransportOperator family)† ∘L
        newSuffixFrame lambda family.visiblePrimes ∘L
          parameterizedSoninGramInvSqrt lambda 1 family.visiblePrimes
            (by norm_num) := by
  rw [finiteEulerMetricCoframe_eq_transportAdjoint_comp_dualFrame]
  apply ContinuousLinearMap.ext
  intro x
  simp only [finiteEulerDualFrame, newSuffixFrame,
    parameterizedSoninPolarFrame, ContinuousLinearMap.comp_apply]
  rw [parameterizedSoninFrame_one_eq_finiteEulerFrame]
  have hsqrt := parameterizedSoninGramInvSqrt_mul_self
    lambda 1 family.visiblePrimes (by norm_num)
  have hsqrtPoint := congrArg
    (fun operator : sourceSoninCarrier lambda →L[ℂ]
      sourceSoninCarrier lambda => operator x) hsqrt
  rw [parameterizedSoninGramInv_one_eq_finiteEulerGramInv] at hsqrtPoint
  simpa only [ContinuousLinearMap.comp_apply] using
    congrArg (fun y : sourceSoninCarrier lambda =>
      ((finiteEulerTransportOperator family)†)
        (finiteEulerFrame lambda family y)) hsqrtPoint.symm

/-- Complete Schur--polar readback of the raw metric coframe.  The only
scalar outside the normalized forward telescope is the exact upper Euler
factor; it has not been estimated or hidden in a premise. -/
theorem finiteEulerMetricCoframe_eq_upperFactor_schurPolarProduct
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteEulerMetricCoframe lambda family =
      (finiteEulerUpperFactor family.visiblePrimes : ℂ) •
        ((suffixEulerAmbientProduct family.visiblePrimes)† ∘L
          newSuffixFrame lambda family.visiblePrimes ∘L
            parameterizedSoninGramInvSqrt lambda 1 family.visiblePrimes
              (by norm_num)) := by
  rw [finiteEulerMetricCoframe_eq_transportAdjoint_polar_sqrt]
  have hupper :=
    upperFactor_smul_suffixEulerAmbientProduct_adjoint family.visiblePrimes
  apply ContinuousLinearMap.ext
  intro x
  have hpoint := congrArg
    (fun operator : finiteSCarrier →L[ℂ] finiteSCarrier =>
      operator (newSuffixFrame lambda family.visiblePrimes
        (parameterizedSoninGramInvSqrt lambda 1 family.visiblePrimes
          (by norm_num) x))) hupper
  simpa only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, map_smul] using hpoint.symm

/-- The actual boundary outputs after the final inverse-Gram square-root
source coordinate used by the raw metric coframe. -/
noncomputable def finiteEulerMetricCoframeBoundaryMaps
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    List (sourceSoninCarrier lambda →L[ℂ] finiteSCarrier) :=
  (suffixEulerBoundaryOutputMaps lambda family.visiblePrimes).map
    (fun output => output ∘L
      parameterizedSoninGramInvSqrt lambda 1 family.visiblePrimes
        (by norm_num))

/-- Fully expanded Schur--polar telescope for the raw metric coframe.  It is
the terminal survivor plus every genuine rectangular boundary dagger, in the
exact ambient/source order forced by the finite Euler product. -/
theorem finiteEulerMetricCoframe_eq_survivor_add_boundarySum
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteEulerMetricCoframe lambda family =
      (finiteEulerUpperFactor family.visiblePrimes : ℂ) •
        (newSuffixFrame lambda [] ∘L
            (suffixEulerTransitionProduct lambda family.visiblePrimes)† ∘L
              parameterizedSoninGramInvSqrt lambda 1 family.visiblePrimes
                (by norm_num) +
          (finiteEulerMetricCoframeBoundaryMaps lambda family).sum) := by
  rw [finiteEulerMetricCoframe_eq_upperFactor_schurPolarProduct]
  have htelescope :=
    suffixEulerAmbientProduct_adjoint_comp_terminalPolarFrame
      lambda family.visiblePrimes
  apply ContinuousLinearMap.ext
  intro x
  have hpoint := congrArg
    (fun operator : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier =>
      operator (parameterizedSoninGramInvSqrt lambda 1
        family.visiblePrimes (by norm_num) x)) htelescope
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply] at hpoint ⊢
  rw [hpoint]
  rw [finiteEulerMetricCoframeBoundaryMaps, sum_map_comp_apply]

end CCM24FiniteSSchurPolarTelescoping
end CCM25Concrete
end Source
end ConnesWeilRH
