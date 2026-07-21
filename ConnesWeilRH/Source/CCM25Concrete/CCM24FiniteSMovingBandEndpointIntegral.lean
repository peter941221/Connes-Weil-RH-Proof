/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSMovingBandCalculus
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSRadialGeneratorInvariance
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Endpoint integral for the synchronized moving Sonin band

The moving-band calculus already gives the operator-norm derivative of the
root-sandwiched band.  This module consumes that derivative with the Banach
space fundamental theorem of calculus.  It also records, pointwise in the
synchronized parameter, the exact deletion of the radial crossing: the
complete five-branch owner is the negative Sonin crossing, before any
integration or norm.

The interval-integrability hypothesis is intentionally explicit.  It is a
standard analytic obligation for the eventual Gate 3U producer, not a stored
RH or positivity premise.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSMovingBandEndpointIntegral

open CC20Concrete
open MeasureTheory
open scoped InnerProduct InnerProductSpace
open CCM24FiniteSProjectionTrace
open CCM24FiniteSProjectionTrace.FinitePrimePowerFamily
open CCM24FiniteSBandTrace
open CCM24FiniteSCompletedMovingCrossing
open CCM24FiniteSMovingBandCalculus
open CCM24FiniteSRadialGeneratorInvariance
open CCM24FiniteSRootSandwichedMovingFlow
open intervalIntegral

local notation "Op" => finiteSCarrier →L[ℂ] finiteSCarrier

/-- The root-smoothed complete five-branch crossing at synchronized time.
The five branches remain inside this one operator; no branchwise estimate is
introduced by the definition. -/
noncomputable def actualCompletedRootCrossing
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) : Op :=
  rootConvolution owner ∘L
    completedMovingCrossing
      (radialSupportProjection lambda)
      (CCM24FiniteSParameterizedSoninProjection.parameterizedFourierSupportProjection
        lambda alpha S halpha)
      (CCM24FiniteSParameterizedSoninProjection.parameterizedProlateRemainder
        lambda alpha S halpha)
      (CCM24FiniteSParameterizedEulerGenerator.parameterizedFiniteEulerGenerator
        alpha S) ∘L
    (rootConvolution owner)†

/-- Radial support invariance deletes the outer crossing before the Hermitian
completion is formed.  The remaining moving flow is the negative completed
crossing plus its adjoint. -/
theorem actualMovingSoninRootFlow_eq_neg_completedRootCrossing_add_adjoint
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    actualMovingSoninRootFlow owner lambda alpha S =
      -actualCompletedRootCrossing owner lambda alpha S halpha -
        (actualCompletedRootCrossing owner lambda alpha S halpha).adjoint := by
  rw [actualMovingSoninRootFlow_eq_crossing_add_adjoint]
  have hcross := rootSandwiched_completedMovingCrossing_eq_neg_soninCrossing
    (rootConvolution owner) lambda alpha S halpha
  have hcross' :
      actualCompletedRootCrossing owner lambda alpha S halpha =
        -actualMovingSoninRootCrossing owner lambda alpha S := by
    simpa only [actualCompletedRootCrossing] using hcross
  rw [hcross']
  simp only [map_neg, neg_neg, sub_neg_eq_add]

/-! The endpoint identity is stated for the actual finite-S family, so the
visible-prime list is the same list selected by the arithmetic owner. -/

theorem integral_actualMovingSoninRootFlow_eq_neg_rootSandwichedBandResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    (family : FinitePrimePowerFamily)
    (hflow : IntervalIntegrable
      (fun alpha : ℝ =>
        actualMovingSoninRootFlow owner lambda alpha family.visiblePrimes)
      volume 0 1) :
    (∫ alpha : ℝ in 0..1,
      actualMovingSoninRootFlow owner lambda alpha family.visiblePrimes) =
      -rootSandwichedBandResponse owner lambda family := by
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt
        (fun beta : ℝ =>
          actualRootSandwichedSoninBand owner lambda beta
            family.visiblePrimes)
        (-actualMovingSoninRootFlow owner lambda x family.visiblePrimes) x := by
    intro x hx
    have hzero_one : (0 : ℝ) ≤ 1 := by norm_num
    have hx' : x ∈ Set.Icc (0 : ℝ) 1 := by
      simpa only [Set.uIcc_of_le hzero_one] using hx
    apply hasDerivAt_actualRootSandwichedSoninBand owner lambda x
      family.visiblePrimes
    exact abs_le.mpr ⟨by linarith [hx'.1], hx'.2⟩
  have hneg : IntervalIntegrable
      (fun alpha : ℝ =>
        -actualMovingSoninRootFlow owner lambda alpha family.visiblePrimes)
      volume 0 1 := by
    simpa only [Pi.neg_apply] using hflow.neg
  have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun beta : ℝ =>
      actualRootSandwichedSoninBand owner lambda beta family.visiblePrimes)
    (f' := fun beta : ℝ =>
      -actualMovingSoninRootFlow owner lambda beta family.visiblePrimes)
    hderiv hneg
  have hendpoint :
      actualRootSandwichedSoninBand owner lambda 1 family.visiblePrimes -
          actualRootSandwichedSoninBand owner lambda 0 family.visiblePrimes =
        rootSandwichedBandResponse owner lambda family :=
    actualRootSandwichedSoninBand_one_sub_zero owner lambda family
  calc
    (∫ alpha : ℝ in 0..1,
        actualMovingSoninRootFlow owner lambda alpha family.visiblePrimes) =
        -∫ alpha : ℝ in 0..1,
          -actualMovingSoninRootFlow owner lambda alpha family.visiblePrimes := by
      rw [intervalIntegral.integral_neg]
      simp
    _ = -(actualRootSandwichedSoninBand owner lambda 1 family.visiblePrimes -
          actualRootSandwichedSoninBand owner lambda 0 family.visiblePrimes) := by
      rw [hfund]
    _ = -rootSandwichedBandResponse owner lambda family := by
      rw [hendpoint]

end CCM24FiniteSMovingBandEndpointIntegral
end CCM25Concrete
end Source
end ConnesWeilRH
