/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSMovingBandEndpointIntegral
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSParameterizedInverseCalculus
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSParameterizedEulerCommutation

/-!
# Regularity of the synchronized moving Sonin flow

Proof 445 left interval integrability of the complete root-smoothed flow as an
explicit analytic witness.  Here that witness is discharged from the actual
parameterized Euler and Gram calculus: the inverse is continuous on the legal
interval, the product-rule derivative is a finite recursive continuous map, and
the orthogonal root flow is assembled by continuous algebraic operations.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSMovingBandFlowRegularity

open MeasureTheory
open CC20Concrete
open CCM24FiniteSProjectionTrace
open CCM24FiniteSProjectionTrace.FinitePrimePowerFamily
open CCM24FiniteSBandTrace
open CCM24FiniteSParameterizedEulerCalculus
open CCM24FiniteSParameterizedEulerCommutation
open CCM24FiniteSParameterizedEulerGenerator
open CCM24FiniteSParameterizedEulerProduct
open CCM24FiniteSParameterizedInverseCalculus
open CCM24FiniteSGramProjectionCalculus
open CCM24FiniteSOrthogonalProjectionFlow
open CCM24FiniteSRootSandwichedMovingFlow
open CCM24FiniteSMovingBandEndpointIntegral
open intervalIntegral

local notation "Op" => finiteSCarrier →L[ℂ] finiteSCarrier

private theorem continuous_parameterizedFiniteEulerFactor
    (S : List CCM24VisiblePrime) :
    Continuous (fun alpha : ℝ => parameterizedFiniteEulerFactor alpha S) := by
  apply continuous_iff_continuousAt.mpr
  intro alpha
  exact (hasDerivAt_parameterizedFiniteEulerFactor alpha S).continuousAt

private theorem continuous_parameterizedFiniteEulerDerivative
    (S : List CCM24VisiblePrime) :
    Continuous (fun alpha : ℝ => parameterizedFiniteEulerDerivative alpha S) := by
  induction S with
  | nil =>
      simpa [parameterizedFiniteEulerDerivative] using
        (continuous_const : Continuous (fun _ : ℝ => (0 : Op)))
  | cons p S ih =>
      have htail : Continuous
          (fun alpha : ℝ => parameterizedFiniteEulerFactor alpha S) :=
        continuous_parameterizedFiniteEulerFactor S
      have hprime : Continuous
          (fun alpha : ℝ => parameterizedPrimeEulerFactor alpha p) := by
        apply continuous_iff_continuousAt.mpr
        intro alpha
        exact (hasDerivAt_parameterizedPrimeEulerFactor alpha p).continuousAt
      simpa only [parameterizedFiniteEulerDerivative] using
        (continuous_const.mul htail).add (hprime.mul ih)

private theorem continuousOn_parameterizedFiniteEulerInverse
    (S : List CCM24VisiblePrime) :
    ContinuousOn (fun alpha : ℝ => parameterizedFiniteEulerInverse alpha S)
      (Set.Icc (-1 : ℝ) 1) := by
  intro alpha halpha
  exact (hasDerivWithinAt_parameterizedFiniteEulerInverse alpha S
    (abs_le.mpr halpha)).continuousWithinAt

private theorem continuousOn_parameterizedFiniteEulerGenerator
    (S : List CCM24VisiblePrime) :
    ContinuousOn (fun alpha : ℝ => parameterizedFiniteEulerGenerator alpha S)
      (Set.Icc (-1 : ℝ) 1) := by
  have hderiv := continuous_parameterizedFiniteEulerDerivative S
  have hinv := continuousOn_parameterizedFiniteEulerInverse S
  have hright : ContinuousOn
      (fun alpha : ℝ => parameterizedFiniteEulerRightGenerator alpha S)
      (Set.Icc (-1 : ℝ) 1) := by
    simpa only [parameterizedFiniteEulerRightGenerator] using
      hderiv.continuousOn.mul hinv
  apply hright.congr
  intro alpha halpha
  exact
    (parameterizedFiniteEulerRightGenerator_eq_additiveGenerator alpha S
      (abs_le.mpr halpha)).symm

private theorem continuousOn_parameterizedCanonicalGramProjection
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    ContinuousOn
      (fun alpha : ℝ => parameterizedCanonicalGramProjection lambda alpha S)
      (Set.Icc (-1 : ℝ) 1) := by
  intro alpha halpha
  exact (hasDerivAt_parameterizedCanonicalGramProjection lambda alpha S
    (abs_le.mpr halpha)).continuousAt.continuousWithinAt

/-- The complete root-smoothed flow is continuous on the legal synchronized
interval.  This is the regularity producer needed by the endpoint integral. -/
theorem continuousOn_actualMovingSoninRootFlow
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    ContinuousOn
      (fun alpha : ℝ => actualMovingSoninRootFlow owner lambda alpha S)
      (Set.Icc (-1 : ℝ) 1) := by
  let P : ℝ → Op := fun alpha =>
    parameterizedCanonicalGramProjection lambda alpha S
  let X : ℝ → Op := fun alpha =>
    parameterizedFiniteEulerGenerator alpha S
  let crossing : ℝ → Op := fun alpha =>
    ((1 : Op) - P alpha) * X alpha * P alpha
  have hP : ContinuousOn P (Set.Icc (-1 : ℝ) 1) := by
    exact continuousOn_parameterizedCanonicalGramProjection lambda S
  have hX : ContinuousOn X (Set.Icc (-1 : ℝ) 1) := by
    exact continuousOn_parameterizedFiniteEulerGenerator S
  have hcross : ContinuousOn crossing (Set.Icc (-1 : ℝ) 1) := by
    exact (continuousOn_const.sub hP).mul hX |>.mul hP
  have hcrossAdj : ContinuousOn
      (fun alpha => (crossing alpha).adjoint)
      (Set.Icc (-1 : ℝ) 1) := by
    exact ContinuousLinearMap.adjoint.continuous.comp_continuousOn hcross
  have horth : ContinuousOn
      (fun alpha => crossing alpha + (crossing alpha).adjoint)
      (Set.Icc (-1 : ℝ) 1) := hcross.add hcrossAdj
  have hleft : ContinuousOn
      (fun alpha => (rootConvolution owner) *
        (crossing alpha + (crossing alpha).adjoint))
      (Set.Icc (-1 : ℝ) 1) := continuousOn_const.mul horth
  have hfull : ContinuousOn
      (fun alpha => ((rootConvolution owner) *
        (crossing alpha + (crossing alpha).adjoint)) *
          (rootConvolution owner).adjoint)
      (Set.Icc (-1 : ℝ) 1) := hleft.mul continuousOn_const
  simpa only [actualMovingSoninRootFlow, rootSandwichedOrthogonalFlow,
    orthogonalProjectionDerivative, projectionLeftCrossing,
    ContinuousLinearMap.mul_def, P, X, crossing] using hfull

theorem intervalIntegrable_actualMovingSoninRootFlow
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    IntervalIntegrable
      (fun alpha : ℝ =>
      actualMovingSoninRootFlow owner lambda alpha family.visiblePrimes)
      volume 0 1 := by
  have hcont :
      ContinuousOn
        (fun alpha : ℝ =>
          actualMovingSoninRootFlow owner lambda alpha family.visiblePrimes)
        (Set.uIcc (0 : ℝ) 1) := by
    apply (continuousOn_actualMovingSoninRootFlow owner lambda
      family.visiblePrimes).mono
    intro alpha halpha
    have h01 : (0 : ℝ) ≤ 1 := by norm_num
    rw [Set.uIcc_of_le h01] at halpha
    constructor <;> linarith [halpha.1, halpha.2]
  exact hcont.intervalIntegrable

theorem integral_actualMovingSoninRootFlow_eq_neg_bandResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    (∫ alpha : ℝ in 0..1,
      actualMovingSoninRootFlow owner lambda alpha family.visiblePrimes) =
      -rootSandwichedBandResponse owner lambda family := by
  exact integral_actualMovingSoninRootFlow_eq_neg_rootSandwichedBandResponse
    owner lambda family (intervalIntegrable_actualMovingSoninRootFlow
      owner lambda family)

end CCM24FiniteSMovingBandFlowRegularity
end CCM25Concrete
end Source
end ConnesWeilRH
