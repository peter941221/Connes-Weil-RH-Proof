/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSMovingBandFlowRegularity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Finite diagonal integrals for the moving band

The endpoint theorem identifies an operator integral.  This module applies
that identity to one genuine Hilbert-basis coefficient and then to an
arbitrary finite diagonal truncation.  The finite sum is exchanged with the
interval integral only through `intervalIntegral.integral_finsetSum`; no
infinite trace/integral exchange is asserted here.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSMovingBandDiagonalIntegral

open CC20Concrete
open MeasureTheory
open scoped InnerProduct InnerProductSpace
open CCM24FiniteSProjectionTrace
open CCM24FiniteSBandTrace
open CCM24FiniteSMovingBandEndpointIntegral
open CCM24FiniteSRootSandwichedMovingFlow
open CCM24FiniteSMovingBandFlowRegularity
open intervalIntegral

local notation "Op" => finiteSCarrier →L[ℂ] finiteSCarrier

private theorem intervalIntegrable_movingFlow_inner
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (u : finiteSCarrier) :
    IntervalIntegrable
      (fun alpha : ℝ =>
        ⟪u, actualMovingSoninRootFlow owner lambda alpha
          family.visiblePrimes u⟫_ℂ)
      volume 0 1 := by
  have hflow : ContinuousOn
      (fun alpha : ℝ =>
        actualMovingSoninRootFlow owner lambda alpha family.visiblePrimes)
      (Set.Icc (-1 : ℝ) 1) :=
    continuousOn_actualMovingSoninRootFlow owner lambda family.visiblePrimes
  have happly : ContinuousOn
      (fun alpha : ℝ =>
        (actualMovingSoninRootFlow owner lambda alpha family.visiblePrimes) u)
      (Set.Icc (-1 : ℝ) 1) := by
    exact (ContinuousLinearMap.apply ℂ finiteSCarrier u).continuous.comp_continuousOn
      hflow
  have hinner : ContinuousOn
      (fun alpha : ℝ =>
        (innerSL ℂ u)
          ((actualMovingSoninRootFlow owner lambda alpha family.visiblePrimes) u))
      (Set.Icc (-1 : ℝ) 1) := by
    exact (innerSL ℂ u).continuous.comp_continuousOn happly
  have hcont : ContinuousOn
      (fun alpha : ℝ =>
        (innerSL ℂ u)
          ((actualMovingSoninRootFlow owner lambda alpha family.visiblePrimes) u))
      (Set.uIcc (0 : ℝ) 1) := by
    apply hinner.mono
    intro alpha halpha
    have h01 : (0 : ℝ) ≤ 1 := by norm_num
    rw [Set.uIcc_of_le h01] at halpha
    constructor <;> linarith [halpha.1, halpha.2]
  simpa only [innerSL_apply_apply] using hcont.intervalIntegrable

/-- One genuine diagonal coefficient of the endpoint is the signed integral
of the complete moving flow.  The proof uses only a continuous linear map on
the operator space, so it does not cycle an infinite trace. -/
theorem intervalIntegral_inner_actualMovingSoninRootFlow_eq_neg_response
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (u : finiteSCarrier) :
    (∫ alpha : ℝ in 0..1,
      ⟪u, actualMovingSoninRootFlow owner lambda alpha
        family.visiblePrimes u⟫_ℂ) =
      -⟪u, rootSandwichedBandResponse owner lambda family u⟫_ℂ := by
  let coeff : Op →L[ℂ] ℂ :=
    (innerSL ℂ u).comp (ContinuousLinearMap.apply ℂ finiteSCarrier u)
  have hflow :
      IntervalIntegrable
        (fun alpha : ℝ =>
          actualMovingSoninRootFlow owner lambda alpha family.visiblePrimes)
        volume 0 1 :=
    intervalIntegrable_actualMovingSoninRootFlow owner lambda family
  have hcomp := coeff.intervalIntegral_comp_comm hflow
  have hendpoint := integral_actualMovingSoninRootFlow_eq_neg_bandResponse
    owner lambda family
  calc
    (∫ alpha : ℝ in 0..1,
        ⟪u, actualMovingSoninRootFlow owner lambda alpha
          family.visiblePrimes u⟫_ℂ) =
        ∫ alpha : ℝ in 0..1,
          coeff (actualMovingSoninRootFlow owner lambda alpha
            family.visiblePrimes) := by
      simp only [coeff, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.apply_apply, innerSL_apply_apply]
    _ = coeff (∫ alpha : ℝ in 0..1,
          actualMovingSoninRootFlow owner lambda alpha family.visiblePrimes) := hcomp
    _ = coeff (-rootSandwichedBandResponse owner lambda family) := by
      rw [hendpoint]
    _ = -⟪u, rootSandwichedBandResponse owner lambda family u⟫_ℂ := by
      simp only [coeff, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.apply_apply, innerSL_apply_apply,
        map_neg]

/-! At every legal synchronized time, the diagonal of the actual Hermitian
flow is exactly the negative twice-real-part of the complete five-branch
crossing.  This is a pointwise identity, before any finite sum or trace. -/
theorem inner_actualMovingSoninRootFlow_re_eq_neg_two_completedRootCrossing_re
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1)
    (u : finiteSCarrier) :
    (⟪u, actualMovingSoninRootFlow owner lambda alpha S u⟫_ℂ).re =
      -2 *
        (⟪u, actualCompletedRootCrossing owner lambda alpha S halpha u⟫_ℂ).re := by
  rw [actualMovingSoninRootFlow_eq_neg_completedRootCrossing_add_adjoint
    owner lambda alpha S halpha]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.neg_apply,
    inner_sub_right, inner_neg_right,
    ContinuousLinearMap.adjoint_inner_right, Complex.neg_re,
    Complex.sub_re]
  have hsymm :
      (⟪actualCompletedRootCrossing owner lambda alpha S halpha u, u⟫_ℂ).re =
        (⟪u, actualCompletedRootCrossing owner lambda alpha S halpha u⟫_ℂ).re :=
    inner_re_symm (𝕜 := ℂ) _ _
  rw [hsymm]
  ring

/-! The finite diagonal theorem below is deliberately weaker than an ordinary
trace theorem: `J` is finite, so the sum/integral interchange is elementary
and carries no hidden summability assumption on the full Hilbert basis. -/

theorem finiteDiagonalResponse_re_eq_neg_integral_finiteDiagonalFlow_re
    {ι : Type*} (basis : HilbertBasis ι ℂ finiteSCarrier)
    (J : Finset ι)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    (∑ i ∈ J,
      (⟪basis i, rootSandwichedBandResponse owner lambda family (basis i)⟫_ℂ).re) =
      -∫ alpha : ℝ in 0..1,
        ∑ i ∈ J,
          (⟪basis i, actualMovingSoninRootFlow owner lambda alpha
            family.visiblePrimes (basis i)⟫_ℂ).re := by
  have hinner : ∀ i ∈ J,
      IntervalIntegrable
        (fun alpha : ℝ =>
          ⟪basis i, actualMovingSoninRootFlow owner lambda alpha
            family.visiblePrimes (basis i)⟫_ℂ)
        volume 0 1 := by
    intro i hi
    exact intervalIntegrable_movingFlow_inner owner lambda family (basis i)
  have hcoeff : ∀ i ∈ J,
      (∫ alpha : ℝ in 0..1,
        (⟪basis i, actualMovingSoninRootFlow owner lambda alpha
          family.visiblePrimes (basis i)⟫_ℂ).re) =
        - (⟪basis i, rootSandwichedBandResponse owner lambda family
            (basis i)⟫_ℂ).re := by
    intro i hi
    have hcomplex := intervalIntegral_inner_actualMovingSoninRootFlow_eq_neg_response
      owner lambda family (basis i)
    have hreal :
        (∫ alpha : ℝ in 0..1,
          (⟪basis i, actualMovingSoninRootFlow owner lambda alpha
            family.visiblePrimes (basis i)⟫_ℂ).re) =
          (-⟪basis i, rootSandwichedBandResponse owner lambda family
            (basis i)⟫_ℂ).re := by
      calc
        (∫ alpha : ℝ in 0..1,
            (⟪basis i, actualMovingSoninRootFlow owner lambda alpha
              family.visiblePrimes (basis i)⟫_ℂ).re) =
            (∫ alpha : ℝ in 0..1,
              ⟪basis i, actualMovingSoninRootFlow owner lambda alpha
                family.visiblePrimes (basis i)⟫_ℂ).re :=
          intervalIntegral_re (𝕜 := ℂ) (hinner i hi)
        _ = (-⟪basis i, rootSandwichedBandResponse owner lambda family
              (basis i)⟫_ℂ).re := congrArg Complex.re hcomplex
    simpa only [map_neg] using hreal
  calc
    (∑ i ∈ J,
        (⟪basis i, rootSandwichedBandResponse owner lambda family
          (basis i)⟫_ℂ).re) =
        ∑ i ∈ J, -(∫ alpha : ℝ in 0..1,
          (⟪basis i, actualMovingSoninRootFlow owner lambda alpha
            family.visiblePrimes (basis i)⟫_ℂ).re) := by
      apply Finset.sum_congr rfl
      intro i hi
      linarith [hcoeff i hi]
    _ = -∑ i ∈ J, (∫ alpha : ℝ in 0..1,
          (⟪basis i, actualMovingSoninRootFlow owner lambda alpha
            family.visiblePrimes (basis i)⟫_ℂ).re) := by
      simp only [Finset.sum_neg_distrib]
    _ = -∫ alpha : ℝ in 0..1,
          ∑ i ∈ J,
            (⟪basis i, actualMovingSoninRootFlow owner lambda alpha
              family.visiblePrimes (basis i)⟫_ℂ).re := by
      have hsum :
          (∫ alpha : ℝ in 0..1,
            ∑ i ∈ J,
              (⟪basis i, actualMovingSoninRootFlow owner lambda alpha
                family.visiblePrimes (basis i)⟫_ℂ).re) =
            ∑ i ∈ J, (∫ alpha : ℝ in 0..1,
              (⟪basis i, actualMovingSoninRootFlow owner lambda alpha
                family.visiblePrimes (basis i)⟫_ℂ).re) := by
        exact intervalIntegral.integral_finsetSum
          (fun i hi =>
            ⟨(hinner i hi).1.re, (hinner i hi).2.re⟩)
      exact congrArg (fun value : ℝ => -value) hsum.symm

end CCM24FiniteSMovingBandDiagonalIntegral
end CCM25Concrete
end Source
end ConnesWeilRH
