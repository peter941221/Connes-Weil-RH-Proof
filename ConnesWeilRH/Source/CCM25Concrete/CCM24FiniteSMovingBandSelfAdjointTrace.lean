/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSMovingBandTraceLimit

/-!
# Self-adjointness of the moving-band endpoint response

The endpoint response is a convolution-root sandwich of a difference of two
orthogonal projections.  This module records the resulting self-adjointness
and the consequence that any legal ordinary diagonal trace is real.

This is a carrier and scalar-readback bridge only.  It does not manufacture
the missing same-carrier `IsTraceClassAlong` witness.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSMovingBandSelfAdjointTrace

open CC20Concrete
open CCM24FiniteSProjectionTrace
open CCM24FiniteSBandTrace
open CCM24FiniteSFixedQuotientCarrier
open CCM24FiniteSPairedFirstJetRemainder
open CCM24FiniteSCanonicalCompletedResponse
open CCM24FiniteSMovingBandTraceLimit
open CCM24FiniteSMovingBandDiagonalIntegral
open CCM24FiniteSRootSandwichedMovingFlow
open scoped InnerProduct InnerProductSpace

local notation "Op" => finiteSCarrier →L[ℂ] finiteSCarrier

private theorem summable_abs_of_bounded_finset_signed_sums
    {ι : Type*} (a : ι → ℝ) (C : ℝ)
    (hbound : ∀ J : Finset ι, |∑ i ∈ J, a i| ≤ C) :
    Summable fun i => |a i| := by
  classical
  have hC : 0 ≤ C := by
    simpa using hbound ∅
  refine summable_of_sum_le (c := 2 * C) (fun i => abs_nonneg _) ?_
  intro J
  let p : ι → Prop := fun i => 0 ≤ a i
  let Jpos := J.filter p
  let Jneg := J.filter (fun i => ¬ p i)
  have hsplit :
      (∑ i ∈ Jpos, |a i|) + ∑ i ∈ Jneg, |a i| =
        ∑ i ∈ J, |a i| := by
    exact Finset.sum_filter_add_sum_filter_not J p (fun i => |a i|)
  have hpos :
      ∑ i ∈ Jpos, |a i| = ∑ i ∈ Jpos, a i := by
    apply Finset.sum_congr rfl
    intro i hi
    exact abs_of_nonneg (Finset.mem_filter.1 hi).2
  have hneg :
      ∑ i ∈ Jneg, |a i| = -∑ i ∈ Jneg, a i := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [abs_of_neg (lt_of_not_ge (Finset.mem_filter.1 hi).2)]
  have hposBound : |∑ i ∈ Jpos, a i| ≤ C := hbound Jpos
  have hnegBound : |∑ i ∈ Jneg, a i| ≤ C := hbound Jneg
  rw [← hsplit, hpos, hneg]
  calc
    (∑ i ∈ Jpos, a i) + -∑ i ∈ Jneg, a i ≤
        |∑ i ∈ Jpos, a i| + |∑ i ∈ Jneg, a i| := by
      apply add_le_add
      · exact le_abs_self _
      · exact neg_le_abs _
    _ ≤ C + C := add_le_add hposBound hnegBound
    _ = 2 * C := by ring

theorem inner_selfAdjoint_eq_re
    (operator : Op) (hself : operator.adjoint = operator)
    (u : finiteSCarrier) :
    ⟪u, operator u⟫_ℂ = ((⟪u, operator u⟫_ℂ).re : ℂ) := by
  symm
  apply Complex.conj_eq_iff_re.mp
  calc
    star (⟪u, operator u⟫_ℂ) =
        ⟪operator u, u⟫_ℂ := inner_conj_symm (𝕜 := ℂ) _ _
    _ = ⟪u, operator.adjoint u⟫_ℂ := by
      rw [ContinuousLinearMap.adjoint_inner_right]
    _ = ⟪u, operator u⟫_ℂ := by rw [hself]

theorem isTraceClassAlong_of_selfAdjoint_finiteDiagonalBound
    {ι : Type*} (basis : HilbertBasis ι ℂ finiteSCarrier)
    (operator : Op) (hself : operator.adjoint = operator) (C : ℝ)
    (hbound : ∀ J : Finset ι,
      |∑ i ∈ J, (⟪basis i, operator (basis i)⟫_ℂ).re| ≤ C) :
    PositiveTrace.IsTraceClassAlong basis operator := by
  rw [PositiveTrace.IsTraceClassAlong]
  apply Summable.of_norm
  have habs : Summable fun i =>
      |(⟪basis i, operator (basis i)⟫_ℂ).re| :=
    summable_abs_of_bounded_finset_signed_sums
      (fun i => (⟪basis i, operator (basis i)⟫_ℂ).re) C hbound
  have hnorm :
      (fun i => ‖⟪basis i, operator (basis i)⟫_ℂ‖) =
        fun i => |(⟪basis i, operator (basis i)⟫_ℂ).re| := by
    funext i
    let z := ⟪basis i, operator (basis i)⟫_ℂ
    have hz : z = (z.re : ℂ) :=
      inner_selfAdjoint_eq_re operator hself (basis i)
    calc
      ‖z‖ = ‖(z.re : ℂ)‖ := congrArg norm hz
      _ = |z.re| := by
        rw [Complex.norm_real, Real.norm_eq_abs]
  rw [hnorm]
  exact habs

theorem soninBandDifference_adjoint_eq
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    (soninBandDifference lambda family).adjoint =
      soninBandDifference lambda family := by
  rw [soninBandDifference]
  have hadj :
      (targetBandProjection lambda family - sourceBandProjection lambda).adjoint =
        (targetBandProjection lambda family).adjoint -
          (sourceBandProjection lambda).adjoint := by
    apply ContinuousLinearMap.ext
    intro u
    exact ext_inner_right ℂ fun v => by
      simp only [ContinuousLinearMap.adjoint_inner_left,
        ContinuousLinearMap.sub_apply, inner_sub_left, inner_sub_right]
  have htarget : (targetBandProjection lambda family).adjoint =
      targetBandProjection lambda family :=
    (targetBandProjection_isStarProjection lambda family)
      |>.isSelfAdjoint.adjoint_eq
  have hsource : (sourceBandProjection lambda).adjoint =
      sourceBandProjection lambda :=
    (sourceBandProjection_isStarProjection lambda)
      |>.isSelfAdjoint.adjoint_eq
  rw [hadj, htarget, hsource]

theorem rootSandwichedBandResponse_adjoint_eq
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    (rootSandwichedBandResponse owner lambda family).adjoint =
      rootSandwichedBandResponse owner lambda family := by
  rw [rootSandwichedBandResponse, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
    soninBandDifference_adjoint_eq lambda family]
  apply ContinuousLinearMap.ext
  intro u
  rfl

theorem ordinaryTraceAlong_selfAdjoint_im_eq_zero
    {ι : Type*} (basis : HilbertBasis ι ℂ finiteSCarrier)
    (operator : Op)
    (hself : operator.adjoint = operator) :
    (PositiveTrace.ordinaryTraceAlong basis operator).im = 0 := by
  have htrace := PositiveTrace.ordinaryTraceAlong_adjoint basis operator
  rw [hself] at htrace
  have him := congrArg Complex.im htrace
  rw [Complex.star_def] at him
  simp only [Complex.conj_im] at him
  linarith

theorem ordinaryTraceAlong_rootSandwichedBandResponse_im_eq_zero
    {ι : Type*} (basis : HilbertBasis ι ℂ finiteSCarrier)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    (PositiveTrace.ordinaryTraceAlong basis
      (rootSandwichedBandResponse owner lambda family)).im = 0 := by
  exact ordinaryTraceAlong_selfAdjoint_im_eq_zero basis _
    (rootSandwichedBandResponse_adjoint_eq owner lambda family)

theorem ordinaryTraceAlong_rootSandwichedBandResponse_eq_re
    {ι : Type*} (basis : HilbertBasis ι ℂ finiteSCarrier)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    PositiveTrace.ordinaryTraceAlong basis
      (rootSandwichedBandResponse owner lambda family) =
      ((PositiveTrace.ordinaryTraceAlong basis
        (rootSandwichedBandResponse owner lambda family)).re : ℂ) := by
  apply Complex.ext
  · simp
  · exact ordinaryTraceAlong_rootSandwichedBandResponse_im_eq_zero basis
      owner lambda family

theorem canonicalOrdinaryTraceAlong_norm_le_supportRadiusPolynomial_of_finiteDiagonalBound
    {ι : Type*} (basis : HilbertBasis ι ℂ finiteSCarrier)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    (htrace : PositiveTrace.IsTraceClassAlong basis
      (rootSandwichedBandResponse owner lambda (canonicalFamily owner)))
    (hbound : ∀ J : Finset ι,
      |∫ alpha : ℝ in 0..1,
        ∑ i ∈ J,
          (⟪basis i, actualMovingSoninRootFlow owner lambda alpha
            (canonicalFamily owner).visiblePrimes (basis i)⟫_ℂ).re| ≤
        2 * (owner.supportRadius + Real.log 3) *
          (1 + owner.supportRadius + Real.log 3)) :
    ‖PositiveTrace.ordinaryTraceAlong basis
      (rootSandwichedBandResponse owner lambda (canonicalFamily owner))‖ ≤
      2 * (owner.supportRadius + Real.log 3) *
        (1 + owner.supportRadius + Real.log 3) := by
  rw [ordinaryTraceAlong_rootSandwichedBandResponse_eq_re basis owner lambda]
  simpa only [Complex.norm_real, Real.norm_eq_abs] using
    (canonicalOrdinaryTraceAlong_re_abs_le_supportRadiusPolynomial_of_finiteDiagonalBound
      basis owner lambda htrace hbound)

end CCM24FiniteSMovingBandSelfAdjointTrace
end CCM25Concrete
end Source
end ConnesWeilRH
