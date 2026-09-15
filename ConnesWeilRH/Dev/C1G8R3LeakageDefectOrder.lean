/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3LeakageDoubledShift

/-!
# R3 leakage defect: positive contraction and exact leakage energy

The doubled-shift normal form identifies the open leakage input as
`p_b - p_b q_1 p_b`.  This leaf records its order structure on the actual
finite-S carrier.  The defect is the compression of the complementary
Fourier projection, hence it is positive and bounded by the radial projection
and by the identity.  Its quadratic form is exactly the squared norm of the
complementary leakage column.

No Schatten estimate, trace limit, sign conclusion, or RH premise is used.
-/

namespace ConnesWeilRH
namespace Dev

open Source
open Source.CC20Concrete
open Source.CCM25Concrete
open Source.CCM25Concrete.CCM24FiniteSProjectionTrace
open Source.CCM25Concrete.CCM24FiniteSRootCompletedFirstJet
open Source.CCM25Concrete.CCM24UnitScaleProlateAlignment
open scoped ComplexConjugate InnerProductSpace

local notation "Carrier" =>
  Source.CCM25Concrete.CCM24FiniteSProjectionTrace.finiteSCarrier
local notation "Op" => Carrier →L[ℂ] Carrier

theorem doubledShiftRadialProjection_sub_alternatingProduct_eq_complement_sandwich
    (b : ℝ) :
    doubledShiftRadialProjection b - doubledShiftAlternatingProduct b =
      doubledShiftRadialProjection b *
        (1 - sourceFourierSupportProjection unitSoninScale) *
          doubledShiftRadialProjection b := by
  unfold doubledShiftAlternatingProduct
  let p : Op := doubledShiftRadialProjection b
  let q : Op := sourceFourierSupportProjection unitSoninScale
  have hp : p * p = p :=
    (doubledShiftRadialProjection_isStarProjection b).isIdempotentElem
  change p - p * q * p = p * (1 - q) * p
  calc
    p - p * q * p = p * p - p * q * p := by rw [hp]
    _ = p * (1 - q) * p := by noncomm_ring

theorem doubledShiftRadialProjection_sub_alternatingProduct_eq_adjoint_comp_self
    (b : ℝ) :
    doubledShiftRadialProjection b - doubledShiftAlternatingProduct b =
    ((1 - sourceFourierSupportProjection unitSoninScale) *
          doubledShiftRadialProjection b).adjoint *
        ((1 - sourceFourierSupportProjection unitSoninScale) *
          doubledShiftRadialProjection b) := by
  rw [doubledShiftRadialProjection_sub_alternatingProduct_eq_complement_sandwich]
  let p : Op := doubledShiftRadialProjection b
  let q : Op := sourceFourierSupportProjection unitSoninScale
  have hq : IsStarProjection q :=
    sourceFourierSupportProjection_isStarProjection unitSoninScale
  have hqadj : ContinuousLinearMap.adjoint (1 - q) = 1 - q := by
    simpa only [ContinuousLinearMap.one_def, map_sub] using
      hq.one_sub.isSelfAdjoint.adjoint_eq
  have hp : ContinuousLinearMap.adjoint p = p :=
    (doubledShiftRadialProjection_isStarProjection b).isSelfAdjoint.adjoint_eq
  have hqid : IsIdempotentElem (1 - q) := hq.one_sub.isIdempotentElem
  have hqcomp : (1 - q) ∘L (1 - q) = 1 - q := by
    simpa only [ContinuousLinearMap.mul_def] using hqid
  change p * (1 - q) * p =
    ContinuousLinearMap.adjoint ((1 - q) * p) * ((1 - q) * p)
  simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.adjoint_comp,
    hqadj, hp, ContinuousLinearMap.comp_assoc]
  apply ContinuousLinearMap.ext
  intro v
  have hqcomp_apply := DFunLike.congr_fun hqcomp (p v)
  simp only [ContinuousLinearMap.comp_apply] at hqcomp_apply ⊢
  rw [hqcomp_apply]

theorem doubledShiftRadialProjection_sub_alternatingProduct_isPositive
    (b : ℝ) :
    (doubledShiftRadialProjection b - doubledShiftAlternatingProduct b).IsPositive := by
  rw [doubledShiftRadialProjection_sub_alternatingProduct_eq_complement_sandwich]
  let p : Op := doubledShiftRadialProjection b
  let q : Op := sourceFourierSupportProjection unitSoninScale
  have hq : (1 - q).IsPositive :=
    ContinuousLinearMap.IsPositive.of_isStarProjection
      (sourceFourierSupportProjection_isStarProjection unitSoninScale).one_sub
  have hp : IsSelfAdjoint p := isSelfAdjoint_starProjection _
  have hpos := hq.conj_adjoint p
  rw [hp.adjoint_eq] at hpos
  simpa only [p, q, ContinuousLinearMap.mul_def] using hpos

theorem doubledShiftRadialProjection_sub_alternatingProduct_le_radialProjection
    (b : ℝ) :
    doubledShiftRadialProjection b - doubledShiftAlternatingProduct b <=
      doubledShiftRadialProjection b := by
  rw [ContinuousLinearMap.le_def]
  simpa only [sub_sub_cancel] using
    doubledShiftAlternatingProduct_isPositive b

theorem doubledShiftRadialProjection_sub_alternatingProduct_le_id
    (b : ℝ) :
    doubledShiftRadialProjection b - doubledShiftAlternatingProduct b <=
      ContinuousLinearMap.id ℂ Carrier := by
  apply (doubledShiftRadialProjection_sub_alternatingProduct_le_radialProjection b).trans
  rw [ContinuousLinearMap.le_def]
  exact ContinuousLinearMap.IsPositive.of_isStarProjection
    (doubledShiftRadialProjection_isStarProjection b).one_sub

theorem doubledShiftRadialProjection_sub_alternatingProduct_norm_le_one
    (b : ℝ) :
    ‖doubledShiftRadialProjection b - doubledShiftAlternatingProduct b‖ ≤ 1 := by
  rw [doubledShiftRadialProjection_sub_alternatingProduct_eq_complement_sandwich]
  let p : Op := doubledShiftRadialProjection b
  let q : Op := sourceFourierSupportProjection unitSoninScale
  have hp : ‖p‖ ≤ 1 :=
    IsStarProjection.norm_le _ (doubledShiftRadialProjection_isStarProjection b)
  have hq : ‖1 - q‖ ≤ 1 :=
    IsStarProjection.norm_le _
      (sourceFourierSupportProjection_isStarProjection unitSoninScale).one_sub
  calc
    ‖doubledShiftRadialProjection b *
        (1 - sourceFourierSupportProjection unitSoninScale) *
          doubledShiftRadialProjection b‖ = ‖p * (1 - q) * p‖ := by rfl
    _ ≤ ‖p * (1 - q)‖ * ‖p‖ := norm_mul_le _ _
    _ ≤ (‖p‖ * ‖1 - q‖) * ‖p‖ := by
      gcongr
      exact norm_mul_le _ _
    _ ≤ (1 * 1) * 1 := by gcongr
    _ = 1 := by norm_num

theorem doubledShiftRadialProjection_sub_alternatingProduct_postcomp_basisEnergy_le
    {ι : Type*} (b : ℝ) (basis : HilbertBasis ι ℂ Carrier)
    (factor : Carrier →L[ℂ] Carrier)
    (hfactor : Summable (fun i => ‖factor (basis i)‖ ^ 2)) :
    (∑' i, ‖((doubledShiftRadialProjection b -
      doubledShiftAlternatingProduct b) ∘L factor) (basis i)‖ ^ 2) ≤
      ∑' i, ‖factor (basis i)‖ ^ 2 := by
  exact basisEnergy_postcomp_le_of_norm_le_one basis factor
    (doubledShiftRadialProjection b - doubledShiftAlternatingProduct b)
    hfactor (doubledShiftRadialProjection_sub_alternatingProduct_norm_le_one b)

theorem doubledShiftRadialProjection_sub_alternatingProduct_unit_range_leg_energy_le
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    {ι : Type*} (b : ℝ) (basis : HilbertBasis ι ℂ Carrier) :
    (∑' i, ‖((doubledShiftRadialProjection b -
      doubledShiftAlternatingProduct b) ∘L
        sourceRootCompletedRangeLeftLeg owner unitSoninScale) (basis i)‖ ^ 2) ≤
      ∑' i, ‖sourceRootCompletedRangeLeftLeg owner unitSoninScale
        (basis i)‖ ^ 2 := by
  exact doubledShiftRadialProjection_sub_alternatingProduct_postcomp_basisEnergy_le
    b basis (sourceRootCompletedRangeLeftLeg owner unitSoninScale)
    (sourceRootCompletedRangeLeftLeg_unit_summable owner basis)

theorem doubledShiftRadialProjection_sub_alternatingProduct_re_inner_eq_normSq
    (b : ℝ) (v : Carrier) :
    (⟪v, (doubledShiftRadialProjection b -
      doubledShiftAlternatingProduct b) v⟫_ℂ).re =
      ‖((1 - sourceFourierSupportProjection unitSoninScale) *
        doubledShiftRadialProjection b) v‖ ^ 2 := by
  rw [doubledShiftRadialProjection_sub_alternatingProduct_eq_adjoint_comp_self]
  exact (ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right
    ((1 - sourceFourierSupportProjection unitSoninScale) *
      doubledShiftRadialProjection b) v).symm

end Dev
end ConnesWeilRH
