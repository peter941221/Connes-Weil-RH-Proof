/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.CCM24EulerTransport
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# CCM24 radial support on the global logarithmic carrier

For `rho = exp t`, the condition that a radial function vanish for
`rho < lambda` is exactly vanishing on `t < log lambda`. This module realizes
that condition as the kernel of the genuine `L2` restriction map. It then
proves that the concrete finite Euler transport and its inverse preserve this
closed support subspace.
-/

namespace ConnesWeilRH
namespace Source
namespace CC20Concrete

open MeasureTheory Set

/-- A positive CCM24 Sonin support scale. -/
abbrev CCM24SoninScale := {lambda : ℝ // 0 < lambda}

/-- The forbidden lower logarithmic region `t < log lambda`. -/
noncomputable def ccm24LogRadialLowerRegion
    (lambda : CCM24SoninScale) : Set ℝ :=
  Set.Iio (Real.log lambda)

theorem measurableSet_ccm24LogRadialLowerRegion
    (lambda : CCM24SoninScale) :
    MeasurableSet (ccm24LogRadialLowerRegion lambda) :=
  measurableSet_Iio

/-- Restriction to the forbidden radial region. -/
noncomputable def ccm24LogRadialLowerRestriction
    (lambda : CCM24SoninScale) :
    cc20GlobalLogCrossingL2 →L[ℂ]
      Lp ℂ 2 (volume.restrict (ccm24LogRadialLowerRegion lambda)) :=
  LpToLpRestrictCLM ℝ ℂ ℂ volume 2 (ccm24LogRadialLowerRegion lambda)

/-- The actual closed radial support condition on the common logarithmic
carrier: functions that vanish below `log lambda`. -/
noncomputable def ccm24LogRadialSupportClosedSubspace
    (lambda : CCM24SoninScale) :
    ClosedSubmodule ℂ cc20GlobalLogCrossingL2 where
  toSubmodule := (ccm24LogRadialLowerRestriction lambda).ker
  isClosed' := (ccm24LogRadialLowerRestriction lambda).isClosed_ker

/-- The canonical orthogonal projection onto the radial support subspace. -/
noncomputable def ccm24LogRadialSupportProjection
    (lambda : CCM24SoninScale) :
    cc20GlobalLogCrossingL2 →L[ℂ] cc20GlobalLogCrossingL2 :=
  (ccm24LogRadialSupportClosedSubspace lambda).toSubmodule.starProjection

theorem ccm24LogRadialSupportProjection_isStarProjection
    (lambda : CCM24SoninScale) :
    IsStarProjection (ccm24LogRadialSupportProjection lambda) :=
  isStarProjection_starProjection

/-- Membership is the source support condition itself, expressed almost
everywhere on the global logarithmic carrier. -/
theorem mem_ccm24LogRadialSupportClosedSubspace_iff
    (lambda : CCM24SoninScale) (u : cc20GlobalLogCrossingL2) :
    u ∈ ccm24LogRadialSupportClosedSubspace lambda ↔
      ∀ᵐ t ∂volume, t < Real.log lambda → u t = 0 := by
  constructor
  · intro hu
    change ccm24LogRadialLowerRestriction lambda u = 0 at hu
    have hzero :
        ∀ᵐ t ∂(volume.restrict (ccm24LogRadialLowerRegion lambda)),
          (ccm24LogRadialLowerRestriction lambda u : ℝ → ℂ) t = 0 := by
      rw [Lp.ext_iff] at hu
      filter_upwards
        [hu, Lp.coeFn_zero ℂ 2
          (volume.restrict (ccm24LogRadialLowerRegion lambda))] with
          t hzeroAt hzeroCoeAt
      rw [hzeroCoeAt] at hzeroAt
      exact hzeroAt
    have hcoe := LpToLpRestrictCLM_coeFn ℂ
      (ccm24LogRadialLowerRegion lambda) u
    have hrestricted :
        ∀ᵐ t ∂(volume.restrict (ccm24LogRadialLowerRegion lambda)),
          u t = 0 := by
      filter_upwards [hzero, hcoe] with t hzeroAt hcoeAt
      rw [← hcoeAt]
      exact hzeroAt
    have hambient :=
      (ae_restrict_iff'
        (measurableSet_ccm24LogRadialLowerRegion lambda)).mp hrestricted
    simpa only [ccm24LogRadialLowerRegion, Set.mem_Iio] using hambient
  · intro hu
    change ccm24LogRadialLowerRestriction lambda u = 0
    unfold ccm24LogRadialLowerRestriction
    rw [Lp.ext_iff]
    have hrestricted :
        ∀ᵐ t ∂(volume.restrict (ccm24LogRadialLowerRegion lambda)),
          u t = 0 := by
      apply (ae_restrict_iff'
        (measurableSet_ccm24LogRadialLowerRegion lambda)).mpr
      simpa only [ccm24LogRadialLowerRegion, Set.mem_Iio] using hu
    filter_upwards
      [LpToLpRestrictCLM_coeFn ℂ
        (ccm24LogRadialLowerRegion lambda) u,
        hrestricted,
        Lp.coeFn_zero ℂ 2
          (volume.restrict (ccm24LogRadialLowerRegion lambda))] with
          t hcoeAt hzeroAt hzeroCoeAt
    rw [hcoeAt, hzeroAt, hzeroCoeAt]
    rfl

theorem ccm24LogRadialSupportProjection_eq_self_iff
    (lambda : CCM24SoninScale) (u : cc20GlobalLogCrossingL2) :
    ccm24LogRadialSupportProjection lambda u = u ↔
      u ∈ ccm24LogRadialSupportClosedSubspace lambda :=
  Submodule.starProjection_eq_self_iff

/-- A translation toward smaller log coordinates preserves every upper
radial support condition. -/
theorem cc20GlobalLogTranslation_mem_ccm24LogRadialSupport
    (lambda : CCM24SoninScale) (b : ℝ) (hb : b ≤ 0)
    {u : cc20GlobalLogCrossingL2}
    (hu : u ∈ ccm24LogRadialSupportClosedSubspace lambda) :
    cc20GlobalLogTranslation b u ∈
      ccm24LogRadialSupportClosedSubspace lambda := by
  rw [mem_ccm24LogRadialSupportClosedSubspace_iff] at hu ⊢
  have hshift :=
    (measurePreserving_add_right volume b).quasiMeasurePreserving.ae hu
  filter_upwards
    [cc20GlobalLogTranslation_coeFn b u, hshift] with t htransAt hzeroAt
  intro ht
  rw [htransAt]
  exact hzeroAt (by linarith)

theorem ccm24PrimeEulerContraction_mem_logRadialSupport
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    {u : cc20GlobalLogCrossingL2}
    (hu : u ∈ ccm24LogRadialSupportClosedSubspace lambda) :
    ccm24PrimeEulerContraction p u ∈
      ccm24LogRadialSupportClosedSubspace lambda := by
  change (ccm24PrimeEulerCoefficient p : ℂ) •
      cc20GlobalLogTranslation (-Real.log p) u ∈
    ccm24LogRadialSupportClosedSubspace lambda
  apply (ccm24LogRadialSupportClosedSubspace lambda).smul_mem
  apply cc20GlobalLogTranslation_mem_ccm24LogRadialSupport lambda
  · exact neg_nonpos.mpr (Real.log_nonneg (by exact_mod_cast p.property.le))
  · exact hu

theorem ccm24PrimeEulerTransportEquiv_mem_logRadialSupport
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    {u : cc20GlobalLogCrossingL2}
    (hu : u ∈ ccm24LogRadialSupportClosedSubspace lambda) :
    ccm24PrimeEulerTransportEquiv p u ∈
      ccm24LogRadialSupportClosedSubspace lambda := by
  rw [ccm24PrimeEulerTransportEquiv_apply]
  exact (ccm24LogRadialSupportClosedSubspace lambda).sub_mem hu
    ((ccm24LogRadialSupportClosedSubspace lambda).smul_mem _
      (cc20GlobalLogTranslation_mem_ccm24LogRadialSupport lambda
        (-Real.log p)
        (neg_nonpos.mpr (Real.log_nonneg (by exact_mod_cast p.property.le))) hu))

theorem ccm24PrimeEulerInverseOperator_mem_logRadialSupport
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    {u : cc20GlobalLogCrossingL2}
    (hu : u ∈ ccm24LogRadialSupportClosedSubspace lambda) :
    ccm24PrimeEulerInverseOperator p u ∈
      ccm24LogRadialSupportClosedSubspace lambda := by
  have hsummable : Summable (fun n : ℕ => ccm24PrimeEulerContraction p ^ n) :=
    summable_geometric_of_norm_lt_one
      (norm_ccm24PrimeEulerContraction_lt_one p)
  unfold ccm24PrimeEulerInverseOperator
  have heval :
      (∑' n : ℕ, ccm24PrimeEulerContraction p ^ n) u =
        ∑' n : ℕ, (ccm24PrimeEulerContraction p ^ n) u := by
    simpa using
      (ContinuousLinearMap.apply ℂ cc20GlobalLogCrossingL2 u).map_tsum
        hsummable
  rw [heval]
  apply tsum_mem (ccm24LogRadialSupportClosedSubspace lambda).isClosed
  intro n
  induction n with
  | zero => simpa using hu
  | succ n ih =>
      rw [pow_succ', ContinuousLinearMap.mul_apply]
      exact ccm24PrimeEulerContraction_mem_logRadialSupport lambda p ih

theorem ccm24PrimeEulerTransportEquiv_symm_mem_logRadialSupport
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    {u : cc20GlobalLogCrossingL2}
    (hu : u ∈ ccm24LogRadialSupportClosedSubspace lambda) :
    (ccm24PrimeEulerTransportEquiv p).symm u ∈
      ccm24LogRadialSupportClosedSubspace lambda := by
  change (ccm24PrimeEulerTransportEquiv p).symm.toContinuousLinearMap u ∈
    ccm24LogRadialSupportClosedSubspace lambda
  rw [ccm24PrimeEulerTransportEquiv_symm_toContinuousLinearMap]
  exact ccm24PrimeEulerInverseOperator_mem_logRadialSupport lambda p hu

theorem ccm24FiniteEulerTransportEquiv_mem_logRadialSupport
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime)
    {u : cc20GlobalLogCrossingL2}
    (hu : u ∈ ccm24LogRadialSupportClosedSubspace lambda) :
    ccm24FiniteEulerTransportEquiv S u ∈
      ccm24LogRadialSupportClosedSubspace lambda := by
  induction S generalizing u with
  | nil => simpa using hu
  | cons p S ih =>
      rw [ccm24FiniteEulerTransportEquiv_cons_apply]
      exact ccm24PrimeEulerTransportEquiv_mem_logRadialSupport lambda p (ih hu)

theorem ccm24FiniteEulerTransportEquiv_symm_mem_logRadialSupport
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime)
    {u : cc20GlobalLogCrossingL2}
    (hu : u ∈ ccm24LogRadialSupportClosedSubspace lambda) :
    (ccm24FiniteEulerTransportEquiv S).symm u ∈
      ccm24LogRadialSupportClosedSubspace lambda := by
  induction S generalizing u with
  | nil => simpa using hu
  | cons p S ih =>
      have hmember := ih
        (ccm24PrimeEulerTransportEquiv_symm_mem_logRadialSupport lambda p hu)
      have heq :
          (ccm24FiniteEulerTransportEquiv (p :: S)).symm u =
            (ccm24FiniteEulerTransportEquiv S).symm
              ((ccm24PrimeEulerTransportEquiv p).symm u) := by
        apply (ccm24FiniteEulerTransportEquiv (p :: S)).injective
        rw [(ccm24FiniteEulerTransportEquiv (p :: S)).apply_symm_apply]
        rw [ccm24FiniteEulerTransportEquiv_cons_apply]
        rw [(ccm24FiniteEulerTransportEquiv S).apply_symm_apply]
        rw [(ccm24PrimeEulerTransportEquiv p).apply_symm_apply]
      rw [heq]
      exact hmember

/-- The concrete finite Euler equivalence maps the actual radial support
closed subspace onto itself, not merely into itself. -/
theorem ccm24FiniteEulerTransport_maps_logRadialSupport
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    ClosedSubmodule.mapEquiv (ccm24FiniteEulerTransportEquiv S)
        (ccm24LogRadialSupportClosedSubspace lambda) =
      ccm24LogRadialSupportClosedSubspace lambda := by
  ext u
  constructor
  · intro hu
    have hpre := (ClosedSubmodule.mem_mapEquiv_iff
      (ccm24FiniteEulerTransportEquiv S)
      (ccm24LogRadialSupportClosedSubspace lambda) u).1 hu
    simpa using ccm24FiniteEulerTransportEquiv_mem_logRadialSupport
      lambda S hpre
  · intro hu
    apply (ClosedSubmodule.mem_mapEquiv_iff
      (ccm24FiniteEulerTransportEquiv S)
      (ccm24LogRadialSupportClosedSubspace lambda) u).2
    exact ccm24FiniteEulerTransportEquiv_symm_mem_logRadialSupport
      lambda S hu

end CC20Concrete
end Source
end ConnesWeilRH
