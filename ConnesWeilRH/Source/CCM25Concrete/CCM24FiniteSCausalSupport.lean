/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSGramResponse

/-!
# Causal radial-support factorization for the finite Euler transport

The finite Euler transport and its inverse preserve the actual upper radial
support subspace.  This module records the resulting block-triangular
identities on the literal common-log carrier.  These are source-specific
identities: they do not follow merely from invertibility or from a lower
operator bound.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCausalSupport

open scoped ComplexConjugate

open CC20Concrete
open CCM24FiniteSProjectionTrace
open CCM24FiniteSGramResponse

/-- The orthogonal complement of the common upper radial-support projection. -/
noncomputable def radialComplementProjection (lambda : CCM24SoninScale) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  ContinuousLinearMap.id ℂ finiteSCarrier - radialSupportProjection lambda

/-- The ambient finite Euler transport selected by the same prime-power
family as the arithmetic ledger. -/
noncomputable def finiteEulerTransportOperator
    (family : FinitePrimePowerFamily) : finiteSCarrier →L[ℂ] finiteSCarrier :=
  (ccm24FiniteEulerTransportEquiv family.visiblePrimes).toContinuousLinearMap

/-- The inverse ambient finite Euler transport. -/
noncomputable def finiteEulerInverseOperator
    (family : FinitePrimePowerFamily) : finiteSCarrier →L[ℂ] finiteSCarrier :=
  (ccm24FiniteEulerTransportEquiv family.visiblePrimes).symm.toContinuousLinearMap

theorem radialSupportProjection_comp_transport_comp_self
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    radialSupportProjection lambda ∘L
        finiteEulerTransportOperator family ∘L
        radialSupportProjection lambda =
      finiteEulerTransportOperator family ∘L
        radialSupportProjection lambda := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply]
  apply (ccm24LogRadialSupportProjection_eq_self_iff lambda _).mpr
  apply ccm24FiniteEulerTransportEquiv_mem_logRadialSupport
  exact Submodule.starProjection_apply_mem _ _

theorem radialComplementProjection_comp_transport_comp_radialSupport
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    radialComplementProjection lambda ∘L
        finiteEulerTransportOperator family ∘L
        radialSupportProjection lambda = 0 := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [radialComplementProjection, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.zero_apply]
  apply sub_eq_zero.mpr
  simpa only [ContinuousLinearMap.comp_apply] using
    (congrFun (congrArg DFunLike.coe
      (radialSupportProjection_comp_transport_comp_self lambda family)) u).symm

theorem radialSupportProjection_comp_inverse_comp_self
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    radialSupportProjection lambda ∘L
        finiteEulerInverseOperator family ∘L
        radialSupportProjection lambda =
      finiteEulerInverseOperator family ∘L
        radialSupportProjection lambda := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply]
  apply (ccm24LogRadialSupportProjection_eq_self_iff lambda _).mpr
  apply ccm24FiniteEulerTransportEquiv_symm_mem_logRadialSupport
  exact Submodule.starProjection_apply_mem _ _

theorem radialComplementProjection_comp_inverse_comp_radialSupport
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    radialComplementProjection lambda ∘L
        finiteEulerInverseOperator family ∘L
        radialSupportProjection lambda = 0 := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [radialComplementProjection, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.zero_apply]
  apply sub_eq_zero.mpr
  simpa only [ContinuousLinearMap.comp_apply] using
    (congrFun (congrArg DFunLike.coe
      (radialSupportProjection_comp_inverse_comp_self lambda family)) u).symm

theorem sourceInclusion_mem_radialSupport
    (lambda : CCM24SoninScale) (u : sourceSoninCarrier lambda) :
    sourceInclusion lambda u ∈
      ccm24LogRadialSupportClosedSubspace lambda := by
  exact (Submodule.mem_inf.mp u.property).1

theorem radialSupportProjection_comp_sourceInclusion
    (lambda : CCM24SoninScale) :
    radialSupportProjection lambda ∘L sourceInclusion lambda =
      sourceInclusion lambda := by
  apply ContinuousLinearMap.ext
  intro u
  exact (ccm24LogRadialSupportProjection_eq_self_iff lambda _).mpr
    (sourceInclusion_mem_radialSupport lambda u)

/-- The transported Sonin frame stays inside the actual upper radial support.
This is the concrete causal input missing from abstract direct-sum guards. -/
theorem finiteEulerFrame_mem_radialSupport
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (u : sourceSoninCarrier lambda) :
    finiteEulerFrame lambda family u ∈
      ccm24LogRadialSupportClosedSubspace lambda := by
  rw [finiteEulerFrame_eq_transport_comp_inclusion]
  exact ccm24FiniteEulerTransportEquiv_mem_logRadialSupport
    lambda family.visiblePrimes (sourceInclusion_mem_radialSupport lambda u)

theorem radialSupportProjection_comp_finiteEulerFrame
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    radialSupportProjection lambda ∘L finiteEulerFrame lambda family =
      finiteEulerFrame lambda family := by
  apply ContinuousLinearMap.ext
  intro u
  exact (ccm24LogRadialSupportProjection_eq_self_iff lambda _).mpr
    (finiteEulerFrame_mem_radialSupport lambda family u)

theorem radialComplementProjection_comp_finiteEulerFrame
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    radialComplementProjection lambda ∘L finiteEulerFrame lambda family = 0 := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [radialComplementProjection, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.zero_apply]
  apply sub_eq_zero.mpr
  simpa only [ContinuousLinearMap.comp_apply] using
    (congrFun (congrArg DFunLike.coe
      (radialSupportProjection_comp_finiteEulerFrame lambda family)) u).symm

end CCM24FiniteSCausalSupport
end CCM25Concrete
end Source
end ConnesWeilRH
