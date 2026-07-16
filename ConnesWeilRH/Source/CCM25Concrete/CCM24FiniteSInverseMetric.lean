/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCausalSupport

/-!
# Ambient inverse metric for the finite Euler transport

This module constructs the inverse of the actual ambient Euler metric
`T†T` and records the condition-number-free normalized covariance.  The
normalization is performed before taking an operator norm.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSInverseMetric

open scoped InnerProduct

open CC20Concrete
open CCM24FiniteSProjectionTrace
open CCM24FiniteSGramResponse
open CCM24FiniteSCausalSupport

/-- The ambient inverse metric `T⁻¹(T⁻¹)†`. -/
noncomputable def finiteEulerAmbientGramInv
    (family : FinitePrimePowerFamily) : finiteSCarrier →L[ℂ] finiteSCarrier :=
  finiteEulerInverseOperator family ∘L
    (finiteEulerInverseOperator family)†

theorem inverse_comp_transport
    (family : FinitePrimePowerFamily) :
    finiteEulerInverseOperator family ∘L
        finiteEulerTransportOperator family =
      ContinuousLinearMap.id ℂ finiteSCarrier := by
  apply ContinuousLinearMap.ext
  intro u
  exact (ccm24FiniteEulerTransportEquiv family.visiblePrimes).symm_apply_apply u

theorem transport_comp_inverse
    (family : FinitePrimePowerFamily) :
    finiteEulerTransportOperator family ∘L
        finiteEulerInverseOperator family =
      ContinuousLinearMap.id ℂ finiteSCarrier := by
  apply ContinuousLinearMap.ext
  intro u
  exact (ccm24FiniteEulerTransportEquiv family.visiblePrimes).apply_symm_apply u

theorem transportAdjoint_comp_inverseAdjoint
    (family : FinitePrimePowerFamily) :
    (finiteEulerTransportOperator family)† ∘L
        (finiteEulerInverseOperator family)† =
      ContinuousLinearMap.id ℂ finiteSCarrier := by
  have h := congrArg ContinuousLinearMap.adjoint
    (inverse_comp_transport family)
  simpa only [ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_id] using h

theorem inverseAdjoint_comp_transportAdjoint
    (family : FinitePrimePowerFamily) :
    (finiteEulerInverseOperator family)† ∘L
        (finiteEulerTransportOperator family)† =
      ContinuousLinearMap.id ℂ finiteSCarrier := by
  have h := congrArg ContinuousLinearMap.adjoint
    (transport_comp_inverse family)
  simpa only [ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_id] using h

theorem finiteEulerAmbientGram_comp_inv
    (family : FinitePrimePowerFamily) :
    finiteEulerAmbientGram family ∘L finiteEulerAmbientGramInv family =
      ContinuousLinearMap.id ℂ finiteSCarrier := by
  apply ContinuousLinearMap.ext
  intro u
  change ((finiteEulerTransportOperator family)†)
      (finiteEulerTransportOperator family
        (finiteEulerInverseOperator family
          (((finiteEulerInverseOperator family)†) u))) = u
  rw [show finiteEulerTransportOperator family
      (finiteEulerInverseOperator family
        (((finiteEulerInverseOperator family)†) u)) =
      ((finiteEulerInverseOperator family)†) u by
    exact congrFun (congrArg DFunLike.coe (transport_comp_inverse family)) _]
  exact congrFun (congrArg DFunLike.coe
    (transportAdjoint_comp_inverseAdjoint family)) u

theorem finiteEulerAmbientGramInv_comp_gram
    (family : FinitePrimePowerFamily) :
    finiteEulerAmbientGramInv family ∘L finiteEulerAmbientGram family =
      ContinuousLinearMap.id ℂ finiteSCarrier := by
  apply ContinuousLinearMap.ext
  intro u
  change finiteEulerInverseOperator family
      (((finiteEulerInverseOperator family)†)
        (((finiteEulerTransportOperator family)†)
          (finiteEulerTransportOperator family u))) = u
  rw [show ((finiteEulerInverseOperator family)†)
      (((finiteEulerTransportOperator family)†)
        (finiteEulerTransportOperator family u)) =
      finiteEulerTransportOperator family u by
    exact congrFun (congrArg DFunLike.coe
      (inverseAdjoint_comp_transportAdjoint family)) _]
  exact congrFun (congrArg DFunLike.coe (inverse_comp_transport family)) u

theorem finiteEulerAmbientGramInv_isPositive
    (family : FinitePrimePowerFamily) :
    (finiteEulerAmbientGramInv family).IsPositive := by
  exact ContinuousLinearMap.isPositive_self_comp_adjoint
    (finiteEulerInverseOperator family)

/-- The Markov-normalized inverse transport `c_S T_S⁻¹`. -/
noncomputable def normalizedFiniteEulerInverse
    (family : FinitePrimePowerFamily) : finiteSCarrier →L[ℂ] finiteSCarrier :=
  (finiteEulerLowerFactor family.visiblePrimes : ℂ) •
    finiteEulerInverseOperator family

theorem norm_normalizedFiniteEulerInverse_le_one
    (family : FinitePrimePowerFamily) :
    ‖normalizedFiniteEulerInverse family‖ ≤ 1 := by
  exact norm_lowerFactor_smul_finiteEulerInverseOperator_le_one
    family.visiblePrimes

/-- The normalized inverse covariance is formed as `N N†`; this keeps the
Euler lower factor inside the positive operator before estimation. -/
noncomputable def normalizedFiniteEulerInverseCovariance
    (family : FinitePrimePowerFamily) : finiteSCarrier →L[ℂ] finiteSCarrier :=
  normalizedFiniteEulerInverse family ∘L
    (normalizedFiniteEulerInverse family)†

theorem normalizedFiniteEulerInverseCovariance_isPositive
    (family : FinitePrimePowerFamily) :
    (normalizedFiniteEulerInverseCovariance family).IsPositive := by
  exact ContinuousLinearMap.isPositive_self_comp_adjoint
    (normalizedFiniteEulerInverse family)

theorem norm_normalizedFiniteEulerInverseCovariance_le_one
    (family : FinitePrimePowerFamily) :
    ‖normalizedFiniteEulerInverseCovariance family‖ ≤ 1 := by
  calc
    ‖normalizedFiniteEulerInverseCovariance family‖ ≤
        ‖normalizedFiniteEulerInverse family‖ *
          ‖(normalizedFiniteEulerInverse family)†‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ = ‖normalizedFiniteEulerInverse family‖ *
          ‖normalizedFiniteEulerInverse family‖ := by
      rw [ContinuousLinearMap.adjoint.norm_map]
    _ ≤ 1 * 1 := mul_le_mul
      (norm_normalizedFiniteEulerInverse_le_one family)
      (norm_normalizedFiniteEulerInverse_le_one family)
      (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

end CCM24FiniteSInverseMetric
end CCM25Concrete
end Source
end ConnesWeilRH
