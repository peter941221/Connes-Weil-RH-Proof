/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaAmbientDefectFactorization

/-!
# Ambient-channel difference identity

The normalized Euler transport and the antiresonant ambient-loss factor are
not merely comparable at the level of norms. Their adjoints satisfy the exact
one-prime identity

```text
H_p† - I = -sqrt(q_p) * E_p†.
```

This is the scalar bridge needed when an adjacent signed coframe telescope is
rewritten into the ambient-loss channel. It introduces no inverse transport,
spectral gap, or source estimate.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeAmbientChannel

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCompletedJuliaAmbientDefectFactorization
open CCM24FiniteSProjectionTrace

theorem normalizedPrimeEulerFrameTransport_adjoint_sub_id_eq_neg_sqrtCoefficient_smul_primeEulerAmbientLossFactor_adjoint
    (p : CCM24VisiblePrime) :
    (normalizedPrimeEulerFrameTransport p)† -
        ContinuousLinearMap.id ℂ finiteSCarrier =
      -((Real.sqrt (ccm24PrimeEulerCoefficient p) : ℂ) •
        (primeEulerAmbientLossFactor p)†) := by
  have hcoeff : 0 ≤ ccm24PrimeEulerCoefficient p :=
    ccm24PrimeEulerCoefficient_nonneg p
  have hdenReal : (1 + ccm24PrimeEulerCoefficient p : ℝ) ≠ 0 := by
    exact ne_of_gt (add_pos_of_pos_of_nonneg zero_lt_one hcoeff)
  have hdenComplex :
      (1 + (ccm24PrimeEulerCoefficient p : ℂ)) ≠ 0 := by
    exact_mod_cast hdenReal
  have hsqrt :
      (Real.sqrt (ccm24PrimeEulerCoefficient p) : ℂ) ^ 2 =
        (ccm24PrimeEulerCoefficient p : ℂ) := by
    exact_mod_cast Real.sq_sqrt hcoeff
  rw [normalizedPrimeEulerFrameTransport_adjoint_eq,
    primeEulerAmbientLossFactor_adjoint_eq]
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.neg_apply, map_sub, map_add, smul_sub, smul_add,
    smul_smul]
  rw [primeEulerAmbientLossScale]
  push_cast
  have hscale :
      (Real.sqrt (ccm24PrimeEulerCoefficient p) : ℂ) *
          ((Real.sqrt (ccm24PrimeEulerCoefficient p) : ℂ) /
            (1 + (ccm24PrimeEulerCoefficient p : ℂ))) =
        (ccm24PrimeEulerCoefficient p : ℂ) *
          (1 + (ccm24PrimeEulerCoefficient p : ℂ))⁻¹ := by
    rw [div_eq_mul_inv, ← mul_assoc, ← pow_two, hsqrt]
  rw [hscale]
  have hcoeff :
      (1 + (ccm24PrimeEulerCoefficient p : ℂ))⁻¹ - 1 =
        -(ccm24PrimeEulerCoefficient p : ℂ) *
          (1 + (ccm24PrimeEulerCoefficient p : ℂ))⁻¹ := by
    field_simp [hdenComplex]
    ring
  calc
    (1 + (ccm24PrimeEulerCoefficient p : ℂ))⁻¹ • x -
          ((1 + (ccm24PrimeEulerCoefficient p : ℂ))⁻¹ *
            (ccm24PrimeEulerCoefficient p : ℂ)) •
            (cc20GlobalLogTranslation
              (Real.log p)).toContinuousLinearMap x - x =
        ((1 + (ccm24PrimeEulerCoefficient p : ℂ))⁻¹ - 1) • x -
          ((ccm24PrimeEulerCoefficient p : ℂ) *
            (1 + (ccm24PrimeEulerCoefficient p : ℂ))⁻¹) •
            (cc20GlobalLogTranslation
              (Real.log p)).toContinuousLinearMap x := by
      module
    _ = -((ccm24PrimeEulerCoefficient p : ℂ) *
          (1 + (ccm24PrimeEulerCoefficient p : ℂ))⁻¹) • x -
          ((ccm24PrimeEulerCoefficient p : ℂ) *
            (1 + (ccm24PrimeEulerCoefficient p : ℂ))⁻¹) •
            (cc20GlobalLogTranslation
              (Real.log p)).toContinuousLinearMap x := by
      rw [hcoeff]
      module
    _ = -(((ccm24PrimeEulerCoefficient p : ℂ) *
          (1 + (ccm24PrimeEulerCoefficient p : ℂ))⁻¹) • x +
          ((ccm24PrimeEulerCoefficient p : ℂ) *
          (1 + (ccm24PrimeEulerCoefficient p : ℂ))⁻¹) •
            (cc20GlobalLogTranslation
              (Real.log p)).toContinuousLinearMap x) := by
      simp only [neg_smul, sub_eq_add_neg, neg_add]

/-! ## A reusable one-step signed difference -/

/-!
For any output row, the adjacent normalized Euler difference can be pulled
back through the ambient-loss coordinate.  Keeping this as a composition
identity is important: later estimates can add it to a boundary readout
before taking a norm.
-/
theorem comp_normalizedPrimeEulerFrameTransport_adjoint_sub_comp_eq_neg_sqrtCoefficient_comp_ambientLossFactor_adjoint
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    (p : CCM24VisiblePrime)
    (row : finiteSCarrier →L[ℂ] G) :
    row ∘L (normalizedPrimeEulerFrameTransport p)† - row =
      -((Real.sqrt (ccm24PrimeEulerCoefficient p) : ℂ) •
        (row ∘L (primeEulerAmbientLossFactor p)†)) := by
  have htransport :=
    normalizedPrimeEulerFrameTransport_adjoint_sub_id_eq_neg_sqrtCoefficient_smul_primeEulerAmbientLossFactor_adjoint
      p
  apply ContinuousLinearMap.ext
  intro x
  have hpoint := congrArg
    (fun operator : finiteSCarrier →L[ℂ] finiteSCarrier => row (operator x))
    htransport
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.neg_apply] at hpoint ⊢
  simpa only [map_sub, map_neg, map_smul] using hpoint

end CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeAmbientChannel
end CCM25Concrete
end Source
end ConnesWeilRH
