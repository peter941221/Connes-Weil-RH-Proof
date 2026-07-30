/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorSingleChannelKernel
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorSingleChannelRouteDomination

/-!
# Renewal-deviation form of the antiresonant denominator

The complete Proof 628 denominator has the exact same-order normal form

```text
sqrt(q_p) L_p^dagger N_p^dagger
  = N_p^dagger - rho_p I.
```

No factors are commuted.  After the actual new frame is attached, the
route-uniform relative-energy statement is equivalent, with the same bound,
to a weighted estimate against this normalized renewal deviation.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorSingleChannelRenewalDeviation

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCausalMarkov
open CCM24FiniteSCompletedJuliaAmbientDefectFactorization
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorGap
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorRouteValidFactorization
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorSingleChannelFactorization
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorSingleChannelKernel
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeAmbientChannel
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSProjectionTrace
open CCM24FiniteSSchurMarkovPairing

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! ## Exact ambient and source normal forms -/

/-- The normalized inverse differs from its Markov scalar by exactly the
antiresonant loss followed by that same inverse. -/
theorem primeEulerRenewalDeviation_eq_sqrtCoefficient_smul_lossAdjoint_comp_inverseAdjoint
    (p : CCM24VisiblePrime) :
    (normalizedPrimeEulerInverse p)† -
        (primeSchurMarkovScalar p : ℂ) •
          ContinuousLinearMap.id ℂ finiteSCarrier =
      (Real.sqrt (ccm24PrimeEulerCoefficient p) : ℂ) •
        ((primeEulerAmbientLossFactor p)† ∘L
          (normalizedPrimeEulerInverse p)†) := by
  apply ContinuousLinearMap.ext
  intro x
  have hdiff := DFunLike.congr_fun
    (normalizedPrimeEulerFrameTransport_adjoint_sub_id_eq_neg_sqrtCoefficient_smul_primeEulerAmbientLossFactor_adjoint
      p) (((normalizedPrimeEulerInverse p)†) x)
  have hpair := DFunLike.congr_fun
    (normalizedPrimeEulerFrameTransport_adjoint_comp_inverse_adjoint p) x
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply] at hdiff
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply] at hpair
  rw [hpair] at hdiff
  have hneg := congrArg Neg.neg hdiff
  simpa only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply,
    neg_neg, neg_sub] using hneg

/-- The source-facing normalized renewal deviation. -/
noncomputable def suffixEulerFrameRenewalDeviationColumn
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    sourceSoninCarrier lambda →L[ℂ] finiteSCarrier :=
  ((normalizedPrimeEulerInverse p)† -
      (primeSchurMarkovScalar p : ℂ) •
        ContinuousLinearMap.id ℂ finiteSCarrier) ∘L
    (suffixEulerFrameSchurStep lambda p S).newFrame

/-- The renewed denominator is the renewal deviation with its exact
`sqrt(q_p)` scale restored. -/
theorem suffixEulerFrameRenewalDeviationColumn_eq_sqrtCoefficient_smul_renewedColumn
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixEulerFrameRenewalDeviationColumn lambda p S =
      (Real.sqrt (ccm24PrimeEulerCoefficient p) : ℂ) •
        suffixEulerFrameRenewedAntiresonantColumn lambda p S := by
  apply ContinuousLinearMap.ext
  intro x
  have hpoint := DFunLike.congr_fun
    (primeEulerRenewalDeviation_eq_sqrtCoefficient_smul_lossAdjoint_comp_inverseAdjoint
      p) ((suffixEulerFrameSchurStep lambda p S).newFrame x)
  simpa only [suffixEulerFrameRenewalDeviationColumn,
    suffixEulerFrameRenewedAntiresonantColumn,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply] using
      hpoint

/-- Pointwise norm readback of the exact scalar normal form. -/
theorem norm_suffixEulerFrameRenewalDeviationColumn_apply
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (x : sourceSoninCarrier lambda) :
    ‖suffixEulerFrameRenewalDeviationColumn lambda p S x‖ =
      Real.sqrt (ccm24PrimeEulerCoefficient p) *
        ‖suffixEulerFrameRenewedAntiresonantColumn lambda p S x‖ := by
  have hpoint := DFunLike.congr_fun
    (suffixEulerFrameRenewalDeviationColumn_eq_sqrtCoefficient_smul_renewedColumn
      lambda p S) x
  rw [hpoint, ContinuousLinearMap.smul_apply, norm_smul,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]

/-- Squaring the source normal form exposes the exact Euler weight. -/
theorem norm_sq_suffixEulerFrameRenewalDeviationColumn_apply
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (x : sourceSoninCarrier lambda) :
    ‖suffixEulerFrameRenewalDeviationColumn lambda p S x‖ ^ 2 =
      ccm24PrimeEulerCoefficient p *
        ‖suffixEulerFrameRenewedAntiresonantColumn lambda p S x‖ ^ 2 := by
  rw [norm_suffixEulerFrameRenewalDeviationColumn_apply, mul_pow,
    Real.sq_sqrt (ccm24PrimeEulerCoefficient_nonneg p)]

/-! ## Equivalent route-uniform weighted target -/

/-- Bone 1 written against the normalized renewal deviation.  The factor
`q_p` on the numerator is forced by the exact denominator scale. -/
def SuffixRawOldCarrierAntiresonantInteriorRouteUniformRenewalDeviationDomination
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (bound : ℝ) : Prop :=
  0 ≤ bound ∧
    ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixRouteValidStep p S →
        ∀ x : sourceSoninCarrier lambda,
          ccm24PrimeEulerCoefficient p *
              ‖signedCompressedInteriorOwner owner lambda p S x‖ ^ 2 ≤
            bound ^ 2 *
              ‖suffixEulerFrameRenewalDeviationColumn lambda p S x‖ ^ 2

theorem routeUniformRenewalDeviationDomination_of_renewedAmbientDomination
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {bound : ℝ}
    (hdom :
      SuffixRawOldCarrierAntiresonantInteriorRouteUniformRenewedAmbientDomination
        owner lambda bound) :
    SuffixRawOldCarrierAntiresonantInteriorRouteUniformRenewalDeviationDomination
      owner lambda bound := by
  refine ⟨hdom.1, ?_⟩
  intro p S hvalid x
  have hpoint := hdom.2 p S hvalid x
  have hq : 0 ≤ ccm24PrimeEulerCoefficient p :=
    ccm24PrimeEulerCoefficient_nonneg p
  have hnorm :=
    norm_sq_suffixEulerFrameRenewalDeviationColumn_apply lambda p S x
  calc
      ccm24PrimeEulerCoefficient p *
          ‖signedCompressedInteriorOwner owner lambda p S x‖ ^ 2 ≤
        ccm24PrimeEulerCoefficient p *
          (bound ^ 2 *
            ‖suffixEulerFrameRenewedAntiresonantColumn lambda p S x‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hpoint hq
    _ = bound ^ 2 *
          (ccm24PrimeEulerCoefficient p *
            ‖suffixEulerFrameRenewedAntiresonantColumn lambda p S x‖ ^ 2) := by
      ring
    _ = bound ^ 2 *
          ‖suffixEulerFrameRenewalDeviationColumn lambda p S x‖ ^ 2 := by
      rw [← hnorm]

theorem renewedAmbientDomination_of_routeUniformRenewalDeviationDomination
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {bound : ℝ}
    (hdom :
      SuffixRawOldCarrierAntiresonantInteriorRouteUniformRenewalDeviationDomination
        owner lambda bound) :
    SuffixRawOldCarrierAntiresonantInteriorRouteUniformRenewedAmbientDomination
      owner lambda bound := by
  refine ⟨hdom.1, ?_⟩
  intro p S hvalid x
  have hpoint := hdom.2 p S hvalid x
  have hp0 : (0 : ℝ) < (p : ℝ) := by
    exact_mod_cast (lt_trans Nat.zero_lt_one p.property)
  have hq : 0 < ccm24PrimeEulerCoefficient p := by
    unfold ccm24PrimeEulerCoefficient
    exact div_pos zero_lt_one (Real.sqrt_pos.2 hp0)
  have hnorm :=
    norm_sq_suffixEulerFrameRenewalDeviationColumn_apply lambda p S x
  have hscaled :
      ccm24PrimeEulerCoefficient p *
          ‖signedCompressedInteriorOwner owner lambda p S x‖ ^ 2 ≤
        ccm24PrimeEulerCoefficient p *
          (bound ^ 2 *
            ‖suffixEulerFrameRenewedAntiresonantColumn lambda p S x‖ ^ 2) := by
    calc
      ccm24PrimeEulerCoefficient p *
          ‖signedCompressedInteriorOwner owner lambda p S x‖ ^ 2 ≤
        bound ^ 2 *
          ‖suffixEulerFrameRenewalDeviationColumn lambda p S x‖ ^ 2 :=
      hpoint
    _ = bound ^ 2 *
          (ccm24PrimeEulerCoefficient p *
            ‖suffixEulerFrameRenewedAntiresonantColumn lambda p S x‖ ^ 2) := by
      rw [hnorm]
    _ = ccm24PrimeEulerCoefficient p *
          (bound ^ 2 *
            ‖suffixEulerFrameRenewedAntiresonantColumn lambda p S x‖ ^ 2) := by
      ring
  nlinarith

/-- The route-uniform Bone 1 target is unchanged after moving the explicit
`sqrt(q_p)` denominator scale to the numerator energy. -/
theorem routeUniformRenewedAmbientDomination_iff_renewalDeviationDomination
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (bound : ℝ) :
    SuffixRawOldCarrierAntiresonantInteriorRouteUniformRenewedAmbientDomination
        owner lambda bound ↔
      SuffixRawOldCarrierAntiresonantInteriorRouteUniformRenewalDeviationDomination
        owner lambda bound := by
  constructor
  · exact routeUniformRenewalDeviationDomination_of_renewedAmbientDomination
  · exact renewedAmbientDomination_of_routeUniformRenewalDeviationDomination

end CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorSingleChannelRenewalDeviation
end CCM25Concrete
end Source
end ConnesWeilRH
