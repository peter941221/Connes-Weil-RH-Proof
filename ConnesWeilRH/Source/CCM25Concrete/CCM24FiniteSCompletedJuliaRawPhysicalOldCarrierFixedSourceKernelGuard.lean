/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierReduction
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Fixed-source approximate-kernel guard for the old-carrier analysis

The old-carrier analysis has a genuine, elementary small-coefficient channel.
For the empty suffix, feed it the fixed source frame `newSuffixFrame lambda []`.
The ambient loss is `O(sqrt(q_p))`, while the moving-boundary channel is
`O(q_p)`, where `q_p = p^(-1/2)`.  Thus this family is an actual approximate
kernel whenever `q_p -> 0` and the source vector is fixed.

This is not yet the Proof 583 obstruction: the one-prime boundary moment must
stay bounded below on the same columns, and the present estimate does not
provide that lower bound.  The point of this module is to rule out treating a
fixed source vector as if it already supplied the missing moment witness.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierFixedSourceKernelGuard

open scoped InnerProduct InnerProductSpace
open scoped Topology

open CC20Concrete
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCompletedJuliaAmbientDefectFactorization
open CCM24FiniteSCompletedJuliaRawPhysicalFactorization
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierReduction
open CCM24FiniteSFixedSourcePolar
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSProjectionTrace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) :
      CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

local notation "SourceOp" lambda =>
  sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda

/-! ## Elementary one-prime norm controls -/

theorem primeEulerAmbientLossFactor_adjoint_norm_le_two_sqrt_coefficient
    (p : CCM24VisiblePrime) :
    ‖(primeEulerAmbientLossFactor p)†‖ ≤
      2 * Real.sqrt (ccm24PrimeEulerCoefficient p) := by
  rw [primeEulerAmbientLossFactor_adjoint_eq]
  have hq : 0 ≤ ccm24PrimeEulerCoefficient p :=
    ccm24PrimeEulerCoefficient_nonneg p
  have hscale : 0 ≤ primeEulerAmbientLossScale p := by
    unfold primeEulerAmbientLossScale
    positivity
  have hscale_le : primeEulerAmbientLossScale p ≤
      Real.sqrt (ccm24PrimeEulerCoefficient p) := by
    unfold primeEulerAmbientLossScale
    apply (div_le_iff₀ (by linarith :
      0 < 1 + ccm24PrimeEulerCoefficient p)).2
    nlinarith [Real.sqrt_nonneg (ccm24PrimeEulerCoefficient p)]
  have htranslation :
      ‖(cc20GlobalLogTranslation
          (Real.log p)).toContinuousLinearMap‖ ≤ (1 : ℝ) := by
    exact (cc20GlobalLogTranslation
      (Real.log p)).norm_toContinuousLinearMap_le
  have hadd := ContinuousLinearMap.opNorm_add_le
    (ContinuousLinearMap.id ℂ finiteSCarrier)
    (cc20GlobalLogTranslation (Real.log p)).toContinuousLinearMap
  calc
    ‖(primeEulerAmbientLossScale p : ℂ) •
        (ContinuousLinearMap.id ℂ finiteSCarrier +
          (cc20GlobalLogTranslation
            (Real.log p)).toContinuousLinearMap)‖ =
      ‖(primeEulerAmbientLossScale p : ℂ)‖ *
        ‖ContinuousLinearMap.id ℂ finiteSCarrier +
          (cc20GlobalLogTranslation
            (Real.log p)).toContinuousLinearMap‖ := by
      rw [norm_smul]
    _ = primeEulerAmbientLossScale p *
        ‖ContinuousLinearMap.id ℂ finiteSCarrier +
          (cc20GlobalLogTranslation
            (Real.log p)).toContinuousLinearMap‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hscale]
    _ ≤ primeEulerAmbientLossScale p *
        (‖ContinuousLinearMap.id ℂ finiteSCarrier‖ +
          ‖(cc20GlobalLogTranslation
            (Real.log p)).toContinuousLinearMap‖) := by
      exact mul_le_mul_of_nonneg_left hadd hscale
    _ ≤ primeEulerAmbientLossScale p * 2 := by
      have hid : ‖ContinuousLinearMap.id ℂ finiteSCarrier‖ ≤ (1 : ℝ) :=
        ContinuousLinearMap.norm_id_le
      nlinarith [htranslation]
    _ ≤ Real.sqrt (ccm24PrimeEulerCoefficient p) * 2 := by
      exact mul_le_mul_of_nonneg_right hscale_le (by norm_num)
    _ = 2 * Real.sqrt (ccm24PrimeEulerCoefficient p) := by ring

theorem normalizedPrimeEulerFrameTransport_adjoint_sub_id_norm_le_two_coefficient
    (p : CCM24VisiblePrime) :
    ‖(normalizedPrimeEulerFrameTransport p)† -
        ContinuousLinearMap.id ℂ finiteSCarrier‖ ≤
      2 * ccm24PrimeEulerCoefficient p := by
  let transport := normalizedPrimeEulerFrameTransport p
  have hq : 0 ≤ ccm24PrimeEulerCoefficient p :=
    ccm24PrimeEulerCoefficient_nonneg p
  have hdenom : 0 < 1 + ccm24PrimeEulerCoefficient p := by
    linarith
  have hdenomC : (1 + (ccm24PrimeEulerCoefficient p : ℂ)) ≠ 0 := by
    exact_mod_cast (ne_of_gt hdenom)
  have hadjoint_sub :
      ((transport)† - ContinuousLinearMap.id ℂ finiteSCarrier)† =
        transport - ContinuousLinearMap.id ℂ finiteSCarrier := by
    have hsub (A B : finiteSCarrier →L[ℂ] finiteSCarrier) :
        (A - B)† = A† - B† := by
      apply ContinuousLinearMap.ext
      intro x
      exact ext_inner_right ℂ fun y => by
        simp only [ContinuousLinearMap.adjoint_inner_left,
          ContinuousLinearMap.sub_apply, inner_sub_left, inner_sub_right]
    rw [hsub, ContinuousLinearMap.adjoint_adjoint,
      ContinuousLinearMap.adjoint_id]
  have hnorm_eq :
      ‖(transport)† - ContinuousLinearMap.id ℂ finiteSCarrier‖ =
        ‖transport - ContinuousLinearMap.id ℂ finiteSCarrier‖ := by
    calc
      ‖(transport)† - ContinuousLinearMap.id ℂ finiteSCarrier‖ =
          ‖((transport)† - ContinuousLinearMap.id ℂ finiteSCarrier)†‖ := by
            symm
            exact ContinuousLinearMap.adjoint.norm_map _
      _ = ‖transport - ContinuousLinearMap.id ℂ finiteSCarrier‖ := by
        rw [hadjoint_sub]
  rw [hnorm_eq]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  dsimp only [transport]
  rw [normalizedPrimeEulerFrameTransport,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply]
  change ‖((1 + (ccm24PrimeEulerCoefficient p : ℂ))⁻¹) •
      (ccm24PrimeEulerTransportEquiv p x) - x‖ ≤
    2 * ccm24PrimeEulerCoefficient p * ‖x‖
  rw [ccm24PrimeEulerTransportEquiv_apply]
  have hrewrite :
      ((1 + (ccm24PrimeEulerCoefficient p : ℂ))⁻¹) •
          (x - (ccm24PrimeEulerCoefficient p : ℂ) •
            cc20GlobalLogTranslation (-Real.log p) x) - x =
        (((1 + (ccm24PrimeEulerCoefficient p : ℂ))⁻¹ - 1) • x) -
          ((ccm24PrimeEulerCoefficient p : ℂ) /
            (1 + (ccm24PrimeEulerCoefficient p : ℂ))) •
            cc20GlobalLogTranslation (-Real.log p) x := by
    simp only [smul_sub, smul_smul, one_smul, sub_smul]
    field_simp [hdenomC]
    module
  rw [hrewrite]
  have hquot :
      ‖((ccm24PrimeEulerCoefficient p : ℂ) /
          (1 + (ccm24PrimeEulerCoefficient p : ℂ)))‖ ≤
        ccm24PrimeEulerCoefficient p := by
    have hdenomNorm :
        ‖(1 + (ccm24PrimeEulerCoefficient p : ℂ))‖ =
          1 + ccm24PrimeEulerCoefficient p := by
      have hcast :
          (1 + (ccm24PrimeEulerCoefficient p : ℂ)) =
            ((1 + ccm24PrimeEulerCoefficient p : ℝ) : ℂ) := by
        norm_num
      rw [hcast, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hdenom]
    rw [div_eq_mul_inv, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hq, norm_inv, hdenomNorm,
      ← div_eq_mul_inv]
    apply (div_le_iff₀ hdenom).2
    nlinarith
  have hdiff :
      ‖((1 + (ccm24PrimeEulerCoefficient p : ℂ))⁻¹ - 1)‖ ≤
        ccm24PrimeEulerCoefficient p := by
    have hident :
        (1 + (ccm24PrimeEulerCoefficient p : ℂ))⁻¹ - 1 =
          -((ccm24PrimeEulerCoefficient p : ℂ) /
            (1 + (ccm24PrimeEulerCoefficient p : ℂ))) := by
      field_simp [hdenomC]
      ring
    rw [hident, norm_neg]
    exact hquot
  have htransNorm :
      ‖cc20GlobalLogTranslation (-Real.log p) x‖ = ‖x‖ := by
    exact norm_cc20GlobalLogTranslation _ _
  calc
    ‖(((1 + (ccm24PrimeEulerCoefficient p : ℂ))⁻¹ - 1) • x) -
        ((ccm24PrimeEulerCoefficient p : ℂ) /
          (1 + (ccm24PrimeEulerCoefficient p : ℂ))) •
          cc20GlobalLogTranslation (-Real.log p) x‖ ≤
        ‖(((1 + (ccm24PrimeEulerCoefficient p : ℂ))⁻¹ - 1) • x)‖ +
          ‖((ccm24PrimeEulerCoefficient p : ℂ) /
            (1 + (ccm24PrimeEulerCoefficient p : ℂ))) •
            cc20GlobalLogTranslation (-Real.log p) x‖ := norm_sub_le _ _
    _ = ‖(1 + (ccm24PrimeEulerCoefficient p : ℂ))⁻¹ - 1‖ * ‖x‖ +
          ‖((ccm24PrimeEulerCoefficient p : ℂ) /
            (1 + (ccm24PrimeEulerCoefficient p : ℂ)))‖ *
            ‖cc20GlobalLogTranslation (-Real.log p) x‖ := by
      rw [norm_smul, norm_smul]
    _ ≤ ccm24PrimeEulerCoefficient p * ‖x‖ +
          ccm24PrimeEulerCoefficient p * ‖x‖ := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right hdiff (norm_nonneg _))
        (mul_le_mul hquot htransNorm.le (norm_nonneg _) hq)
    _ = 2 * ccm24PrimeEulerCoefficient p * ‖x‖ := by ring

/-! ## The fixed-source old-carrier column -/

theorem suffixEulerFrameAmbientBoundaryOldCarrierAnalysis_norm_le_on_newSuffixFrame
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (x : sourceSoninCarrier lambda) :
    ‖suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p []
        (newSuffixFrame lambda [] x)‖ ≤
      (2 * Real.sqrt (ccm24PrimeEulerCoefficient p) +
          2 * ccm24PrimeEulerCoefficient p) * ‖x‖ := by
  let N := newSuffixFrame lambda []
  let transport := normalizedPrimeEulerFrameTransport p
  let projection : finiteSCarrier →L[ℂ] finiteSCarrier :=
    N ∘L ContinuousLinearMap.adjoint N
  let complement : finiteSCarrier →L[ℂ] finiteSCarrier :=
    ContinuousLinearMap.id ℂ finiteSCarrier - projection
  have hN :
      ContinuousLinearMap.adjoint N ∘L N =
        ContinuousLinearMap.id ℂ (sourceSoninCarrier lambda) := by
    simpa only [N, newSuffixFrame] using
      parameterizedSoninPolarFrame_adjoint_comp_self lambda 1 [] (by norm_num)
  have hprojection : IsStarProjection projection := by
    refine
      { isIdempotentElem := ?_
        isSelfAdjoint := ?_ }
    · have hsq : projection ∘L projection = projection := by
        apply ContinuousLinearMap.ext
        intro z
        have h := congrArg
          (fun T : sourceSoninCarrier lambda →L[ℂ]
            sourceSoninCarrier lambda => N ∘L T) hN
        simpa only [projection, ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.id_apply] using
          congrArg (fun T : sourceSoninCarrier lambda →L[ℂ]
            finiteSCarrier => T (ContinuousLinearMap.adjoint N z)) h
      simpa only [ContinuousLinearMap.mul_def] using hsq
    · change projection† = projection
      simp only [projection, ContinuousLinearMap.adjoint_comp,
        ContinuousLinearMap.adjoint_adjoint]
  have hcomplement : IsStarProjection complement := by
    simpa only [complement] using hprojection.one_sub
  have hcomplementNorm : ‖complement‖ ≤ (1 : ℝ) :=
    IsStarProjection.norm_le _ hcomplement
  have hNnorm : ‖N x‖ = ‖x‖ := by
    simpa only [N, newSuffixFrame] using
      parameterizedSoninPolarFrame_isometry lambda 1 [] (by norm_num) x
  have hprojectionN : projection (N x) = N x := by
    have hpoint := congrArg
      (fun T : sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda =>
        T x) hN
    have hpoint' : ContinuousLinearMap.adjoint N (N x) = x := by
      simpa only [ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.id_apply] using hpoint
    change N (ContinuousLinearMap.adjoint N (N x)) = N x
    exact congrArg N hpoint'
  have hcomplementN : complement (N x) = 0 := by
    simp only [complement, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.id_apply]
    rw [hprojectionN]
    simp
  have htransportDiff :
      ‖ContinuousLinearMap.adjoint transport -
          ContinuousLinearMap.id ℂ finiteSCarrier‖ ≤
        2 * ccm24PrimeEulerCoefficient p := by
    simpa only [transport] using
      normalizedPrimeEulerFrameTransport_adjoint_sub_id_norm_le_two_coefficient p
  have hambient :
      ‖ContinuousLinearMap.adjoint (primeEulerAmbientLossFactor p) (N x)‖ ≤
        2 * Real.sqrt (ccm24PrimeEulerCoefficient p) * ‖x‖ := by
    calc
      ‖ContinuousLinearMap.adjoint (primeEulerAmbientLossFactor p) (N x)‖ ≤
          ‖ContinuousLinearMap.adjoint (primeEulerAmbientLossFactor p)‖ *
            ‖N x‖ :=
        (ContinuousLinearMap.adjoint (primeEulerAmbientLossFactor p)).le_opNorm _
      _ ≤ 2 * Real.sqrt (ccm24PrimeEulerCoefficient p) * ‖x‖ := by
        rw [hNnorm]
        exact mul_le_mul_of_nonneg_right
          (primeEulerAmbientLossFactor_adjoint_norm_le_two_sqrt_coefficient p)
          (norm_nonneg _)
  have hboundary :
      ‖complement (ContinuousLinearMap.adjoint transport (N x))‖ ≤
        2 * ccm24PrimeEulerCoefficient p * ‖x‖ := by
    have hsplit :
        complement (ContinuousLinearMap.adjoint transport (N x)) =
          complement ((ContinuousLinearMap.adjoint transport -
            ContinuousLinearMap.id ℂ finiteSCarrier) (N x)) := by
      calc
        complement (ContinuousLinearMap.adjoint transport (N x)) =
            complement ((ContinuousLinearMap.adjoint transport -
              ContinuousLinearMap.id ℂ finiteSCarrier) (N x) + N x) := by
          congr 1
          simp
        _ = complement ((ContinuousLinearMap.adjoint transport -
              ContinuousLinearMap.id ℂ finiteSCarrier) (N x)) +
            complement (N x) := by rw [map_add]
        _ = complement ((ContinuousLinearMap.adjoint transport -
              ContinuousLinearMap.id ℂ finiteSCarrier) (N x)) := by
          rw [hcomplementN, add_zero]
    rw [hsplit]
    calc
      ‖complement ((ContinuousLinearMap.adjoint transport -
          ContinuousLinearMap.id ℂ finiteSCarrier) (N x))‖ ≤
          ‖complement‖ *
            ‖(ContinuousLinearMap.adjoint transport -
              ContinuousLinearMap.id ℂ finiteSCarrier) (N x)‖ :=
        complement.le_opNorm _
      _ ≤ 1 * (‖ContinuousLinearMap.adjoint transport -
            ContinuousLinearMap.id ℂ finiteSCarrier‖ * ‖N x‖) := by
        have hDpoint :=
          (ContinuousLinearMap.adjoint transport -
            ContinuousLinearMap.id ℂ finiteSCarrier).le_opNorm (N x)
        exact mul_le_mul
          hcomplementNorm
          hDpoint
          (norm_nonneg _) (by positivity)
      _ ≤ 2 * ccm24PrimeEulerCoefficient p * ‖x‖ := by
        rw [one_mul]
        rw [hNnorm]
        exact mul_le_mul_of_nonneg_right htransportDiff
          (norm_nonneg _)
  have hpacked :
      suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p []
          (N x) =
        suffixEulerFrameAmbientBoundaryLeftEmbedding
            (ContinuousLinearMap.adjoint (primeEulerAmbientLossFactor p) (N x)) +
          suffixEulerFrameAmbientBoundaryRightEmbedding
            (complement (ContinuousLinearMap.adjoint transport (N x))) := by
    rw [suffixEulerFrameAmbientBoundaryOldCarrierAnalysis_apply]
    change WithLp.toLp 2
        (ContinuousLinearMap.adjoint (primeEulerAmbientLossFactor p) (N x),
          complement (ContinuousLinearMap.adjoint transport (N x))) = _
    simpa only [WithLp.toLp_fst, WithLp.toLp_snd] using
      ((suffixEulerFrameAmbientBoundary_left_add_right
        (WithLp.toLp 2
          (ContinuousLinearMap.adjoint (primeEulerAmbientLossFactor p) (N x),
            complement (ContinuousLinearMap.adjoint transport (N x))))).symm)
  calc
    ‖suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p []
        (N x)‖ ≤
        ‖suffixEulerFrameAmbientBoundaryLeftEmbedding
            (ContinuousLinearMap.adjoint (primeEulerAmbientLossFactor p) (N x))‖ +
          ‖suffixEulerFrameAmbientBoundaryRightEmbedding
            (complement (ContinuousLinearMap.adjoint transport (N x)))‖ := by
      rw [hpacked]
      exact norm_add_le _ _
    _ ≤ ‖ContinuousLinearMap.adjoint (primeEulerAmbientLossFactor p) (N x)‖ +
          ‖complement (ContinuousLinearMap.adjoint transport (N x))‖ := by
      apply add_le_add
      · calc
          ‖suffixEulerFrameAmbientBoundaryLeftEmbedding
              (ContinuousLinearMap.adjoint (primeEulerAmbientLossFactor p) (N x))‖ ≤
              ‖suffixEulerFrameAmbientBoundaryLeftEmbedding‖ *
                ‖ContinuousLinearMap.adjoint (primeEulerAmbientLossFactor p) (N x)‖ :=
            suffixEulerFrameAmbientBoundaryLeftEmbedding.le_opNorm _
          _ ≤ ‖ContinuousLinearMap.adjoint (primeEulerAmbientLossFactor p) (N x)‖ := by
            calc
              _ ≤ 1 *
                  ‖ContinuousLinearMap.adjoint
                    (primeEulerAmbientLossFactor p) (N x)‖ :=
                mul_le_mul_of_nonneg_right
                  suffixEulerFrameAmbientBoundaryLeftEmbedding_norm_le_one
                  (norm_nonneg _)
              _ = _ := by simp
      · calc
          ‖suffixEulerFrameAmbientBoundaryRightEmbedding
              (complement (ContinuousLinearMap.adjoint transport (N x)))‖ ≤
              ‖suffixEulerFrameAmbientBoundaryRightEmbedding‖ *
                ‖complement (ContinuousLinearMap.adjoint transport (N x))‖ :=
            suffixEulerFrameAmbientBoundaryRightEmbedding.le_opNorm _
          _ ≤ ‖complement (ContinuousLinearMap.adjoint transport (N x))‖ := by
            calc
              _ ≤ 1 *
                  ‖complement (ContinuousLinearMap.adjoint transport (N x))‖ :=
                mul_le_mul_of_nonneg_right
                  suffixEulerFrameAmbientBoundaryRightEmbedding_norm_le_one
                  (norm_nonneg _)
              _ = _ := by simp
    _ ≤ (2 * Real.sqrt (ccm24PrimeEulerCoefficient p) +
          2 * ccm24PrimeEulerCoefficient p) * ‖x‖ := by
      convert add_le_add hambient hboundary using 1 <;> ring

/-! ## Sequence form of the fixed-source guard -/

theorem tendsto_suffixEulerFrameAmbientBoundaryOldCarrierAnalysis_norm_on_newSuffixFrame_of_tendsto_coefficient
    (lambda : CCM24SoninScale) (x : sourceSoninCarrier lambda)
    (prime : ℕ → CCM24VisiblePrime)
    (hcoeff : Filter.Tendsto
      (fun n => ccm24PrimeEulerCoefficient (prime n))
      Filter.atTop (𝓝 0)) :
    Filter.Tendsto
      (fun n =>
        ‖suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda (prime n) []
          (newSuffixFrame lambda [] x)‖)
      Filter.atTop (𝓝 0) := by
  have hroot : Filter.Tendsto
      (fun n => Real.sqrt (ccm24PrimeEulerCoefficient (prime n)))
      Filter.atTop (𝓝 0) := by
    simpa using hcoeff.sqrt
  have hupper : Filter.Tendsto
      (fun n =>
        (2 * Real.sqrt (ccm24PrimeEulerCoefficient (prime n)) +
          2 * ccm24PrimeEulerCoefficient (prime n)) * ‖x‖)
      Filter.atTop (𝓝 0) := by
    have hsum : Filter.Tendsto
        (fun n =>
          2 * Real.sqrt (ccm24PrimeEulerCoefficient (prime n)) +
            2 * ccm24PrimeEulerCoefficient (prime n))
        Filter.atTop (𝓝 0) := by
      simpa using
        (hroot.const_mul (2 : ℝ)).add (hcoeff.const_mul (2 : ℝ))
    simpa using hsum.mul_const ‖x‖
  apply squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hupper
  exact suffixEulerFrameAmbientBoundaryOldCarrierAnalysis_norm_le_on_newSuffixFrame
    lambda (prime n) x

/-! ## Moving source columns

The fixed-column estimate is also uniform over any norm-bounded source
sequence.  This is the form needed for a genuine translated or scattering
witness: the source vector may depend on the visible prime, but its norm may
not grow while the Euler coefficient decays.
-/

theorem tendsto_suffixEulerFrameAmbientBoundaryOldCarrierAnalysis_norm_on_newSuffixFrame_of_tendsto_coefficient_of_uniformly_bounded_source
    (lambda : CCM24SoninScale) (x : ℕ → sourceSoninCarrier lambda)
    (prime : ℕ → CCM24VisiblePrime)
    (hcoeff : Filter.Tendsto
      (fun n => ccm24PrimeEulerCoefficient (prime n))
      Filter.atTop (𝓝 0))
    {bound : ℝ} (hbound : 0 ≤ bound)
    (hx : ∀ n, ‖x n‖ ≤ bound) :
    Filter.Tendsto
      (fun n =>
        ‖suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda (prime n) []
          (newSuffixFrame lambda [] (x n))‖)
      Filter.atTop (𝓝 0) := by
  have hroot : Filter.Tendsto
      (fun n => Real.sqrt (ccm24PrimeEulerCoefficient (prime n)))
      Filter.atTop (𝓝 0) := by
    simpa using hcoeff.sqrt
  have hfactor : Filter.Tendsto
      (fun n =>
        2 * Real.sqrt (ccm24PrimeEulerCoefficient (prime n)) +
          2 * ccm24PrimeEulerCoefficient (prime n))
      Filter.atTop (𝓝 0) := by
    simpa using
      (hroot.const_mul (2 : ℝ)).add (hcoeff.const_mul (2 : ℝ))
  have hupper : Filter.Tendsto
      (fun n =>
        (2 * Real.sqrt (ccm24PrimeEulerCoefficient (prime n)) +
          2 * ccm24PrimeEulerCoefficient (prime n)) * bound)
      Filter.atTop (𝓝 0) := by
    simpa using hfactor.mul_const bound
  apply squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hupper
  calc
    ‖suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda (prime n) []
        (newSuffixFrame lambda [] (x n))‖ ≤
        (2 * Real.sqrt (ccm24PrimeEulerCoefficient (prime n)) +
          2 * ccm24PrimeEulerCoefficient (prime n)) * ‖x n‖ :=
      suffixEulerFrameAmbientBoundaryOldCarrierAnalysis_norm_le_on_newSuffixFrame
        lambda (prime n) (x n)
    _ ≤ (2 * Real.sqrt (ccm24PrimeEulerCoefficient (prime n)) +
          2 * ccm24PrimeEulerCoefficient (prime n)) * bound := by
      apply mul_le_mul_of_nonneg_left (hx n)
      have hq : 0 ≤ ccm24PrimeEulerCoefficient (prime n) :=
        ccm24PrimeEulerCoefficient_nonneg (prime n)
      have hsqrt : 0 ≤ Real.sqrt (ccm24PrimeEulerCoefficient (prime n)) :=
        Real.sqrt_nonneg _
      nlinarith

/-! The project-level `CCM24VisiblePrime` carrier only records `p > 1`.
This explicit sequence is therefore a coefficient-decay sanity check, not a
claim that every term is arithmetically prime. -/

noncomputable def canonicalVisiblePrimeSequence (n : ℕ) : CCM24VisiblePrime :=
  ⟨(n + 2) ^ 2, by
    have hn : 2 ≤ n + 2 := by omega
    have hsq : 2 * 2 ≤ (n + 2) * (n + 2) := Nat.mul_le_mul hn hn
    nlinarith
  ⟩

theorem tendsto_ccm24PrimeEulerCoefficient_canonicalVisiblePrimeSequence :
    Filter.Tendsto
      (fun n =>
        ccm24PrimeEulerCoefficient (canonicalVisiblePrimeSequence n))
      Filter.atTop (𝓝 0) := by
  have hdiv : Filter.Tendsto
      (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 2))
      Filter.atTop (𝓝 0) := by
    have hdivOne : Filter.Tendsto
        (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
        Filter.atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    simpa [Function.comp_def, Nat.cast_add, add_assoc, one_add_one_eq_two] using
      hdivOne.comp (Filter.tendsto_add_atTop_nat 1)
  convert hdiv using 1
  ext n
  have hn : (0 : ℝ) ≤ (n : ℝ) + 2 := by positivity
  simp [canonicalVisiblePrimeSequence, ccm24PrimeEulerCoefficient,
    Nat.cast_pow, Real.sqrt_sq_eq_abs, hn]

theorem tendsto_suffixEulerFrameAmbientBoundaryOldCarrierAnalysis_norm_on_canonicalVisiblePrimeSequence
    (lambda : CCM24SoninScale) (x : sourceSoninCarrier lambda) :
    Filter.Tendsto
      (fun n =>
        ‖suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda
          (canonicalVisiblePrimeSequence n) []
          (newSuffixFrame lambda [] x)‖)
      Filter.atTop (𝓝 0) :=
  tendsto_suffixEulerFrameAmbientBoundaryOldCarrierAnalysis_norm_on_newSuffixFrame_of_tendsto_coefficient
    lambda x canonicalVisiblePrimeSequence
    tendsto_ccm24PrimeEulerCoefficient_canonicalVisiblePrimeSequence

end CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierFixedSourceKernelGuard
end CCM25Concrete
end Source
end ConnesWeilRH
