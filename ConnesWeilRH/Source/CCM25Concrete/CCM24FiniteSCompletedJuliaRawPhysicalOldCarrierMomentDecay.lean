/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierMovingMomentColumnSelector
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSNormalizedCausalCoframe
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSActualMovingProjection
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSParameterizedZeroEndpoint
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSActualSchurEndpointAlignmentResidual
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSRawLocalTraceFactorization
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSGramResponse
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSGramProjectionCalculus
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSFixedQuotientCarrier
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSNormalizedPhysicalResponse
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaJointProducer
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSTransportBounds
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCausalSupport
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSActualBandQuadraticCycle
import ConnesWeilRH.Source.CC20Concrete.InvertibleTransportSonin

/-!
# One-prime old-carrier moment decay

The arithmetic-prime column selector from Proof 588 requires a positive
operator-norm lower bound for a signed one-prime moment.  This module records
the opposite source-specific behavior.  The Euler coefficient
`q_p = p^(-1/2)` is the small parameter: the forward coframe starts at zero,
the transported Sonin projection moves by an `O(q_p)` crossing flow, and the
normalized metric leakage is therefore also `O(q_p)`.  The raw metric
coframe is recovered by the lower-factor scalar, which stays uniformly away
from zero for visible primes.

The final consequence is that the genuine signed moment column tends to zero
along the arithmetic primes.  It closes the current operator-norm lower-bound
fork by showing that this particular Bone 1 column cannot supply its witness.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierMomentDecay

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

open scoped InnerProduct InnerProductSpace
open scoped Topology

open CC20Concrete
open _root_.ConnesWeilRH.CC20Concrete
open CCM24FiniteSProjectionTrace
open CCM24FiniteSCausalMarkov
open CCM24FiniteSParameterizedEulerGenerator
open CCM24FiniteSParameterizedEulerEquiv
open CCM24FiniteSParameterizedSoninSubspace
open CCM24FiniteSParameterizedSoninProjection
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSActualMovingProjection
open CCM24FiniteSGramFlowCollapse
open CCM24FiniteSOrthogonalProjectionFlow
open CCM24FiniteSParameterizedZeroEndpoint
open CCM24FiniteSNormalizedCoframe
open CCM24FiniteSNormalizedCausalCoframe
open CCM24FiniteSNormalizedPhysicalResponse
open CCM24FiniteSCoframeResponse
open CCM24FiniteSRawLocalTraceFactorization
open CCM24FiniteSGramResponse
open CCM24FiniteSGramProjectionCalculus
open CCM24FiniteSFixedQuotientCarrier
open CCM24FiniteSCompletedJuliaJointProducer
open CCM24FiniteSTransportBounds
open CCM24FiniteSCausalSupport
open CCM24FiniteSActualBandQuadraticCycle
open CCM24FiniteSActualSchurEndpointAlignmentResidual
open CCM24FiniteSCompletedJuliaRawCoframeBoundaryTelescope
open CCM24FiniteSCompletedJuliaRawPhysicalOnePrimeMomentObstruction
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierMovingMomentColumnSelector

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) :
      CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

noncomputable local instance targetTransportedSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
      CompleteSpace (targetTransportedSoninCarrier lambda family) :=
  (transportedClosedSubmodule
    (ccm24FiniteEulerTransportEquiv family.visiblePrimes)
    (ccm24ArchimedeanSoninClosedSubspace lambda)).isClosed.completeSpace_coe

local notation "SourceOp" lambda =>
  sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda

/-! ## The one-prime Euler scale -/

theorem norm_ccm24PrimeEulerContraction_le
    (p : CCM24VisiblePrime) :
    ‖ccm24PrimeEulerContraction p‖ ≤
      ccm24PrimeEulerCoefficient p := by
  rw [ccm24PrimeEulerContraction, norm_smul]
  calc
    ‖(ccm24PrimeEulerCoefficient p : ℂ)‖ *
          ‖(cc20GlobalLogTranslation (-Real.log p)).toContinuousLinearMap‖ ≤
        ‖(ccm24PrimeEulerCoefficient p : ℂ)‖ * 1 := by
      exact mul_le_mul_of_nonneg_left
        (cc20GlobalLogTranslation (-Real.log p)).norm_toContinuousLinearMap_le
        (norm_nonneg _)
    _ = ccm24PrimeEulerCoefficient p := by
      rw [mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (ccm24PrimeEulerCoefficient_nonneg p)]

theorem norm_parameterizedPrimeEulerInverse_le_four
    (alpha : ℝ) (p : CCM24VisiblePrime)
    (hα0 : 0 ≤ alpha) (hα1 : alpha ≤ 1) :
    ‖parameterizedPrimeEulerInverse alpha p‖ ≤ 4 := by
  let A := parameterizedPrimeEulerContraction alpha p
  have hA : ‖A‖ ≤ (3 / 4 : ℝ) := by
    rw [show A = parameterizedPrimeEulerContraction alpha p by rfl,
      parameterizedPrimeEulerContraction, norm_smul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hα0]
    calc
      alpha * ‖ccm24PrimeEulerContraction p‖ ≤
          alpha * ccm24PrimeEulerCoefficient p := by
        exact mul_le_mul_of_nonneg_left
          (norm_ccm24PrimeEulerContraction_le p) hα0
      _ ≤ 3 / 4 := by
        exact (mul_le_of_le_one_left
          (ccm24PrimeEulerCoefficient_nonneg p) hα1).trans
          (ccm24PrimeEulerCoefficient_le_three_quarters p)
  have hAlt : ‖A‖ < 1 := lt_of_le_of_lt hA (by norm_num)
  have hsummable : Summable (fun n : ℕ => A ^ n) :=
    summable_geometric_of_norm_lt_one hAlt
  calc
    ‖parameterizedPrimeEulerInverse alpha p‖ =
        ‖∑' n : ℕ, A ^ n‖ := by
      rfl
    _ ≤ ‖(1 : finiteSCarrier →L[ℂ] finiteSCarrier)‖ - 1 +
        (1 - ‖A‖)⁻¹ :=
      tsum_geometric_le_of_norm_lt_one A hAlt
    _ ≤ 4 := by
      have hdenom : 0 < 1 - ‖A‖ := sub_pos.mpr hAlt
      have hinv : (1 - ‖A‖)⁻¹ ≤ (4 : ℝ) := by
        apply (inv_le_iff_one_le_mul₀ hdenom).2
        nlinarith [hA]
      have hid : ‖(1 : finiteSCarrier →L[ℂ] finiteSCarrier)‖ ≤ 1 := by
        change ‖ContinuousLinearMap.id ℂ finiteSCarrier‖ ≤ (1 : ℝ)
        exact ContinuousLinearMap.norm_id_le
      nlinarith

theorem norm_parameterizedPrimeEulerGenerator_le_four_mul_coefficient
    (alpha : ℝ) (p : CCM24VisiblePrime)
    (hα0 : 0 ≤ alpha) (hα1 : alpha ≤ 1) :
    ‖parameterizedPrimeEulerGenerator alpha p‖ ≤
      4 * ccm24PrimeEulerCoefficient p := by
  unfold parameterizedPrimeEulerGenerator
  calc
    ‖-ccm24PrimeEulerContraction p *
        parameterizedPrimeEulerInverse alpha p‖ ≤
      ‖ccm24PrimeEulerContraction p‖ *
        ‖parameterizedPrimeEulerInverse alpha p‖ := by
      change ‖-(ccm24PrimeEulerContraction p ∘L
          parameterizedPrimeEulerInverse alpha p)‖ ≤ _
      rw [norm_neg]
      exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ccm24PrimeEulerCoefficient p * 4 := by
      exact mul_le_mul
        (norm_ccm24PrimeEulerContraction_le p)
        (norm_parameterizedPrimeEulerInverse_le_four alpha p hα0 hα1)
        (norm_nonneg _) (ccm24PrimeEulerCoefficient_nonneg p)
    _ = 4 * ccm24PrimeEulerCoefficient p := by ring

/-! ## The moving projection estimate -/

theorem norm_orthogonalProjectionDerivative_le_two_mul
    (P X : finiteSCarrier →L[ℂ] finiteSCarrier)
    (hP : IsStarProjection P) :
    ‖orthogonalProjectionDerivative P X‖ ≤ 2 * ‖X‖ := by
  rw [orthogonalProjectionDerivative_eq_twoCrossings P X hP.isSelfAdjoint,
    ContinuousLinearMap.mul_def]
  have hPnorm : ‖P‖ ≤ (1 : ℝ) := IsStarProjection.norm_le _ hP
  have hPcomp : ‖ContinuousLinearMap.id ℂ finiteSCarrier - P‖ ≤
      (1 : ℝ) := by
    exact IsStarProjection.norm_le _ hP.one_sub
  calc
    ‖(ContinuousLinearMap.id ℂ finiteSCarrier - P) * X * P +
        P * ContinuousLinearMap.adjoint X *
          (ContinuousLinearMap.id ℂ finiteSCarrier - P)‖ ≤
      ‖(ContinuousLinearMap.id ℂ finiteSCarrier - P) * X * P‖ +
        ‖P * ContinuousLinearMap.adjoint X *
          (ContinuousLinearMap.id ℂ finiteSCarrier - P)‖ := norm_add_le _ _
    _ ≤ (‖ContinuousLinearMap.id ℂ finiteSCarrier - P‖ * ‖X‖ * ‖P‖) +
        (‖P‖ * ‖ContinuousLinearMap.adjoint X‖ *
          ‖ContinuousLinearMap.id ℂ finiteSCarrier - P‖) := by
      apply add_le_add
      · calc
          ‖(ContinuousLinearMap.id ℂ finiteSCarrier - P) ∘L X ∘L P‖ ≤
              ‖(ContinuousLinearMap.id ℂ finiteSCarrier - P) ∘L X‖ * ‖P‖ :=
            ContinuousLinearMap.opNorm_comp_le
              ((ContinuousLinearMap.id ℂ finiteSCarrier - P) ∘L X) P
          _ ≤ (‖ContinuousLinearMap.id ℂ finiteSCarrier - P‖ * ‖X‖) * ‖P‖ := by
            gcongr
            exact ContinuousLinearMap.opNorm_comp_le _ _
      · calc
          ‖P ∘L ContinuousLinearMap.adjoint X ∘L
              (ContinuousLinearMap.id ℂ finiteSCarrier - P)‖ ≤
              ‖P ∘L ContinuousLinearMap.adjoint X‖ *
                ‖ContinuousLinearMap.id ℂ finiteSCarrier - P‖ :=
            ContinuousLinearMap.opNorm_comp_le
              (P ∘L ContinuousLinearMap.adjoint X)
              (ContinuousLinearMap.id ℂ finiteSCarrier - P)
          _ ≤ (‖P‖ * ‖ContinuousLinearMap.adjoint X‖) *
              ‖ContinuousLinearMap.id ℂ finiteSCarrier - P‖ := by
            gcongr
            exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤
        (‖X‖ * ‖P‖) + (‖P‖ * ‖X‖) := by
      rw [ContinuousLinearMap.adjoint.norm_map]
      apply add_le_add
      · calc
          ‖ContinuousLinearMap.id ℂ finiteSCarrier - P‖ * ‖X‖ * ‖P‖ =
              ‖ContinuousLinearMap.id ℂ finiteSCarrier - P‖ *
                (‖X‖ * ‖P‖) := by ring
          _ ≤ 1 * (‖X‖ * ‖P‖) := by
            exact mul_le_mul_of_nonneg_right hPcomp
              (mul_nonneg (norm_nonneg X) (norm_nonneg P))
          _ = ‖X‖ * ‖P‖ := by ring
      · calc
          ‖P‖ * ‖X‖ * ‖ContinuousLinearMap.id ℂ finiteSCarrier - P‖ =
              (‖P‖ * ‖X‖) *
                ‖ContinuousLinearMap.id ℂ finiteSCarrier - P‖ := by ring
          _ ≤ (‖P‖ * ‖X‖) * 1 := by
            exact mul_le_mul_of_nonneg_left hPcomp
              (mul_nonneg (norm_nonneg P) (norm_nonneg X))
          _ = ‖P‖ * ‖X‖ := by ring
    _ ≤ 2 * ‖X‖ := by
      have hfirst : ‖X‖ * ‖P‖ ≤ ‖X‖ := by
        simpa only [mul_one] using
          (mul_le_mul_of_nonneg_left hPnorm (norm_nonneg X))
      have hsecond : ‖P‖ * ‖X‖ ≤ ‖X‖ := by
        simpa only [one_mul] using
          (mul_le_mul_of_nonneg_right hPnorm (norm_nonneg X))
      nlinarith

theorem norm_parameterizedCanonicalGramProjection_derivative_le_eight_mul_coefficient
    (lambda : CCM24SoninScale) (alpha : ℝ) (p : CCM24VisiblePrime)
    (hα0 : 0 ≤ alpha) (hα1 : alpha ≤ 1) :
    ‖parameterizedCanonicalGramProjectionDerivative lambda alpha [p]
        (by
          rw [abs_of_nonneg hα0]
          exact hα1)‖ ≤
      8 * ccm24PrimeEulerCoefficient p := by
  rw [parameterizedCanonicalGramProjectionDerivative_eq_orthogonalFlow
    lambda alpha [p] (by
      rw [abs_of_nonneg hα0]
      exact hα1)]
  calc
    ‖orthogonalProjectionDerivative
        (parameterizedCanonicalGramProjection lambda alpha [p])
        (parameterizedFiniteEulerGenerator alpha [p])‖ ≤
      2 * ‖parameterizedFiniteEulerGenerator alpha [p]‖ :=
        norm_orthogonalProjectionDerivative_le_two_mul _ _
          (parameterizedCanonicalGramProjection_isStarProjection
            lambda alpha [p] (by
              rw [abs_of_nonneg hα0]
              exact hα1))
    _ ≤ 2 * (4 * ccm24PrimeEulerCoefficient p) := by
      gcongr
      simpa only [parameterizedFiniteEulerGenerator_cons,
        parameterizedFiniteEulerGenerator_nil, add_zero] using
        norm_parameterizedPrimeEulerGenerator_le_four_mul_coefficient
          alpha p hα0 hα1
    _ = 8 * ccm24PrimeEulerCoefficient p := by ring

theorem norm_parameterizedCanonicalGramProjection_one_sub_zero_le_eight_mul_coefficient
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) :
    ‖parameterizedCanonicalGramProjection lambda 1 [p] -
        parameterizedCanonicalGramProjection lambda 0 [p]‖ ≤
      8 * ccm24PrimeEulerCoefficient p := by
  let f : ℝ → finiteSCarrier →L[ℂ] finiteSCarrier :=
    fun alpha => parameterizedCanonicalGramProjection lambda alpha [p]
  let f' : ℝ → finiteSCarrier →L[ℂ] finiteSCarrier := fun alpha =>
    if h : |alpha| ≤ 1 then
      parameterizedCanonicalGramProjectionDerivative lambda alpha [p] h
    else
      (0 : finiteSCarrier →L[ℂ] finiteSCarrier)
  have hderiv : ∀ alpha ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt f (f' alpha) (Set.Icc (0 : ℝ) 1) alpha := by
    intro alpha hα
    have halpha : |alpha| ≤ 1 := by
      rw [abs_of_nonneg (by linarith [hα.1])]
      exact hα.2
    simp only [f', dif_pos halpha]
    exact (hasDerivAt_parameterizedCanonicalGramProjection
      lambda alpha [p] halpha).hasDerivWithinAt
  have hbound : ∀ alpha ∈ Set.Ico (0 : ℝ) 1,
      ‖f' alpha‖ ≤ 8 * ccm24PrimeEulerCoefficient p := by
    intro alpha hα
    have halpha : |alpha| ≤ 1 := by
      rw [abs_of_nonneg (by linarith [hα.1])]
      exact le_of_lt hα.2
    simp only [f', dif_pos halpha]
    exact norm_parameterizedCanonicalGramProjection_derivative_le_eight_mul_coefficient
      lambda alpha p hα.1 hα.2.le
  have hpath := norm_image_sub_le_of_norm_deriv_le_segment'
    (a := (0 : ℝ)) (b := 1) hderiv hbound
      (1 : ℝ) (by norm_num)
  simpa only [f, sub_zero, mul_one] using hpath

/-! ## The one-prime finite-family bridge -/

noncomputable def singlePrimeFamily
    (p : CCM24VisiblePrime) (hp : Nat.Prime p.1) :
    FinitePrimePowerFamily where
  terms := {(p.1, 1)}
  prime := by
    intro pm hpm
    rcases Finset.mem_singleton.mp hpm with rfl
    exact hp
  exponent_ne_zero := by
    intro pm hpm
    rcases Finset.mem_singleton.mp hpm with rfl
    norm_num

theorem singlePrimeFamily_visiblePrimes
    (p : CCM24VisiblePrime) (hp : Nat.Prime p.1) :
    (singlePrimeFamily p hp).visiblePrimes = [p] := by
  rw [FinitePrimePowerFamily.visiblePrimes]
  have hattach :
      (singlePrimeFamily p hp).terms.attach =
        ({⟨(p.1, 1), by simp [singlePrimeFamily]⟩} :
          Finset {pm // pm ∈ (singlePrimeFamily p hp).terms}) := by
    ext pm
    constructor
    · intro hpm
      have hterm : pm.1 = (p.1, 1) := by
        exact Finset.mem_singleton.mp (by
          simpa [singlePrimeFamily] using pm.2)
      have heq : pm = ⟨(p.1, 1), by simp [singlePrimeFamily]⟩ :=
        Subtype.ext hterm
      simpa [heq]
    · intro hpm
      have heq : pm = ⟨(p.1, 1), by simp [singlePrimeFamily]⟩ :=
        Finset.mem_singleton.mp hpm
      subst pm
      exact Finset.mem_attach _ _
  rw [hattach, Finset.image_singleton]
  simp [singlePrimeFamily]

theorem targetTransportedSoninProjection_eq_parameterizedCanonicalGramProjection
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (hp : Nat.Prime p.1) :
    targetTransportedSoninInclusion lambda (singlePrimeFamily p hp) ∘L
        (targetTransportedSoninInclusion lambda (singlePrimeFamily p hp))† =
      parameterizedCanonicalGramProjection lambda 1 [p] := by
  have htransported :
      transportedClosedSubmodule
          (ccm24FiniteEulerTransportEquiv [p])
          (ccm24ArchimedeanSoninClosedSubspace lambda) =
        parameterizedSoninClosedSubspace lambda 1 [p] (by norm_num) := by
    rw [← parameterizedFiniteEulerEquiv_one [p]]
    exact parameterizedFiniteEulerEquiv_maps_sonin lambda 1 [p] (by norm_num)
  rw [targetTransportedSoninInclusion, Submodule.adjoint_subtypeL]
  change (transportedClosedSubmodule
      (ccm24FiniteEulerTransportEquiv (singlePrimeFamily p hp).visiblePrimes)
      (ccm24ArchimedeanSoninClosedSubspace lambda)).toSubmodule.starProjection =
    parameterizedCanonicalGramProjection lambda 1 [p]
  rw [singlePrimeFamily_visiblePrimes p hp]
  change (transportedClosedSubmodule
      (ccm24FiniteEulerTransportEquiv [p])
      (ccm24ArchimedeanSoninClosedSubspace lambda)).toSubmodule.starProjection =
    parameterizedCanonicalGramProjection lambda 1 [p]
  rw [parameterizedCanonicalGramProjection_eq_soninProjection
      lambda 1 [p] (by norm_num), htransported]
  rfl

/-! ## One-prime normalized transport differences -/

theorem norm_primeEulerTransport_sub_id_le_coefficient
    (p : CCM24VisiblePrime) :
    ‖(ccm24PrimeEulerTransportEquiv p).toContinuousLinearMap -
        ContinuousLinearMap.id ℂ finiteSCarrier‖ ≤
      ccm24PrimeEulerCoefficient p := by
  have hq : 0 ≤ ccm24PrimeEulerCoefficient p :=
    ccm24PrimeEulerCoefficient_nonneg p
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  change ‖ccm24PrimeEulerTransportEquiv p x - x‖ ≤
    ccm24PrimeEulerCoefficient p * ‖x‖
  rw [ccm24PrimeEulerTransportEquiv_apply]
  simp only [sub_sub_cancel_left]
  rw [norm_neg, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hq, norm_cc20GlobalLogTranslation]

theorem norm_primeEulerTransportAdjoint_sub_id_le_coefficient
    (p : CCM24VisiblePrime) :
    ‖(ccm24PrimeEulerTransportEquiv p).toContinuousLinearMap† -
        ContinuousLinearMap.id ℂ finiteSCarrier‖ ≤
      ccm24PrimeEulerCoefficient p := by
  have hadjoint_sub (A B : finiteSCarrier →L[ℂ] finiteSCarrier) :
      (A - B)† = A† - B† := by
    apply ContinuousLinearMap.ext
    intro x
    exact ext_inner_right ℂ fun y => by
      simp only [ContinuousLinearMap.adjoint_inner_left,
        ContinuousLinearMap.sub_apply, inner_sub_left, inner_sub_right]
  have hnorm :
      ‖(ccm24PrimeEulerTransportEquiv p).toContinuousLinearMap† -
          ContinuousLinearMap.id ℂ finiteSCarrier‖ =
        ‖(ccm24PrimeEulerTransportEquiv p).toContinuousLinearMap -
          ContinuousLinearMap.id ℂ finiteSCarrier‖ := by
    calc
      _ = ‖((ccm24PrimeEulerTransportEquiv p).toContinuousLinearMap† -
          ContinuousLinearMap.id ℂ finiteSCarrier)†‖ := by
        symm
        exact ContinuousLinearMap.adjoint.norm_map _
      _ = ‖(ccm24PrimeEulerTransportEquiv p).toContinuousLinearMap -
          ContinuousLinearMap.id ℂ finiteSCarrier‖ := by
        rw [hadjoint_sub, ContinuousLinearMap.adjoint_adjoint,
          ContinuousLinearMap.adjoint_id]
  rw [hnorm]
  exact norm_primeEulerTransport_sub_id_le_coefficient p

theorem norm_lowerPrimeEulerTransportAdjoint_sub_id_le_two_mul_coefficient
    (p : CCM24VisiblePrime) :
    ‖((1 - ccm24PrimeEulerCoefficient p : ℝ) : ℂ) •
        (ccm24PrimeEulerTransportEquiv p).toContinuousLinearMap† -
        ContinuousLinearMap.id ℂ finiteSCarrier‖ ≤
      2 * ccm24PrimeEulerCoefficient p := by
  let q := ccm24PrimeEulerCoefficient p
  let a := 1 - q
  have hq : 0 ≤ q := ccm24PrimeEulerCoefficient_nonneg p
  have hq1 : q ≤ 1 := (ccm24PrimeEulerCoefficient_lt_one p).le
  have ha0 : 0 ≤ a := by dsimp [a]; linarith
  have ha1 : a ≤ 1 := by dsimp [a]; linarith
  have hsplit :
      ((a : ℝ) : ℂ) •
          (ccm24PrimeEulerTransportEquiv p).toContinuousLinearMap† -
          ContinuousLinearMap.id ℂ finiteSCarrier =
        ((a : ℝ) : ℂ) •
            ((ccm24PrimeEulerTransportEquiv p).toContinuousLinearMap† -
              ContinuousLinearMap.id ℂ finiteSCarrier) +
          ((-q : ℝ) : ℂ) • ContinuousLinearMap.id ℂ finiteSCarrier := by
    apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, map_sub]
    have hqa : ((a : ℝ) : ℂ) = 1 - (q : ℂ) := by
      dsimp [a]
      push_cast
      ring
    have hnegq : ((-q : ℝ) : ℂ) = -(q : ℂ) := by
      push_cast
      rfl
    rw [hqa, hnegq]
    simp only [sub_smul, smul_sub, one_smul, neg_smul, smul_eq_mul]
    abel_nf <;> ring
  rw [show ((1 - ccm24PrimeEulerCoefficient p : ℝ) : ℂ) =
      ((a : ℝ) : ℂ) by rfl, hsplit]
  have hnorma : ‖((a : ℝ) : ℂ)‖ = a := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha0]
  have hnormq : ‖((-q : ℝ) : ℂ)‖ = q := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    ring
  calc
    ‖((a : ℝ) : ℂ) •
          ((ccm24PrimeEulerTransportEquiv p).toContinuousLinearMap† -
            ContinuousLinearMap.id ℂ finiteSCarrier) +
        ((-q : ℝ) : ℂ) • ContinuousLinearMap.id ℂ finiteSCarrier‖ ≤
      ‖((a : ℝ) : ℂ) •
          ((ccm24PrimeEulerTransportEquiv p).toContinuousLinearMap† -
            ContinuousLinearMap.id ℂ finiteSCarrier)‖ +
        ‖((-q : ℝ) : ℂ) • ContinuousLinearMap.id ℂ finiteSCarrier‖ :=
      norm_add_le _ _
    _ = a * ‖(ccm24PrimeEulerTransportEquiv p).toContinuousLinearMap† -
          ContinuousLinearMap.id ℂ finiteSCarrier‖ +
        q * ‖ContinuousLinearMap.id ℂ finiteSCarrier‖ := by
      rw [norm_smul, norm_smul, hnorma, hnormq]
    _ ≤ a * q + q * 1 := by
      gcongr
      · exact norm_primeEulerTransportAdjoint_sub_id_le_coefficient p
      · exact ContinuousLinearMap.norm_id_le
    _ ≤ 2 * q := by nlinarith

theorem norm_lowerPrimeEulerInverse_sub_id_le_two_mul_coefficient
    (p : CCM24VisiblePrime) :
    ‖((1 - ccm24PrimeEulerCoefficient p : ℝ) : ℂ) •
        (ccm24PrimeEulerTransportEquiv p).symm.toContinuousLinearMap -
        ContinuousLinearMap.id ℂ finiteSCarrier‖ ≤
      2 * ccm24PrimeEulerCoefficient p := by
  let q := ccm24PrimeEulerCoefficient p
  let a := 1 - q
  let T := (ccm24PrimeEulerTransportEquiv p).toContinuousLinearMap
  let Tinv := (ccm24PrimeEulerTransportEquiv p).symm.toContinuousLinearMap
  let N := ((a : ℝ) : ℂ) • Tinv
  have hq : 0 ≤ q := ccm24PrimeEulerCoefficient_nonneg p
  have hprod : Tinv ∘L T = ContinuousLinearMap.id ℂ finiteSCarrier := by
    apply ContinuousLinearMap.ext
    intro x
    exact (ccm24PrimeEulerTransportEquiv p).symm_apply_apply x
  have hNnorm : ‖N‖ ≤ 1 := by
    have hTinvlist :
        (ccm24FiniteEulerTransportEquiv [p]).symm.toContinuousLinearMap =
          (ccm24PrimeEulerTransportEquiv p).symm.toContinuousLinearMap := by
      apply ContinuousLinearMap.ext
      intro x
      change (ccm24FiniteEulerTransportEquiv [p]).symm x =
        (ccm24PrimeEulerTransportEquiv p).symm x
      rw [finiteEulerTransportEquiv_symm_cons_apply p [] x]
      simp [ccm24FiniteEulerTransportEquiv_nil]
    change ‖((1 - ccm24PrimeEulerCoefficient p : ℝ) : ℂ) •
      (ccm24PrimeEulerTransportEquiv p).symm.toContinuousLinearMap‖ ≤ 1
    rw [← hTinvlist]
    simpa [finiteEulerLowerFactor] using
      (norm_lowerFactor_smul_finiteEulerInverseOperator_le_one [p])
  have hsplit : N - ContinuousLinearMap.id ℂ finiteSCarrier =
      N ∘L (ContinuousLinearMap.id ℂ finiteSCarrier - T) +
        ((-q : ℝ) : ℂ) • ContinuousLinearMap.id ℂ finiteSCarrier := by
    apply ContinuousLinearMap.ext
    intro x
    have hprodPoint := congrArg
      (fun operator : finiteSCarrier →L[ℂ] finiteSCarrier => operator x)
      hprod
    simp only [N, ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.smul_apply, map_sub] at hprodPoint ⊢
    rw [hprodPoint]
    have hqa : ((a : ℝ) : ℂ) = 1 - (q : ℂ) := by
      dsimp [a]
      push_cast
      ring
    have hnegq : ((-q : ℝ) : ℂ) = -(q : ℂ) := by
      push_cast
      rfl
    rw [hqa, hnegq]
    simp only [sub_smul, smul_sub, one_smul, neg_smul, smul_eq_mul]
    abel_nf <;> ring
  rw [show ((1 - ccm24PrimeEulerCoefficient p : ℝ) : ℂ) •
      (ccm24PrimeEulerTransportEquiv p).symm.toContinuousLinearMap = N by
        rfl, hsplit]
  have hTdiff :
      ‖ContinuousLinearMap.id ℂ finiteSCarrier - T‖ ≤ q := by
    dsimp [T, q]
    calc
      ‖ContinuousLinearMap.id ℂ finiteSCarrier -
          (ccm24PrimeEulerTransportEquiv p).toContinuousLinearMap‖ =
          ‖-((ccm24PrimeEulerTransportEquiv p).toContinuousLinearMap -
            ContinuousLinearMap.id ℂ finiteSCarrier)‖ := by
        rw [neg_sub]
      _ = ‖(ccm24PrimeEulerTransportEquiv p).toContinuousLinearMap -
          ContinuousLinearMap.id ℂ finiteSCarrier‖ := norm_neg _
      _ ≤ q := norm_primeEulerTransport_sub_id_le_coefficient p
  have hnormq : ‖((-q : ℝ) : ℂ)‖ = q := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    ring
  have hnegterm :
      ‖((-q : ℝ) : ℂ) • ContinuousLinearMap.id ℂ finiteSCarrier‖ ≤ q * 1 := by
    rw [norm_smul, hnormq]
    exact mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le
      (by positivity)
  calc
    ‖N ∘L (ContinuousLinearMap.id ℂ finiteSCarrier - T) +
          ((-q : ℝ) : ℂ) • ContinuousLinearMap.id ℂ finiteSCarrier‖ ≤
      ‖N ∘L (ContinuousLinearMap.id ℂ finiteSCarrier - T)‖ +
        ‖((-q : ℝ) : ℂ) • ContinuousLinearMap.id ℂ finiteSCarrier‖ :=
      norm_add_le _ _
    _ ≤ ‖N‖ * ‖ContinuousLinearMap.id ℂ finiteSCarrier - T‖ + q * 1 := by
      calc
        ‖N ∘L (ContinuousLinearMap.id ℂ finiteSCarrier - T)‖ +
              ‖((-q : ℝ) : ℂ) • ContinuousLinearMap.id ℂ finiteSCarrier‖ ≤
            ‖N‖ * ‖ContinuousLinearMap.id ℂ finiteSCarrier - T‖ +
              ‖((-q : ℝ) : ℂ) • ContinuousLinearMap.id ℂ finiteSCarrier‖ := by
          exact add_le_add
            (ContinuousLinearMap.opNorm_comp_le N
              (ContinuousLinearMap.id ℂ finiteSCarrier - T))
            (le_refl _)
        _ ≤ ‖N‖ * ‖ContinuousLinearMap.id ℂ finiteSCarrier - T‖ + q * 1 := by
          exact add_le_add (le_refl _) hnegterm
    _ ≤ 1 * q + q * 1 := by
      exact add_le_add
        (mul_le_mul hNnorm hTdiff (norm_nonneg _) (by norm_num))
        (le_refl _)
    _ = 2 * q := by ring

theorem norm_lowerPrimeEulerInverseAdjoint_sub_id_le_two_mul_coefficient
    (p : CCM24VisiblePrime) :
    ‖((1 - ccm24PrimeEulerCoefficient p : ℝ) : ℂ) •
        (ccm24PrimeEulerTransportEquiv p).symm.toContinuousLinearMap† -
        ContinuousLinearMap.id ℂ finiteSCarrier‖ ≤
      2 * ccm24PrimeEulerCoefficient p := by
  let q := ccm24PrimeEulerCoefficient p
  let a := 1 - q
  let Tinv := (ccm24PrimeEulerTransportEquiv p).symm.toContinuousLinearMap
  have hsub (A B : finiteSCarrier →L[ℂ] finiteSCarrier) :
      (A - B)† = A† - B† := by
    apply ContinuousLinearMap.ext
    intro x
    exact ext_inner_right ℂ fun y => by
      simp only [ContinuousLinearMap.adjoint_inner_left,
        ContinuousLinearMap.sub_apply, inner_sub_left, inner_sub_right]
  have hsmul (A : finiteSCarrier →L[ℂ] finiteSCarrier) :
      (((a : ℝ) : ℂ) • A)† = ((a : ℝ) : ℂ) • A† := by
    calc
      (((a : ℝ) : ℂ) • A)† =
          (starRingEnd ℂ) ((a : ℝ) : ℂ) • A† :=
        ContinuousLinearMap.adjoint.map_smulₛₗ _ _
      _ = ((a : ℝ) : ℂ) • A† := by
        congr 1
        change star ((a : ℝ) : ℂ) = ((a : ℝ) : ℂ)
        simpa only [Complex.star_def] using Complex.conj_ofReal a
  have hnorm :
      ‖((a : ℝ) : ℂ) • Tinv† - ContinuousLinearMap.id ℂ finiteSCarrier‖ =
        ‖((a : ℝ) : ℂ) • Tinv - ContinuousLinearMap.id ℂ finiteSCarrier‖ := by
    calc
      _ = ‖(((a : ℝ) : ℂ) • Tinv† -
          ContinuousLinearMap.id ℂ finiteSCarrier)†‖ := by
        symm
        exact ContinuousLinearMap.adjoint.norm_map _
      _ = ‖((a : ℝ) : ℂ) • Tinv -
          ContinuousLinearMap.id ℂ finiteSCarrier‖ := by
        rw [hsub, hsmul, ContinuousLinearMap.adjoint_adjoint,
          ContinuousLinearMap.adjoint_id]
  rw [show ((1 - ccm24PrimeEulerCoefficient p : ℝ) : ℂ) •
      (ccm24PrimeEulerTransportEquiv p).symm.toContinuousLinearMap† =
        ((a : ℝ) : ℂ) • Tinv† by rfl, hnorm]
  exact norm_lowerPrimeEulerInverse_sub_id_le_two_mul_coefficient p

theorem norm_suffixActualBandForwardCoframe_singlePrime_le_two_mul_coefficient
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) :
    ‖suffixActualBandForwardCoframe lambda [p]‖ ≤
      2 * ccm24PrimeEulerCoefficient p := by
  have hzero : sourceBandProjection lambda ∘L sourceInclusion lambda = 0 :=
    sourceBandProjection_comp_sourceInclusion_eq_zero lambda
  have hNlist : normalizedFiniteEulerInverseList [p] =
      normalizedPrimeEulerInverse p := by
    rw [normalizedFiniteEulerInverseList_cons]
    have hnil : normalizedFiniteEulerInverseList [] =
        ContinuousLinearMap.id ℂ finiteSCarrier := by
      have h := finiteEulerCausalAverage_eq_normalizedInverse []
      simpa only [finiteEulerCausalAverage] using h.symm
    rw [hnil]
    simp
  have hNdiff : ‖normalizedFiniteEulerInverseList [p] -
      ContinuousLinearMap.id ℂ finiteSCarrier‖ ≤
      2 * ccm24PrimeEulerCoefficient p := by
    rw [hNlist]
    simpa [normalizedPrimeEulerInverse] using
      (norm_lowerPrimeEulerInverse_sub_id_le_two_mul_coefficient p)
  have hband : ‖sourceBandProjection lambda‖ ≤ 1 :=
    IsStarProjection.norm_le _ (sourceBandProjection_isStarProjection lambda)
  have hinclusion : ‖sourceInclusion lambda‖ ≤ 1 :=
    Submodule.norm_subtypeL_le _
  have hrewrite :
      suffixActualBandForwardCoframe lambda [p] =
        sourceBandProjection lambda ∘L
            (normalizedFiniteEulerInverseList [p] -
              ContinuousLinearMap.id ℂ finiteSCarrier) ∘L
          sourceInclusion lambda := by
    apply ContinuousLinearMap.ext
    intro x
    have hzeroPoint := congrArg
      (fun operator : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier =>
        operator x) hzero
    simp only [suffixActualBandForwardCoframe,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.zero_apply, map_sub] at hzeroPoint ⊢
    have hzeroPoint' :
        sourceBandProjection lambda
            ((ContinuousLinearMap.id ℂ finiteSCarrier)
              (sourceInclusion lambda x)) = 0 := by
      simpa only [ContinuousLinearMap.id_apply] using hzeroPoint
    rw [hzeroPoint']
    abel
  rw [hrewrite]
  calc
    ‖sourceBandProjection lambda ∘L
          (normalizedFiniteEulerInverseList [p] -
            ContinuousLinearMap.id ℂ finiteSCarrier) ∘L
        sourceInclusion lambda‖ ≤
        ‖sourceBandProjection lambda‖ *
          ‖normalizedFiniteEulerInverseList [p] -
            ContinuousLinearMap.id ℂ finiteSCarrier‖ *
          ‖sourceInclusion lambda‖ := by
      calc
        _ ≤ ‖sourceBandProjection lambda ∘L
              (normalizedFiniteEulerInverseList [p] -
                ContinuousLinearMap.id ℂ finiteSCarrier)‖ *
              ‖sourceInclusion lambda‖ :=
          ContinuousLinearMap.opNorm_comp_le
            (sourceBandProjection lambda ∘L
              (normalizedFiniteEulerInverseList [p] -
                ContinuousLinearMap.id ℂ finiteSCarrier))
            (sourceInclusion lambda)
        _ ≤ (‖sourceBandProjection lambda‖ *
              ‖normalizedFiniteEulerInverseList [p] -
                ContinuousLinearMap.id ℂ finiteSCarrier‖) *
              ‖sourceInclusion lambda‖ := by
          exact mul_le_mul_of_nonneg_right
            (ContinuousLinearMap.opNorm_comp_le
              (sourceBandProjection lambda)
              (normalizedFiniteEulerInverseList [p] -
                ContinuousLinearMap.id ℂ finiteSCarrier))
            (norm_nonneg (sourceInclusion lambda))
    _ ≤ 1 * (2 * ccm24PrimeEulerCoefficient p) * 1 := by
      have hq : 0 ≤ ccm24PrimeEulerCoefficient p :=
        ccm24PrimeEulerCoefficient_nonneg p
      calc
        ‖sourceBandProjection lambda‖ *
              ‖normalizedFiniteEulerInverseList [p] -
                ContinuousLinearMap.id ℂ finiteSCarrier‖ *
              ‖sourceInclusion lambda‖ ≤
            1 * ‖normalizedFiniteEulerInverseList [p] -
                ContinuousLinearMap.id ℂ finiteSCarrier‖ *
              ‖sourceInclusion lambda‖ := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hband
              (norm_nonneg
                (normalizedFiniteEulerInverseList [p] -
                  ContinuousLinearMap.id ℂ finiteSCarrier)))
            (norm_nonneg (sourceInclusion lambda))
        _ ≤ 1 * (2 * ccm24PrimeEulerCoefficient p) *
              ‖sourceInclusion lambda‖ := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hNdiff (by positivity))
            (norm_nonneg (sourceInclusion lambda))
        _ ≤ 1 * (2 * ccm24PrimeEulerCoefficient p) * 1 := by
          exact mul_le_mul_of_nonneg_left hinclusion
            (by positivity)
    _ = 2 * ccm24PrimeEulerCoefficient p := by ring

theorem norm_lowerPrimeEulerCovariance_gap_le_twelve_mul_coefficient
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) :
    ‖(((1 - ccm24PrimeEulerCoefficient p : ℝ) : ℂ) •
          (ccm24PrimeEulerTransportEquiv p).toContinuousLinearMap†) ∘L
        parameterizedCanonicalGramProjection lambda 1 [p] ∘L
          (((1 - ccm24PrimeEulerCoefficient p : ℝ) : ℂ) •
            (ccm24PrimeEulerTransportEquiv p).symm.toContinuousLinearMap†) -
      sourceSoninProjection lambda‖ ≤
      12 * ccm24PrimeEulerCoefficient p := by
  let q := ccm24PrimeEulerCoefficient p
  let a := 1 - q
  let T := (ccm24PrimeEulerTransportEquiv p).toContinuousLinearMap
  let Tinv := (ccm24PrimeEulerTransportEquiv p).symm.toContinuousLinearMap
  let A := ((a : ℝ) : ℂ) • T†
  let B := ((a : ℝ) : ℂ) • Tinv†
  let P := parameterizedCanonicalGramProjection lambda 1 [p]
  let R := sourceSoninProjection lambda
  let I := ContinuousLinearMap.id ℂ finiteSCarrier
  have hA : ‖A - I‖ ≤ 2 * q := by
    dsimp [A, T, I, a, q]
    exact norm_lowerPrimeEulerTransportAdjoint_sub_id_le_two_mul_coefficient p
  have hB : ‖B - I‖ ≤ 2 * q := by
    dsimp [B, Tinv, I, a, q]
    exact norm_lowerPrimeEulerInverseAdjoint_sub_id_le_two_mul_coefficient p
  have hP : ‖P - R‖ ≤ 8 * q := by
    dsimp [P, R, q]
    calc
      ‖parameterizedCanonicalGramProjection lambda 1 [p] -
          sourceSoninProjection lambda‖ =
          ‖parameterizedCanonicalGramProjection lambda 1 [p] -
            parameterizedCanonicalGramProjection lambda 0 [p]‖ := by
        rw [parameterizedCanonicalGramProjection_zero]
      _ ≤ 8 * ccm24PrimeEulerCoefficient p :=
        norm_parameterizedCanonicalGramProjection_one_sub_zero_le_eight_mul_coefficient
          lambda p
  have hPnorm : ‖P‖ ≤ 1 :=
    IsStarProjection.norm_le _
      (parameterizedCanonicalGramProjection_isStarProjection
        lambda 1 [p] (by norm_num))
  have hRnorm : ‖R‖ ≤ 1 :=
    IsStarProjection.norm_le _ (sourceSoninProjection_isStarProjection lambda)
  have hAnorm : ‖A‖ ≤ 1 := by
    have hTlist : ccm24FiniteEulerTransportEquiv [p] =
        ccm24PrimeEulerTransportEquiv p := by
      apply ContinuousLinearEquiv.ext
      funext x
      rw [ccm24FiniteEulerTransportEquiv_cons_apply p [] x]
      simp [ccm24FiniteEulerTransportEquiv_nil]
    have h := norm_lowerFactor_smul_finiteEulerTransportAdjoint_le_one [p]
    rw [hTlist] at h
    change ‖((1 - ccm24PrimeEulerCoefficient p : ℝ) : ℂ) •
        (ccm24PrimeEulerTransportEquiv p).toContinuousLinearMap†‖ ≤ 1
    simpa [finiteEulerLowerFactor] using h
  have hBnorm : ‖B‖ ≤ 1 := by
    have hTinvlist :
        (ccm24FiniteEulerTransportEquiv [p]).symm =
          (ccm24PrimeEulerTransportEquiv p).symm := by
      apply ContinuousLinearEquiv.ext
      funext x
      rw [finiteEulerTransportEquiv_symm_cons_apply p [] x]
      simp [ccm24FiniteEulerTransportEquiv_nil]
    have h := norm_lowerFactor_smul_finiteEulerInverseOperator_le_one [p]
    rw [hTinvlist] at h
    have h' : ‖((a : ℝ) : ℂ) • Tinv‖ ≤ 1 := by
      simpa [finiteEulerLowerFactor, Tinv, a, q] using h
    have hnorm : ‖B‖ = ‖((a : ℝ) : ℂ) • Tinv‖ := by
      have hsmul : (((a : ℝ) : ℂ) • Tinv)† =
          ((a : ℝ) : ℂ) • Tinv† := by
        calc
          (((a : ℝ) : ℂ) • Tinv)† =
              (starRingEnd ℂ) ((a : ℝ) : ℂ) • Tinv† :=
            ContinuousLinearMap.adjoint.map_smulₛₗ _ _
          _ = ((a : ℝ) : ℂ) • Tinv† := by
            congr 1
            change star ((a : ℝ) : ℂ) = ((a : ℝ) : ℂ)
            simpa only [Complex.star_def] using Complex.conj_ofReal a
      change ‖((a : ℝ) : ℂ) • Tinv†‖ =
        ‖((a : ℝ) : ℂ) • Tinv‖
      rw [← hsmul, ContinuousLinearMap.adjoint.norm_map]
    rw [hnorm]
    exact h'
  have hX : ‖(A - I) ∘L P ∘L B‖ ≤
      ‖A - I‖ * ‖P‖ * ‖B‖ := by
    calc
      ‖(A - I) ∘L P ∘L B‖ ≤
          ‖(A - I) ∘L P‖ * ‖B‖ :=
        ContinuousLinearMap.opNorm_comp_le ((A - I) ∘L P) B
      _ ≤ (‖A - I‖ * ‖P‖) * ‖B‖ := by
        exact mul_le_mul_of_nonneg_right
          (ContinuousLinearMap.opNorm_comp_le (A - I) P)
          (norm_nonneg B)
  have hY : ‖(P - R) ∘L B‖ ≤ ‖P - R‖ * ‖B‖ :=
    ContinuousLinearMap.opNorm_comp_le _ _
  have hZ : ‖R ∘L (B - I)‖ ≤ ‖R‖ * ‖B - I‖ :=
    ContinuousLinearMap.opNorm_comp_le _ _
  have hdecomp : A ∘L P ∘L B - R =
      (A - I) ∘L P ∘L B + (P - R) ∘L B + R ∘L (B - I) := by
    apply ContinuousLinearMap.ext
    intro x
    simp only [I, ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, map_sub]
    module
  have hq : 0 ≤ q := by
    dsimp [q]
    exact ccm24PrimeEulerCoefficient_nonneg p
  have hX' : ‖(A - I) ∘L P ∘L B‖ ≤ (2 * q) * 1 * 1 := by
    calc
      _ ≤ ‖A - I‖ * ‖P‖ * ‖B‖ := hX
      _ ≤ (2 * q) * ‖P‖ * ‖B‖ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hA (norm_nonneg P))
          (norm_nonneg B)
      _ ≤ (2 * q) * 1 * ‖B‖ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hPnorm (by positivity))
          (norm_nonneg B)
      _ ≤ (2 * q) * 1 * 1 := by
        exact mul_le_mul_of_nonneg_left hBnorm (by positivity)
  have hY' : ‖(P - R) ∘L B‖ ≤ (8 * q) * 1 := by
    calc
      _ ≤ ‖P - R‖ * ‖B‖ := hY
      _ ≤ (8 * q) * 1 := by
        exact mul_le_mul hP hBnorm (norm_nonneg B) (by positivity)
  have hZ' : ‖R ∘L (B - I)‖ ≤ 1 * (2 * q) := by
    calc
      _ ≤ ‖R‖ * ‖B - I‖ := hZ
      _ ≤ 1 * (2 * q) := by
        exact mul_le_mul hRnorm hB (norm_nonneg (B - I)) (by norm_num)
  rw [show (((1 - ccm24PrimeEulerCoefficient p : ℝ) : ℂ) • T†) = A by rfl,
      show (((1 - ccm24PrimeEulerCoefficient p : ℝ) : ℂ) • Tinv†) = B by rfl,
    show parameterizedCanonicalGramProjection lambda 1 [p] = P by rfl,
    show sourceSoninProjection lambda = R by rfl, hdecomp]
  calc
    ‖(A - I) ∘L P ∘L B + (P - R) ∘L B + R ∘L (B - I)‖ ≤
        ‖(A - I) ∘L P ∘L B‖ + ‖(P - R) ∘L B‖ +
          ‖R ∘L (B - I)‖ := by
      calc
        _ ≤ ‖(A - I) ∘L P ∘L B + (P - R) ∘L B‖ +
              ‖R ∘L (B - I)‖ := norm_add_le _ _
        _ ≤ (‖(A - I) ∘L P ∘L B‖ + ‖(P - R) ∘L B‖) +
              ‖R ∘L (B - I)‖ := by
          gcongr
          exact norm_add_le _ _
        _ = _ := by ring
    _ ≤ (2 * q) * 1 * 1 + (8 * q) * 1 + 1 * (2 * q) := by
      exact add_le_add (add_le_add hX' hY') hZ'
    _ = 12 * q := by ring

theorem norm_normalizedPhysicalLeakage_singlePrime_le_twelve_mul_coefficient
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (hp : Nat.Prime p.1) :
    ‖normalizedSourcePhysicalCoframeLeakage
        lambda (singlePrimeFamily p hp)‖ ≤
      12 * ccm24PrimeEulerCoefficient p := by
  let q := ccm24PrimeEulerCoefficient p
  let a := 1 - q
  let family := singlePrimeFamily p hp
  let T := (ccm24PrimeEulerTransportEquiv p).toContinuousLinearMap
  let Tinv := (ccm24PrimeEulerTransportEquiv p).symm.toContinuousLinearMap
  let A := ((a : ℝ) : ℂ) • T†
  let B := ((a : ℝ) : ℂ) • Tinv†
  let P := parameterizedCanonicalGramProjection lambda 1 [p]
  let R := sourceSoninProjection lambda
  let I := ContinuousLinearMap.id ℂ finiteSCarrier
  have hvisible : family.visiblePrimes = [p] := by
    dsimp [family]
    exact singlePrimeFamily_visiblePrimes p hp
  have htransport : finiteEulerTransportOperator family = T := by
    unfold finiteEulerTransportOperator
    rw [hvisible]
    apply ContinuousLinearMap.ext
    intro x
    change ccm24FiniteEulerTransportEquiv [p] x =
      ccm24PrimeEulerTransportEquiv p x
    rw [ccm24FiniteEulerTransportEquiv_cons_apply p [] x]
    simp [ccm24FiniteEulerTransportEquiv_nil]
  have hinverse : finiteEulerInverseOperator family = Tinv := by
    unfold finiteEulerInverseOperator
    rw [hvisible]
    apply ContinuousLinearMap.ext
    intro x
    change (ccm24FiniteEulerTransportEquiv [p]).symm x =
      (ccm24PrimeEulerTransportEquiv p).symm x
    rw [finiteEulerTransportEquiv_symm_cons_apply p [] x]
    simp [ccm24FiniteEulerTransportEquiv_nil]
  have hprojection :
      targetTransportedSoninInclusion lambda (singlePrimeFamily p hp) ∘L
          (targetTransportedSoninInclusion lambda (singlePrimeFamily p hp))† =
        parameterizedCanonicalGramProjection lambda 1 [p] := by
    exact targetTransportedSoninProjection_eq_parameterizedCanonicalGramProjection
      lambda p hp
  have hzero : (I - R) ∘L R = 0 := by
    apply ContinuousLinearMap.ext
    intro x
    have hidem := congrArg
      (fun operator : finiteSCarrier →L[ℂ] finiteSCarrier => operator x)
      (sourceSoninProjection_isStarProjection lambda).isIdempotentElem
    simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.zero_apply] at hidem ⊢
    rw [sub_eq_zero.mpr]
    exact hidem.symm
  have hcollapse :
      (I - R) ∘L A ∘L P ∘L B ∘L sourceInclusion lambda =
        (I - R) ∘L (A ∘L P ∘L B - R) ∘L sourceInclusion lambda := by
    apply ContinuousLinearMap.ext
    intro x
    have hzeroPoint := congrArg
      (fun operator : finiteSCarrier →L[ℂ] finiteSCarrier =>
        operator (sourceInclusion lambda x)) hzero
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.zero_apply,
      map_sub] at hzeroPoint ⊢
    rw [hzeroPoint]
    simpa only [sub_zero]
  have hgap : ‖A ∘L P ∘L B - R‖ ≤ 12 * q := by
    dsimp [A, B, P, R, I, T, Tinv, a, q]
    exact norm_lowerPrimeEulerCovariance_gap_le_twelve_mul_coefficient
      lambda p
  have hcompnorm : ‖I - R‖ ≤ 1 := by
    dsimp [I, R]
    exact norm_sourceSoninComplement_le_one lambda
  have hinclusion : ‖sourceInclusion lambda‖ ≤ 1 :=
    Submodule.norm_subtypeL_le _
  rw [normalizedPhysicalLeakage_eq_causal_covariance]
  rw [htransport, hinverse]
  have hc : finiteEulerLowerFactor family.visiblePrimes = a := by
    rw [hvisible]
    simp [finiteEulerLowerFactor, a, q]
  have hfamily : (singlePrimeFamily p hp).visiblePrimes = family.visiblePrimes := rfl
  have hpairTarget :
      (I - R) ∘L
          (((finiteEulerLowerFactor family.visiblePrimes : ℂ) • T†) ∘L
            targetTransportedSoninInclusion lambda (singlePrimeFamily p hp) ∘L
              (targetTransportedSoninInclusion lambda
                (singlePrimeFamily p hp))† ∘L
            ((finiteEulerLowerFactor family.visiblePrimes : ℂ) • Tinv†)) ∘L
        sourceInclusion lambda =
      (I - R) ∘L A ∘L P ∘L B ∘L sourceInclusion lambda := by
    rw [hc]
    have hpair := congrArg
      (fun X : finiteSCarrier →L[ℂ] finiteSCarrier =>
        (I - R) ∘L
            (((finiteEulerLowerFactor family.visiblePrimes : ℂ) • T†) ∘L
              X ∘L
              ((finiteEulerLowerFactor family.visiblePrimes : ℂ) • Tinv†)) ∘L
            sourceInclusion lambda)
      (targetTransportedSoninProjection_eq_parameterizedCanonicalGramProjection
        lambda p hp)
    rw [hc] at hpair
    simpa only [A, B, ContinuousLinearMap.comp_assoc] using hpair
  have hpairTargetRight := hpairTarget
  simp only [ContinuousLinearMap.comp_assoc] at hpairTargetRight
  rw [hfamily]
  rw [hpairTargetRight]
  rw [hcollapse]
  calc
    ‖(I - R) ∘L (A ∘L P ∘L B - R) ∘L sourceInclusion lambda‖ ≤
        ‖I - R‖ * ‖A ∘L P ∘L B - R‖ * ‖sourceInclusion lambda‖ := by
      calc
        _ ≤ ‖(I - R) ∘L (A ∘L P ∘L B - R)‖ *
              ‖sourceInclusion lambda‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ (‖I - R‖ * ‖A ∘L P ∘L B - R‖) *
              ‖sourceInclusion lambda‖ := by
          gcongr
          exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * (12 * q) * 1 := by
      gcongr
      have hq : 0 ≤ q := by
        dsimp [q]
        exact ccm24PrimeEulerCoefficient_nonneg p
      positivity
    _ = 12 * q := by ring

theorem norm_suffixActualBandMetricCoframe_sub_sourceInclusion_singlePrime_le
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (hp : Nat.Prime p.1) :
    ‖suffixActualBandMetricCoframe lambda [p] - sourceInclusion lambda‖ ≤
      192 * ccm24PrimeEulerCoefficient p := by
  let q := ccm24PrimeEulerCoefficient p
  let a := 1 - q
  let family := singlePrimeFamily p hp
  let M := suffixActualBandMetricCoframe lambda [p]
  let J := sourceInclusion lambda
  let R := sourceSoninProjection lambda
  let I := ContinuousLinearMap.id ℂ finiteSCarrier
  have hvisible : family.visiblePrimes = [p] := by
    dsimp [family]
    exact singlePrimeFamily_visiblePrimes p hp
  have hmetric : M = finiteEulerMetricCoframe lambda family := by
    dsimp [M]
    simpa [hvisible] using
      (suffixActualBandMetricCoframe_visiblePrimes_eq_finiteEulerMetricCoframe
        lambda family)
  have hcomp : (I - R) ∘L M = M - J := by
    apply ContinuousLinearMap.ext
    intro x
    have hM := congrArg
      (fun operator : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier =>
        operator x)
      (sourceSoninProjection_comp_suffixActualBandMetricCoframe lambda [p])
    have hJ := congrArg
      (fun operator : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier =>
        operator x)
      (sourceSoninProjection_comp_sourceInclusion_eq_self lambda)
    simp only [I, R, M, J, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply] at hM hJ ⊢
    rw [hM]
  have hmetricLeak :
      normalizedSourcePhysicalCoframeLeakage lambda family =
        (((1 - q : ℝ) : ℂ) ^ 2) • (M - J) := by
    rw [normalizedSourcePhysicalCoframeLeakage_eq_complement_comp,
      normalizedFiniteEulerMetricCoframe, hvisible, ← hmetric]
    apply ContinuousLinearMap.ext
    intro x
    have hcompPoint := congrArg
      (fun operator : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier =>
        operator x) hcomp
    simp only [I, R, M, J, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.comp_apply, map_smul,
      ContinuousLinearMap.sub_apply] at hcompPoint ⊢
    rw [hcompPoint]
    simp [finiteEulerLowerFactor, q]
  have hleak : ‖normalizedSourcePhysicalCoframeLeakage lambda family‖ ≤
      12 * q := by
    dsimp [q]
    exact norm_normalizedPhysicalLeakage_singlePrime_le_twelve_mul_coefficient
      lambda p hp
  have hq : q ≤ 3 / 4 := by
    dsimp [q]
    exact ccm24PrimeEulerCoefficient_le_three_quarters p
  have ha_pos : 0 < a := by
    dsimp [a]
    exact sub_pos.mpr (lt_of_le_of_lt hq (by norm_num))
  have ha_quarter : (1 / 4 : ℝ) ≤ a := by
    dsimp [a]
    linarith
  have ha_inv : a⁻¹ ≤ (4 : ℝ) := by
    apply (inv_le_iff_one_le_mul₀ (by positivity)).2
    linarith
  have ha_inv_nonneg : 0 ≤ a⁻¹ := le_of_lt (inv_pos.mpr ha_pos)
  have ha_inv_sq : a⁻¹ ^ 2 ≤ (16 : ℝ) := by
    nlinarith [sq_nonneg (4 - a⁻¹)]
  have hscalar : ‖(((a : ℝ) : ℂ) ^ 2)‖ = a ^ 2 := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (le_of_lt ha_pos)]
  have hnormeq :
      ‖normalizedSourcePhysicalCoframeLeakage lambda family‖ ≤
        a ^ 2 * ‖M - J‖ := by
    rw [hmetricLeak]
    calc
      ‖(((a : ℝ) : ℂ) ^ 2) • (M - J)‖ ≤
          ‖((a : ℝ) : ℂ) ^ 2‖ * ‖M - J‖ :=
        ContinuousLinearMap.opNorm_smul_le _ _
      _ = a ^ 2 * ‖M - J‖ := by rw [hscalar]
  have hscalar_inv :
      (((a⁻¹ : ℝ) : ℂ) ^ 2) * (((a : ℝ) : ℂ) ^ 2) = 1 := by
    push_cast
    field_simp [ne_of_gt ha_pos]
  have hMidentity :
      M - J = (((a⁻¹ : ℝ) : ℂ) ^ 2) •
        normalizedSourcePhysicalCoframeLeakage lambda family := by
    rw [hmetricLeak]
    apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.smul_apply, smul_smul]
    rw [hscalar_inv, one_smul]
  have hMbound : ‖M - J‖ ≤
      16 * ‖normalizedSourcePhysicalCoframeLeakage lambda family‖ := by
    calc
      ‖M - J‖ = ‖(((a⁻¹ : ℝ) : ℂ) ^ 2) •
          normalizedSourcePhysicalCoframeLeakage lambda family‖ := by
        rw [hMidentity]
      _ ≤ ‖((a⁻¹ : ℝ) : ℂ) ^ 2‖ *
          ‖normalizedSourcePhysicalCoframeLeakage lambda family‖ :=
        ContinuousLinearMap.opNorm_smul_le _ _
      _ = a⁻¹ ^ 2 *
          ‖normalizedSourcePhysicalCoframeLeakage lambda family‖ := by
        have hinvnorm : ‖((a⁻¹ : ℝ) : ℂ)‖ = a⁻¹ := by
          rw [Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg ha_inv_nonneg]
        rw [norm_pow, hinvnorm]
      _ ≤ 16 *
          ‖normalizedSourcePhysicalCoframeLeakage lambda family‖ := by
        exact mul_le_mul_of_nonneg_right ha_inv_sq
          (norm_nonneg
            (normalizedSourcePhysicalCoframeLeakage lambda family))
  calc
    ‖suffixActualBandMetricCoframe lambda [p] -
        sourceInclusion lambda‖ ≤
        16 * ‖normalizedSourcePhysicalCoframeLeakage lambda family‖ := by
      simpa [M, J] using hMbound
    _ ≤ 16 * (12 * ccm24PrimeEulerCoefficient p) := by
      exact mul_le_mul_of_nonneg_left hleak (by positivity)
    _ = 192 * ccm24PrimeEulerCoefficient p := by ring

theorem norm_onePrimeBoundaryMomentColumn_le
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (hp : Nat.Prime p.1) :
    ‖onePrimeBoundaryMomentColumn owner lambda p‖ ≤
      196 * ccm24PrimeEulerCoefficient p * ‖detectorOperator owner‖ := by
  let q := ccm24PrimeEulerCoefficient p
  let F := suffixActualBandForwardCoframe lambda [p]
  let E := suffixActualBandForwardEndpointCoframe lambda [p]
  let J := sourceInclusion lambda
  let K := detectorOperator owner
  have hF : ‖F‖ ≤ 2 * q := by
    dsimp [F, q]
    exact norm_suffixActualBandForwardCoframe_singlePrime_le_two_mul_coefficient
      lambda p
  have hM : ‖suffixActualBandMetricCoframe lambda [p] - J‖ ≤ 192 * q := by
    dsimp [J, q]
    exact norm_suffixActualBandMetricCoframe_sub_sourceInclusion_singlePrime_le
      lambda p hp
  have hE : ‖E - J‖ ≤ 194 * q := by
    have hsplit : E - J = F +
        (suffixActualBandMetricCoframe lambda [p] - J) := by
      apply ContinuousLinearMap.ext
      intro x
      simp only [E, F, suffixActualBandForwardEndpointCoframe,
        ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply]
      module
    rw [hsplit]
    calc
      ‖F + (suffixActualBandMetricCoframe lambda [p] - J)‖ ≤
          ‖F‖ + ‖suffixActualBandMetricCoframe lambda [p] - J‖ :=
        norm_add_le F (suffixActualBandMetricCoframe lambda [p] - J)
      _ ≤ 2 * q + 192 * q := by gcongr
      _ = 194 * q := by ring
  have hJ : ‖J‖ ≤ 1 := by
    dsimp [J]
    exact Submodule.norm_subtypeL_le _
  have hJadj : ‖J†‖ ≤ 1 := by
    have hadjoint : ‖J†‖ = ‖J‖ :=
      ContinuousLinearMap.adjoint.norm_map _
    rw [hadjoint]
    exact hJ
  have hraw0 : ‖rawCoframeBoundaryMoment owner lambda
        (suffixActualBandForwardCoframe lambda [p])
        (suffixActualBandForwardEndpointCoframe lambda [p])‖ ≤
      196 * q * ‖K‖ := by
    rw [suffixActualBandRawCoframeBoundaryMoment_eq_leakage]
    have hfirst : ‖(E - J)† ∘L K ∘L J‖ ≤
        ‖E - J‖ * ‖K‖ * ‖J‖ := by
      calc
        ‖(E - J)† ∘L K ∘L J‖ ≤
            ‖(E - J)† ∘L K‖ * ‖J‖ :=
          ContinuousLinearMap.opNorm_comp_le ((E - J)† ∘L K) J
        _ ≤ (‖E - J‖ * ‖K‖) * ‖J‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg J)
          calc
            ‖(E - J)† ∘L K‖ ≤ ‖(E - J)†‖ * ‖K‖ :=
              ContinuousLinearMap.opNorm_comp_le ((E - J)†) K
            _ = ‖E - J‖ * ‖K‖ := by
              exact congrArg (fun r : ℝ => r * ‖K‖)
                (ContinuousLinearMap.adjoint.norm_map (E - J))
    have hsecond : ‖J† ∘L K ∘L F‖ ≤
        ‖J†‖ * ‖K‖ * ‖F‖ := by
      calc
        ‖J† ∘L K ∘L F‖ ≤ ‖J† ∘L K‖ * ‖F‖ :=
          ContinuousLinearMap.opNorm_comp_le (J† ∘L K) F
        _ ≤ (‖J†‖ * ‖K‖) * ‖F‖ := by
          exact mul_le_mul_of_nonneg_right
            (ContinuousLinearMap.opNorm_comp_le (J†) K)
            (norm_nonneg F)
    have hq : 0 ≤ q := ccm24PrimeEulerCoefficient_nonneg p
    have h194 : 0 ≤ 194 * q := by positivity
    have hfirstBound :
        ‖E - J‖ * ‖K‖ * ‖J‖ ≤ (194 * q) * ‖K‖ * 1 := by
      calc
        ‖E - J‖ * ‖K‖ * ‖J‖ =
            ‖E - J‖ * (‖K‖ * ‖J‖) := by ring
        _ ≤ (194 * q) * (‖K‖ * ‖J‖) := by
          exact mul_le_mul_of_nonneg_right hE
            (mul_nonneg (norm_nonneg K) (norm_nonneg J))
        _ ≤ (194 * q) * (‖K‖ * 1) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hJ (norm_nonneg K)) h194
        _ = (194 * q) * ‖K‖ * 1 := by ring
    have hsecondBound :
        ‖J†‖ * ‖K‖ * ‖F‖ ≤ 1 * ‖K‖ * (2 * q) := by
      calc
        ‖J†‖ * ‖K‖ * ‖F‖ =
            (‖J†‖ * ‖K‖) * ‖F‖ := by ring
        _ ≤ (1 * ‖K‖) * ‖F‖ := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hJadj (norm_nonneg K))
            (norm_nonneg F)
        _ ≤ (1 * ‖K‖) * (2 * q) := by
          exact mul_le_mul_of_nonneg_left hF
            (mul_nonneg (by norm_num) (norm_nonneg K))
    calc
      ‖(E - J)† ∘L K ∘L J + J† ∘L K ∘L F‖ ≤
          ‖(E - J)† ∘L K ∘L J‖ + ‖J† ∘L K ∘L F‖ :=
        norm_add_le ((E - J)† ∘L K ∘L J) (J† ∘L K ∘L F)
      _ ≤ (‖E - J‖ * ‖K‖ * ‖J‖) +
          (‖J†‖ * ‖K‖ * ‖F‖) := add_le_add hfirst hsecond
      _ ≤ (194 * q) * ‖K‖ * 1 + 1 * ‖K‖ * (2 * q) := by
        exact add_le_add hfirstBound hsecondBound
      _ = 196 * q * ‖K‖ := by ring
  have hraw : ‖onePrimeBoundaryMoment owner lambda p‖ ≤
      196 * q * ‖K‖ := by
    simpa only [onePrimeBoundaryMoment] using hraw0
  have hold : ‖(suffixEulerFrameSchurStep lambda p []).oldFrame‖ ≤ 1 := by
    change ‖oldSuffixFrame lambda p []‖ ≤ 1
    exact CCM24FiniteSJuliaCausal.norm_le_one_of_isometric_inclusion
      (oldSuffixFrame lambda p []) (by
        intro x
        exact CCM24FiniteSFixedSourcePolar.parameterizedSoninPolarFrame_isometry
          lambda 1 (p :: [])
          (by norm_num) x)
  have hnew : ‖newSuffixFrame lambda []‖ ≤ 1 :=
    CCM24FiniteSJuliaCausal.norm_le_one_of_isometric_inclusion
      (newSuffixFrame lambda []) (by
        intro x
        exact CCM24FiniteSFixedSourcePolar.parameterizedSoninPolarFrame_isometry
          lambda 1 []
          (by norm_num) x)
  change ‖onePrimeBoundaryMoment owner lambda p ∘L
        ContinuousLinearMap.adjoint
          (suffixEulerFrameSchurStep lambda p []).oldFrame ∘L
        newSuffixFrame lambda []‖ ≤ 196 * q * ‖K‖
  have holdAdjoint :
      ‖ContinuousLinearMap.adjoint
          (suffixEulerFrameSchurStep lambda p []).oldFrame‖ ≤ 1 := by
    calc
      ‖ContinuousLinearMap.adjoint
          (suffixEulerFrameSchurStep lambda p []).oldFrame‖ =
          ‖(suffixEulerFrameSchurStep lambda p []).oldFrame‖ :=
        ContinuousLinearMap.adjoint.norm_map _
      _ ≤ 1 := hold
  have hqColumn : 0 ≤ q := ccm24PrimeEulerCoefficient_nonneg p
  have hC : 0 ≤ 196 * q * ‖K‖ := by
    exact mul_nonneg (mul_nonneg (by norm_num) hqColumn)
      (norm_nonneg K)
  calc
    ‖onePrimeBoundaryMoment owner lambda p ∘L
          ContinuousLinearMap.adjoint
            (suffixEulerFrameSchurStep lambda p []).oldFrame ∘L
          newSuffixFrame lambda []‖ ≤
        ‖onePrimeBoundaryMoment owner lambda p‖ *
        ‖ContinuousLinearMap.adjoint
            (suffixEulerFrameSchurStep lambda p []).oldFrame‖ *
          ‖newSuffixFrame lambda []‖ := by
      calc
        _ ≤ ‖onePrimeBoundaryMoment owner lambda p ∘L
              ContinuousLinearMap.adjoint
                (suffixEulerFrameSchurStep lambda p []).oldFrame‖ *
              ‖newSuffixFrame lambda []‖ :=
          ContinuousLinearMap.opNorm_comp_le
            (onePrimeBoundaryMoment owner lambda p ∘L
              ContinuousLinearMap.adjoint
                (suffixEulerFrameSchurStep lambda p []).oldFrame)
            (newSuffixFrame lambda [])
        _ ≤ (‖onePrimeBoundaryMoment owner lambda p‖ *
              ‖ContinuousLinearMap.adjoint
                (suffixEulerFrameSchurStep lambda p []).oldFrame‖) *
              ‖newSuffixFrame lambda []‖ := by
          exact mul_le_mul_of_nonneg_right
            (ContinuousLinearMap.opNorm_comp_le
              (onePrimeBoundaryMoment owner lambda p)
              (ContinuousLinearMap.adjoint
                (suffixEulerFrameSchurStep lambda p []).oldFrame))
            (norm_nonneg (newSuffixFrame lambda []))
    _ ≤ (196 * ccm24PrimeEulerCoefficient p *
          ‖detectorOperator owner‖) * 1 * 1 := by
      calc
        (‖onePrimeBoundaryMoment owner lambda p‖ *
            ‖ContinuousLinearMap.adjoint
              (suffixEulerFrameSchurStep lambda p []).oldFrame‖) *
            ‖newSuffixFrame lambda []‖ ≤
          (196 * q * ‖K‖ *
            ‖ContinuousLinearMap.adjoint
              (suffixEulerFrameSchurStep lambda p []).oldFrame‖) *
            ‖newSuffixFrame lambda []‖ := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hraw
              (norm_nonneg
                (ContinuousLinearMap.adjoint
                  (suffixEulerFrameSchurStep lambda p []).oldFrame)))
            (norm_nonneg (newSuffixFrame lambda []))
        _ ≤ (196 * q * ‖K‖ * 1) * ‖newSuffixFrame lambda []‖ := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left holdAdjoint hC)
            (norm_nonneg (newSuffixFrame lambda []))
        _ ≤ (196 * q * ‖K‖ * 1) * 1 := by
          exact mul_le_mul_of_nonneg_left hnew
            (by positivity)
    _ = 196 * ccm24PrimeEulerCoefficient p * ‖detectorOperator owner‖ := by
      ring

theorem tendsto_onePrimeBoundaryMomentColumn_norm_arithmeticVisiblePrimeSequence
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    Filter.Tendsto
      (fun n =>
        ‖onePrimeBoundaryMomentColumn owner lambda
          (arithmeticVisiblePrimeSequence n)‖)
      Filter.atTop (𝓝 0) := by
  have hcoeff :=
    tendsto_ccm24PrimeEulerCoefficient_arithmeticVisiblePrimeSequence
  have hupper : ∀ n,
      ‖onePrimeBoundaryMomentColumn owner lambda
          (arithmeticVisiblePrimeSequence n)‖ ≤
        196 * ccm24PrimeEulerCoefficient
          (arithmeticVisiblePrimeSequence n) *
          ‖detectorOperator owner‖ := by
    intro n
    exact norm_onePrimeBoundaryMomentColumn_le owner lambda
      (arithmeticVisiblePrimeSequence n)
      (arithmeticVisiblePrimeSequence_isPrime n)
  have hlimit : Filter.Tendsto
      (fun n =>
        196 * ccm24PrimeEulerCoefficient
          (arithmeticVisiblePrimeSequence n) *
          ‖detectorOperator owner‖)
      Filter.atTop (𝓝 0) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (hcoeff.const_mul (196 * ‖detectorOperator owner‖))
  exact squeeze_zero
    (fun n => norm_nonneg
      (onePrimeBoundaryMomentColumn owner lambda
        (arithmeticVisiblePrimeSequence n))) hupper hlimit

theorem not_exists_eventually_arithmeticPrime_column_norm_gt
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    ¬ ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ᶠ n in Filter.atTop,
        epsilon <
          ‖onePrimeBoundaryMomentColumn owner lambda
            (arithmeticVisiblePrimeSequence n)‖ := by
  intro hexists
  obtain ⟨epsilon, hepsilon, hcolumn⟩ := hexists
  have hlimit :=
    tendsto_onePrimeBoundaryMomentColumn_norm_arithmeticVisiblePrimeSequence
      owner lambda
  rcases (Metric.tendsto_atTop.1 hlimit) (epsilon / 2) (by positivity) with
    ⟨N, hN⟩
  have hsmall : ∀ᶠ n in Filter.atTop,
      ‖onePrimeBoundaryMomentColumn owner lambda
          (arithmeticVisiblePrimeSequence n)‖ < epsilon / 2 := by
    filter_upwards [Filter.eventually_ge_atTop N] with n hn
    have hdist := hN n hn
    simpa [Real.dist_eq,
      abs_of_nonneg (norm_nonneg
        (onePrimeBoundaryMomentColumn owner lambda
          (arithmeticVisiblePrimeSequence n)))] using hdist
  have hboth : ∀ᶠ n in Filter.atTop,
      epsilon < ‖onePrimeBoundaryMomentColumn owner lambda
          (arithmeticVisiblePrimeSequence n)‖ ∧
        ‖onePrimeBoundaryMomentColumn owner lambda
          (arithmeticVisiblePrimeSequence n)‖ < epsilon / 2 :=
    hcolumn.and hsmall
  obtain ⟨n, hn⟩ := hboth.exists
  linarith [hn.1, hn.2]

/-
/-! ## The one-prime Euler scale (legacy duplicate) -/

namespace Legacy

theorem norm_ccm24PrimeEulerContraction_le_legacy
    (p : CCM24VisiblePrime) :
    ‖ccm24PrimeEulerContraction p‖ ≤
      ccm24PrimeEulerCoefficient p := by
  rw [ccm24PrimeEulerContraction, norm_smul]
  calc
    ‖(ccm24PrimeEulerCoefficient p : ℂ)‖ *
          ‖(cc20GlobalLogTranslation (-Real.log p)).toContinuousLinearMap‖ ≤
        ‖(ccm24PrimeEulerCoefficient p : ℂ)‖ * 1 := by
      exact mul_le_mul_of_nonneg_left
        (cc20GlobalLogTranslation (-Real.log p)).norm_toContinuousLinearMap_le
        (norm_nonneg _)
    _ = ccm24PrimeEulerCoefficient p := by
      rw [mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (ccm24PrimeEulerCoefficient_nonneg p)]

theorem norm_parameterizedPrimeEulerInverse_le_four
    (alpha : ℝ) (p : CCM24VisiblePrime)
    (hα0 : 0 ≤ alpha) (hα1 : alpha ≤ 1) :
    ‖parameterizedPrimeEulerInverse alpha p‖ ≤ 4 := by
  let A := parameterizedPrimeEulerContraction alpha p
  have hA : ‖A‖ ≤ (3 / 4 : ℝ) := by
    dsimp [A, parameterizedPrimeEulerContraction]
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hα0]
    calc
      alpha * ‖ccm24PrimeEulerContraction p‖ ≤
          alpha * ccm24PrimeEulerCoefficient p := by
        exact mul_le_mul_of_nonneg_left
          (norm_ccm24PrimeEulerContraction_le p) hα0
      _ ≤ 3 / 4 := by
        exact mul_le_of_le_one_left
          (ccm24PrimeEulerCoefficient_le_three_quarters p)
          (by linarith)
  have hAlt : ‖A‖ < 1 := lt_of_le_of_lt hA (by norm_num)
  have hsummable : Summable (fun n : ℕ => A ^ n) :=
    summable_geometric_of_norm_lt_one hAlt
  calc
    ‖parameterizedPrimeEulerInverse alpha p‖ =
        ‖∑' n : ℕ, A ^ n‖ := by
      rfl
    _ ≤ ∑' n : ℕ, ‖A ^ n‖ := norm_tsum_le_tsum_norm hsummable
    _ = ∑' n : ℕ, ‖A‖ ^ n := by
      apply tsum_congr
      intro n
      rw [norm_pow]
    _ = (1 - ‖A‖)⁻¹ := by
      exact tsum_geometric_of_norm_lt_one hAlt
    _ ≤ 4 := by
      have hdenom : 0 < 1 - ‖A‖ := sub_pos.mpr hAlt
      apply (inv_le_iff₀ hdenom).2
      nlinarith [hA]

theorem norm_parameterizedPrimeEulerGenerator_le_four_mul_coefficient
    (alpha : ℝ) (p : CCM24VisiblePrime)
    (hα0 : 0 ≤ alpha) (hα1 : alpha ≤ 1) :
    ‖parameterizedPrimeEulerGenerator alpha p‖ ≤
      4 * ccm24PrimeEulerCoefficient p := by
  unfold parameterizedPrimeEulerGenerator
  calc
    ‖-ccm24PrimeEulerContraction p *
        parameterizedPrimeEulerInverse alpha p‖ ≤
      ‖ccm24PrimeEulerContraction p‖ *
        ‖parameterizedPrimeEulerInverse alpha p‖ := by
      simpa only [norm_neg] using
        (ContinuousLinearMap.opNorm_comp_le
          (ccm24PrimeEulerContraction p)
          (parameterizedPrimeEulerInverse alpha p))
    _ ≤ ccm24PrimeEulerCoefficient p * 4 := by
      exact mul_le_mul
        (norm_ccm24PrimeEulerContraction_le p)
        (norm_parameterizedPrimeEulerInverse_le_four alpha p hα0 hα1)
        (norm_nonneg _) (ccm24PrimeEulerCoefficient_nonneg p)
    _ = 4 * ccm24PrimeEulerCoefficient p := by ring

/-! ## The moving projection estimate -/

theorem norm_orthogonalProjectionDerivative_le_two_mul
    (P X : finiteSCarrier →L[ℂ] finiteSCarrier)
    (hP : IsStarProjection P) :
    ‖orthogonalProjectionDerivative P X‖ ≤ 2 * ‖X‖ := by
  rw [orthogonalProjectionDerivative_eq_twoCrossings P X hP.isSelfAdjoint]
  have hPnorm : ‖P‖ ≤ (1 : ℝ) := IsStarProjection.norm_le _ hP
  have hPcomp : ‖ContinuousLinearMap.id ℂ finiteSCarrier - P‖ ≤
      (1 : ℝ) := by
    exact IsStarProjection.norm_le _ hP.one_sub
  calc
    ‖(ContinuousLinearMap.id ℂ finiteSCarrier - P) * X * P +
        P * ContinuousLinearMap.adjoint X *
          (ContinuousLinearMap.id ℂ finiteSCarrier - P)‖ ≤
      ‖(ContinuousLinearMap.id ℂ finiteSCarrier - P) * X * P‖ +
        ‖P * ContinuousLinearMap.adjoint X *
          (ContinuousLinearMap.id ℂ finiteSCarrier - P)‖ := norm_add_le _ _
    _ ≤ (‖ContinuousLinearMap.id ℂ finiteSCarrier - P‖ * ‖X‖ * ‖P‖) +
        (‖P‖ * ‖ContinuousLinearMap.adjoint X‖ *
          ‖ContinuousLinearMap.id ℂ finiteSCarrier - P‖) := by
      gcongr
      · exact ContinuousLinearMap.opNorm_comp_le _ _
      · rw [ContinuousLinearMap.adjoint.norm_map]
        exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 2 * ‖X‖ := by
      rw [ContinuousLinearMap.adjoint.norm_map]
      nlinarith [norm_nonneg X, hPnorm, hPcomp]

theorem norm_parameterizedCanonicalGramProjection_derivative_le_eight_mul_coefficient
    (lambda : CCM24SoninScale) (alpha : ℝ) (p : CCM24VisiblePrime)
    (hα0 : 0 ≤ alpha) (hα1 : alpha ≤ 1) :
    ‖parameterizedCanonicalGramProjectionDerivative lambda alpha [p]‖ ≤
      8 * ccm24PrimeEulerCoefficient p := by
  rw [parameterizedCanonicalGramProjectionDerivative_eq_orthogonalFlow
    lambda alpha [p] (by
      rw [abs_of_nonneg hα0]
      exact hα1)]
  calc
    ‖orthogonalProjectionDerivative
        (parameterizedCanonicalGramProjection lambda alpha [p])
        (parameterizedFiniteEulerGenerator alpha [p])‖ ≤
      2 * ‖parameterizedFiniteEulerGenerator alpha [p]‖ :=
        norm_orthogonalProjectionDerivative_le_two_mul _ _
          (parameterizedCanonicalGramProjection_isStarProjection
            lambda alpha [p] (by
              rw [abs_of_nonneg hα0]
              exact hα1))
    _ ≤ 2 * (4 * ccm24PrimeEulerCoefficient p) := by
      gcongr
      simpa only [parameterizedFiniteEulerGenerator_cons,
        parameterizedFiniteEulerGenerator_nil, add_zero] using
        norm_parameterizedPrimeEulerGenerator_le_four_mul_coefficient
          alpha p hα0 hα1
    _ = 8 * ccm24PrimeEulerCoefficient p := by ring

theorem norm_parameterizedCanonicalGramProjection_one_sub_zero_le_eight_mul_coefficient
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) :
    ‖parameterizedCanonicalGramProjection lambda 1 [p] -
        parameterizedCanonicalGramProjection lambda 0 [p]‖ ≤
      8 * ccm24PrimeEulerCoefficient p := by
  let f : ℝ → finiteSCarrier →L[ℂ] finiteSCarrier :=
    fun alpha => parameterizedCanonicalGramProjection lambda alpha [p]
  let f' : ℝ → finiteSCarrier →L[ℂ] finiteSCarrier := fun alpha =>
    if h : |alpha| ≤ 1 then
      parameterizedCanonicalGramProjectionDerivative lambda alpha [p] h
    else
      (0 : finiteSCarrier →L[ℂ] finiteSCarrier)
  have hderiv : ∀ alpha ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt f (f' alpha)
        (Set.Icc (0 : ℝ) 1) alpha := by
    intro alpha hα
    have halpha : |alpha| ≤ 1 := by
      rw [abs_of_nonneg (by linarith [hα.1])]
      exact hα.2
    simp only [f', dif_pos halpha]
    exact (hasDerivAt_parameterizedCanonicalGramProjection
      lambda alpha [p] halpha).hasDerivWithinAt
  have hbound : ∀ alpha ∈ Set.Ico (0 : ℝ) 1,
      ‖f' alpha‖ ≤
        8 * ccm24PrimeEulerCoefficient p := by
    intro alpha hα
    have halpha : |alpha| ≤ 1 := by
      rw [abs_of_nonneg (by linarith [hα.1])]
      exact le_of_lt hα.2
    simp only [f', dif_pos halpha]
    exact norm_parameterizedCanonicalGramProjection_derivative_le_eight_mul_coefficient
      lambda alpha p hα.1 hα.2.le
  have hpath := norm_image_sub_le_of_norm_deriv_le_segment'
    (a := (0 : ℝ)) (b := 1) hderiv hbound
      (1 : ℝ) (by norm_num)
  simpa only [f, sub_zero, mul_one] using hpath

end Legacy
-/

end CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierMomentDecay
end CCM25Concrete
end Source
end ConnesWeilRH
