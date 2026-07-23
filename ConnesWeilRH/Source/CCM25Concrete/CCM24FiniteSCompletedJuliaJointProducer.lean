/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaUniformCoDefectFactor

/-!
# Reverse recovery and the joint producer boundary

Proof 511 records the exact reverse direction left open by Proof 510.  A
co-defect factor controls the local two-sided mismatch, while the one-sided
intertwining defect is recovered through the scalar-normalized forward Euler
transition.  Consequently the recovered physical bound carries the factor

```text
||(primeSchurMarkovScalar p)^(-1) * transition(p,S)||.
```

This is a genuine quantitative reverse theorem, not a contraction claim.  The
general uniform-transition contract is exposed explicitly, and the later
elementary bound section supplies the concrete family bound `8`.  No
co-defect producer, Gate 3U estimate, finite-S sign, Burnol identity, or RH
premise is asserted here.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedJuliaJointProducer

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCompletedJuliaAmbientDefectFactorization
open CCM24FiniteSCompletedJuliaMismatchFactorization
open CCM24FiniteSCompletedJuliaNonpolarMismatchNormalForm
open CCM24FiniteSCompletedJuliaUniformRawReadout
open CCM24FiniteSCompletedJuliaUniformCoDefectFactor
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSJuliaBessel
open CCM24FiniteSJuliaCoDefect
open CCM24FiniteSProjectionTrace
open CCM24FiniteSSchurMarkovPairing

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! ## One-step reverse recovery -/

/-- The scalar-normalized forward transition appearing in the exact recovery
of the one-sided intertwining defect. -/
noncomputable def suffixMismatchScaledForwardTransition
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
  (primeSchurMarkovScalar p : ℂ)⁻¹ •
    suffixEulerFrameTransition lambda p S

@[simp]
theorem suffixMismatchScaledForwardTransition_apply
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (x : sourceSoninCarrier lambda) :
    suffixMismatchScaledForwardTransition lambda p S x =
      (primeSchurMarkovScalar p : ℂ)⁻¹ •
        suffixEulerFrameTransition lambda p S x := by
  rfl

/-- The co-defect factor gives the local adjoint factorization needed by the
reverse readback. -/
theorem coDefectFactor_adjoint_factorization
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {bound : ℝ}
    (data : SuffixMismatchCoDefectFactorData owner lambda p S bound) :
    (suffixActualBandLocalRoutePolarRawMismatchDefect owner lambda p S)† =
      (ContinuousLinearMap.adjoint data.rightFactor) ∘L
        (suffixEulerFrameSchurStep lambda p S).leftCoDefect := by
  have hadjoint := congrArg ContinuousLinearMap.adjoint data.factorization
  have hself : IsSelfAdjoint
      (suffixEulerFrameSchurStep lambda p S).leftCoDefect := by
    simpa only [RectangularSchurCoDefectStepData.leftCoDefect] using
      (canonicalJuliaDefect_isSelfAdjoint
        (ContinuousLinearMap.adjoint
          (suffixEulerFrameSchurStep lambda p S).transition)
        (suffixEulerFrameSchurStep lambda p S).transitionAdjointContract)
  simpa only [ContinuousLinearMap.adjoint_comp, hself.adjoint_eq] using hadjoint

set_option maxHeartbeats 4000000 in
-- The adjoint norm-square calculation needs the larger local heartbeat budget.
/-- Every local co-defect factor recovers a one-sided Douglas estimate.  The
bound is deliberately multiplied by the norm of the scalar-normalized
forward transition. -/
theorem coDefectFactor_toAdjointDouglasDomination
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {bound : ℝ}
    (data : SuffixMismatchCoDefectFactorData owner lambda p S bound) :
    SuffixMismatchAdjointDouglasDomination owner lambda p S
      (‖suffixMismatchScaledForwardTransition lambda p S‖ * bound) := by
  have hbound : 0 ≤ bound := by
    exact le_trans (norm_nonneg data.rightFactor) data.rightFactor_norm_le
  have hscaled : 0 ≤ ‖suffixMismatchScaledForwardTransition lambda p S‖ :=
    norm_nonneg (suffixMismatchScaledForwardTransition lambda p S)
  refine ⟨mul_nonneg hscaled hbound, ?_⟩
  intro x
  have hlocal :=
    coDefectFactor_adjoint_factorization data
  have hintertwining :=
    suffixActualBandRoutePolarRawMismatchIntertwiningDefect_adjoint_eq
      owner lambda p S
  have hright :
      ‖(ContinuousLinearMap.adjoint data.rightFactor)
          ((suffixEulerFrameSchurStep lambda p S).leftCoDefect x)‖ ≤
        bound *
          ‖(suffixEulerFrameSchurStep lambda p S).leftCoDefect x‖ := by
    calc
      ‖(ContinuousLinearMap.adjoint data.rightFactor)
          ((suffixEulerFrameSchurStep lambda p S).leftCoDefect x)‖ ≤
          ‖ContinuousLinearMap.adjoint data.rightFactor‖ *
            ‖(suffixEulerFrameSchurStep lambda p S).leftCoDefect x‖ :=
        (ContinuousLinearMap.adjoint data.rightFactor).le_opNorm _
      _ = ‖data.rightFactor‖ *
            ‖(suffixEulerFrameSchurStep lambda p S).leftCoDefect x‖ := by
        rw [show ‖ContinuousLinearMap.adjoint data.rightFactor‖ =
            ‖data.rightFactor‖ by
          exact ContinuousLinearMap.adjoint.norm_map _]
      _ ≤ bound *
            ‖(suffixEulerFrameSchurStep lambda p S).leftCoDefect x‖ := by
        exact mul_le_mul_of_nonneg_right data.rightFactor_norm_le
          (norm_nonneg _)
  have htransition :
      ‖ContinuousLinearMap.adjoint
          (suffixMismatchScaledForwardTransition lambda p S)
          ((ContinuousLinearMap.adjoint data.rightFactor)
            ((suffixEulerFrameSchurStep lambda p S).leftCoDefect x))‖ ≤
        ‖suffixMismatchScaledForwardTransition lambda p S‖ *
          ‖(ContinuousLinearMap.adjoint data.rightFactor)
            ((suffixEulerFrameSchurStep lambda p S).leftCoDefect x)‖ :=
    calc
      _ ≤ ‖ContinuousLinearMap.adjoint
          (suffixMismatchScaledForwardTransition lambda p S)‖ *
          ‖(ContinuousLinearMap.adjoint data.rightFactor)
            ((suffixEulerFrameSchurStep lambda p S).leftCoDefect x)‖ :=
        (ContinuousLinearMap.adjoint
          (suffixMismatchScaledForwardTransition lambda p S)).le_opNorm _
      _ = _ := by
        rw [show ‖ContinuousLinearMap.adjoint
            (suffixMismatchScaledForwardTransition lambda p S)‖ =
              ‖suffixMismatchScaledForwardTransition lambda p S‖ by
          exact ContinuousLinearMap.adjoint.norm_map _]
  have hnorm :
      ‖((suffixActualBandRoutePolarRawMismatchIntertwiningDefect
          owner lambda p S)†) x‖ ≤
        (‖suffixMismatchScaledForwardTransition lambda p S‖ * bound) *
          ‖(suffixEulerFrameSchurStep lambda p S).leftCoDefect x‖ := by
    rw [hintertwining]
    simp only [ContinuousLinearMap.comp_apply]
    rw [hlocal]
    calc
      ‖ContinuousLinearMap.adjoint
          (suffixMismatchScaledForwardTransition lambda p S)
          ((ContinuousLinearMap.adjoint data.rightFactor)
            ((suffixEulerFrameSchurStep lambda p S).leftCoDefect x))‖ ≤
          ‖suffixMismatchScaledForwardTransition lambda p S‖ *
            ‖(ContinuousLinearMap.adjoint data.rightFactor)
              ((suffixEulerFrameSchurStep lambda p S).leftCoDefect x)‖ :=
        htransition
      _ ≤ ‖suffixMismatchScaledForwardTransition lambda p S‖ *
          (bound *
            ‖(suffixEulerFrameSchurStep lambda p S).leftCoDefect x‖) := by
        exact mul_le_mul_of_nonneg_left hright hscaled
      _ = (‖suffixMismatchScaledForwardTransition lambda p S‖ * bound) *
          ‖(suffixEulerFrameSchurStep lambda p S).leftCoDefect x‖ := by
        ring
  have hsquare := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg
    (mul_nonneg hscaled hbound) (norm_nonneg _))).mpr hnorm
  simpa only [mul_pow] using hsquare

set_option maxHeartbeats 4000000 in
-- The two-channel norm-square calculation needs the larger local heartbeat budget.
/-- The reverse estimate can be handed back to the physical two-channel
owner, but only with its pair-dependent transition factor. -/
theorem coDefectFactor_toAmbientBoundaryDomination
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {bound : ℝ}
    (data : SuffixMismatchCoDefectFactorData owner lambda p S bound) :
    SuffixMismatchAmbientBoundaryDomination owner lambda p S
      (‖suffixMismatchScaledForwardTransition lambda p S‖ * bound) := by
  apply (suffixMismatchAmbientBoundaryDomination_iff_douglas
    owner lambda p S _).mpr
  exact
    coDefectFactor_toAdjointDouglasDomination data

/-! ## The exact uniformity contract -/

/-- An explicit bound for the scalar-normalized forward transitions.  This is
the additional source theorem required to turn a co-defect factor family back
into one uniform physical domination family. -/
structure SuffixMismatchUniformScaledForwardTransitionBoundData
    (lambda : CCM24SoninScale) (transitionBound : ℝ) where
  transitionBound_nonneg : 0 ≤ transitionBound
  transition_norm_le : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
    ‖suffixMismatchScaledForwardTransition lambda p S‖ ≤ transitionBound

/-! ## Proof 512: the transition bound is elementary, but not contractive -/

/-- Every visible place satisfies `p >= 2`, so its critical-line Euler
coefficient is at most `3/4`. -/
theorem ccm24PrimeEulerCoefficient_le_three_quarters
    (p : CCM24VisiblePrime) :
    ccm24PrimeEulerCoefficient p ≤ (3 / 4 : ℝ) := by
  unfold ccm24PrimeEulerCoefficient
  have hpNat : 2 ≤ p.1 := by
    omega
  have hp : (2 : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast hpNat
  have hsqrt : (4 / 3 : ℝ) < Real.sqrt (p : ℝ) := by
    apply (Real.lt_sqrt (by norm_num)).2
    nlinarith [hp]
  have hsqrtPos : 0 < Real.sqrt (p : ℝ) := by
    exact lt_trans (by norm_num) hsqrt
  apply (div_le_iff₀ hsqrtPos).2
  nlinarith [hsqrt]

/-- The Schur--Markov scalar is uniformly bounded away from zero. -/
theorem primeSchurMarkovScalar_ge_one_eighth
    (p : CCM24VisiblePrime) :
    (1 / 8 : ℝ) ≤ primeSchurMarkovScalar p := by
  rw [primeSchurMarkovScalar]
  have hcoeff := ccm24PrimeEulerCoefficient_le_three_quarters p
  have hdenom : 0 < 1 + ccm24PrimeEulerCoefficient p :=
    add_pos_of_pos_of_nonneg zero_lt_one
      (ccm24PrimeEulerCoefficient_nonneg p)
  apply (le_div_iff₀ hdenom).2
  nlinarith [hcoeff]

/-- The scalar-normalized forward transition has a genuine uniform finite
bound.  The bound is `8`, not `1`; the reverse transition is the contraction,
while scalar-normalized forward recovery pays the inverse Schur--Markov scalar.
-/
theorem suffixMismatchScaledForwardTransition_norm_le_eight
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    ‖suffixMismatchScaledForwardTransition lambda p S‖ ≤ 8 := by
  rw [suffixMismatchScaledForwardTransition]
  have hscalar := primeSchurMarkovScalar_ge_one_eighth p
  have hscalarPos := primeSchurMarkovScalar_pos p
  have hscalarNorm :
      ‖((primeSchurMarkovScalar p : ℂ)⁻¹)‖ =
        (primeSchurMarkovScalar p)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hscalarPos]
  have hinv : (primeSchurMarkovScalar p)⁻¹ ≤ (8 : ℝ) := by
    have hinvNonneg : 0 ≤ (primeSchurMarkovScalar p)⁻¹ :=
      le_of_lt (inv_pos.mpr hscalarPos)
    have hmul : primeSchurMarkovScalar p *
        (primeSchurMarkovScalar p)⁻¹ = 1 := by
      exact mul_inv_cancel₀ (ne_of_gt hscalarPos)
    nlinarith
  calc
    ‖((primeSchurMarkovScalar p : ℂ)⁻¹) •
        suffixEulerFrameTransition lambda p S‖ ≤
      ‖((primeSchurMarkovScalar p : ℂ)⁻¹)‖ *
        ‖suffixEulerFrameTransition lambda p S‖ := by
      exact ContinuousLinearMap.opNorm_smul_le _ _
    _ = (primeSchurMarkovScalar p)⁻¹ *
        ‖suffixEulerFrameTransition lambda p S‖ := by
      rw [hscalarNorm]
    _ ≤ (primeSchurMarkovScalar p)⁻¹ * 1 := by
        exact mul_le_mul_of_nonneg_left
          (suffixEulerFrameTransition_norm_le_one lambda p S)
          (le_of_lt (inv_pos.mpr hscalarPos))
    _ ≤ 8 * 1 := by
      exact mul_le_mul_of_nonneg_right hinv zero_le_one
    _ = 8 := by norm_num

/-- Canonical family witness for the elementary transition bound. -/
noncomputable def canonicalUniformScaledForwardTransitionBoundData
    (lambda : CCM24SoninScale) :
    SuffixMismatchUniformScaledForwardTransitionBoundData lambda 8 :=
  { transitionBound_nonneg := by norm_num
    transition_norm_le := fun p S =>
      suffixMismatchScaledForwardTransition_norm_le_eight lambda p S }

set_option maxHeartbeats 4000000 in
-- The family-level norm-square calculation needs the larger local heartbeat budget.
/-- Under an explicit uniform transition bound, a uniform co-defect factor
family does recover a uniform physical domination family. -/
theorem SuffixMismatchAmbientBoundaryUniformCoDefectFactorData.toUniformDomination
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {bound transitionBound : ℝ}
    (data : SuffixMismatchAmbientBoundaryUniformCoDefectFactorData
      owner lambda bound)
    (transitionData :
      SuffixMismatchUniformScaledForwardTransitionBoundData
        lambda transitionBound) :
    SuffixMismatchAmbientBoundaryUniformDominationData owner lambda
      (transitionBound * bound) := by
  refine
    { bound_nonneg := mul_nonneg transitionData.transitionBound_nonneg
        data.bound_nonneg
      domination := fun p S => ?_ }
  apply (suffixMismatchAmbientBoundaryDomination_iff_douglas
    owner lambda p S _).mpr
  have hfactor := data.factor p S
  refine ⟨mul_nonneg
      (transitionData.transitionBound_nonneg) data.bound_nonneg, ?_⟩
  intro x
  have hlocal :=
    coDefectFactor_adjoint_factorization hfactor
  have hintertwining :=
    suffixActualBandRoutePolarRawMismatchIntertwiningDefect_adjoint_eq
      owner lambda p S
  have hscaled := transitionData.transition_norm_le p S
  have hbound := hfactor.rightFactor_norm_le
  have hpoint :
      ‖((suffixActualBandRoutePolarRawMismatchIntertwiningDefect
          owner lambda p S)†) x‖ ≤
        (transitionBound * bound) *
          ‖(suffixEulerFrameSchurStep lambda p S).leftCoDefect x‖ := by
    rw [hintertwining]
    simp only [ContinuousLinearMap.comp_apply]
    rw [hlocal]
    calc
      ‖ContinuousLinearMap.adjoint
          (suffixMismatchScaledForwardTransition lambda p S)
          ((ContinuousLinearMap.adjoint hfactor.rightFactor)
            ((suffixEulerFrameSchurStep lambda p S).leftCoDefect x))‖ ≤
          ‖ContinuousLinearMap.adjoint
              (suffixMismatchScaledForwardTransition lambda p S)‖ *
            ‖(ContinuousLinearMap.adjoint hfactor.rightFactor)
              ((suffixEulerFrameSchurStep lambda p S).leftCoDefect x)‖ :=
        (ContinuousLinearMap.adjoint
          (suffixMismatchScaledForwardTransition lambda p S)).le_opNorm _
      _ = ‖suffixMismatchScaledForwardTransition lambda p S‖ *
            ‖(ContinuousLinearMap.adjoint hfactor.rightFactor)
              ((suffixEulerFrameSchurStep lambda p S).leftCoDefect x)‖ := by
        rw [show ‖ContinuousLinearMap.adjoint
            (suffixMismatchScaledForwardTransition lambda p S)‖ =
              ‖suffixMismatchScaledForwardTransition lambda p S‖ by
          exact ContinuousLinearMap.adjoint.norm_map _]
      _ ≤ ‖suffixMismatchScaledForwardTransition lambda p S‖ *
          (bound *
            ‖(suffixEulerFrameSchurStep lambda p S).leftCoDefect x‖) := by
        have hright := (ContinuousLinearMap.adjoint hfactor.rightFactor).le_opNorm
          ((suffixEulerFrameSchurStep lambda p S).leftCoDefect x)
        rw [show ‖ContinuousLinearMap.adjoint hfactor.rightFactor‖ =
            ‖hfactor.rightFactor‖ by
          exact ContinuousLinearMap.adjoint.norm_map _] at hright
        exact mul_le_mul_of_nonneg_left
          (le_trans hright
            (mul_le_mul_of_nonneg_right hbound (norm_nonneg _)))
          (norm_nonneg (suffixMismatchScaledForwardTransition lambda p S))
      _ ≤ transitionBound *
          (bound *
            ‖(suffixEulerFrameSchurStep lambda p S).leftCoDefect x‖) := by
        exact mul_le_mul_of_nonneg_right hscaled
          (mul_nonneg data.bound_nonneg (norm_nonneg _))
      _ = (transitionBound * bound) *
          ‖(suffixEulerFrameSchurStep lambda p S).leftCoDefect x‖ := by
        ring
  have hsquare := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg
    (mul_nonneg transitionData.transitionBound_nonneg data.bound_nonneg)
    (norm_nonneg _))).mpr hpoint
  simpa only [mul_pow] using hsquare

theorem SuffixMismatchAmbientBoundaryUniformCoDefectFactorData.toUniformDomination_eight
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {bound : ℝ}
    (data : SuffixMismatchAmbientBoundaryUniformCoDefectFactorData
      owner lambda bound) :
    SuffixMismatchAmbientBoundaryUniformDominationData owner lambda
      (8 * bound) := by
  exact SuffixMismatchAmbientBoundaryUniformCoDefectFactorData.toUniformDomination data
    (canonicalUniformScaledForwardTransitionBoundData lambda)

end CCM24FiniteSCompletedJuliaJointProducer
end CCM25Concrete
end Source
end ConnesWeilRH
