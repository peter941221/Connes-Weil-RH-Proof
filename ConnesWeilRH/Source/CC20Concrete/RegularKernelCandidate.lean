/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.SineIntegral

/-!
# Archimedean scalar candidate for the CC20 regular remainder

This module deliberately stops before defining a source owner.  It records the
ordinary scalar profile obtained after removing the Dirac part of `Q delta`.
The operator action, measurability on the two-variable kernel, and
square-integrability remain separate obligations.
-/

namespace ConnesWeilRH
namespace Source
namespace CC20Concrete

open Filter
open scoped Topology

/-- The continuous quotient profile `Si(x)/x`, including its value at zero. -/
noncomputable def siQuotientProfile (x : ℝ) : ℝ := sineIntegralQuotient x

/--
The ordinary scalar profile of the CC20 scaling remainder before applying the
quantized differential `Q`.  Writing it through `siQuotientProfile` removes
the apparent singularities at `rho = 1` from the definition.
-/
noncomputable def cc20DeltaRegular (rho : ℝ) : ℝ :=
  2 * Real.sqrt rho *
    (siQuotientProfile (2 * Real.pi * (1 + rho)) +
      siQuotientProfile (2 * Real.pi * (rho - 1)))

noncomputable def siQuotientDerivativeProfile (x : ℝ) : ℝ :=
  (Real.sinc x * x - sineIntegral x) / x ^ 2

noncomputable def cc20DeltaBranchSum (rho : ℝ) : ℝ :=
  siQuotientProfile (2 * Real.pi * (1 + rho)) +
    siQuotientProfile (2 * Real.pi * (rho - 1))

noncomputable def cc20DeltaBranchSumDerivative (rho : ℝ) : ℝ :=
  2 * Real.pi * siQuotientDerivativeProfile (2 * Real.pi * (1 + rho)) +
    2 * Real.pi * siQuotientDerivativeProfile (2 * Real.pi * (rho - 1))

noncomputable def cc20DeltaBranchSumSecondDerivative (rho : ℝ) : ℝ :=
  (2 * Real.pi) ^ 2 * sineIntegralQuotientSecondDerivativeProfile
      (2 * Real.pi * (1 + rho)) +
    (2 * Real.pi) ^ 2 * sineIntegralQuotientSecondDerivativeProfile
      (2 * Real.pi * (rho - 1))

noncomputable def cc20DeltaRegularDerivative (rho : ℝ) : ℝ :=
  (2 * (1 / (2 * Real.sqrt rho))) *
      (siQuotientProfile (2 * Real.pi * (1 + rho)) +
        siQuotientProfile (2 * Real.pi * (rho - 1))) +
    (2 * Real.sqrt rho) *
      (2 * Real.pi * siQuotientDerivativeProfile (2 * Real.pi * (1 + rho)) +
        2 * Real.pi * siQuotientDerivativeProfile (2 * Real.pi * (rho - 1)))

noncomputable def cc20DeltaRegularSecondDerivative (rho : ℝ) : ℝ :=
  2 * Real.sqrt rho *
      ((2 * Real.pi) ^ 2 * sineIntegralQuotientSecondDerivativeProfile
          (2 * Real.pi * (1 + rho)) +
        (2 * Real.pi) ^ 2 * sineIntegralQuotientSecondDerivativeProfile
          (2 * Real.pi * (rho - 1))) +
    (2 / Real.sqrt rho) *
      (2 * Real.pi * siQuotientDerivativeProfile (2 * Real.pi * (1 + rho)) +
        2 * Real.pi * siQuotientDerivativeProfile (2 * Real.pi * (rho - 1))) -
    (1 / (2 * rho * Real.sqrt rho)) *
      (siQuotientProfile (2 * Real.pi * (1 + rho)) +
        siQuotientProfile (2 * Real.pi * (rho - 1)))

/-- Continuous repair of the second-derivative formula at both affine branch
arguments. It agrees with `cc20DeltaRegularSecondDerivative` away from
`rho = -1, 1`. -/
noncomputable def cc20DeltaRegularSecondDerivativeExtension (rho : ℝ) : ℝ :=
  2 * Real.sqrt rho *
      ((2 * Real.pi) ^ 2 * sineIntegralQuotientSecondDerivativeExtension
          (2 * Real.pi * (1 + rho)) +
        (2 * Real.pi) ^ 2 * sineIntegralQuotientSecondDerivativeExtension
          (2 * Real.pi * (rho - 1))) +
    (2 / Real.sqrt rho) *
      (2 * Real.pi * siQuotientDerivativeProfile (2 * Real.pi * (1 + rho)) +
        2 * Real.pi * siQuotientDerivativeProfile (2 * Real.pi * (rho - 1))) -
    (1 / (2 * rho * Real.sqrt rho)) *
      (siQuotientProfile (2 * Real.pi * (1 + rho)) +
        siQuotientProfile (2 * Real.pi * (rho - 1)))

/-- Explicit algebraic candidate for `Q(delta)` on the non-diagonal region
`rho > 1`.  Its equality with the differential operator and its kernel action
are separate theorems, intentionally not fields of this definition. -/
noncomputable def cc20QDeltaRegularCandidate (rho : ℝ) : ℝ :=
  -(rho * cc20DeltaRegularDerivative rho + rho ^ 2 *
      cc20DeltaRegularSecondDerivative rho) + cc20DeltaRegular rho / 4

/-- Continuous-at-the-diagonal version of the ordinary Q-delta scalar. -/
noncomputable def cc20QDeltaRegularContinuousCandidate (rho : ℝ) : ℝ :=
  -(rho * cc20DeltaRegularDerivative rho + rho ^ 2 *
      cc20DeltaRegularSecondDerivativeExtension rho) + cc20DeltaRegular rho / 4

/-- The multiplicative-coordinate differential operator
`-(rho*d/drho)^2 + 1/4` on an ordinary twice-differentiable profile. -/
noncomputable def multiplicativeQ (f : ℝ → ℝ) (rho : ℝ) : ℝ :=
  -(rho * deriv f rho + rho ^ 2 * deriv (deriv f) rho) + f rho / 4

@[fun_prop, continuity]
theorem continuous_siQuotientProfile : Continuous siQuotientProfile :=
  continuous_sineIntegralQuotient

@[fun_prop, continuity]
theorem continuous_siQuotientDerivativeProfile :
    Continuous siQuotientDerivativeProfile := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · subst x
    simpa [siQuotientDerivativeProfile] using
      hasDerivAt_siQuotientDerivativeProfile_zero.continuousAt
  · unfold siQuotientDerivativeProfile
    exact (((Real.continuous_sinc.continuousAt.mul continuousAt_id).sub
      continuous_sineIntegral.continuousAt).div (continuousAt_id.pow 2)
        (pow_ne_zero 2 hx))

theorem continuousAt_cc20QDeltaRegularContinuousCandidate_one :
    ContinuousAt cc20QDeltaRegularContinuousCandidate 1 := by
  unfold cc20QDeltaRegularContinuousCandidate cc20DeltaRegularDerivative
    cc20DeltaRegularSecondDerivativeExtension cc20DeltaRegular
  have hsqrt : ContinuousAt Real.sqrt (1 : ℝ) := Real.continuous_sqrt.continuousAt
  have hsqrtNe : Real.sqrt (1 : ℝ) ≠ 0 := by norm_num
  fun_prop (disch := aesop)

set_option maxHeartbeats 800000 in
-- The expanded rational Q-delta expression needs a larger normalization budget.
theorem continuousAt_cc20QDeltaRegularCandidate_of_one_lt {rho : ℝ}
    (hrho : 1 < rho) : ContinuousAt cc20QDeltaRegularCandidate rho := by
  unfold cc20QDeltaRegularCandidate cc20DeltaRegularDerivative
    cc20DeltaRegularSecondDerivative cc20DeltaRegular
  have hrhoPos : 0 < rho := lt_trans zero_lt_one hrho
  have hminus : 2 * Real.pi * (rho - 1) ≠ 0 := by positivity
  have hplus : 2 * Real.pi * (1 + rho) ≠ 0 := by positivity
  have hsqrt : Real.sqrt rho ≠ 0 := Real.sqrt_ne_zero'.mpr hrhoPos
  fun_prop (disch := aesop)

theorem cc20DeltaRegularSecondDerivativeExtension_eq
    {rho : ℝ} (hminus : rho ≠ 1) (hplus : rho ≠ -1) :
    cc20DeltaRegularSecondDerivativeExtension rho =
      cc20DeltaRegularSecondDerivative rho := by
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hminusArg : 2 * Real.pi * (rho - 1) ≠ 0 :=
    mul_ne_zero hpi (sub_ne_zero.mpr hminus)
  have hplusArg : 2 * Real.pi * (1 + rho) ≠ 0 := by
    apply mul_ne_zero hpi
    intro h
    apply hplus
    linarith
  simp [cc20DeltaRegularSecondDerivativeExtension,
    cc20DeltaRegularSecondDerivative,
    sineIntegralQuotientSecondDerivativeExtension_of_ne_zero hminusArg,
    sineIntegralQuotientSecondDerivativeExtension_of_ne_zero hplusArg]

theorem cc20QDeltaRegularContinuousCandidate_eq
    {rho : ℝ} (hminus : rho ≠ 1) (hplus : rho ≠ -1) :
    cc20QDeltaRegularContinuousCandidate rho = cc20QDeltaRegularCandidate rho := by
  rw [cc20QDeltaRegularContinuousCandidate, cc20QDeltaRegularCandidate,
    cc20DeltaRegularSecondDerivativeExtension_eq hminus hplus]

theorem cc20QDeltaRegularContinuousCandidate_one :
    cc20QDeltaRegularContinuousCandidate 1 =
      8 * Real.pi ^ 2 / 9 + sineIntegralQuotient (4 * Real.pi) - 1 / 2 := by
  unfold cc20QDeltaRegularContinuousCandidate cc20DeltaRegularDerivative
    cc20DeltaRegularSecondDerivativeExtension cc20DeltaRegular
    siQuotientProfile siQuotientDerivativeProfile
  have hs4 : Real.sin (4 * Real.pi) = 0 := by
    convert Real.sin_nat_mul_pi 4 using 1 <;> norm_num
  have hc4 : Real.cos (4 * Real.pi) = 1 := by
    convert Real.cos_nat_mul_pi 4 using 1 <;> norm_num
  have hsinc4 : Real.sinc (4 * Real.pi) = 0 := by
    rw [Real.sinc_of_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)]
    rw [show (4 : ℝ) * Real.pi = (4 : ℕ) * Real.pi by norm_num,
      Real.sin_nat_mul_pi]
    simp
  have hS4 : sineIntegralQuotientSecondDerivativeProfile (4 * Real.pi) =
      (2 * Real.pi + sineIntegral (4 * Real.pi)) / (32 * Real.pi ^ 3) := by
    unfold sineIntegralQuotientSecondDerivativeProfile
    rw [hsinc4, hs4, hc4]
    field_simp [Real.pi_ne_zero]
    ring
  have hsinc4' : Real.sinc (Real.pi * 4) = 0 := by
    simpa [mul_comm] using hsinc4
  have hS4' : sineIntegralQuotientSecondDerivativeProfile (Real.pi * 4) =
      (2 * Real.pi + sineIntegral (Real.pi * 4)) / (32 * Real.pi ^ 3) := by
    simpa [mul_comm] using hS4
  norm_num
  have hsinc4'' : Real.sinc (2 * Real.pi * 2) = 0 := by
    convert hsinc4 using 1 <;> ring
  have hS4'' : sineIntegralQuotientSecondDerivativeProfile (2 * Real.pi * 2) =
      (2 * Real.pi + sineIntegral (2 * Real.pi * 2)) / (32 * Real.pi ^ 3) := by
    convert hS4 using 1 <;> ring
  have hExt4 : sineIntegralQuotientSecondDerivativeExtension (2 * Real.pi * 2) =
      sineIntegralQuotientSecondDerivativeProfile (2 * Real.pi * 2) := by
    apply sineIntegralQuotientSecondDerivativeExtension_of_ne_zero
    positivity
  rw [hExt4, hS4'', hsinc4'']
  simp [sineIntegralQuotientSecondDerivativeExtension_of_ne_zero,
    Real.pi_ne_zero, hs4, hc4, hsinc4, hS4, hsinc4', hS4']
  rw [sineIntegralQuotient_eq_div (4 * Real.pi)
    (mul_ne_zero (by norm_num) Real.pi_ne_zero)]
  field_simp [Real.pi_ne_zero]
  ring

theorem tendsto_cc20QDeltaRegularCandidate_one_right :
    Tendsto cc20QDeltaRegularCandidate (𝓝[>] (1 : ℝ))
      (𝓝 (8 * Real.pi ^ 2 / 9 + sineIntegralQuotient (4 * Real.pi) - 1 / 2)) := by
  have hcont := continuousAt_cc20QDeltaRegularContinuousCandidate_one
  have ht := hcont.tendsto.mono_left
    (nhdsWithin_le_nhds : 𝓝[>] (1 : ℝ) ≤ 𝓝 1)
  rw [cc20QDeltaRegularContinuousCandidate_one] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with rho hrho
  have hrho' : 1 < rho := hrho
  apply cc20QDeltaRegularContinuousCandidate_eq
  · intro h
    exact (ne_of_gt hrho') h
  · intro h
    rw [h] at hrho'
    linarith

theorem continuous_cc20DeltaRegular : Continuous cc20DeltaRegular := by
  unfold cc20DeltaRegular siQuotientProfile
  have hplus : Continuous (fun rho : ℝ =>
      sineIntegralQuotient (2 * Real.pi * (1 + rho))) :=
    continuous_sineIntegralQuotient.comp (by fun_prop)
  have hminus : Continuous (fun rho : ℝ =>
      sineIntegralQuotient (2 * Real.pi * (rho - 1))) :=
    continuous_sineIntegralQuotient.comp (by fun_prop)
  exact (continuous_const.mul Real.continuous_sqrt).mul (hplus.add hminus)

theorem hasDerivAt_inv_sqrt {rho : ℝ} (hrho : 0 < rho) :
    HasDerivAt (fun r : ℝ => 1 / Real.sqrt r)
      (-1 / (2 * rho * Real.sqrt rho)) rho := by
  have hsqrt := Real.hasDerivAt_sqrt (ne_of_gt hrho)
  have hsqrtNe : Real.sqrt rho ≠ 0 := Real.sqrt_ne_zero'.mpr hrho
  have hdiv := (hasDerivAt_const (x := rho) (c := (1 : ℝ))).div hsqrt hsqrtNe
  convert hdiv using 1
  rw [Real.sq_sqrt hrho.le]
  field_simp
  ring

theorem hasDerivAt_siQuotientDerivativeProfile_comp
    {f : ℝ → ℝ} {f' x : ℝ} (hf : HasDerivAt f f' x) (hfx : f x ≠ 0) :
    HasDerivAt (fun y => siQuotientDerivativeProfile (f y))
      (sineIntegralQuotientSecondDerivativeProfile (f x) * f') x := by
  have hraw := (hasDerivAt_deriv_sineIntegralQuotient (f x) hfx).comp x hf
  have hlocal : (fun y => siQuotientDerivativeProfile (f y)) =ᶠ[𝓝 x]
      ((deriv sineIntegralQuotient) ∘ f) := by
    filter_upwards [hf.continuousAt.eventually_ne hfx] with y hy
    exact (deriv_sineIntegralQuotient (f y) hy).symm
  simpa [siQuotientDerivativeProfile, Function.comp_def] using
    hraw.congr_of_eventuallyEq hlocal

theorem hasDerivAt_cc20DeltaBranchSum {rho : ℝ} (hrho : 1 < rho) :
    HasDerivAt cc20DeltaBranchSum (cc20DeltaBranchSumDerivative rho) rho := by
  have hplusArg : HasDerivAt (fun r : ℝ => 2 * Real.pi * (1 + r))
      (2 * Real.pi) rho := by
    convert ((hasDerivAt_const (x := rho) (c := (1 : ℝ))).add
      (hasDerivAt_id' rho)).const_mul (2 * Real.pi) using 1 <;> ring
  have hminusArg : HasDerivAt (fun r : ℝ => 2 * Real.pi * (r - 1))
      (2 * Real.pi) rho := by
    convert ((hasDerivAt_id' rho).sub
      (hasDerivAt_const (x := rho) (c := (1 : ℝ)))).const_mul (2 * Real.pi) using 1 <;> ring
  have hplusNe : 2 * Real.pi * (1 + rho) ≠ 0 := by positivity
  have hminusNe : 2 * Real.pi * (rho - 1) ≠ 0 := by positivity
  have hplus := (hasDerivAt_sineIntegralQuotient
    (2 * Real.pi * (1 + rho)) hplusNe).comp rho hplusArg
  have hminus := (hasDerivAt_sineIntegralQuotient
    (2 * Real.pi * (rho - 1)) hminusNe).comp rho hminusArg
  convert hplus.add hminus using 1 <;>
    simp [cc20DeltaBranchSum, cc20DeltaBranchSumDerivative,
      siQuotientProfile, siQuotientDerivativeProfile] <;> ring

theorem hasDerivAt_cc20DeltaBranchSumDerivative {rho : ℝ} (hrho : 1 < rho) :
    HasDerivAt cc20DeltaBranchSumDerivative
      (cc20DeltaBranchSumSecondDerivative rho) rho := by
  have hplusArg : HasDerivAt (fun r : ℝ => 2 * Real.pi * (1 + r))
      (2 * Real.pi) rho := by
    convert ((hasDerivAt_const (x := rho) (c := (1 : ℝ))).add
      (hasDerivAt_id' rho)).const_mul (2 * Real.pi) using 1 <;> ring
  have hminusArg : HasDerivAt (fun r : ℝ => 2 * Real.pi * (r - 1))
      (2 * Real.pi) rho := by
    convert ((hasDerivAt_id' rho).sub
      (hasDerivAt_const (x := rho) (c := (1 : ℝ)))).const_mul (2 * Real.pi) using 1 <;> ring
  have hplusNe : 2 * Real.pi * (1 + rho) ≠ 0 := by positivity
  have hminusNe : 2 * Real.pi * (rho - 1) ≠ 0 := by positivity
  have hplus := hasDerivAt_siQuotientDerivativeProfile_comp hplusArg hplusNe
  have hminus := hasDerivAt_siQuotientDerivativeProfile_comp hminusArg hminusNe
  have hsum := (hplus.const_mul (2 * Real.pi)).add
    (hminus.const_mul (2 * Real.pi))
  convert hsum using 1 <;>
    simp [cc20DeltaBranchSumDerivative, cc20DeltaBranchSumSecondDerivative] <;> ring

theorem hasDerivAt_cc20DeltaRegular {rho : ℝ} (hrho : 1 < rho) :
    HasDerivAt cc20DeltaRegular (cc20DeltaRegularDerivative rho) rho := by
  have hplusArg : HasDerivAt (fun r : ℝ => 2 * Real.pi * (1 + r))
      (2 * Real.pi) rho := by
    convert ((hasDerivAt_const (x := rho) (c := (1 : ℝ))).add
      (hasDerivAt_id' rho)).const_mul (2 * Real.pi) using 1 <;> ring
  have hminusArg : HasDerivAt (fun r : ℝ => 2 * Real.pi * (r - 1))
      (2 * Real.pi) rho := by
    convert ((hasDerivAt_id' rho).sub
      (hasDerivAt_const (x := rho) (c := (1 : ℝ)))).const_mul (2 * Real.pi) using 1 <;> ring
  have hplusNe : 2 * Real.pi * (1 + rho) ≠ 0 := by positivity
  have hminusNe : 2 * Real.pi * (rho - 1) ≠ 0 := by positivity
  have hplus := (hasDerivAt_sineIntegralQuotient
    (2 * Real.pi * (1 + rho)) hplusNe).comp rho hplusArg
  have hminus := (hasDerivAt_sineIntegralQuotient
    (2 * Real.pi * (rho - 1)) hminusNe).comp rho hminusArg
  have hsum : HasDerivAt
      (fun r : ℝ => sineIntegralQuotient (2 * Real.pi * (1 + r)) +
        sineIntegralQuotient (2 * Real.pi * (r - 1)))
      (2 * Real.pi * siQuotientDerivativeProfile (2 * Real.pi * (1 + rho)) +
        2 * Real.pi * siQuotientDerivativeProfile (2 * Real.pi * (rho - 1))) rho := by
    convert hplus.add hminus using 1 <;>
      simp [siQuotientDerivativeProfile, Function.comp_def] <;> ring
  have hsqrt := Real.hasDerivAt_sqrt (ne_of_gt (lt_trans zero_lt_one hrho))
  have hfactor : HasDerivAt (fun r : ℝ => 2 * Real.sqrt r)
      (2 * (1 / (2 * Real.sqrt rho))) rho := by
    convert (hasDerivAt_const (x := rho) (c := (2 : ℝ))).mul hsqrt using 1 <;> ring
  have hprod := hfactor.mul hsum
  simpa [cc20DeltaRegular, cc20DeltaRegularDerivative,
    siQuotientProfile, Function.comp_def] using hprod

theorem deriv_cc20DeltaRegular_of_one_lt {rho : ℝ} (hrho : 1 < rho) :
    deriv cc20DeltaRegular rho = cc20DeltaRegularDerivative rho :=
  (hasDerivAt_cc20DeltaRegular hrho).deriv

theorem hasDerivAt_deriv_cc20DeltaRegular {rho : ℝ} (hrho : 1 < rho) :
    HasDerivAt (deriv cc20DeltaRegular)
      (cc20DeltaRegularSecondDerivative rho) rho := by
  have hrhoPos : 0 < rho := lt_trans zero_lt_one hrho
  have hsum := hasDerivAt_cc20DeltaBranchSum hrho
  have hsum' := hasDerivAt_cc20DeltaBranchSumDerivative hrho
  have hsqrt := Real.hasDerivAt_sqrt (ne_of_gt hrhoPos)
  have hfactor : HasDerivAt (fun r : ℝ => 2 * Real.sqrt r)
      (1 / Real.sqrt rho) rho := by
    convert (hasDerivAt_const (x := rho) (c := (2 : ℝ))).mul hsqrt using 1 <;> ring
  have hinvSqrt := hasDerivAt_inv_sqrt hrhoPos
  have hraw := (hinvSqrt.mul hsum).add (hfactor.mul hsum')
  have hexplicit : HasDerivAt
      (fun r : ℝ => (1 / Real.sqrt r) * cc20DeltaBranchSum r +
        (2 * Real.sqrt r) * cc20DeltaBranchSumDerivative r)
      (cc20DeltaRegularSecondDerivative rho) rho := by
    convert hraw using 1 <;>
      simp [cc20DeltaRegularSecondDerivative, cc20DeltaBranchSum,
        cc20DeltaBranchSumDerivative, cc20DeltaBranchSumSecondDerivative] <;> ring
  have hlocal : deriv cc20DeltaRegular =ᶠ[𝓝 rho]
      (fun r : ℝ => (1 / Real.sqrt r) * cc20DeltaBranchSum r +
        (2 * Real.sqrt r) * cc20DeltaBranchSumDerivative r) := by
    filter_upwards [(continuousAt_const.eventually_lt continuousAt_id hrho)] with r hr
    simp only [id_eq] at hr
    rw [deriv_cc20DeltaRegular_of_one_lt hr]
    change (2 * (1 / (2 * Real.sqrt r))) * cc20DeltaBranchSum r +
      (2 * Real.sqrt r) * cc20DeltaBranchSumDerivative r =
        (1 / Real.sqrt r) * cc20DeltaBranchSum r +
          (2 * Real.sqrt r) * cc20DeltaBranchSumDerivative r
    have hsqrtNe : Real.sqrt r ≠ 0 :=
      Real.sqrt_ne_zero'.mpr (lt_trans zero_lt_one hr)
    field_simp [hsqrtNe]
  exact hexplicit.congr_of_eventuallyEq hlocal

theorem secondDeriv_cc20DeltaRegular_of_one_lt {rho : ℝ} (hrho : 1 < rho) :
    deriv (deriv cc20DeltaRegular) rho =
      cc20DeltaRegularSecondDerivative rho :=
  (hasDerivAt_deriv_cc20DeltaRegular hrho).deriv

theorem multiplicativeQ_cc20DeltaRegular_of_one_lt {rho : ℝ} (hrho : 1 < rho) :
    multiplicativeQ cc20DeltaRegular rho = cc20QDeltaRegularCandidate rho := by
  rw [multiplicativeQ, cc20QDeltaRegularCandidate,
    deriv_cc20DeltaRegular_of_one_lt hrho,
    secondDeriv_cc20DeltaRegular_of_one_lt hrho]

theorem cc20QDeltaRegularCandidate_eq_branch_derivatives
    {rho : ℝ} (hrho : 0 < rho) :
    cc20QDeltaRegularCandidate rho =
      -4 * rho * Real.sqrt rho * cc20DeltaBranchSumDerivative rho -
        2 * rho ^ 2 * Real.sqrt rho *
          cc20DeltaBranchSumSecondDerivative rho := by
  have hsqrt : Real.sqrt rho ≠ 0 := Real.sqrt_ne_zero'.mpr hrho
  unfold cc20QDeltaRegularCandidate cc20DeltaRegularDerivative
    cc20DeltaRegularSecondDerivative cc20DeltaRegular
    cc20DeltaBranchSumDerivative cc20DeltaBranchSumSecondDerivative
  field_simp [hsqrt]
  rw [Real.sq_sqrt hrho.le]
  ring

end CC20Concrete
end Source
end ConnesWeilRH
