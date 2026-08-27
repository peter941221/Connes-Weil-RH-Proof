/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The CC20 endpoint `Qepsilon` kernel formula

This file records the raw spectral formula used by Connes--Consani for the
endpoint kernel, independently of the older `Q(delta)` regular profile.

For an actual prolate realization, `analyticMode n` is `xi_n^an`,
`analyticModeDeriv n` is its derivative, `eigenvalue n` is `lambda(n)`, and
`endpointSlope` is `epsilon'(1+)`.  Equations (99) and (104) of
<https://arxiv.org/html/2006.13771> then give the definitions below.

This is a formula layer only.  It does not yet construct the prolate modes,
prove convergence of the spectral series, or prove the resulting windowed
kernel is in `L2`.  Those are the remaining analytic inputs needed before
`C1CC20LpOperator` can construct the paper's `kf_I`.
-/

namespace ConnesWeilRH
namespace Source
namespace CC20Concrete

open MeasureTheory
open scoped Interval

/-- Input data for the upper-scale form of the CC20 endpoint spectral series.

The strict eigenvalue bound makes the denominator in equation (99) nonzero.
The concrete prolate realization and the series convergence estimates remain
separate proof obligations. -/
structure CC20EndpointSpectralData where
  eigenvalue : Nat -> Real
  analyticMode : Nat -> Real -> Real
  analyticModeDeriv : Nat -> Real -> Real
  endpointSlope : Real
  eigenvalue_sq_lt_one : forall n, eigenvalue n ^ 2 < 1
  endpointSlope_summable : Summable (fun n =>
    (eigenvalue n ^ 2 / (1 - eigenvalue n ^ 2)) * analyticMode n 1 ^ 2)
  endpointSlope_eq_spectral : endpointSlope = tsum (fun n =>
    (eigenvalue n ^ 2 / (1 - eigenvalue n ^ 2)) * analyticMode n 1 ^ 2)
  endpointSlope_pos : 0 < endpointSlope

/-- The coefficient `lambda(n)^2 / (1 - lambda(n)^2)` in equations (99) and
(100) of the CC20 paper. -/
noncomputable def CC20EndpointSpectralData.weight
    (data : CC20EndpointSpectralData) (n : Nat) : Real :=
  data.eigenvalue n ^ 2 / (1 - data.eigenvalue n ^ 2)

theorem CC20EndpointSpectralData.weight_denominator_pos
    (data : CC20EndpointSpectralData) (n : Nat) :
    0 < 1 - data.eigenvalue n ^ 2 := by
  exact sub_pos.mpr (data.eigenvalue_sq_lt_one n)

/-- The upper-scale summand for `epsilon(rho)` after the analytic continuation
rewrite in CC20 Lemma 4.  The paper uses this formula for `rho >= 1`; later
analytic theorems must carry that domain condition explicitly. -/
noncomputable def CC20EndpointSpectralData.epsilonUpperSummand
    (data : CC20EndpointSpectralData) (n : Nat) (rho : Real) : Real :=
  data.weight n *
    (rho ^ (1 / 2 : Real) *
      (∫ x in rho⁻¹..1, data.analyticMode n x *
        data.analyticMode n (rho * x)))

/-- The spectral formula for the upper-scale branch of `epsilon`.  No
convergence claim is bundled into this definition: a later prolate realization
must prove that the displayed `tsum` is the analytic series on its domain. -/
noncomputable def CC20EndpointSpectralData.epsilonUpper
    (data : CC20EndpointSpectralData) (rho : Real) : Real :=
  tsum fun n => data.epsilonUpperSummand n rho

theorem CC20EndpointSpectralData.epsilonUpper_one
    (data : CC20EndpointSpectralData) : data.epsilonUpper 1 = 0 := by
  unfold epsilonUpper epsilonUpperSummand
  simp

/-- The `C_n(rho)` summand in CC20 equation (99).  This uses the paper's
analytic continuation form, so it contains only `xi_n^an` and its derivative. -/
noncomputable def CC20EndpointSpectralData.qEpsilonSummand
    (data : CC20EndpointSpectralData) (n : Nat) (rho : Real) : Real :=
  data.weight n *
    (rho ^ (1 / 2 : Real) *
        (∫ x in rho⁻¹..1,
          (x * data.analyticModeDeriv n x) *
            ((rho * x) * data.analyticModeDeriv n (rho * x))) +
      rho ^ (-3 / 2 : Real) * data.analyticModeDeriv n rho⁻¹ *
          data.analyticMode n 1 -
        rho ^ (3 / 2 : Real) * data.analyticMode n 1 *
          data.analyticModeDeriv n rho)

/-- The paper's `Qepsilon(rho)` formal spectral series from equation (99). -/
noncomputable def CC20EndpointSpectralData.qEpsilon
    (data : CC20EndpointSpectralData) (rho : Real) : Real :=
  tsum fun n => data.qEpsilonSummand n rho

/-- Each equation-(99) summand vanishes at `rho = 1`.  This is purely
algebraic: the interval integral has equal endpoints and the two boundary
terms cancel. -/
theorem CC20EndpointSpectralData.qEpsilonSummand_one
    (data : CC20EndpointSpectralData) (n : Nat) :
    data.qEpsilonSummand n 1 = 0 := by
  unfold qEpsilonSummand
  rw [mul_eq_zero]
  right
  simp
  ring

/-- CC20 Remark 6, derived directly from the formal equation-(99) series:
`Qepsilon(1) = 0`.  No spectral convergence estimate is needed for this exact
value because every individual summand is identically zero at `rho = 1`. -/
theorem CC20EndpointSpectralData.qEpsilon_one
    (data : CC20EndpointSpectralData) : data.qEpsilon 1 = 0 := by
  unfold qEpsilon
  have hzero : (fun n => data.qEpsilonSummand n 1) = fun _ => 0 := by
    funext n
    exact data.qEpsilonSummand_one n
  rw [hzero]
  exact tsum_zero

/-- The scalar additive kernel in CC20 equation (104), before restricting the
two input variables to a finite interval `I`. -/
noncomputable def CC20EndpointSpectralData.endpointAdditiveKernel
    (data : CC20EndpointSpectralData) (v : Real) : Real :=
  data.qEpsilon (Real.exp |v|) / (2 * data.endpointSlope)

/-- The raw additive kernel has zero value at the diagonal displacement. -/
theorem CC20EndpointSpectralData.endpointAdditiveKernel_zero
    (data : CC20EndpointSpectralData) : data.endpointAdditiveKernel 0 = 0 := by
  simp [endpointAdditiveKernel, data.qEpsilon_one]

/-- The two-variable raw kernel of the CC20 compact operator `K_I`: interval
restriction is deliberately external to this definition. -/
noncomputable def CC20EndpointSpectralData.endpointWindowKernel
    (data : CC20EndpointSpectralData) (p : Real × Real) : Real :=
  data.endpointAdditiveKernel (p.2 - p.1)

/-- The paper's raw `K_I` kernel has zero pointwise diagonal.  This does not
by itself make a statement about an induced integral operator, since a diagonal
is a measure-zero set. -/
theorem CC20EndpointSpectralData.endpointWindowKernel_diagonal
    (data : CC20EndpointSpectralData) (x : Real) :
    data.endpointWindowKernel (x, x) = 0 := by
  simp [endpointWindowKernel, data.endpointAdditiveKernel_zero]

/-- The integral of the raw diagonal is zero for every measure.  This is the
pointwise-kernel statement in CC20 Remark 6, not a theorem identifying this
integral with an operator trace. -/
theorem CC20EndpointSpectralData.integral_endpointWindowKernel_diagonal_zero
    (data : CC20EndpointSpectralData) (mu : Measure Real) :
    (∫ x, data.endpointWindowKernel (x, x) ∂mu) = 0 := by
  have hzero : (fun x : Real => data.endpointWindowKernel (x, x)) = fun _ => 0 := by
    funext x
    exact data.endpointWindowKernel_diagonal x
  rw [hzero]
  simp

/-- Complex-valued version of the raw endpoint kernel, with the exact type
expected by the existing `C1CC20LpOperator.applyKernel` foundation. -/
noncomputable def CC20EndpointSpectralData.endpointWindowKernelComplex
    (data : CC20EndpointSpectralData) (p : Real × Real) : Complex :=
  (data.endpointWindowKernel p : Complex)

theorem CC20EndpointSpectralData.endpointWindowKernelComplex_diagonal
    (data : CC20EndpointSpectralData) (x : Real) :
    data.endpointWindowKernelComplex (x, x) = 0 := by
  simp [endpointWindowKernelComplex, data.endpointWindowKernel_diagonal]

end CC20Concrete
end Source
end ConnesWeilRH
