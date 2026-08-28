/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1CC20Eq115Table
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Tactic.IntervalCases

/-!
# Probe for the (gamma) Bessel-coercivity brick

Probes the risky ingredients before committing to the full leaf: the
positivity discharge of the 1732-branch coefficient chain, and the interval
Fourier integral of the window exponential by FTOC.  Transient file;
delete once the brick lands.
-/

namespace ConnesWeilRH.Source.C1CC20GammaBesselProbe

open MeasureTheory Set intervalIntegral
open scoped Interval
open C1CC20FiniteRankApproximation C1CC20RawKernelMass C1CC20Eq115Table

-- Risk 1: the coefficient chain is everywhere positive.
set_option maxRecDepth 30000 in
example : ∀ n : Fin 1732, (0 : ℚ) < cc20Eq115CoefficientQ n := by
  intro n
  cases n with
  | mk k hk =>
      interval_cases k
      <;> norm_num [cc20Eq115CoefficientQ]

-- Risk 2: the window exponential integrates to the Kronecker delta.
theorem window_exp_integral (n : ℤ) :
    ∫ x in (-cc20RootLength / 2)..(cc20RootLength / 2),
      Complex.exp
        (((2 * Real.pi * (n : ℝ) * x / cc20RootLength : Real) : Complex) * Complex.I) =
      if n = 0 then (cc20RootLength : ℂ) else 0 := by
  have hLc : (cc20RootLength : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr cc20RootLength_pos.ne'
  by_cases hn : n = 0
  · rw [if_pos hn]
    subst hn
    simp only [Int.cast_zero, mul_zero, zero_mul, zero_div, Complex.ofReal_zero,
      Complex.exp_zero]
    rw [intervalIntegral.integral_const, neg_div, sub_neg_eq_add, add_halves,
      Algebra.smul_def, mul_one]
    exact rfl
  · have hc : (2 * Real.pi * (n : ℝ) / cc20RootLength : ℝ) ≠ 0 := by
      refine div_ne_zero ?_ cc20RootLength_pos.ne'
      exact mul_ne_zero (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero)
        (Int.cast_ne_zero.mpr hn)
    have hc0 : ((2 * Real.pi * (n : ℝ) / cc20RootLength : Real) : Complex) * Complex.I ≠ 0 :=
      mul_ne_zero (Complex.ofReal_ne_zero.mpr hc) Complex.I_ne_zero
    set c : ℂ := ((2 * Real.pi * (n : ℝ) / cc20RootLength : Real) : Complex) * Complex.I with hcdef
    have hcexp : ∀ x : ℝ,
        HasDerivAt (fun y : ℝ => Complex.exp (c * (y : ℂ)))
          (c * Complex.exp (c * (x : ℂ))) x := by
      intro x
      have he : HasDerivAt (fun y : ℂ => Complex.exp (c * y))
          (c * Complex.exp (c * x)) (x : ℂ) := by
        rw [(fun α β => by ring : ∀ α β : ℂ, α * Complex.exp β = Complex.exp β * α)]
        refine (Complex.hasDerivAt_exp (c * x)).comp (x : ℂ) ?_
        simpa using (hasDerivAt_id (x := (x : ℂ))).const_mul c
      exact he.comp_ofReal
    have hF : ∀ x : ℝ,
        HasDerivAt (fun x : ℝ => c⁻¹ * Complex.exp (c * (x : ℂ)))
          (Complex.exp (c * (x : ℂ))) x := by
      intro x
      convert hcexp x |>.const_mul (c⁻¹) using 1
      field_simp
    have hcong :
        (fun x : ℝ => Complex.exp
          (((2 * Real.pi * (n : ℝ) * x / cc20RootLength : Real) : ℂ) * Complex.I)) =
          fun x : ℝ => Complex.exp (c * (x : ℂ)) := by
      funext x
      congr 1
      rw [hcdef]
      push_cast
      ring
    have hcont : Continuous (fun x : ℝ => c * (x : ℂ)) :=
      continuous_const.mul Complex.continuous_ofReal
    have hintg : IntervalIntegrable (fun x : ℝ => Complex.exp (c * (x : ℂ))) volume
        (-cc20RootLength / 2) (cc20RootLength / 2) := by
      apply Continuous.intervalIntegrable
      refine Complex.continuous_exp.comp hcont
    rw [hcong, integral_eq_sub_of_hasDerivAt (fun x _ => hF x) hintg, if_neg hn]
    show c⁻¹ * Complex.exp (c * ((cc20RootLength / 2 : ℝ) : ℂ)) -
        c⁻¹ * Complex.exp (c * ((-(cc20RootLength) / 2 : ℝ) : ℂ)) = 0
    have he1 : c * ((cc20RootLength / 2 : ℝ) : ℂ) = (n : ℂ) * (Real.pi * Complex.I) := by
      rw [hcdef]
      push_cast
      field_simp [hLc]
    have he2 : c * ((-(cc20RootLength) / 2 : ℝ) : ℂ) =
        (n : ℂ) * (Real.pi * Complex.I) - (2 : ℂ) * ((n : ℂ) * (Real.pi * Complex.I)) := by
      rw [hcdef]
      push_cast
      field_simp [hLc]
      ring
    rw [he1, he2, Complex.exp_sub]
    have htwo : Complex.exp ((2 : ℂ) * ((n : ℂ) * (Real.pi * Complex.I))) = 1 := by
      rw [show (2 : ℂ) * ((n : ℂ) * (Real.pi * Complex.I)) =
          (n : ℂ) * (2 * (Real.pi * Complex.I)) by ring,
        Complex.exp_int_mul, ← mul_assoc, Complex.exp_two_pi_mul_I, one_zpow]
    rw [htwo, div_one]
    ring

end ConnesWeilRH.Source.C1CC20GammaBesselProbe
