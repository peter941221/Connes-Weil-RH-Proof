import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

/-!
# Certified arctan bounds at small rationals (in-repo, no external dependency)

Milestone M1 (docs/886). Via the FTC (hasDerivAt_arctan, derivative 1/(1+t^2)), for
`0 <= x` we prove `x/(1+x^2) <= arctan x <= x` using the monotonic interval integral and
pointwise bounds `1/(1+x^2) <= 1/(1+t^2) <= 1` on `[0,x]`. Self-contained real-analysis;
no Stirling / arg-Gamma assumed.
-/

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace ArctanCert

open MeasureTheory
open Set
noncomputable section

lemma integrand_cont (x : ℝ) :
    IntervalIntegrable (fun y : ℝ => (1 : ℝ) / (1 + y ^ 2)) volume (0 : ℝ) x := by
  have hpos : ∀ y : ℝ, 1 + y ^ 2 ≠ (0 : ℝ) := by intro y; positivity
  exact (by fun_prop : Continuous fun y : ℝ => (1 : ℝ) / (1 + y ^ 2)).intervalIntegrable 0 x

theorem arctan_mem_integral (x : ℝ) :
    Real.arctan x = ∫ y in (0 : ℝ)..x, (1 : ℝ) / (1 + y ^ 2) := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := Real.arctan)
    (f' := fun y : ℝ => (1 : ℝ) / (1 + y ^ 2)) (a := 0) (b := x)
    (fun y hy => Real.hasDerivAt_arctan y) (integrand_cont x)
  rw [Real.arctan_zero, sub_zero] at h
  exact h.symm

lemma one_le_one_add_sq (y : ℝ) : (1 : ℝ) ≤ 1 + y ^ 2 := by nlinarith [sq_nonneg y]

lemma integrand_le_one (y : ℝ) : (1 : ℝ) / (1 + y ^ 2) ≤ 1 := by
  rw [one_div]; exact inv_le_one_of_one_le₀ (one_le_one_add_sq y)

lemma integrand_lower (x t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) x) :
    (1 : ℝ) / (1 + x ^ 2) ≤ (1 : ℝ) / (1 + t ^ 2) := by
  have hxpos : (0 : ℝ) < 1 + x ^ 2 := by positivity
  have htpos : (0 : ℝ) < 1 + t ^ 2 := by positivity
  have hdiff : (1 : ℝ) / (1 + x ^ 2) - (1 : ℝ) / (1 + t ^ 2) =
      ((1 + t ^ 2) - (1 + x ^ 2)) / ((1 + x ^ 2) * (1 + t ^ 2)) := by
    field_simp [ne_of_gt hxpos, ne_of_gt htpos]
  have hx2 : t ^ 2 ≤ x ^ 2 := by nlinarith [sq_nonneg (x - t), ht.1, ht.2]
  have hnum : (1 + t ^ 2) - (1 + x ^ 2) ≤ (0 : ℝ) := by nlinarith
  have hden : (0 : ℝ) < (1 + x ^ 2) * (1 + t ^ 2) := by positivity
  have hq : ((1 + t ^ 2) - (1 + x ^ 2)) / ((1 + x ^ 2) * (1 + t ^ 2)) ≤ (0 : ℝ) := by
    exact div_nonpos_of_nonpos_of_nonneg hnum (le_of_lt hden)
  have hsub : (1 : ℝ) / (1 + x ^ 2) - (1 : ℝ) / (1 + t ^ 2) ≤ 0 := by
    rwa [hdiff]
  nlinarith

theorem arctan_le_self (x : ℝ) (hx : 0 ≤ x) : Real.arctan x ≤ x := by
  rw [arctan_mem_integral x]
  have hg : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume (0 : ℝ) x := by
    exact (by fun_prop : Continuous fun _ : ℝ => (1 : ℝ)).intervalIntegrable 0 x
  have hmono := intervalIntegral.integral_mono_on (a := 0) (b := x) (μ := volume) hx
    (integrand_cont x) hg (by intro y hy; exact integrand_le_one y)
  rw [intervalIntegral.integral_const] at hmono
  simpa [sub_zero, one_mul] using hmono

theorem lower_le_arctan (x : ℝ) (hx : 0 ≤ x) : x / (1 + x ^ 2) ≤ Real.arctan x := by
  rw [arctan_mem_integral x]
  have hc : IntervalIntegrable (fun t : ℝ => (1 : ℝ) / (1 + x ^ 2)) volume (0 : ℝ) x := by
    have hpos : (1 : ℝ) + x ^ 2 ≠ 0 := by positivity
    exact (by fun_prop : Continuous fun t : ℝ => (1 : ℝ) / (1 + x ^ 2)).intervalIntegrable 0 x
  have hmono := intervalIntegral.integral_mono_on (a := 0) (b := x) (μ := volume) hx
    hc (integrand_cont x) (by intro y hy; exact integrand_lower x y hy)
  calc
    x / (1 + x ^ 2) = (1 / (1 + x ^ 2)) * x := by ring
    _ = (1 / (1 + x ^ 2)) * (x - 0) := by ring
    _ = ∫ _ in (0 : ℝ)..x, (1 : ℝ) / (1 + x ^ 2) := by
      rw [intervalIntegral.integral_const]
      simp [mul_comm, sub_zero]
    _ ≤ ∫ y in (0 : ℝ)..x, (1 : ℝ) / (1 + y ^ 2) := hmono

/-- Certified rational arctan bounds at 1/4: 4/17 <= atan(1/4) <= 1/4. -/
theorem arctan_fourth : (4 : ℝ) / 17 ≤ Real.arctan (1 / 4) ∧ Real.arctan (1 / 4) ≤ (1 : ℝ) / 4 := by
  constructor
  · have h := lower_le_arctan (1 / 4) (by norm_num)
    have hv : (1 / 4) / (1 + (1 / 4 : ℝ) ^ 2) = (4 : ℝ) / 17 := by norm_num
    rwa [hv] at h
  · exact arctan_le_self (1 / 4) (by norm_num)

/-- Certified rational arctan bounds at 1/6: 6/37 <= atan(1/6) <= 1/6. -/
theorem arctan_sixth : (6 : ℝ) / 37 ≤ Real.arctan (1 / 6) ∧ Real.arctan (1 / 6) ≤ (1 : ℝ) / 6 := by
  constructor
  · have h := lower_le_arctan (1 / 6) (by norm_num)
    have hv : (1 / 6) / (1 + (1 / 6 : ℝ) ^ 2) = (6 : ℝ) / 37 := by norm_num
    rwa [hv] at h
  · exact arctan_le_self (1 / 6) (by norm_num)

/-- Certified rational arctan bounds at 1/8: 8/65 <= atan(1/8) <= 1/8. -/
theorem arctan_eighth : (8 : ℝ) / 65 ≤ Real.arctan (1 / 8) ∧ Real.arctan (1 / 8) ≤ (1 : ℝ) / 8 := by
  constructor
  · have h := lower_le_arctan (1 / 8) (by norm_num)
    have hv : (1 / 8) / (1 + (1 / 8 : ℝ) ^ 2) = (8 : ℝ) / 65 := by norm_num
    rwa [hv] at h
  · exact arctan_le_self (1 / 8) (by norm_num)

theorem arctan_half : (2 : ℝ) / 5 ≤ Real.arctan (1 / 2) ∧ Real.arctan (1 / 2) ≤ (1 : ℝ) / 2 := by
  constructor
  · have h := lower_le_arctan (1 / 2) (by norm_num)
    have hv : (1 / 2) / (1 + (1 / 2 : ℝ) ^ 2) = (2 : ℝ) / 5 := by norm_num
    rwa [hv] at h
  · exact arctan_le_self (1 / 2) (by norm_num)

end
end ArctanCert
end Dev
end Source
end ConnesWeilRH
