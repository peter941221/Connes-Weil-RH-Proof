/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.CC20YoshidaNearZeros
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable

/-!
# Jensen reduction for the source zeta-zero count

This module constructs the entire completed zeta function whose zeros contain
the source spectral index and reduces its closed-ball count to a circle norm
bound through Mathlib's Jensen inequality.
-/

namespace ConnesWeilRH
namespace Source
namespace CC20ZetaCounting

open scoped Topology
open Complex MeromorphicOn
open CC20YoshidaNearZeros

/-- The entire Riemann xi normalization written using Mathlib's pole-removed
completed zeta. The additive `1` is forced by
`completedRiemannZeta = completedRiemannZeta₀ - 1/s - 1/(1-s)`. -/
noncomputable def completedRiemannXi (s : ℂ) : ℂ :=
  s * (s - 1) * completedRiemannZeta₀ s + 1

theorem differentiable_completedRiemannXi :
    Differentiable ℂ completedRiemannXi := by
  unfold completedRiemannXi
  exact ((differentiable_id.mul
    (differentiable_id.sub (differentiable_const (c := (1 : ℂ))))).mul
      differentiable_completedZeta₀).add (differentiable_const (c := (1 : ℂ)))

theorem analyticOnNhd_completedRiemannXi (S : Set ℂ) :
    AnalyticOnNhd ℂ completedRiemannXi S :=
  fun z _hz => differentiable_completedRiemannXi.analyticAt z

/-- The modified theta kernel whose Mellin transform is Mathlib's entire
completed zeta. This is a transparent name for the kernel already constructed
by the Riemann zeta functional-equation package. -/
noncomputable def completedRiemannXiKernel : ℝ -> ℂ :=
  (HurwitzZeta.hurwitzEvenFEPair 0).f_modif

/-- Above one, the modified kernel is the ordinary theta kernel with its
constant term removed. -/
theorem completedRiemannXiKernel_eq_evenKernel_sub_one_of_one_lt
    {t : ℝ} (ht : 1 < t) :
    completedRiemannXiKernel t =
      (HurwitzZeta.evenKernel 0 t : ℂ) - 1 := by
  simp [completedRiemannXiKernel, WeakFEPair.f_modif,
    HurwitzZeta.hurwitzEvenFEPair, ht, ht.le]

/-- Below one, the modified kernel subtracts the singular
`t^(-1/2)` term dictated by the theta functional equation. -/
theorem completedRiemannXiKernel_eq_evenKernel_sub_rpow_of_mem_Ioo
    {t : ℝ} (ht : t ∈ Set.Ioo 0 1) :
    completedRiemannXiKernel t =
      (HurwitzZeta.evenKernel 0 t : ℂ) - (t ^ (-(1 / 2 : ℝ)) : ℝ) := by
  simp [completedRiemannXiKernel, WeakFEPair.f_modif,
    HurwitzZeta.hurwitzEvenFEPair, ht.1, ht.2, ht.2.le]

/-- The small-`t` kernel is the large-`t` decaying kernel at `1/t`, multiplied
by the exact theta scaling factor. -/
theorem completedRiemannXiKernel_eq_rpow_mul_evenKernel_inv_sub_one
    {t : ℝ} (ht : t ∈ Set.Ioo 0 1) :
    completedRiemannXiKernel t =
      (1 / t ^ (1 / 2 : ℝ) : ℝ) *
        ((HurwitzZeta.evenKernel 0 (1 / t) : ℂ) - 1) := by
  rw [completedRiemannXiKernel_eq_evenKernel_sub_rpow_of_mem_Ioo ht]
  rw [HurwitzZeta.evenKernel_functional_equation]
  rw [show HurwitzZeta.cosKernel 0 = HurwitzZeta.evenKernel 0 by
    exact HurwitzZeta.evenKernel_eq_cosKernel_of_zero.symm]
  rw [Real.rpow_neg ht.1.le]
  push_cast
  ring

/-- The explicit constant in the theta-tail bound on `[1, infinity)`. -/
noncomputable def completedRiemannXiKernelTailConstant : ℝ :=
  2 / (1 - Real.exp (-Real.pi))

theorem completedRiemannXiKernelTailConstant_nonneg :
    0 <= completedRiemannXiKernelTailConstant := by
  unfold completedRiemannXiKernelTailConstant
  have hexp : Real.exp (-Real.pi) < 1 := by
    rw [Real.exp_lt_one_iff]
    exact neg_neg_of_pos Real.pi_pos
  exact div_nonneg (by norm_num) (by linarith)

/-- Explicit exponential decay of the modified theta kernel above one. -/
theorem norm_completedRiemannXiKernel_le_exp_of_one_lt
    {t : ℝ} (ht : 1 < t) :
    ‖completedRiemannXiKernel t‖ <=
      completedRiemannXiKernelTailConstant * Real.exp (-Real.pi * t) := by
  rw [completedRiemannXiKernel_eq_evenKernel_sub_one_of_one_lt ht]
  have htheta : (HurwitzZeta.evenKernel 0 t : ℂ) =
      jacobiTheta (Complex.I * t) := by
    rw [show HurwitzZeta.evenKernel 0 t = HurwitzZeta.cosKernel 0 t by
      exact congrFun HurwitzZeta.evenKernel_eq_cosKernel_of_zero t]
    have hc := HurwitzZeta.cosKernel_def (0 : ℝ) t
    simpa [jacobiTheta_eq_jacobiTheta₂] using hc
  rw [htheta]
  have hraw := norm_jacobiTheta_sub_one_le
    (τ := Complex.I * t) (by simpa using (show 0 < t by linarith))
  simp only [Complex.mul_im, Complex.I_re, zero_mul, Complex.I_im,
    one_mul, Complex.ofReal_re, zero_add] at hraw
  calc
    ‖jacobiTheta (Complex.I * t) - 1‖ <=
        2 / (1 - Real.exp (-Real.pi * t)) * Real.exp (-Real.pi * t) := hraw
    _ <= completedRiemannXiKernelTailConstant * Real.exp (-Real.pi * t) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      unfold completedRiemannXiKernelTailConstant
      have hexpLt : Real.exp (-Real.pi * t) < Real.exp (-Real.pi) := by
        apply Real.exp_lt_exp.mpr
        nlinarith [Real.pi_pos]
      have hdenPos : 0 < 1 - Real.exp (-Real.pi * t) := by
        have : Real.exp (-Real.pi * t) < 1 := by
          rw [Real.exp_lt_one_iff]
          nlinarith [Real.pi_pos]
        linarith
      have hdenBasePos : 0 < 1 - Real.exp (-Real.pi) := by
        have : Real.exp (-Real.pi) < 1 := by
          rw [Real.exp_lt_one_iff]
          exact neg_neg_of_pos Real.pi_pos
        linarith
      exact div_le_div_of_nonneg_left (by norm_num) hdenBasePos
        (by linarith)

/-- The theta functional equation transfers the same explicit exponential
tail to the small interval. -/
theorem norm_completedRiemannXiKernel_le_inv_exp_of_mem_Ioo
    {t : ℝ} (ht : t ∈ Set.Ioo 0 1) :
    ‖completedRiemannXiKernel t‖ <=
      (1 / t ^ (1 / 2 : ℝ)) *
        (completedRiemannXiKernelTailConstant * Real.exp (-Real.pi * (1 / t))) := by
  rw [completedRiemannXiKernel_eq_rpow_mul_evenKernel_inv_sub_one ht, norm_mul,
    Complex.norm_real, Real.norm_of_nonneg (by
      exact div_nonneg zero_le_one (Real.rpow_nonneg ht.1.le _))]
  apply mul_le_mul_of_nonneg_left _
    (div_nonneg zero_le_one (Real.rpow_nonneg ht.1.le _))
  rw [← completedRiemannXiKernel_eq_evenKernel_sub_one_of_one_lt]
  · exact norm_completedRiemannXiKernel_le_exp_of_one_lt
      (one_lt_one_div ht.1 ht.2)
  · exact one_lt_one_div ht.1 ht.2

/-- Mathlib's pole-removed completed zeta is exactly the Mellin transform of
the modified theta kernel, with the normalization `s / 2` and `1 / 2`. -/
theorem completedRiemannZeta₀_eq_mellin_completedRiemannXiKernel (s : ℂ) :
    completedRiemannZeta₀ s = mellin completedRiemannXiKernel (s / 2) / 2 := by
  rfl

/-- The real Mellin moment controlling the norm of the completed-zeta
integral. Its parameter is the real part of the original xi variable. -/
noncomputable def completedRiemannXiKernelMoment (sigma : ℝ) : ℝ :=
  ∫ t : ℝ in Set.Ioi 0,
    t ^ (sigma / 2 - 1) * ‖completedRiemannXiKernel t‖

/-- The exponential moments used to integrate the large theta-kernel branch
are exactly real Gamma values. Keeping the scale `r` explicit avoids losing
the decisive `pi^(-a)` factor later. -/
theorem integral_rpow_mul_exp_neg_mul_Ioi_eq_gamma
    {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    (∫ t : ℝ in Set.Ioi 0,
      t ^ (a - 1) * Real.exp (-(r * t))) =
        (1 / r) ^ a * Real.Gamma a := by
  exact Real.integral_rpow_mul_exp_neg_mul_Ioi ha hr

/-- At an integer exponent the preceding Gamma moment is a factorial. This is
the form used by the dyadic growth estimate. -/
theorem integral_pow_mul_exp_neg_pi_eq_factorial (n : ℕ) :
    (∫ t : ℝ in Set.Ioi 0,
      t ^ n * Real.exp (-(Real.pi * t))) =
        (1 / Real.pi) ^ (n + 1 : ℝ) * (n.factorial : ℝ) := by
  rw [show (fun t : ℝ => t ^ n * Real.exp (-(Real.pi * t))) =
      fun t : ℝ => t ^ (((n : ℝ) + 1) - 1) *
        Real.exp (-(Real.pi * t)) by
    funext t
    norm_num]
  rw [integral_rpow_mul_exp_neg_mul_Ioi_eq_gamma
    (a := (n : ℝ) + 1) (by positivity) Real.pi_pos]
  congr 1
  simpa only [Nat.cast_add, Nat.cast_one] using Real.Gamma_nat_eq_factorial n

/-- A deliberately elementary upper bound for the integer Gamma values. Its
logarithm is `n * log n`, which is subquadratic on dyadic radii and therefore
strong enough for the spectral `q < 4` threshold. -/
theorem integral_pow_mul_exp_neg_pi_le_pow_self (n : ℕ) :
    (∫ t : ℝ in Set.Ioi 0,
      t ^ n * Real.exp (-(Real.pi * t))) <= (n : ℝ) ^ n := by
  rw [integral_pow_mul_exp_neg_pi_eq_factorial]
  have hpiInv : 0 <= (1 / Real.pi) ^ (n + 1 : ℝ) :=
    Real.rpow_nonneg (by positivity) _
  have hpiInvLe : (1 / Real.pi) ^ (n + 1 : ℝ) <= 1 := by
    apply Real.rpow_le_one
    · positivity
    · rw [div_le_one Real.pi_pos]
      linarith [Real.two_le_pi]
    · positivity
  calc
    (1 / Real.pi) ^ (n + 1 : ℝ) * (n.factorial : ℝ) <=
        1 * (n.factorial : ℝ) := by
      gcongr
    _ <= (n : ℝ) ^ n := by
      simpa only [one_mul] using
        (show (n.factorial : ℝ) <= (n : ℝ) ^ n by
          exact_mod_cast Nat.factorial_le_pow n)

/-- The norm of the pole-removed completed zeta depends on a complex argument
only through the real Mellin moment at its real part. -/
theorem norm_completedRiemannZeta₀_le_kernelMoment (s : ℂ) :
    ‖completedRiemannZeta₀ s‖ <= completedRiemannXiKernelMoment s.re / 2 := by
  rw [completedRiemannZeta₀_eq_mellin_completedRiemannXiKernel, norm_div]
  rw [Complex.norm_two]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  calc
    ‖mellin completedRiemannXiKernel (s / 2)‖ <=
        ∫ t : ℝ in Set.Ioi 0,
          ‖(t : ℂ) ^ (s / 2 - 1) • completedRiemannXiKernel t‖ := by
      exact MeasureTheory.norm_integral_le_integral_norm _
    _ = completedRiemannXiKernelMoment s.re := by
      unfold completedRiemannXiKernelMoment
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      change ‖(t : ℂ) ^ (s / 2 - 1) • completedRiemannXiKernel t‖ =
        t ^ (s.re / 2 - 1) * ‖completedRiemannXiKernel t‖
      rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht]
      congr 2
      norm_num [Complex.div_re]

/-- Xi is controlled by a quadratic polynomial factor times the real modified
theta-kernel moment. After the preceding theorem, this is a purely real
integral-growth problem. -/
theorem norm_completedRiemannXi_le_kernelMoment (s : ℂ) :
    ‖completedRiemannXi s‖ <=
      ‖s‖ * ‖s - 1‖ * (completedRiemannXiKernelMoment s.re / 2) + 1 := by
  unfold completedRiemannXi
  calc
    ‖s * (s - 1) * completedRiemannZeta₀ s + 1‖ <=
        ‖s * (s - 1) * completedRiemannZeta₀ s‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
    _ = ‖s‖ * ‖s - 1‖ * ‖completedRiemannZeta₀ s‖ + 1 := by
      rw [norm_mul, norm_mul]
      norm_num
    _ <= ‖s‖ * ‖s - 1‖ *
        (completedRiemannXiKernelMoment s.re / 2) + 1 := by
      gcongr
      exact norm_completedRiemannZeta₀_le_kernelMoment s

/-- The project normalization of xi satisfies the standard functional
equation. This lets growth estimates fold the left half-plane onto the right
without changing the function value. -/
theorem completedRiemannXi_one_sub (s : ℂ) :
    completedRiemannXi (1 - s) = completedRiemannXi s := by
  rw [completedRiemannXi, completedRiemannXi,
    completedRiemannZeta₀_one_sub]
  ring

/-- Every point can be folded across the critical line to one with real part
at least `1/2`, preserving the xi value. -/
theorem exists_half_le_re_and_completedRiemannXi_eq (s : ℂ) :
    ∃ w : ℂ, (1 / 2 : ℝ) ≤ w.re ∧
      completedRiemannXi w = completedRiemannXi s := by
  by_cases hs : (1 / 2 : ℝ) ≤ s.re
  · exact ⟨s, hs, rfl⟩
  · refine ⟨1 - s, ?_, completedRiemannXi_one_sub s⟩
    simp only [Complex.sub_re, Complex.one_re]
    linarith

/-- Norm form of the xi folding theorem, suitable for circle-growth
majorants. -/
theorem exists_half_le_re_and_norm_completedRiemannXi_eq (s : ℂ) :
    ∃ w : ℂ, (1 / 2 : ℝ) ≤ w.re ∧
      ‖completedRiemannXi w‖ = ‖completedRiemannXi s‖ := by
  rcases exists_half_le_re_and_completedRiemannXi_eq s with ⟨w, hw, hxi⟩
  exact ⟨w, hw, congrArg norm hxi⟩

/-- Folding across the critical line increases the distance from the origin by
at most one. Thus a right-half-plane growth estimate on a ball of radius
`R + 1` controls xi on the full ball of radius `R`. -/
theorem exists_half_le_re_norm_le_add_one_and_norm_completedRiemannXi_eq
    (s : ℂ) :
    ∃ w : ℂ, (1 / 2 : ℝ) ≤ w.re ∧ ‖w‖ ≤ ‖s‖ + 1 ∧
      ‖completedRiemannXi w‖ = ‖completedRiemannXi s‖ := by
  by_cases hs : (1 / 2 : ℝ) ≤ s.re
  · exact ⟨s, hs, by linarith [norm_nonneg s], rfl⟩
  · refine ⟨1 - s, ?_, ?_, congrArg norm (completedRiemannXi_one_sub s)⟩
    · simp only [Complex.sub_re, Complex.one_re]
      linarith
    · calc
        ‖(1 : ℂ) - s‖ ≤ ‖(1 : ℂ)‖ + ‖s‖ := norm_sub_le _ _
        _ = ‖s‖ + 1 := by norm_num; ring

theorem completedRiemannXi_eq_mul_completedRiemannZeta
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    completedRiemannXi s = s * (s - 1) * completedRiemannZeta s := by
  rw [completedRiemannXi, completedRiemannZeta_eq]
  have hsSub : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have honeSub : 1 - s ≠ 0 := sub_ne_zero.mpr hs1.symm
  field_simp [hs0, hsSub, honeSub]
  ring

theorem completedRiemannZeta_eq_zero_of_sourceNontrivialZero
    {z : ℂ} (hz : RHDefinitionBridge.standard.sourceNontrivialZero z) :
    completedRiemannZeta z = 0 := by
  have hzRe : 0 < z.re := sourceNontrivialZero_zero_lt_re hz
  have hz0 : z ≠ 0 := by
    intro h
    subst z
    norm_num at hzRe
  have hgamma : Complex.Gammaℝ z ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hzRe
  have hzeta := hz.zeta_zero
  rw [riemannZeta_def_of_ne_zero hz0] at hzeta
  exact (div_eq_zero_iff.mp hzeta).resolve_right hgamma

theorem completedRiemannXi_eq_zero_of_sourceNontrivialZero
    {z : ℂ} (hz : RHDefinitionBridge.standard.sourceNontrivialZero z) :
    completedRiemannXi z = 0 := by
  have hz0 : z ≠ 0 := by
    intro h
    subst z
    simpa [riemannZeta_zero] using hz.zeta_zero
  rw [completedRiemannXi_eq_mul_completedRiemannZeta hz0 hz.not_pole,
    completedRiemannZeta_eq_zero_of_sourceNontrivialZero hz, mul_zero]

theorem completedRiemannXi_two_ne_zero : completedRiemannXi 2 ≠ 0 := by
  have hzeta : riemannZeta (2 : ℂ) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by norm_num)
  have hcompleted : completedRiemannZeta (2 : ℂ) ≠ 0 := by
    intro hzero
    apply hzeta
    rw [riemannZeta_def_of_ne_zero (by norm_num), hzero, zero_div]
  rw [completedRiemannXi_eq_mul_completedRiemannZeta (by norm_num) (by norm_num)]
  exact mul_ne_zero (mul_ne_zero (by norm_num) (by norm_num)) hcompleted

theorem completedRiemannXi_analyticOrderAt_ne_top (z : ℂ) :
    analyticOrderAt completedRiemannXi z ≠ ⊤ := by
  intro htop
  have hzero : completedRiemannXi = 0 :=
    (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero z
      differentiable_completedRiemannXi.analyticAt).mp htop
  exact completedRiemannXi_two_ne_zero (congrFun hzero 2)

/-- Source zeros in a closed ball inject into the divisor support of xi on the
same ball. This is the exact same-index bridge needed before Jensen counting. -/
theorem sourceNontrivialZerosInClosedBall_ncard_le_xi_divisor_support
    (c : ℂ) (r : ℝ) :
    (sourceNontrivialZerosInClosedBall c r).ncard ≤
      (Function.support
        (divisor completedRiemannXi (Metric.closedBall c |r|))).ncard := by
  apply Set.ncard_le_ncard
  · intro z hz
    rw [Function.mem_support]
    have hzball : z ∈ Metric.closedBall c |r| := by
      exact Metric.closedBall_subset_closedBall (le_abs_self r) hz.1
    rw [(analyticOnNhd_completedRiemannXi _).divisor_apply hzball]
    have horder : analyticOrderAt completedRiemannXi z ≠ 0 :=
      (differentiable_completedRiemannXi.analyticAt z).analyticOrderAt_ne_zero.mpr
        (completedRiemannXi_eq_zero_of_sourceNontrivialZero hz.2)
    have htop := completedRiemannXi_analyticOrderAt_ne_top z
    simpa [WithTop.untop₀_eq_zero, WithTop.map_eq_some_iff] using And.intro horder htop
  · exact (divisor completedRiemannXi (Metric.closedBall c |r|)).finiteSupport
      (isCompact_closedBall c |r|)

/-- Jensen's inequality converted from divisor multiplicity to the number of
distinct source nontrivial zeros in the smaller ball. -/
theorem sourceNontrivialZerosInClosedBall_ncard_le_of_xi_sphere_bound
    {c : ℂ} {r R M : ℝ} (hr : 0 < |r|) (hrR : |r| < |R|)
    (hM : 1 ≤ M) (hcenter : completedRiemannXi c ≠ 0)
    (hsphere : ∀ z ∈ Metric.sphere c |R|, ‖completedRiemannXi z‖ ≤ M) :
    ((sourceNontrivialZerosInClosedBall c r).ncard : ℝ) ≤
      Real.log (M / ‖completedRiemannXi c‖) / Real.log (R / r) := by
  calc
    ((sourceNontrivialZerosInClosedBall c r).ncard : ℝ) ≤
        ((Function.support
          (divisor completedRiemannXi (Metric.closedBall c |r|))).ncard : ℝ) := by
            exact_mod_cast
              sourceNontrivialZerosInClosedBall_ncard_le_xi_divisor_support c r
    _ ≤ ∑ᶠ u, divisor completedRiemannXi (Metric.closedBall c |r|) u := by
      let d := divisor completedRiemannXi (Metric.closedBall c |r|)
      have hfinite : (Function.support d).Finite :=
        d.finiteSupport (isCompact_closedBall c |r|)
      have hsum : ∑ᶠ z, d z = ∑ z ∈ hfinite.toFinset, d z :=
        finsum_eq_sum_of_support_subset d (by simpa using hfinite.coe_toFinset.le)
      have hcard : ((Function.support d).ncard : ℤ) ≤ ∑ᶠ z, d z := by
        calc
          ((Function.support d).ncard : ℤ) =
              ∑ _z ∈ hfinite.toFinset, (1 : ℤ) := by
                rw [Set.ncard_eq_toFinset_card _ hfinite]
                simp
          _ ≤ ∑ z ∈ hfinite.toFinset, d z := by
            gcongr with z hz
            have hzSupport : z ∈ Function.support d := hfinite.mem_toFinset.mp hz
            have hdNonneg : 0 ≤ d z :=
              (analyticOnNhd_completedRiemannXi _).divisor_nonneg z
            have hdNe : d z ≠ 0 := hzSupport
            omega
          _ = ∑ᶠ z, d z := hsum.symm
      exact_mod_cast hcard
    _ ≤ Real.log (M / ‖completedRiemannXi c‖) / Real.log (R / r) :=
      (analyticOnNhd_completedRiemannXi _).sum_divisor_le
        hr hrR hM hcenter hsphere

/-- The source symmetric-height window lies in the radius `T + 2` ball around
the Jensen base point `2`. -/
theorem sourceNontrivialZerosInSymmetricHeight_map_subset_closedBall_two
    {T : ℝ} :
    (fun z : sourceNontrivialZeroSet => z.1) ''
        sourceNontrivialZerosInSymmetricHeight T ⊆
      sourceNontrivialZerosInClosedBall 2 (T + 2) := by
  intro z hz
  rcases hz with ⟨w, hw, rfl⟩
  change |w.1.im| ≤ T at hw
  have hreSub : w.1.re - 2 ≤ 0 := by
    linarith [sourceNontrivialZero_re_lt_one w.2]
  refine ⟨?_, w.2⟩
  rw [Metric.mem_closedBall, dist_eq_norm]
  calc
    ‖w.1 - 2‖ ≤ |(w.1 - 2).re| + |(w.1 - 2).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ = 2 - w.1.re + |w.1.im| := by
      rw [Complex.sub_re, Complex.sub_im]
      norm_num
      rw [abs_of_nonpos hreSub]
      ring
    _ ≤ T + 2 := by
      linarith [sourceNontrivialZero_zero_lt_re w.2]

theorem sourceNontrivialZerosInSymmetricHeight_ncard_le_closedBall_two
    (T : ℝ) :
    (sourceNontrivialZerosInSymmetricHeight T).ncard ≤
      (sourceNontrivialZerosInClosedBall 2 (T + 2)).ncard := by
  refine Set.ncard_le_ncard_of_injOn
    (t := sourceNontrivialZerosInClosedBall 2 (T + 2))
    (fun z : sourceNontrivialZeroSet => z.1) ?_ ?_
    (sourceNontrivialZerosInClosedBall_finite 2 (T + 2))
  · intro z hz
    exact sourceNontrivialZerosInSymmetricHeight_map_subset_closedBall_two
      ⟨z, hz, rfl⟩
  · intro x _hx y _hy hxy
    exact Subtype.ext hxy

/-- A circle bound for xi around `2` directly controls the symmetric source
zero count. The remaining analytic task may therefore work only with xi. -/
theorem sourceNontrivialZerosInSymmetricHeight_ncard_le_of_xi_sphere_bound
    {T R M : ℝ} (hT : -2 < T) (hR : T + 2 < |R|)
    (hM : 1 ≤ M)
    (hsphere : ∀ z ∈ Metric.sphere (2 : ℂ) |R|,
      ‖completedRiemannXi z‖ ≤ M) :
    ((sourceNontrivialZerosInSymmetricHeight T).ncard : ℝ) ≤
      Real.log (M / ‖completedRiemannXi 2‖) /
        Real.log (R / (T + 2)) := by
  have hTtwo : 0 < T + 2 := by linarith
  calc
    ((sourceNontrivialZerosInSymmetricHeight T).ncard : ℝ) ≤
        ((sourceNontrivialZerosInClosedBall 2 (T + 2)).ncard : ℝ) := by
          exact_mod_cast
            sourceNontrivialZerosInSymmetricHeight_ncard_le_closedBall_two T
    _ ≤ Real.log (M / ‖completedRiemannXi 2‖) /
        Real.log (R / (T + 2)) :=
      sourceNontrivialZerosInClosedBall_ncard_le_of_xi_sphere_bound
        (by simpa [abs_of_pos hTtwo] using hTtwo)
        (by simpa [abs_of_pos hTtwo] using hR)
        hM completedRiemannXi_two_ne_zero hsphere

/-- Exponential xi growth on the circle of twice the counting radius gives a
source zero-count bound with the fixed Jensen denominator `log 2`. -/
theorem sourceNontrivialZerosInSymmetricHeight_ncard_le_of_xi_exp_sphere_bound
    {T G : ℝ} (hT : -2 < T) (hG : 0 ≤ G)
    (hsphere : ∀ z ∈ Metric.sphere (2 : ℂ) (2 * (T + 2)),
      ‖completedRiemannXi z‖ ≤ Real.exp G) :
    ((sourceNontrivialZerosInSymmetricHeight T).ncard : ℝ) ≤
      (G - Real.log ‖completedRiemannXi 2‖) / Real.log 2 := by
  have hTtwo : 0 < T + 2 := by linarith
  have hRadius : 0 < 2 * (T + 2) := mul_pos (by norm_num) hTtwo
  have hJensen :=
    sourceNontrivialZerosInSymmetricHeight_ncard_le_of_xi_sphere_bound
      hT (R := 2 * (T + 2)) (M := Real.exp G)
      (by rw [abs_of_pos hRadius]; linarith)
      (by simpa using Real.one_le_exp hG)
      (by simpa [abs_of_pos hRadius] using hsphere)
  have hxiNorm : ‖completedRiemannXi 2‖ ≠ 0 :=
    norm_ne_zero_iff.mpr completedRiemannXi_two_ne_zero
  calc
    ((sourceNontrivialZerosInSymmetricHeight T).ncard : ℝ) ≤
        Real.log (Real.exp G / ‖completedRiemannXi 2‖) /
          Real.log (2 * (T + 2) / (T + 2)) := hJensen
    _ = (G - Real.log ‖completedRiemannXi 2‖) / Real.log 2 := by
      rw [Real.log_div (Real.exp_ne_zero G) hxiNorm, Real.log_exp]
      congr 2
      field_simp

/-- Geometric xi circle growth with shell ratio below `4` is sufficient for
absolute convergence of a quadratically decaying source spectral sum. This
connects the sharp summability threshold directly to the Jensen consumer and
does not require the stronger Riemann--von Mangoldt asymptotic. -/
theorem sourceNontrivialZero_summable_of_xi_geometric_sphere_bounds
    (rho : ℂ) (f : sourceNontrivialZeroSet -> Real)
    (hf : forall z, 0 <= f z) {K B q : Real}
    (hB : 0 <= B) (hq : 0 <= q) (hq4 : q < 4)
    (hspheres : forall n : Nat, exists G : Real,
      0 <= G ∧
      (forall z, z ∈ Metric.sphere (2 : ℂ)
          (2 * (|rho.im| + (2 : Real) ^ (n + 1) + 2)) ->
        ‖completedRiemannXi z‖ <= Real.exp G) ∧
      (G - Real.log ‖completedRiemannXi 2‖) / Real.log 2 <= K * q ^ n)
    (hpoint : forall n (z : sourceNontrivialZeroDyadicShell rho n),
      f z <= B / ((2 : Real) ^ n) ^ 2) :
    Summable f := by
  apply sourceNontrivialZero_summable_of_symmetricHeight_geometric_bounds
    rho f hf hB hq hq4
  · intro n
    rcases hspheres n with ⟨G, hG, hsphere, hnormalized⟩
    exact (sourceNontrivialZerosInSymmetricHeight_ncard_le_of_xi_exp_sphere_bound
      (T := |rho.im| + (2 : Real) ^ (n + 1))
      (by
        have him : 0 <= |rho.im| := abs_nonneg _
        have hpow : 0 < (2 : Real) ^ (n + 1) := pow_pos (by norm_num) _
        linarith)
      hG hsphere).trans hnormalized
  · exact hpoint

/-- It is enough to prove the geometric xi majorants on right-half-plane
balls. The xi functional equation folds each Jensen-circle point into this
domain; the radius budget is the circle radius, plus two for its center and
one for the fold. -/
theorem sourceNontrivialZero_summable_of_xi_right_halfplane_ball_bounds
    (rho : ℂ) (f : sourceNontrivialZeroSet -> Real)
    (hf : forall z, 0 <= f z) {K B q : Real}
    (hB : 0 <= B) (hq : 0 <= q) (hq4 : q < 4)
    (hballs : forall n : Nat, exists G : Real,
      0 <= G ∧
      (forall w : ℂ, (1 / 2 : Real) <= w.re ->
        ‖w‖ <= 2 * (|rho.im| + (2 : Real) ^ (n + 1) + 2) + 3 ->
        ‖completedRiemannXi w‖ <= Real.exp G) ∧
      (G - Real.log ‖completedRiemannXi 2‖) / Real.log 2 <= K * q ^ n)
    (hpoint : forall n (z : sourceNontrivialZeroDyadicShell rho n),
      f z <= B / ((2 : Real) ^ n) ^ 2) :
    Summable f := by
  apply sourceNontrivialZero_summable_of_xi_geometric_sphere_bounds
    rho f hf hB hq hq4
  · intro n
    rcases hballs n with ⟨G, hG, hball, hnormalized⟩
    refine ⟨G, hG, ?_, hnormalized⟩
    intro z hz
    rcases exists_half_le_re_norm_le_add_one_and_norm_completedRiemannXi_eq z with
      ⟨w, hwRe, hwNorm, hxiNorm⟩
    rw [← hxiNorm]
    apply hball w hwRe
    have hzDist : dist z 2 =
        2 * (|rho.im| + (2 : Real) ^ (n + 1) + 2) := by
      rw [dist_eq_norm]
      simpa [Metric.mem_sphere] using hz
    have hzNorm : ‖z‖ <=
        2 * (|rho.im| + (2 : Real) ^ (n + 1) + 2) + 2 := by
      calc
        ‖z‖ = dist z 0 := (dist_zero_right z).symm
        _ <= dist z 2 + dist 2 0 := dist_triangle _ _ _
        _ = 2 * (|rho.im| + (2 : Real) ^ (n + 1) + 2) + 2 := by
          rw [hzDist]
          norm_num
    linarith
  · exact hpoint

end CC20ZetaCounting
end Source
end ConnesWeilRH
