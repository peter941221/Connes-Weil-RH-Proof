/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.CC20YoshidaNearZeros
import Mathlib.Analysis.Complex.JensenFormula

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

end CC20ZetaCounting
end Source
end ConnesWeilRH
