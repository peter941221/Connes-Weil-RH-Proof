/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import Mathlib

/-!
# Kolmogorov ceiling: the real-analysis engine of record 1692's Theorem D

Record 1692 decides the committed MP carrier negatively (`N^p[e^{i gamma}]
= {0}` for every `p`, lambda-uniform, no epsilon-gap).  Its proof combines
two paper-level inputs (cited there, not formalized here) with one pure
real-analysis engine, which is what THIS brick machine-checks:

* paper input 1 (MP 2010 basic criterion): carrier nonemptiness gives a
  representation `gamma = u - alpha` with `alpha` monotone and `u` a
  conjugate function, for which the paper's Kolmogorov estimate
  `Pi{|u| > A} = o(1/A)` holds (`dPi = dt/(1+t^2)`).
* paper input 2 (Stirling tail growth): the committed phase satisfies
  `gamma x <= -c |x| log |x|` on the left tail for some `c > 0`.
* THIS BRICK (`kolmogorov_ceiling`): no phase with a superlinear left
  tail admits such a representation.  Contradiction — hence the carrier
  is empty.

Contents:

* `poissonDensity` / `poissonMass` : the Poisson measure `dPi = dt/(1+t^2)`
  as a `lintegral` against Lebesgue volume on `R`.
* `KolmogorovAdmissible` : the concrete `O(1/A)` superlevel-set bound —
  exactly the property of the conjugate function used by Theorem D.
* `poissonMass_Ioc_ge` : the explicit half-line mass floor
  `Pi((-2Y, -Y]) >= 1/(5Y)` for `Y >= 1`.
* `kolmogorov_ceiling` : if `gamma = u - alpha` with `alpha` monotone and
  `u` Kolmogorov-admissible, then `gamma` cannot satisfy
  `gamma x <= -c |x| log |x|` for all `x <= -X_0` with `c > 0`.

The mechanism: on the interval `(-2Y, -Y]` (with `Y = A/10` chosen deep
enough in the tail) monotonicity of `alpha` bounds it above by `alpha(-1)`,
so `u = gamma + alpha` is at most `-(c |x| log |x|) + O(1)`, hence
`|u| >= A` on the whole interval; the interval carries Poisson mass at
least `1/(5Y) = 2/A`, contradicting the `1/A` ceiling.  (Monotonicity is
used only through the single constant `alpha(-1)`; no regularity of
`gamma` is used — the tail bound alone drives the estimate.)
-/

namespace ConnesWeilRH.Dev.C1G9R2KolmogorovCeiling

open MeasureTheory Real Set

/-- Poisson density `dPi = dt/(1 + t^2)` (Makarov–Poltoratski 2010). -/
noncomputable def poissonDensity (t : ℝ) : ENNReal :=
  ENNReal.ofReal (1 / (1 + t * t))

theorem measurable_poissonDensity : Measurable poissonDensity := by
  unfold poissonDensity
  exact Measurable.ennreal_ofReal (by measurability)

/-- The `Pi`-mass of a set: the Lebesgue integral of the Poisson density. -/
noncomputable def poissonMass (s : Set ℝ) : ENNReal :=
  ∫⁻ x in s, poissonDensity x ∂volume

/-- Concrete Kolmogorov admissibility: the `Pi`-mass of the superlevel
sets of `u` is `O(1/A)` — the property MP 2010's estimate eq. (kol)
gives for the conjugate function `h~` of an `L^1_Pi` perturbation. -/
def KolmogorovAdmissible (u : ℝ → ℝ) : Prop :=
  ∃ A₀ : ℝ, 0 < A₀ ∧ ∀ A : ℝ, A₀ ≤ A →
    poissonMass {x : ℝ | A ≤ |u x|} ≤ ENNReal.ofReal (1 / A)

/-- Half-line mass floor: for `Y >= 1` the Poisson mass of the interval
`(-2Y, -Y]` is at least `1/(5Y)` (restrict to `|x| <= 2Y`, where the
density is at least `1/(1 + 4Y^2)`, and use Lebesgue measure `Y`). -/
theorem poissonMass_Ioc_ge (Y : ℝ) (hY : 1 ≤ Y) :
    ENNReal.ofReal (1 / (5 * Y)) ≤ poissonMass (Ioc (-2 * Y) (-Y)) := by
  have hYpos : (0 : ℝ) < Y := by linarith
  -- pointwise density floor on the interval
  have hdom : ∀ x ∈ Ioc (-2 * Y) (-Y),
      ENNReal.ofReal (1 / (1 + 4 * Y * Y)) ≤ poissonDensity x := by
    intro x hx
    obtain ⟨hx0, hx1⟩ := hx
    have hsq : x * x ≤ 4 * Y * Y := by
      have hp := mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * Y - x)
        (by linarith : (0 : ℝ) ≤ 2 * Y + x)
      nlinarith
    have hinv : (1 : ℝ) / (1 + 4 * Y * Y) ≤ 1 / (1 + x * x) := by
      field_simp
      linarith [hsq]
    exact ENNReal.ofReal_le_ofReal hinv
  -- the lower bound via indicator functions (pointwise everywhere)
  have hpt : ∀ x : ℝ, (Ioc (-2 * Y) (-Y)).indicator
      (fun _ : ℝ => ENNReal.ofReal (1 / (1 + 4 * Y * Y))) x
      ≤ (Ioc (-2 * Y) (-Y)).indicator poissonDensity x := by
    intro x
    by_cases hx : x ∈ Ioc (-2 * Y) (-Y)
    · simp only [hx, Set.indicator_of_mem]
      exact hdom x hx
    · simp only [Set.indicator_of_notMem hx]
      exact le_refl 0
  have hL : ∫⁻ x, (Ioc (-2 * Y) (-Y)).indicator
      (fun _ : ℝ => ENNReal.ofReal (1 / (1 + 4 * Y * Y))) x ∂volume
      = ∫⁻ x in Ioc (-2 * Y) (-Y), ENNReal.ofReal (1 / (1 + 4 * Y * Y)) ∂volume :=
    lintegral_indicator (measurableSet_Ioc)
      (fun _ : ℝ => ENNReal.ofReal (1 / (1 + 4 * Y * Y)))
  have hR : ∫⁻ x, (Ioc (-2 * Y) (-Y)).indicator poissonDensity x ∂volume
      = poissonMass (Ioc (-2 * Y) (-Y)) := by
    rw [lintegral_indicator (measurableSet_Ioc) poissonDensity]
    rfl
  have hstep2 : ∫⁻ x in Ioc (-2 * Y) (-Y),
      ENNReal.ofReal (1 / (1 + 4 * Y * Y)) ∂volume
      ≤ poissonMass (Ioc (-2 * Y) (-Y)) := by
    calc ∫⁻ x in Ioc (-2 * Y) (-Y), ENNReal.ofReal (1 / (1 + 4 * Y * Y)) ∂volume
        = ∫⁻ x, (Ioc (-2 * Y) (-Y)).indicator
            (fun _ : ℝ => ENNReal.ofReal (1 / (1 + 4 * Y * Y))) x ∂volume := hL.symm
      _ ≤ ∫⁻ x, (Ioc (-2 * Y) (-Y)).indicator poissonDensity x ∂volume :=
          lintegral_mono hpt
      _ = poissonMass (Ioc (-2 * Y) (-Y)) := hR
  -- constant mass over an interval of length Y
  have hvol : volume (Ioc (-2 * Y) (-Y)) = ENNReal.ofReal Y := by
    rw [Real.volume_Ioc]
    congr 1
    linarith
  have hconst : ∫⁻ x in Ioc (-2 * Y) (-Y),
      ENNReal.ofReal (1 / (1 + 4 * Y * Y)) ∂volume
      = ENNReal.ofReal ((1 / (1 + 4 * Y * Y)) * Y) := by
    rw [setLIntegral_const, hvol, ENNReal.ofReal_mul (by positivity)]
  -- the arithmetic: (1/(1+4Y^2)) * Y >= 1/(5Y) for Y >= 1
  have hYY : (1 : ℝ) ≤ Y * Y := by nlinarith
  have hnum : (1 / (1 + 4 * Y * Y)) * Y ≥ 1 / (5 * Y) := by
    field_simp
    linarith
  calc ENNReal.ofReal (1 / (5 * Y))
      ≤ ENNReal.ofReal ((1 / (1 + 4 * Y * Y)) * Y) := ENNReal.ofReal_le_ofReal hnum
    _ = ∫⁻ x in Ioc (-2 * Y) (-Y), ENNReal.ofReal (1 / (1 + 4 * Y * Y)) ∂volume :=
        hconst.symm
    _ ≤ poissonMass (Ioc (-2 * Y) (-Y)) := hstep2

/-- **The Kolmogorov ceiling** (record 1692's engine).  If `gamma = u - alpha`
with `alpha` monotone and `u` Kolmogorov-admissible (superlevel `Pi`-mass
`O(1/A)`), then `gamma` cannot decay superlinearly on the left tail:
`gamma x <= -c |x| log |x|` for `x <= -X_0` with `c > 0` is impossible.

With MP 2010's basic criterion (the carrier gives such a representation
with `u` a conjugate function) and the Stirling tail growth of the
committed phase, this is the contradiction behind Theorem D. -/
theorem kolmogorov_ceiling
    (γ α u : ℝ → ℝ) (c : ℝ) (hc : 0 < c)
    (hmono : Monotone α)
    (hrep : ∀ x, γ x = u x - α x)
    (hkol : KolmogorovAdmissible u)
    (htail : ∃ X₀ : ℝ, ∀ x : ℝ, x ≤ -X₀ → γ x ≤ -c * |x| * Real.log |x|) :
    False := by
  obtain ⟨A₀, hA₀pos, hkol⟩ := hkol
  obtain ⟨X₀, hX₀⟩ := htail
  set c₂ := α (-1) with hc₂
  have hαle : ∀ x ≤ -1, α x ≤ c₂ := fun x hx => hmono hx
  set A := max A₀ (max (10 * max 1 (max X₀ |c₂|)) (10 * Real.exp (20 / c))) with hAdef
  set Y := A / 10 with hYdef
  have hA10 : (10 : ℝ) ≤ A := by
    rw [hAdef]
    have h1' : (10 : ℝ) ≤ 10 * max 1 (max X₀ |c₂|) := by
      have h := mul_le_mul_of_nonneg_left (le_max_left (1 : ℝ) (max X₀ |c₂|))
        (by norm_num : (0 : ℝ) ≤ 10)
      rwa [mul_one] at h
    have h2' : (10 : ℝ) * max 1 (max X₀ |c₂|)
        ≤ max (10 * max 1 (max X₀ |c₂|)) (10 * Real.exp (20 / c)) :=
      le_max_left _ _
    have h3' : max (10 * max 1 (max X₀ |c₂|)) (10 * Real.exp (20 / c))
        ≤ max A₀ (max (10 * max 1 (max X₀ |c₂|)) (10 * Real.exp (20 / c))) :=
      le_max_right _ _
    exact le_trans (le_trans h1' h2') h3'
  have hA₀ : A₀ ≤ A := le_max_left _ _
  have hX0t : (10 : ℝ) * X₀ ≤ A := by
    rw [hAdef]
    have h1 : X₀ ≤ max 1 (max X₀ |c₂|) := le_trans (le_max_left _ _) (le_max_right _ _)
    exact le_trans (mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 10))
      (le_trans (le_max_left _ _) (le_max_right _ _))
  have hY1 : (1 : ℝ) ≤ Y := by rw [hYdef]; linarith
  have hYX : X₀ ≤ Y := by rw [hYdef]; linarith
  have hAt : |c₂| ≤ A := by
    rw [hAdef]
    have h1 : |c₂| ≤ max 1 (max X₀ |c₂|) :=
      le_trans (le_max_right X₀ |c₂|) (le_max_right 1 (max X₀ |c₂|))
    have hM : (0 : ℝ) ≤ max 1 (max X₀ |c₂|) := by positivity
    have h4 : |c₂| ≤ 10 * max 1 (max X₀ |c₂|) := by linarith [h1, hM]
    have h5 : (10 : ℝ) * max 1 (max X₀ |c₂|)
        ≤ max (10 * max 1 (max X₀ |c₂|)) (10 * Real.exp (20 / c)) :=
      le_max_left _ _
    have h6 : max (10 * max 1 (max X₀ |c₂|)) (10 * Real.exp (20 / c))
        ≤ max A₀ (max (10 * max 1 (max X₀ |c₂|)) (10 * Real.exp (20 / c))) :=
      le_max_right _ _
    exact le_trans (le_trans h4 h5) h6
  have hAexp : (10 : ℝ) * Real.exp (20 / c) ≤ A := by
    rw [hAdef]
    have h7 : (10 : ℝ) * Real.exp (20 / c)
        ≤ max (10 * max 1 (max X₀ |c₂|)) (10 * Real.exp (20 / c)) :=
      le_max_right _ _
    have h8 : max (10 * max 1 (max X₀ |c₂|)) (10 * Real.exp (20 / c))
        ≤ max A₀ (max (10 * max 1 (max X₀ |c₂|)) (10 * Real.exp (20 / c))) :=
      le_max_right _ _
    exact le_trans h7 h8
  have hlogY : (20 : ℝ) / c ≤ Real.log Y := by
    have h1 : Real.exp (20 / c) ≤ A / 10 := by linarith
    have h2 := Real.log_le_log (Real.exp_pos (20 / c)) h1
    rwa [Real.log_exp] at h2
  have hYlog : (2 : ℝ) * A ≤ c * Y * Real.log Y := by
    have h1 : c * Y * (20 / c) ≤ c * Y * Real.log Y :=
      mul_le_mul_of_nonneg_left hlogY (mul_nonneg hc.le (by linarith))
    have h2 : c * Y * (20 / c) = 2 * A := by
      rw [hYdef]
      field_simp
      norm_num
    linarith
  -- deep in the left tail, |u| >= A on all of (-2Y, -Y]
  have hkey : ∀ x : ℝ, x ≤ -Y → A ≤ |u x| := by
    intro x hx
    have hx0 : x ≤ 0 := by linarith
    have hxY : Y ≤ |x| := by rw [abs_of_nonpos hx0]; linarith
    have hxX₀ : x ≤ -X₀ := by linarith
    have hx1 : x ≤ -1 := by linarith
    have hγ : γ x ≤ -c * |x| * Real.log |x| := hX₀ x hxX₀
    have hα : α x ≤ c₂ := hαle x hx1
    have hlogx : (0 : ℝ) ≤ Real.log |x| := Real.log_nonneg (by linarith)
    have hlogxy : Real.log Y ≤ Real.log |x| := Real.log_le_log (by linarith) hxY
    have hbig : (2 : ℝ) * A ≤ c * |x| * Real.log |x| := by
      have ha : c * Y ≤ c * |x| := mul_le_mul_of_nonneg_left hxY hc.le
      have hb1 : c * Y * Real.log Y ≤ c * Y * Real.log |x| :=
        mul_le_mul_of_nonneg_left hlogxy (mul_nonneg hc.le (by linarith))
      have hb2 : c * Y * Real.log |x| ≤ c * |x| * Real.log |x| :=
        mul_le_mul_of_nonneg_right ha hlogx
      linarith [hYlog, hb1, hb2]
    have hux : u x = γ x + α x := by rw [hrep x]; ring
    have hneg : u x ≤ -A := by
      linarith [hγ, hα, hux, hbig, le_abs_self c₂]
    have hunn : u x ≤ 0 := by linarith
    rw [abs_of_nonpos hunn]
    linarith
  -- the contradiction chain
  have hsub : Ioc (-2 * Y) (-Y) ⊆ {x : ℝ | A ≤ |u x|} := fun x hx => hkey x hx.2
  have hchain : ENNReal.ofReal (1 / (5 * Y)) ≤ ENNReal.ofReal (1 / A) := by
    calc ENNReal.ofReal (1 / (5 * Y))
        ≤ poissonMass (Ioc (-2 * Y) (-Y)) := poissonMass_Ioc_ge Y hY1
      _ ≤ poissonMass {x : ℝ | A ≤ |u x|} := lintegral_mono_set hsub
      _ ≤ ENNReal.ofReal (1 / A) := hkol A hA₀
  have hApos : (0 : ℝ) < A := by linarith
  have hreal : (1 : ℝ) / (5 * Y) ≤ 1 / A :=
    (ENNReal.ofReal_le_ofReal_iff (div_nonneg zero_le_one hApos.le)).mp hchain
  rw [hYdef] at hreal
  field_simp at hreal
  linarith

end ConnesWeilRH.Dev.C1G9R2KolmogorovCeiling
