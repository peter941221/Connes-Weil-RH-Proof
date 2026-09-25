/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/
import Mathlib
import ConnesWeilRH.Dev.C1GevreyVerticalDecayRung2

/-!
# Gevrey window — brick 2, rung 3: three integration by parts, explicit constants

Rung 2 (`C1GevreyVerticalDecayRung2`) landed the `1 / |w|^2` run.  This module
lands rung 3: the third integration by parts, boundary terms killed by
`gevreyDeriv2 k (±1) = 0` (brick 2), gives

* `laplace_abs_le_rung3`:
  `|∫_{-1}^{1} phi_k(u) e^{w u} du| ≤ e^{|Re w|} * M3(k) / |w|^3`;
* `laplace_abs_le_rung3_vertical`: at `w = a t I` the strip factor is `1`,
  so the bound is `M3(k) / (a |t|)^3`,

where `M3(k) = e^{-k} (9500 k^3 + 19400 k^2 + 6500 k) + 2196115 k^-4
+ 16470860 k^-5 + 19765032 k^-6`.

Constant provenance (checked against 40-dps numerics in the record script):
`phi''' = e^{-k/s} (12 k^2 u s^-4 - 8 k^3 u^3 s^-6 + 48 k^2 u^3 s^-5
- 24 k u s^-3 - 48 k u^3 s^-4)`, `s = 1 - u^2`, and it is ODD in `u` — so
unlike rung 2 the sign on `[5/6, 1)` is NOT fixed for all `k ≥ 1` (at `k = 1`
it flips from positive to negative inside the arc; the rung-2 FTC-exact
outer-mass trick is dropped).  Instead the outer pieces are handled by the
SEVEN-power trade `e^{-k/s} = (e^{-k/(7s)})^7 ≤ (7s/k)^7`: the `s^-6` term of
`phi'''` absorbs six powers of `s` and one survives, so the universal bound
(`abs_gevreyDeriv3_le_septic`) still vanishes at `|u| = 1` and the continuity
glue closes.  The middle `|u| ≤ 5/6` uses the `e^{-k}` cap (attained at
`u = 0`); rational constant bounds give the integer coefficients above
(`(1/3)·7^7·60 = 16470860` and `(1/3)·7^7·72 = 19765032` are exact).

Rungs `n ≥ 4` and the optimized-`n` sqrt law stay priced remainder.
-/

open Real Set Filter Topology MeasureTheory

private lemma sq_lt_one_of_abs_lt_one {u : ℝ} (h : |u| < 1) : u ^ 2 < 1 := by
  obtain ⟨h2, h3⟩ := abs_lt.mp h
  nlinarith [h2, h3]

/-- Triangle inequality for the five-term bracket of `phi'''`, with the
absolute values pushed onto `u`. -/
private lemma abs_sum5_le (k u : ℝ) (hk : (0 : ℝ) < k) (hs : (0 : ℝ) < 1 - u ^ 2) :
    |(12 * k ^ 2 * u / (1 - u ^ 2) ^ 4 - 8 * k ^ 3 * u ^ 3 / (1 - u ^ 2) ^ 6
        + 48 * k ^ 2 * u ^ 3 / (1 - u ^ 2) ^ 5 - 24 * k * u / (1 - u ^ 2) ^ 3
        - 48 * k * u ^ 3 / (1 - u ^ 2) ^ 4)|
      ≤ 12 * k ^ 2 * |u| / (1 - u ^ 2) ^ 4 + 8 * k ^ 3 * |u| ^ 3 / (1 - u ^ 2) ^ 6
        + 48 * k ^ 2 * |u| ^ 3 / (1 - u ^ 2) ^ 5 + 24 * k * |u| / (1 - u ^ 2) ^ 3
        + 48 * k * |u| ^ 3 / (1 - u ^ 2) ^ 4 := by
  have h12b : |12 * k ^ 2 * u / (1 - u ^ 2) ^ 4 - 8 * k ^ 3 * u ^ 3 / (1 - u ^ 2) ^ 6|
      ≤ |12 * k ^ 2 * u / (1 - u ^ 2) ^ 4|
        + |8 * k ^ 3 * u ^ 3 / (1 - u ^ 2) ^ 6| := by
    have h := abs_add_le (12 * k ^ 2 * u / (1 - u ^ 2) ^ 4)
      (-8 * k ^ 3 * u ^ 3 / (1 - u ^ 2) ^ 6)
    have hneg : (-8 : ℝ) * k ^ 3 * u ^ 3 / (1 - u ^ 2) ^ 6
        = -(8 * k ^ 3 * u ^ 3 / (1 - u ^ 2) ^ 6) := by ring
    rw [show (12 * k ^ 2 * u / (1 - u ^ 2) ^ 4 + -8 * k ^ 3 * u ^ 3 / (1 - u ^ 2) ^ 6)
        = 12 * k ^ 2 * u / (1 - u ^ 2) ^ 4 - 8 * k ^ 3 * u ^ 3 / (1 - u ^ 2) ^ 6 from by ring,
      hneg, abs_neg] at h
    exact h
  have h123 : |12 * k ^ 2 * u / (1 - u ^ 2) ^ 4 - 8 * k ^ 3 * u ^ 3 / (1 - u ^ 2) ^ 6
        + 48 * k ^ 2 * u ^ 3 / (1 - u ^ 2) ^ 5|
      ≤ |12 * k ^ 2 * u / (1 - u ^ 2) ^ 4 - 8 * k ^ 3 * u ^ 3 / (1 - u ^ 2) ^ 6|
        + |48 * k ^ 2 * u ^ 3 / (1 - u ^ 2) ^ 5| :=
    abs_add_le (12 * k ^ 2 * u / (1 - u ^ 2) ^ 4 - 8 * k ^ 3 * u ^ 3 / (1 - u ^ 2) ^ 6)
      (48 * k ^ 2 * u ^ 3 / (1 - u ^ 2) ^ 5)
  have h1234 : |12 * k ^ 2 * u / (1 - u ^ 2) ^ 4 - 8 * k ^ 3 * u ^ 3 / (1 - u ^ 2) ^ 6
        + 48 * k ^ 2 * u ^ 3 / (1 - u ^ 2) ^ 5 - 24 * k * u / (1 - u ^ 2) ^ 3|
      ≤ |12 * k ^ 2 * u / (1 - u ^ 2) ^ 4 - 8 * k ^ 3 * u ^ 3 / (1 - u ^ 2) ^ 6
        + 48 * k ^ 2 * u ^ 3 / (1 - u ^ 2) ^ 5|
        + |24 * k * u / (1 - u ^ 2) ^ 3| := by
    have h := abs_add_le (12 * k ^ 2 * u / (1 - u ^ 2) ^ 4 - 8 * k ^ 3 * u ^ 3 / (1 - u ^ 2) ^ 6
        + 48 * k ^ 2 * u ^ 3 / (1 - u ^ 2) ^ 5) (-24 * k * u / (1 - u ^ 2) ^ 3)
    have hneg : (-24 : ℝ) * k * u / (1 - u ^ 2) ^ 3
        = -(24 * k * u / (1 - u ^ 2) ^ 3) := by ring
    rw [show (12 * k ^ 2 * u / (1 - u ^ 2) ^ 4 - 8 * k ^ 3 * u ^ 3 / (1 - u ^ 2) ^ 6
          + 48 * k ^ 2 * u ^ 3 / (1 - u ^ 2) ^ 5 + -24 * k * u / (1 - u ^ 2) ^ 3)
        = 12 * k ^ 2 * u / (1 - u ^ 2) ^ 4 - 8 * k ^ 3 * u ^ 3 / (1 - u ^ 2) ^ 6
          + 48 * k ^ 2 * u ^ 3 / (1 - u ^ 2) ^ 5 - 24 * k * u / (1 - u ^ 2) ^ 3 from by ring,
      hneg, abs_neg] at h
    exact h
  have hgoal : |12 * k ^ 2 * u / (1 - u ^ 2) ^ 4 - 8 * k ^ 3 * u ^ 3 / (1 - u ^ 2) ^ 6
        + 48 * k ^ 2 * u ^ 3 / (1 - u ^ 2) ^ 5 - 24 * k * u / (1 - u ^ 2) ^ 3
        - 48 * k * u ^ 3 / (1 - u ^ 2) ^ 4|
      ≤ |12 * k ^ 2 * u / (1 - u ^ 2) ^ 4 - 8 * k ^ 3 * u ^ 3 / (1 - u ^ 2) ^ 6
        + 48 * k ^ 2 * u ^ 3 / (1 - u ^ 2) ^ 5 - 24 * k * u / (1 - u ^ 2) ^ 3|
        + |48 * k * u ^ 3 / (1 - u ^ 2) ^ 4| := by
    have h := abs_add_le (12 * k ^ 2 * u / (1 - u ^ 2) ^ 4 - 8 * k ^ 3 * u ^ 3 / (1 - u ^ 2) ^ 6
        + 48 * k ^ 2 * u ^ 3 / (1 - u ^ 2) ^ 5 - 24 * k * u / (1 - u ^ 2) ^ 3)
      (-48 * k * u ^ 3 / (1 - u ^ 2) ^ 4)
    have hneg : (-48 : ℝ) * k * u ^ 3 / (1 - u ^ 2) ^ 4
        = -(48 * k * u ^ 3 / (1 - u ^ 2) ^ 4) := by ring
    rw [show (12 * k ^ 2 * u / (1 - u ^ 2) ^ 4 - 8 * k ^ 3 * u ^ 3 / (1 - u ^ 2) ^ 6
          + 48 * k ^ 2 * u ^ 3 / (1 - u ^ 2) ^ 5 - 24 * k * u / (1 - u ^ 2) ^ 3
          + -48 * k * u ^ 3 / (1 - u ^ 2) ^ 4)
        = 12 * k ^ 2 * u / (1 - u ^ 2) ^ 4 - 8 * k ^ 3 * u ^ 3 / (1 - u ^ 2) ^ 6
          + 48 * k ^ 2 * u ^ 3 / (1 - u ^ 2) ^ 5 - 24 * k * u / (1 - u ^ 2) ^ 3
          - 48 * k * u ^ 3 / (1 - u ^ 2) ^ 4 from by ring,
      hneg, abs_neg] at h
    exact h
  have ha1 : |12 * k ^ 2 * u / (1 - u ^ 2) ^ 4| = 12 * k ^ 2 * |u| / (1 - u ^ 2) ^ 4 := by
    rw [abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 12 * k ^ 2),
      abs_of_pos (pow_pos hs 4)]
  have ha2 : |8 * k ^ 3 * u ^ 3 / (1 - u ^ 2) ^ 6| = 8 * k ^ 3 * |u| ^ 3 / (1 - u ^ 2) ^ 6 := by
    rw [abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 8 * k ^ 3), abs_pow,
      abs_of_pos (pow_pos hs 6)]
  have ha3 : |48 * k ^ 2 * u ^ 3 / (1 - u ^ 2) ^ 5|
      = 48 * k ^ 2 * |u| ^ 3 / (1 - u ^ 2) ^ 5 := by
    rw [abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 48 * k ^ 2), abs_pow,
      abs_of_pos (pow_pos hs 5)]
  have ha4 : |24 * k * u / (1 - u ^ 2) ^ 3| = 24 * k * |u| / (1 - u ^ 2) ^ 3 := by
    rw [abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 24 * k),
      abs_of_pos (pow_pos hs 3)]
  have ha5 : |48 * k * u ^ 3 / (1 - u ^ 2) ^ 4| = 48 * k * |u| ^ 3 / (1 - u ^ 2) ^ 4 := by
    rw [abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 48 * k), abs_pow,
      abs_of_pos (pow_pos hs 4)]
  linarith

/-- The interior third-derivative formula of `gevreyInner k`, extended by `0`. -/
noncomputable def gevreyDeriv3 (k u : ℝ) : ℝ :=
  if |u| < 1 then
    Real.exp (-k / (1 - u ^ 2)) *
      (12 * k ^ 2 * u / (1 - u ^ 2) ^ 4 - 8 * k ^ 3 * u ^ 3 / (1 - u ^ 2) ^ 6
        + 48 * k ^ 2 * u ^ 3 / (1 - u ^ 2) ^ 5 - 24 * k * u / (1 - u ^ 2) ^ 3
        - 48 * k * u ^ 3 / (1 - u ^ 2) ^ 4)
  else 0

lemma gevreyDeriv3_of_abs_lt (k u : ℝ) (h : |u| < 1) :
    gevreyDeriv3 k u =
      Real.exp (-k / (1 - u ^ 2)) *
      (12 * k ^ 2 * u / (1 - u ^ 2) ^ 4 - 8 * k ^ 3 * u ^ 3 / (1 - u ^ 2) ^ 6
        + 48 * k ^ 2 * u ^ 3 / (1 - u ^ 2) ^ 5 - 24 * k * u / (1 - u ^ 2) ^ 3
        - 48 * k * u ^ 3 / (1 - u ^ 2) ^ 4) := by
  simp only [gevreyDeriv3, if_pos h]

lemma gevreyDeriv3_of_one_le_abs (k u : ℝ) (h : 1 ≤ |u|) :
    gevreyDeriv3 k u = 0 := by
  simp only [gevreyDeriv3, if_neg (not_lt.mpr h)]

/-- The chain rule: on the interior, `gevreyDeriv2 k` has derivative
`gevreyDeriv3 k`. -/
lemma gevreyDeriv2_hasDerivAt_of_abs_lt (k u : ℝ) (hk : 0 < k) (h : |u| < 1) :
    HasDerivAt (gevreyDeriv2 k) (gevreyDeriv3 k u) u := by
  have hu2 : u ^ 2 < 1 := sq_lt_one_of_abs_lt_one h
  have hs : (0 : ℝ) < 1 - u ^ 2 := by linarith
  have hne : (1 : ℝ) - u ^ 2 ≠ 0 := ne_of_gt hs
  -- base: d/dv (1 - v^2) = -2 u at u
  have hsq : HasDerivAt (fun v : ℝ => (1 : ℝ) - v ^ 2) (-2 * u) u := by
    have h2 : HasDerivAt (fun v : ℝ => v * v) ((1 : ℝ) * u + u * 1) u :=
      HasDerivAt.mul (hasDerivAt_id u) (hasDerivAt_id u)
    rw [show ((1 : ℝ) * u + u * 1) = 2 * u from by ring] at h2
    have h3 : (fun v : ℝ => v * v) = fun v : ℝ => v ^ 2 := by funext v; ring
    rw [h3] at h2
    have h4 : HasDerivAt (fun v : ℝ => (1 : ℝ) - v ^ 2) ((0 : ℝ) - 2 * u) u :=
      HasDerivAt.sub (hasDerivAt_const u (1 : ℝ)) h2
    rwa [show ((0 : ℝ) - 2 * u) = -2 * u from by ring] at h4
  -- A(v) = -k / (1 - v^2),  A'(u) = -2 k u / (1 - u^2)^2
  have hA0 : HasDerivAt (fun v : ℝ => -k / (1 - v ^ 2))
      ((0 * (1 - u ^ 2) - -k * (-2 * u)) / (1 - u ^ 2) ^ 2) u :=
    HasDerivAt.div (hasDerivAt_const u (-k)) hsq hne
  have hAval : ((0 : ℝ) * (1 - u ^ 2) - -k * (-2 * u)) / (1 - u ^ 2) ^ 2
      = -2 * k * u / (1 - u ^ 2) ^ 2 := by
    ring
  rw [hAval] at hA0
  -- (e^A)' = e^A * A'
  have hE1 : HasDerivAt (fun v : ℝ => Real.exp (-k / (1 - v ^ 2)))
      (Real.exp (-k / (1 - u ^ 2)) * (-2 * k * u / (1 - u ^ 2) ^ 2)) u := by
    simpa [Function.comp] using
      HasDerivAt.comp u (Real.hasDerivAt_exp (-k / (1 - u ^ 2))) hA0
  -- powers of the denominator: (1-v^2)^2, ^3, ^4 (ascription keeps the
  -- function beta-reduced so the funext rewrite can fire)
  have hfe2 : (fun v : ℝ => (1 - v ^ 2) * (1 - v ^ 2))
      = fun v : ℝ => (1 - v ^ 2) ^ 2 := by
    funext v; ring
  have hS2 : HasDerivAt (fun v : ℝ => (1 - v ^ 2) * (1 - v ^ 2))
      ((-2 * u) * (1 - u ^ 2) + (1 - u ^ 2) * (-2 * u)) u :=
    HasDerivAt.mul hsq hsq
  rw [hfe2] at hS2
  rw [show ((-2 * u) * (1 - u ^ 2) + (1 - u ^ 2) * (-2 * u))
      = 2 * (1 - u ^ 2) * (-2 * u) from by ring] at hS2
  have hfe3 : (fun v : ℝ => (1 - v ^ 2) ^ 2 * (1 - v ^ 2))
      = fun v : ℝ => (1 - v ^ 2) ^ 3 := by
    funext v; ring
  have hS3 : HasDerivAt (fun v : ℝ => (1 - v ^ 2) ^ 2 * (1 - v ^ 2))
      ((2 * (1 - u ^ 2) * (-2 * u)) * (1 - u ^ 2) + (1 - u ^ 2) ^ 2 * (-2 * u)) u :=
    HasDerivAt.mul hS2 hsq
  rw [hfe3] at hS3
  rw [show (2 * (1 - u ^ 2) * (-2 * u)) * (1 - u ^ 2)
        + (1 - u ^ 2) ^ 2 * (-2 * u) = 3 * (1 - u ^ 2) ^ 2 * (-2 * u) from by ring] at hS3
  have hfe4 : (fun v : ℝ => (1 - v ^ 2) ^ 3 * (1 - v ^ 2))
      = fun v : ℝ => (1 - v ^ 2) ^ 4 := by
    funext v; ring
  have hS4 : HasDerivAt (fun v : ℝ => (1 - v ^ 2) ^ 3 * (1 - v ^ 2))
      ((3 * (1 - u ^ 2) ^ 2 * (-2 * u)) * (1 - u ^ 2) + (1 - u ^ 2) ^ 3 * (-2 * u)) u :=
    HasDerivAt.mul hS3 hsq
  rw [hfe4] at hS4
  rw [show (3 * (1 - u ^ 2) ^ 2 * (-2 * u)) * (1 - u ^ 2)
        + (1 - u ^ 2) ^ 3 * (-2 * u) = 4 * (1 - u ^ 2) ^ 3 * (-2 * u) from by ring] at hS4
  -- B pieces: d/dv of each term of the second-derivative bracket
  have hB1 : HasDerivAt (fun v : ℝ => -2 * k / (1 - v ^ 2) ^ 2)
      (((0 : ℝ) * (1 - u ^ 2) ^ 2 - -2 * k * (2 * (1 - u ^ 2) * (-2 * u)))
        / ((1 - u ^ 2) ^ 2) ^ 2) u :=
    HasDerivAt.div (hasDerivAt_const u (-2 * k)) hS2 (pow_ne_zero 2 hne)
  rw [show ((0 : ℝ) * (1 - u ^ 2) ^ 2 - -2 * k * (2 * (1 - u ^ 2) * (-2 * u)))
        / ((1 - u ^ 2) ^ 2) ^ 2 = -8 * k * u / (1 - u ^ 2) ^ 3 from by field_simp; ring] at hB1
  have hvv : HasDerivAt (fun v : ℝ => v * v) ((1 : ℝ) * u + u * 1) u :=
    HasDerivAt.mul (hasDerivAt_id u) (hasDerivAt_id u)
  rw [show ((1 : ℝ) * u + u * 1) = 2 * u from by ring] at hvv
  have hfevv : (fun v : ℝ => v * v) = fun v : ℝ => v ^ 2 := by funext v; ring
  rw [hfevv] at hvv
  have hB2 : HasDerivAt (fun v : ℝ => 4 * k ^ 2 * v ^ 2 / (1 - v ^ 2) ^ 4)
      (((4 * k ^ 2 * (2 * u)) * (1 - u ^ 2) ^ 4
        - 4 * k ^ 2 * u ^ 2 * (4 * (1 - u ^ 2) ^ 3 * (-2 * u)))
        / ((1 - u ^ 2) ^ 4) ^ 2) u :=
    HasDerivAt.div (hvv.const_mul (4 * k ^ 2)) hS4 (pow_ne_zero 4 hne)
  rw [show ((4 * k ^ 2 * (2 * u)) * (1 - u ^ 2) ^ 4
        - 4 * k ^ 2 * u ^ 2 * (4 * (1 - u ^ 2) ^ 3 * (-2 * u)))
        / ((1 - u ^ 2) ^ 4) ^ 2
      = 8 * k ^ 2 * u / (1 - u ^ 2) ^ 4 + 32 * k ^ 2 * u ^ 3 / (1 - u ^ 2) ^ 5 from by
      field_simp; ring] at hB2
  have hB3 : HasDerivAt (fun v : ℝ => 8 * k * v ^ 2 / (1 - v ^ 2) ^ 3)
      (((8 * k * (2 * u)) * (1 - u ^ 2) ^ 3
        - 8 * k * u ^ 2 * (3 * (1 - u ^ 2) ^ 2 * (-2 * u)))
        / ((1 - u ^ 2) ^ 3) ^ 2) u :=
    HasDerivAt.div (hvv.const_mul (8 * k)) hS3 (pow_ne_zero 3 hne)
  rw [show ((8 * k * (2 * u)) * (1 - u ^ 2) ^ 3
        - 8 * k * u ^ 2 * (3 * (1 - u ^ 2) ^ 2 * (-2 * u)))
        / ((1 - u ^ 2) ^ 3) ^ 2
      = 16 * k * u / (1 - u ^ 2) ^ 3 + 48 * k * u ^ 3 / (1 - u ^ 2) ^ 4 from by
      field_simp; ring] at hB3
  -- combine: d/dv (e^A * B) = e^A * (A' * B + B')
  have hB0 : HasDerivAt (fun v : ℝ =>
        (-2 * k / (1 - v ^ 2) ^ 2 + 4 * k ^ 2 * v ^ 2 / (1 - v ^ 2) ^ 4
          - 8 * k * v ^ 2 / (1 - v ^ 2) ^ 3))
      ((-8 * k * u / (1 - u ^ 2) ^ 3)
        + (8 * k ^ 2 * u / (1 - u ^ 2) ^ 4 + 32 * k ^ 2 * u ^ 3 / (1 - u ^ 2) ^ 5)
        - (16 * k * u / (1 - u ^ 2) ^ 3 + 48 * k * u ^ 3 / (1 - u ^ 2) ^ 4)) u :=
    (hB1.add hB2).sub hB3
  have hmul : HasDerivAt (fun v : ℝ =>
        Real.exp (-k / (1 - v ^ 2)) *
        (-2 * k / (1 - v ^ 2) ^ 2 + 4 * k ^ 2 * v ^ 2 / (1 - v ^ 2) ^ 4
          - 8 * k * v ^ 2 / (1 - v ^ 2) ^ 3))
      ((Real.exp (-k / (1 - u ^ 2)) * (-2 * k * u / (1 - u ^ 2) ^ 2)) *
          (-2 * k / (1 - u ^ 2) ^ 2 + 4 * k ^ 2 * u ^ 2 / (1 - u ^ 2) ^ 4
            - 8 * k * u ^ 2 / (1 - u ^ 2) ^ 3)
        + Real.exp (-k / (1 - u ^ 2)) *
          ((-8 * k * u / (1 - u ^ 2) ^ 3)
            + (8 * k ^ 2 * u / (1 - u ^ 2) ^ 4 + 32 * k ^ 2 * u ^ 3 / (1 - u ^ 2) ^ 5)
            - (16 * k * u / (1 - u ^ 2) ^ 3 + 48 * k * u ^ 3 / (1 - u ^ 2) ^ 4))) u :=
    HasDerivAt.mul hE1 hB0
  have hval2 : (Real.exp (-k / (1 - u ^ 2)) * (-2 * k * u / (1 - u ^ 2) ^ 2)) *
          (-2 * k / (1 - u ^ 2) ^ 2 + 4 * k ^ 2 * u ^ 2 / (1 - u ^ 2) ^ 4
            - 8 * k * u ^ 2 / (1 - u ^ 2) ^ 3)
        + Real.exp (-k / (1 - u ^ 2)) *
          ((-8 * k * u / (1 - u ^ 2) ^ 3)
            + (8 * k ^ 2 * u / (1 - u ^ 2) ^ 4 + 32 * k ^ 2 * u ^ 3 / (1 - u ^ 2) ^ 5)
            - (16 * k * u / (1 - u ^ 2) ^ 3 + 48 * k * u ^ 3 / (1 - u ^ 2) ^ 4))
      = Real.exp (-k / (1 - u ^ 2)) *
        (12 * k ^ 2 * u / (1 - u ^ 2) ^ 4 - 8 * k ^ 3 * u ^ 3 / (1 - u ^ 2) ^ 6
          + 48 * k ^ 2 * u ^ 3 / (1 - u ^ 2) ^ 5 - 24 * k * u / (1 - u ^ 2) ^ 3
          - 48 * k * u ^ 3 / (1 - u ^ 2) ^ 4) := by
    field_simp
    ring
  rw [hval2] at hmul
  rw [gevreyDeriv3_of_abs_lt k u h]
  have hop : {v : ℝ | |v| < 1} ∈ 𝓝 u :=
    (isOpen_lt continuous_abs continuous_one).mem_nhds h
  have hev : (fun v : ℝ => gevreyDeriv2 k v) =ᶠ[𝓝 u]
      (fun v : ℝ => Real.exp (-k / (1 - v ^ 2)) *
        (-2 * k / (1 - v ^ 2) ^ 2 + 4 * k ^ 2 * v ^ 2 / (1 - v ^ 2) ^ 4
          - 8 * k * v ^ 2 / (1 - v ^ 2) ^ 3)) := by
    filter_upwards [hop] with v hv
    exact gevreyDeriv2_of_abs_lt k v hv
  exact hmul.congr_of_eventuallyEq hev

/-- Master septic-type bound for the third derivative (continuity glue).  The
SEVEN-power trade keeps one power of `s = 1 - u^2` alive in every term, so the
bound vanishes at `|u| = 1`. -/
lemma abs_gevreyDeriv3_le_septic (k : ℝ) (hk : 0 < k) (u : ℝ) :
    |gevreyDeriv3 k u| ≤
      7 ^ 7 * (12 * (k ^ 5)⁻¹ * |u| * |1 - u ^ 2| ^ 3
        + 8 * (k ^ 4)⁻¹ * |u| ^ 3 * |1 - u ^ 2|
        + 48 * (k ^ 5)⁻¹ * |u| ^ 3 * (1 - u ^ 2) ^ 2
        + 24 * (k ^ 6)⁻¹ * |u| * (1 - u ^ 2) ^ 4
        + 48 * (k ^ 6)⁻¹ * |u| ^ 3 * |1 - u ^ 2| ^ 3) := by
  rcases lt_or_ge (abs u) 1 with h | h
  · have hu2 : u ^ 2 < 1 := sq_lt_one_of_abs_lt_one h
    have ht : 0 < 1 - u ^ 2 := by linarith
    have habs : |gevreyDeriv3 k u|
        = Real.exp (-k / (1 - u ^ 2)) *
          |(12 * k ^ 2 * u / (1 - u ^ 2) ^ 4 - 8 * k ^ 3 * u ^ 3 / (1 - u ^ 2) ^ 6
            + 48 * k ^ 2 * u ^ 3 / (1 - u ^ 2) ^ 5 - 24 * k * u / (1 - u ^ 2) ^ 3
            - 48 * k * u ^ 3 / (1 - u ^ 2) ^ 4)| := by
      rw [gevreyDeriv3_of_abs_lt k u h]
      simp only [abs_mul, abs_of_pos (Real.exp_pos _)]
    have htri := abs_sum5_le k u hk ht
    have hstep : Real.exp (-k / (1 - u ^ 2))
        = (Real.exp (-k / (7 * (1 - u ^ 2)))) ^ 7 := by
      have h7 : (-k / (1 - u ^ 2)) = ((7 : ℕ) : ℝ) * (-k / (7 * (1 - u ^ 2))) := by
        norm_num
        field_simp
      rw [h7, Real.exp_nat_mul]
    have hle : Real.exp (-k / (7 * (1 - u ^ 2))) ≤ 7 * (1 - u ^ 2) / k :=
      exp_neg_div_le_div k hk _ (by linarith)
    have hs : (0 : ℝ) < 1 - u ^ 2 := ht
    have hsumpos : (0 : ℝ) ≤ 12 * k ^ 2 * |u| / (1 - u ^ 2) ^ 4
        + 8 * k ^ 3 * |u| ^ 3 / (1 - u ^ 2) ^ 6
        + 48 * k ^ 2 * |u| ^ 3 / (1 - u ^ 2) ^ 5 + 24 * k * |u| / (1 - u ^ 2) ^ 3
        + 48 * k * |u| ^ 3 / (1 - u ^ 2) ^ 4 := by
      have p1 : (0 : ℝ) ≤ 12 * k ^ 2 * |u| / (1 - u ^ 2) ^ 4 :=
        div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg k)) (abs_nonneg u))
          (pow_nonneg ht.le 4)
      have p2 : (0 : ℝ) ≤ 8 * k ^ 3 * |u| ^ 3 / (1 - u ^ 2) ^ 6 :=
        div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hk.le 3))
          (pow_nonneg (abs_nonneg u) 3)) (pow_nonneg ht.le 6)
      have p3 : (0 : ℝ) ≤ 48 * k ^ 2 * |u| ^ 3 / (1 - u ^ 2) ^ 5 :=
        div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg k))
          (pow_nonneg (abs_nonneg u) 3)) (pow_nonneg ht.le 5)
      have p4 : (0 : ℝ) ≤ 24 * k * |u| / (1 - u ^ 2) ^ 3 :=
        div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (abs_nonneg u))
          (pow_nonneg ht.le 3)
      have p5 : (0 : ℝ) ≤ 48 * k * |u| ^ 3 / (1 - u ^ 2) ^ 4 :=
        div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by linarith))
          (pow_nonneg (abs_nonneg u) 3)) (pow_nonneg ht.le 4)
      linarith
    calc |gevreyDeriv3 k u|
        = Real.exp (-k / (1 - u ^ 2)) *
          |(12 * k ^ 2 * u / (1 - u ^ 2) ^ 4 - 8 * k ^ 3 * u ^ 3 / (1 - u ^ 2) ^ 6
            + 48 * k ^ 2 * u ^ 3 / (1 - u ^ 2) ^ 5 - 24 * k * u / (1 - u ^ 2) ^ 3
            - 48 * k * u ^ 3 / (1 - u ^ 2) ^ 4)| := habs
      _ ≤ Real.exp (-k / (1 - u ^ 2)) * (12 * k ^ 2 * |u| / (1 - u ^ 2) ^ 4
            + 8 * k ^ 3 * |u| ^ 3 / (1 - u ^ 2) ^ 6
            + 48 * k ^ 2 * |u| ^ 3 / (1 - u ^ 2) ^ 5 + 24 * k * |u| / (1 - u ^ 2) ^ 3
            + 48 * k * |u| ^ 3 / (1 - u ^ 2) ^ 4) :=
          mul_le_mul_of_nonneg_left htri (Real.exp_nonneg _)
      _ = (Real.exp (-k / (7 * (1 - u ^ 2)))) ^ 7 *
            (12 * k ^ 2 * |u| / (1 - u ^ 2) ^ 4 + 8 * k ^ 3 * |u| ^ 3 / (1 - u ^ 2) ^ 6
              + 48 * k ^ 2 * |u| ^ 3 / (1 - u ^ 2) ^ 5 + 24 * k * |u| / (1 - u ^ 2) ^ 3
              + 48 * k * |u| ^ 3 / (1 - u ^ 2) ^ 4) := by
          rw [hstep]
      _ ≤ (7 * (1 - u ^ 2) / k) ^ 7 *
            (12 * k ^ 2 * |u| / (1 - u ^ 2) ^ 4 + 8 * k ^ 3 * |u| ^ 3 / (1 - u ^ 2) ^ 6
              + 48 * k ^ 2 * |u| ^ 3 / (1 - u ^ 2) ^ 5 + 24 * k * |u| / (1 - u ^ 2) ^ 3
              + 48 * k * |u| ^ 3 / (1 - u ^ 2) ^ 4) :=
          mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ (Real.exp_nonneg _) hle 7) hsumpos
      _ = 7 ^ 7 * (12 * (k ^ 5)⁻¹ * |u| * |1 - u ^ 2| ^ 3
            + 8 * (k ^ 4)⁻¹ * |u| ^ 3 * |1 - u ^ 2|
            + 48 * (k ^ 5)⁻¹ * |u| ^ 3 * (1 - u ^ 2) ^ 2
            + 24 * (k ^ 6)⁻¹ * |u| * (1 - u ^ 2) ^ 4
            + 48 * (k ^ 6)⁻¹ * |u| ^ 3 * |1 - u ^ 2| ^ 3) := by
          rw [abs_of_pos ht]
          field_simp
  · have hk5 : (0 : ℝ) ≤ (k ^ 5)⁻¹ := inv_nonneg.mpr (pow_nonneg hk.le 5)
    rw [gevreyDeriv3_of_one_le_abs k u h, abs_zero]
    exact mul_nonneg (by norm_num) (by positivity)

lemma continuous_gevreyDeriv3 (k : ℝ) (hk : 0 < k) : Continuous (gevreyDeriv3 k) := by
  rw [continuous_iff_continuousAt]
  intro u
  rcases lt_trichotomy (abs u) 1 with h | h | h
  · have hden : ContinuousAt (fun v : ℝ => 1 - v ^ 2) u := by fun_prop
    have hu2 : u ^ 2 < 1 := sq_lt_one_of_abs_lt_one h
    have hne : (1 : ℝ) - u ^ 2 ≠ 0 := by linarith
    have h3a : ContinuousAt (fun v : ℝ => 12 * k ^ 2 * v / (1 - v ^ 2) ^ 4) u :=
      ContinuousAt.div (by fun_prop) (hden.pow 4) (pow_ne_zero 4 hne)
    have h3b : ContinuousAt (fun v : ℝ => 8 * k ^ 3 * v ^ 3 / (1 - v ^ 2) ^ 6) u :=
      ContinuousAt.div (by fun_prop) (hden.pow 6) (pow_ne_zero 6 hne)
    have h3c : ContinuousAt (fun v : ℝ => 48 * k ^ 2 * v ^ 3 / (1 - v ^ 2) ^ 5) u :=
      ContinuousAt.div (by fun_prop) (hden.pow 5) (pow_ne_zero 5 hne)
    have h3d : ContinuousAt (fun v : ℝ => 24 * k * v / (1 - v ^ 2) ^ 3) u :=
      ContinuousAt.div (by fun_prop) (hden.pow 3) (pow_ne_zero 3 hne)
    have h3e : ContinuousAt (fun v : ℝ => 48 * k * v ^ 3 / (1 - v ^ 2) ^ 4) u :=
      ContinuousAt.div (by fun_prop) (hden.pow 4) (pow_ne_zero 4 hne)
    have h3 : ContinuousAt (fun v : ℝ =>
        (12 * k ^ 2 * v / (1 - v ^ 2) ^ 4 - 8 * k ^ 3 * v ^ 3 / (1 - v ^ 2) ^ 6
          + 48 * k ^ 2 * v ^ 3 / (1 - v ^ 2) ^ 5 - 24 * k * v / (1 - v ^ 2) ^ 3
          - 48 * k * v ^ 3 / (1 - v ^ 2) ^ 4)) u :=
      (((h3a.sub h3b).add h3c).sub h3d).sub h3e
    have h2 : ContinuousAt (fun v : ℝ => Real.exp (-k / (1 - v ^ 2))) u :=
      Real.continuous_exp.continuousAt.comp
        (continuousAt_const.div hden hne)
    have hform : ContinuousAt (fun v : ℝ =>
        Real.exp (-k / (1 - v ^ 2)) *
        (12 * k ^ 2 * v / (1 - v ^ 2) ^ 4 - 8 * k ^ 3 * v ^ 3 / (1 - v ^ 2) ^ 6
          + 48 * k ^ 2 * v ^ 3 / (1 - v ^ 2) ^ 5 - 24 * k * v / (1 - v ^ 2) ^ 3
          - 48 * k * v ^ 3 / (1 - v ^ 2) ^ 4)) u :=
      h2.mul h3
    have hev : (fun v : ℝ => gevreyDeriv3 k v) =ᶠ[𝓝 u] (fun v : ℝ =>
        Real.exp (-k / (1 - v ^ 2)) *
        (12 * k ^ 2 * v / (1 - v ^ 2) ^ 4 - 8 * k ^ 3 * v ^ 3 / (1 - v ^ 2) ^ 6
          + 48 * k ^ 2 * v ^ 3 / (1 - v ^ 2) ^ 5 - 24 * k * v / (1 - v ^ 2) ^ 3
          - 48 * k * v ^ 3 / (1 - v ^ 2) ^ 4)) := by
      have hop : {v : ℝ | |v| < 1} ∈ 𝓝 u :=
        (isOpen_lt continuous_abs continuous_one).mem_nhds h
      filter_upwards [hop] with v hv
      exact gevreyDeriv3_of_abs_lt k v hv
    rw [ContinuousAt, gevreyDeriv3_of_abs_lt k u h]
    exact hform.congr' hev.symm
  · have hu2 : u ^ 2 = 1 := by
      have hsq := sq_abs u
      rw [h] at hsq
      linarith
    have hz : Tendsto (fun v : ℝ => 7 ^ 7 * (12 * (k ^ 5)⁻¹ * |v| * |1 - v ^ 2| ^ 3
        + 8 * (k ^ 4)⁻¹ * |v| ^ 3 * |1 - v ^ 2|
        + 48 * (k ^ 5)⁻¹ * |v| ^ 3 * (1 - v ^ 2) ^ 2
        + 24 * (k ^ 6)⁻¹ * |v| * (1 - v ^ 2) ^ 4
        + 48 * (k ^ 6)⁻¹ * |v| ^ 3 * |1 - v ^ 2| ^ 3)) (𝓝 u) (𝓝 0) := by
      have hc4 : Continuous (fun v : ℝ => 7 ^ 7 *
        (12 * (k ^ 5)⁻¹ * |v| * |1 - v ^ 2| ^ 3
        + 8 * (k ^ 4)⁻¹ * |v| ^ 3 * |1 - v ^ 2|
        + 48 * (k ^ 5)⁻¹ * |v| ^ 3 * (1 - v ^ 2) ^ 2
        + 24 * (k ^ 6)⁻¹ * |v| * (1 - v ^ 2) ^ 4
        + 48 * (k ^ 6)⁻¹ * |v| ^ 3 * |1 - v ^ 2| ^ 3)) := by
        fun_prop
      have h1 := hc4.tendsto u
      rw [hu2] at h1
      simpa using h1
    have hzero : gevreyDeriv3 k u = 0 := gevreyDeriv3_of_one_le_abs k u h.ge
    rw [ContinuousAt, hzero]
    have hneg : Tendsto (fun v : ℝ => -(7 ^ 7 *
        (12 * (k ^ 5)⁻¹ * |v| * |1 - v ^ 2| ^ 3
        + 8 * (k ^ 4)⁻¹ * |v| ^ 3 * |1 - v ^ 2|
        + 48 * (k ^ 5)⁻¹ * |v| ^ 3 * (1 - v ^ 2) ^ 2
        + 24 * (k ^ 6)⁻¹ * |v| * (1 - v ^ 2) ^ 4
        + 48 * (k ^ 6)⁻¹ * |v| ^ 3 * |1 - v ^ 2| ^ 3))) (𝓝 u) (𝓝 0) := by
      simpa using hz.neg
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hneg hz
      (Filter.Eventually.of_forall fun v =>
        (abs_le.mp (abs_gevreyDeriv3_le_septic k hk v)).1)
      (Filter.Eventually.of_forall fun v =>
        (abs_le.mp (abs_gevreyDeriv3_le_septic k hk v)).2)
  · have hopen : {v : ℝ | 1 < |v|} ∈ 𝓝 u :=
      (isOpen_lt continuous_const continuous_abs).mem_nhds h
    have hev : (fun v : ℝ => gevreyDeriv3 k v) =ᶠ[𝓝 u] (fun _ : ℝ => (0 : ℝ)) := by
      filter_upwards [hopen] with v hv
      exact gevreyDeriv3_of_one_le_abs k v (le_of_lt hv)
    have hzero : gevreyDeriv3 k u = 0 := gevreyDeriv3_of_one_le_abs k u h.le
    rw [ContinuousAt, hzero]
    exact tendsto_const_nhds.congr' hev.symm

lemma intervalIntegrable_gevreyDeriv3 (k : ℝ) (hk : 0 < k) (a b : ℝ) :
    IntervalIntegrable (gevreyDeriv3 k) volume a b :=
  (continuous_gevreyDeriv3 k hk).continuousOn.intervalIntegrable (μ := volume)

/-- Pointwise cap of the septic bound on `|u| ≤ 1`: every `u`-power and every
positive power of `s = 1 - u^2` is at most `1`. -/
private lemma abs_gevreyDeriv3_le_outer_const (k : ℝ) (hk : 1 ≤ k) (u : ℝ)
    (hu : |u| ≤ 1) :
    |gevreyDeriv3 k u| ≤ 7 ^ 7 * (8 * (k ^ 4)⁻¹ + 60 * (k ^ 5)⁻¹ + 72 * (k ^ 6)⁻¹) := by
  have hk' : (0 : ℝ) < k := by linarith
  have hi4 : (0 : ℝ) ≤ (k ^ 4)⁻¹ := inv_nonneg.mpr (pow_nonneg hk'.le 4)
  have hi5 : (0 : ℝ) ≤ (k ^ 5)⁻¹ := inv_nonneg.mpr (pow_nonneg hk'.le 5)
  have hi6 : (0 : ℝ) ≤ (k ^ 6)⁻¹ := inv_nonneg.mpr (pow_nonneg hk'.le 6)
  have hu21 : u ^ 2 ≤ 1 := by
    have h2 : |u| ^ 2 ≤ 1 := le_trans (pow_le_pow_left₀ (abs_nonneg u) hu 2) (by norm_num)
    rwa [sq_abs u] at h2
  have hs0 : (0 : ℝ) ≤ 1 - u ^ 2 := by linarith [sq_nonneg u]
  have hs1 : |1 - u ^ 2| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith [sq_nonneg u]⟩
  have hs3 : |1 - u ^ 2| ^ 3 ≤ 1 :=
    le_trans (pow_le_pow_left₀ (abs_nonneg _) hs1 3) (by norm_num)
  have hsle : (1 : ℝ) - u ^ 2 ≤ 1 := le_of_abs_le hs1
  have hs2 : (1 - u ^ 2) ^ 2 ≤ 1 := le_trans (pow_le_pow_left₀ hs0 hsle 2) (by norm_num)
  have hs4 : (1 - u ^ 2) ^ 4 ≤ 1 := le_trans (pow_le_pow_left₀ hs0 hsle 4) (by norm_num)
  have e1 : 12 * (k ^ 5)⁻¹ * |u| * |1 - u ^ 2| ^ 3 ≤ 12 * (k ^ 5)⁻¹ := by
    have hcap : |u| * |1 - u ^ 2| ^ 3 ≤ (1 : ℝ) * 1 :=
      mul_le_mul hu hs3 (by norm_num) (by norm_num)
    calc 12 * (k ^ 5)⁻¹ * |u| * |1 - u ^ 2| ^ 3
        = 12 * (k ^ 5)⁻¹ * (|u| * |1 - u ^ 2| ^ 3) := by ring
      _ ≤ 12 * (k ^ 5)⁻¹ * ((1 : ℝ) * 1) := mul_le_mul_of_nonneg_left hcap (by positivity)
      _ = 12 * (k ^ 5)⁻¹ := by ring
  have e2 : 8 * (k ^ 4)⁻¹ * |u| ^ 3 * |1 - u ^ 2| ≤ 8 * (k ^ 4)⁻¹ := by
    have hcap : |u| ^ 3 * |1 - u ^ 2| ≤ (1 : ℝ) * 1 :=
      mul_le_mul (le_trans (pow_le_pow_left₀ (abs_nonneg u) hu 3) (by norm_num)) hs1
        (by norm_num) (by norm_num)
    calc 8 * (k ^ 4)⁻¹ * |u| ^ 3 * |1 - u ^ 2|
        = 8 * (k ^ 4)⁻¹ * (|u| ^ 3 * |1 - u ^ 2|) := by ring
      _ ≤ 8 * (k ^ 4)⁻¹ * ((1 : ℝ) * 1) := mul_le_mul_of_nonneg_left hcap (by positivity)
      _ = 8 * (k ^ 4)⁻¹ := by ring
  have e3 : 48 * (k ^ 5)⁻¹ * |u| ^ 3 * (1 - u ^ 2) ^ 2 ≤ 48 * (k ^ 5)⁻¹ := by
    have hcap : |u| ^ 3 * (1 - u ^ 2) ^ 2 ≤ (1 : ℝ) * 1 :=
      mul_le_mul (le_trans (pow_le_pow_left₀ (abs_nonneg u) hu 3) (by norm_num)) hs2
        (by positivity) (by positivity)
    calc 48 * (k ^ 5)⁻¹ * |u| ^ 3 * (1 - u ^ 2) ^ 2
        = 48 * (k ^ 5)⁻¹ * (|u| ^ 3 * (1 - u ^ 2) ^ 2) := by ring
      _ ≤ 48 * (k ^ 5)⁻¹ * ((1 : ℝ) * 1) := mul_le_mul_of_nonneg_left hcap (by positivity)
      _ = 48 * (k ^ 5)⁻¹ := by ring
  have e4 : 24 * (k ^ 6)⁻¹ * |u| * (1 - u ^ 2) ^ 4 ≤ 24 * (k ^ 6)⁻¹ := by
    have hcap : |u| * (1 - u ^ 2) ^ 4 ≤ (1 : ℝ) * 1 :=
      mul_le_mul hu hs4 (by positivity) (by positivity)
    calc 24 * (k ^ 6)⁻¹ * |u| * (1 - u ^ 2) ^ 4
        = 24 * (k ^ 6)⁻¹ * (|u| * (1 - u ^ 2) ^ 4) := by ring
      _ ≤ 24 * (k ^ 6)⁻¹ * ((1 : ℝ) * 1) := mul_le_mul_of_nonneg_left hcap (by positivity)
      _ = 24 * (k ^ 6)⁻¹ := by ring
  have e5 : 48 * (k ^ 6)⁻¹ * |u| ^ 3 * |1 - u ^ 2| ^ 3 ≤ 48 * (k ^ 6)⁻¹ := by
    have hcap : |u| ^ 3 * |1 - u ^ 2| ^ 3 ≤ (1 : ℝ) * 1 :=
      mul_le_mul (le_trans (pow_le_pow_left₀ (abs_nonneg u) hu 3) (by norm_num)) hs3
        (by norm_num) (by norm_num)
    calc 48 * (k ^ 6)⁻¹ * |u| ^ 3 * |1 - u ^ 2| ^ 3
        = 48 * (k ^ 6)⁻¹ * (|u| ^ 3 * |1 - u ^ 2| ^ 3) := by ring
      _ ≤ 48 * (k ^ 6)⁻¹ * ((1 : ℝ) * 1) := mul_le_mul_of_nonneg_left hcap (by positivity)
      _ = 48 * (k ^ 6)⁻¹ := by ring
  have hstep := abs_gevreyDeriv3_le_septic k hk' u
  linarith

/-- Outer integral bound, right piece `[5/6, 1]`. -/
lemma integral_abs_gevreyDeriv3_outer_right_le (k : ℝ) (hk : 1 ≤ k) :
    ∫ u in ((5 : ℝ) / 6)..1, |gevreyDeriv3 k u|
      ≤ 7 ^ 7 * (8 * (k ^ 4)⁻¹ + 60 * (k ^ 5)⁻¹ + 72 * (k ^ 6)⁻¹) / 6 := by
  have hk' : (0 : ℝ) < k := by linarith
  set C : ℝ := 7 ^ 7 * (8 * (k ^ 4)⁻¹ + 60 * (k ^ 5)⁻¹ + 72 * (k ^ 6)⁻¹) with hCdef
  have hint : IntervalIntegrable (fun u => |gevreyDeriv3 k u|) volume ((5 : ℝ) / 6) 1 :=
    (continuous_gevreyDeriv3 k hk').abs.intervalIntegrable (μ := volume) _ _
  have hintC : IntervalIntegrable (fun _ : ℝ => C) volume ((5 : ℝ) / 6) 1 :=
    (continuous_const : Continuous (fun _ : ℝ => C)).intervalIntegrable (μ := volume) _ _
  have hmono := intervalIntegral.integral_mono_on (by norm_num) hint hintC
    (fun x hx => by
      simp only [mem_Icc] at hx
      exact abs_gevreyDeriv3_le_outer_const k hk x (abs_le.mpr ⟨by linarith, by linarith⟩))
  rw [intervalIntegral.integral_const] at hmono
  exact hmono.trans (le_of_eq (by rw [hCdef]; ring))

/-- Outer integral bound, left piece `[-1, -5/6]`. -/
lemma integral_abs_gevreyDeriv3_outer_left_le (k : ℝ) (hk : 1 ≤ k) :
    ∫ u in (-1 : ℝ)..(-(5 : ℝ) / 6), |gevreyDeriv3 k u|
      ≤ 7 ^ 7 * (8 * (k ^ 4)⁻¹ + 60 * (k ^ 5)⁻¹ + 72 * (k ^ 6)⁻¹) / 6 := by
  have hk' : (0 : ℝ) < k := by linarith
  set C : ℝ := 7 ^ 7 * (8 * (k ^ 4)⁻¹ + 60 * (k ^ 5)⁻¹ + 72 * (k ^ 6)⁻¹) with hCdef
  have hint : IntervalIntegrable (fun u => |gevreyDeriv3 k u|) volume (-1 : ℝ)
      (-(5 : ℝ) / 6) :=
    (continuous_gevreyDeriv3 k hk').abs.intervalIntegrable (μ := volume) _ _
  have hintC : IntervalIntegrable (fun _ : ℝ => C) volume (-1 : ℝ) (-(5 : ℝ) / 6) :=
    (continuous_const : Continuous (fun _ : ℝ => C)).intervalIntegrable (μ := volume) _ _
  have hmono := intervalIntegral.integral_mono_on (by norm_num) hint hintC
    (fun x hx => by
      simp only [mem_Icc] at hx
      exact abs_gevreyDeriv3_le_outer_const k hk x (abs_le.mpr ⟨by linarith, by linarith⟩))
  rw [intervalIntegral.integral_const] at hmono
  exact hmono.trans (le_of_eq (by rw [hCdef]; ring))

/-- Pointwise middle bound: the exponential cap is `e^{-k}` (attained at
`u = 0`). -/
lemma abs_gevreyDeriv3_le_mid (k : ℝ) (hk : 1 ≤ k) (u : ℝ) (hu : |u| ≤ 5 / 6) :
    |gevreyDeriv3 k u| ≤
      Real.exp (-k) * (5689 * k ^ 3 + 11580 * k ^ 2 + 3889 * k) := by
  have hk' : (0 : ℝ) < k := by linarith
  have h1 : |u| < 1 := lt_of_le_of_lt hu (by norm_num)
  have hu2 : u ^ 2 < 1 := sq_lt_one_of_abs_lt_one h1
  have ht : 0 < 1 - u ^ 2 := by linarith
  have hsq5 : u ^ 2 ≤ 25 / 36 := by
    obtain ⟨hlo, hhi⟩ := abs_le.mp hu
    nlinarith [hlo, hhi]
  have hs36 : (11 : ℝ) / 36 ≤ 1 - u ^ 2 := by linarith
  have habs : |gevreyDeriv3 k u|
      = Real.exp (-k / (1 - u ^ 2)) *
        |(12 * k ^ 2 * u / (1 - u ^ 2) ^ 4 - 8 * k ^ 3 * u ^ 3 / (1 - u ^ 2) ^ 6
          + 48 * k ^ 2 * u ^ 3 / (1 - u ^ 2) ^ 5 - 24 * k * u / (1 - u ^ 2) ^ 3
          - 48 * k * u ^ 3 / (1 - u ^ 2) ^ 4)| := by
    rw [gevreyDeriv3_of_abs_lt k u h1]
    simp only [abs_mul, abs_of_pos (Real.exp_pos _)]
  have htri := abs_sum5_le k u hk' ht
  have hexp : Real.exp (-k / (1 - u ^ 2)) ≤ Real.exp (-k) := by
    refine Real.exp_le_exp.mpr ?_
    have h2 : (1 : ℝ) - u ^ 2 ≤ 1 := by linarith [sq_nonneg u]
    have h3 : k * (1 - u ^ 2) ≤ k * 1 := mul_le_mul_of_nonneg_left h2 hk'.le
    rw [mul_one] at h3
    have h4 : (-k / (1 - u ^ 2)) ≤ -k := by
      rw [div_le_iff₀ ht]
      linarith
    linarith
  have habs3 : |u| ^ 3 ≤ (5 / 6) ^ 3 := pow_le_pow_left₀ (abs_nonneg u) hu 3
  have hcap1 : (12 : ℝ) * |u| ≤ 1150 * (1 - u ^ 2) ^ 4 := by
    calc 12 * |u| ≤ 10 := by linarith
      _ ≤ 1150 * (11 / 36) ^ 4 := by norm_num
      _ ≤ 1150 * (1 - u ^ 2) ^ 4 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) hs36 4) (by norm_num)
  have hcap2 : (8 : ℝ) * |u| ^ 3 ≤ 5689 * (1 - u ^ 2) ^ 6 := by
    calc 8 * |u| ^ 3 ≤ 8 * (5 / 6) ^ 3 := mul_le_mul_of_nonneg_left habs3 (by norm_num)
      _ ≤ 125 / 27 := by norm_num
      _ ≤ 5689 * (11 / 36) ^ 6 := by norm_num
      _ ≤ 5689 * (1 - u ^ 2) ^ 6 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) hs36 6) (by norm_num)
  have hcap3 : (48 : ℝ) * |u| ^ 3 ≤ 10430 * (1 - u ^ 2) ^ 5 := by
    calc 48 * |u| ^ 3 ≤ 48 * (5 / 6) ^ 3 := mul_le_mul_of_nonneg_left habs3 (by norm_num)
      _ ≤ 250 / 9 := by norm_num
      _ ≤ 10430 * (11 / 36) ^ 5 := by norm_num
      _ ≤ 10430 * (1 - u ^ 2) ^ 5 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) hs36 5) (by norm_num)
  have hcap4 : (24 : ℝ) * |u| ≤ 702 * (1 - u ^ 2) ^ 3 := by
    calc 24 * |u| ≤ 20 := by linarith
      _ ≤ 702 * (11 / 36) ^ 3 := by norm_num
      _ ≤ 702 * (1 - u ^ 2) ^ 3 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) hs36 3) (by norm_num)
  have hcap5 : (48 : ℝ) * |u| ^ 3 ≤ 3187 * (1 - u ^ 2) ^ 4 := by
    calc 48 * |u| ^ 3 ≤ 48 * (5 / 6) ^ 3 := mul_le_mul_of_nonneg_left habs3 (by norm_num)
      _ ≤ 250 / 9 := by norm_num
      _ ≤ 3187 * (11 / 36) ^ 4 := by norm_num
      _ ≤ 3187 * (1 - u ^ 2) ^ 4 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) hs36 4) (by norm_num)
  have hc1 : 12 * k ^ 2 * |u| / (1 - u ^ 2) ^ 4 ≤ 1150 * k ^ 2 := by
    have hks : 12 * k ^ 2 * |u| ≤ k ^ 2 * (1150 * (1 - u ^ 2) ^ 4) := by
      calc 12 * k ^ 2 * |u| = k ^ 2 * (12 * |u|) := by ring
        _ ≤ k ^ 2 * (1150 * (1 - u ^ 2) ^ 4) := mul_le_mul_of_nonneg_left hcap1 (sq_nonneg k)
    rw [div_le_iff₀ (pow_pos ht 4)]
    linarith
  have hc2 : 8 * k ^ 3 * |u| ^ 3 / (1 - u ^ 2) ^ 6 ≤ 5689 * k ^ 3 := by
    have hks : 8 * k ^ 3 * |u| ^ 3 ≤ k ^ 3 * (5689 * (1 - u ^ 2) ^ 6) := by
      calc 8 * k ^ 3 * |u| ^ 3 = k ^ 3 * (8 * |u| ^ 3) := by ring
        _ ≤ k ^ 3 * (5689 * (1 - u ^ 2) ^ 6) :=
            mul_le_mul_of_nonneg_left hcap2 (pow_nonneg hk'.le 3)
    rw [div_le_iff₀ (pow_pos ht 6)]
    linarith
  have hc3 : 48 * k ^ 2 * |u| ^ 3 / (1 - u ^ 2) ^ 5 ≤ 10430 * k ^ 2 := by
    have hks : 48 * k ^ 2 * |u| ^ 3 ≤ k ^ 2 * (10430 * (1 - u ^ 2) ^ 5) := by
      calc 48 * k ^ 2 * |u| ^ 3 = k ^ 2 * (48 * |u| ^ 3) := by ring
        _ ≤ k ^ 2 * (10430 * (1 - u ^ 2) ^ 5) := mul_le_mul_of_nonneg_left hcap3 (sq_nonneg k)
    rw [div_le_iff₀ (pow_pos ht 5)]
    linarith
  have hc4 : 24 * k * |u| / (1 - u ^ 2) ^ 3 ≤ 702 * k := by
    have hks : 24 * k * |u| ≤ k * (702 * (1 - u ^ 2) ^ 3) := by
      calc 24 * k * |u| = k * (24 * |u|) := by ring
        _ ≤ k * (702 * (1 - u ^ 2) ^ 3) := mul_le_mul_of_nonneg_left hcap4 hk'.le
    rw [div_le_iff₀ (pow_pos ht 3)]
    linarith
  have hc5 : 48 * k * |u| ^ 3 / (1 - u ^ 2) ^ 4 ≤ 3187 * k := by
    have hks : 48 * k * |u| ^ 3 ≤ k * (3187 * (1 - u ^ 2) ^ 4) := by
      calc 48 * k * |u| ^ 3 = k * (48 * |u| ^ 3) := by ring
        _ ≤ k * (3187 * (1 - u ^ 2) ^ 4) := mul_le_mul_of_nonneg_left hcap5 hk'.le
    rw [div_le_iff₀ (pow_pos ht 4)]
    linarith
  have hS : (12 * k ^ 2 * |u| / (1 - u ^ 2) ^ 4 + 8 * k ^ 3 * |u| ^ 3 / (1 - u ^ 2) ^ 6
      + 48 * k ^ 2 * |u| ^ 3 / (1 - u ^ 2) ^ 5 + 24 * k * |u| / (1 - u ^ 2) ^ 3
      + 48 * k * |u| ^ 3 / (1 - u ^ 2) ^ 4)
      ≤ 5689 * k ^ 3 + 11580 * k ^ 2 + 3889 * k := by
    linarith
  calc |gevreyDeriv3 k u|
      = Real.exp (-k / (1 - u ^ 2)) *
        |(12 * k ^ 2 * u / (1 - u ^ 2) ^ 4 - 8 * k ^ 3 * u ^ 3 / (1 - u ^ 2) ^ 6
          + 48 * k ^ 2 * u ^ 3 / (1 - u ^ 2) ^ 5 - 24 * k * u / (1 - u ^ 2) ^ 3
          - 48 * k * u ^ 3 / (1 - u ^ 2) ^ 4)| := habs
    _ ≤ Real.exp (-k / (1 - u ^ 2)) *
        (12 * k ^ 2 * |u| / (1 - u ^ 2) ^ 4 + 8 * k ^ 3 * |u| ^ 3 / (1 - u ^ 2) ^ 6
          + 48 * k ^ 2 * |u| ^ 3 / (1 - u ^ 2) ^ 5 + 24 * k * |u| / (1 - u ^ 2) ^ 3
          + 48 * k * |u| ^ 3 / (1 - u ^ 2) ^ 4) :=
        mul_le_mul_of_nonneg_left htri (Real.exp_nonneg _)
    _ ≤ Real.exp (-k) * (5689 * k ^ 3 + 11580 * k ^ 2 + 3889 * k) :=
        mul_le_mul hexp hS (by positivity) (Real.exp_nonneg _)

/-- Total `L^1` mass of the third derivative. -/
lemma integral_abs_gevreyDeriv3_le (k : ℝ) (hk : 1 ≤ k) :
    ∫ u in (-1 : ℝ)..1, |gevreyDeriv3 k u|
      ≤ Real.exp (-k) * (9500 * k ^ 3 + 19400 * k ^ 2 + 6500 * k)
        + 2196115 * (k ^ 4)⁻¹ + 16470860 * (k ^ 5)⁻¹ + 19765032 * (k ^ 6)⁻¹ := by
  have hk' : (0 : ℝ) < k := by linarith
  have hc : ∀ a b : ℝ, IntervalIntegrable (fun u => |gevreyDeriv3 k u|) volume a b :=
    fun a b => (continuous_gevreyDeriv3 k hk').abs.intervalIntegrable (μ := volume) a b
  have hL := integral_abs_gevreyDeriv3_outer_left_le k hk
  have hR := integral_abs_gevreyDeriv3_outer_right_le k hk
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc (-1) (-(5 : ℝ) / 6))
      (hc (-(5 : ℝ) / 6) 1),
    ← intervalIntegral.integral_add_adjacent_intervals (hc (-(5 : ℝ) / 6) ((5 : ℝ) / 6))
      (hc ((5 : ℝ) / 6) 1)]
  set C3 : ℝ := Real.exp (-k) * (5689 * k ^ 3 + 11580 * k ^ 2 + 3889 * k) with hC3def
  have hcst : IntervalIntegrable (fun _ : ℝ => C3) volume (-(5 : ℝ) / 6) ((5 : ℝ) / 6) :=
    (continuous_const : Continuous (fun _ : ℝ => C3)).intervalIntegrable (μ := volume) _ _
  have hmid := intervalIntegral.integral_mono_on
    (by norm_num : (-(5 : ℝ) / 6) ≤ (5 : ℝ) / 6)
    (hc (-(5 : ℝ) / 6) ((5 : ℝ) / 6))
    hcst
    (fun x hx => by
      simp only [mem_Icc] at hx
      rw [hC3def]
      exact abs_gevreyDeriv3_le_mid k hk x (abs_le.mpr ⟨by linarith, by linarith⟩))
  have hconstval : ∫ u in (-(5 : ℝ) / 6)..((5 : ℝ) / 6), C3 = C3 * (5 / 3) := by
    rw [intervalIntegral.integral_const]
    ring
  rw [hconstval] at hmid
  have hout : 7 ^ 7 * (8 * (k ^ 4)⁻¹ + 60 * (k ^ 5)⁻¹ + 72 * (k ^ 6)⁻¹) / 6
      + 7 ^ 7 * (8 * (k ^ 4)⁻¹ + 60 * (k ^ 5)⁻¹ + 72 * (k ^ 6)⁻¹) / 6
      ≤ 2196115 * (k ^ 4)⁻¹ + 16470860 * (k ^ 5)⁻¹ + 19765032 * (k ^ 6)⁻¹ := by
    have hi4 : (0 : ℝ) ≤ (k ^ 4)⁻¹ := inv_nonneg.mpr (pow_nonneg hk'.le 4)
    have hi5 : (0 : ℝ) ≤ (k ^ 5)⁻¹ := inv_nonneg.mpr (pow_nonneg hk'.le 5)
    have hi6 : (0 : ℝ) ≤ (k ^ 6)⁻¹ := inv_nonneg.mpr (pow_nonneg hk'.le 6)
    have c4 : (6588344 : ℝ) / 3 ≤ 2196115 := by norm_num
    have c5 : (49412580 : ℝ) / 3 = 16470860 := by norm_num
    have c6 : (59295096 : ℝ) / 3 = 19765032 := by norm_num
    linarith
  have hm : C3 * (5 / 3) ≤ Real.exp (-k) * (9500 * k ^ 3 + 19400 * k ^ 2 + 6500 * k) := by
    rw [hC3def, mul_assoc]
    have hlin : (5689 * k ^ 3 + 11580 * k ^ 2 + 3889 * k) * (5 / 3)
        ≤ 9500 * k ^ 3 + 19400 * k ^ 2 + 6500 * k := by
      linarith [sq_nonneg k, pow_nonneg hk'.le 3]
    exact mul_le_mul_of_nonneg_left hlin (Real.exp_nonneg _)
  refine le_trans (add_le_add hL (add_le_add hmid hR)) ?_
  linarith

/-- Rung 3 of the vertical-decay ladder: three integration by parts with
explicit constants. -/
theorem laplace_abs_le_rung3 (k : ℝ) (hk : 1 ≤ k) (w : ℂ) (hw : w ≠ 0) :
    ‖∫ u in (-1 : ℝ)..(1 : ℝ), (gevreyInner k u : ℂ) * Complex.exp (w * (u : ℂ))‖
        ≤ Real.exp |w.re| * (Real.exp (-k) * (9500 * k ^ 3 + 19400 * k ^ 2 + 6500 * k)
            + 2196115 * (k ^ 4)⁻¹ + 16470860 * (k ^ 5)⁻¹ + 19765032 * (k ^ 6)⁻¹)
          / ‖w‖ ^ 3 := by
  have hk' : (0 : ℝ) < k := by linarith
  have hcontF : ContinuousOn (fun u : ℝ => (gevreyInner k u : ℂ)) (uIcc (-1 : ℝ) 1) :=
    Continuous.continuousOn
      (Complex.continuous_ofReal.comp (continuous_gevreyInner k hk'))
  have hcontG : ContinuousOn (fun u : ℝ => (gevreyDeriv k u : ℂ)) (uIcc (-1 : ℝ) 1) :=
    Continuous.continuousOn
      (Complex.continuous_ofReal.comp (continuous_gevreyDeriv k hk'))
  have hcontD : ContinuousOn (fun u : ℝ => (gevreyDeriv2 k u : ℂ)) (uIcc (-1 : ℝ) 1) :=
    Continuous.continuousOn
      (Complex.continuous_ofReal.comp (continuous_gevreyDeriv2 k hk'))
  have hcontD3 : ContinuousOn (fun u : ℝ => (gevreyDeriv3 k u : ℂ)) (uIcc (-1 : ℝ) 1) :=
    Continuous.continuousOn
      (Complex.continuous_ofReal.comp (continuous_gevreyDeriv3 k hk'))
  have hcontV : ContinuousOn (fun u : ℝ => Complex.exp (w * (u : ℂ)) / w)
      (uIcc (-1 : ℝ) 1) :=
    Continuous.continuousOn
      (Continuous.div (by fun_prop) continuous_const fun _ => hw)
  have hid : ∀ x : ℝ, HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := fun _ =>
    Complex.ofRealCLM.hasDerivAt
  have hvv' : ∀ x ∈ Ioo (min (-1 : ℝ) 1) (max (-1 : ℝ) 1),
      HasDerivAt (fun u : ℝ => Complex.exp (w * (u : ℂ)) / w)
        (Complex.exp (w * (x : ℂ))) x := by
    intro x _
    have h2 := ((hid x).const_mul w).cexp
    have h3 : Complex.exp (w * (x : ℂ)) * w / w = Complex.exp (w * (x : ℂ)) := by
      field_simp
    simpa [h3] using h2.div_const w
  have hu1' : ∀ x ∈ Ioo (min (-1 : ℝ) 1) (max (-1 : ℝ) 1),
      HasDerivAt (fun u : ℝ => (gevreyInner k u : ℂ)) ((gevreyDeriv k x : ℝ) : ℂ) x := by
    intro x hx
    simp only [mem_Ioo, min_eq_left (by norm_num : (-1 : ℝ) ≤ 1),
      max_eq_right (by norm_num : (-1 : ℝ) ≤ 1)] at hx
    obtain ⟨hx1, hx2⟩ := hx
    have hx' : |x| < 1 := abs_lt.mpr ⟨by linarith, by linarith⟩
    exact hasDerivAt_complex_gevreyInner k x hx'
  have hu2' : ∀ x ∈ Ioo (min (-1 : ℝ) 1) (max (-1 : ℝ) 1),
      HasDerivAt (fun u : ℝ => (gevreyDeriv k u : ℂ)) ((gevreyDeriv2 k x : ℝ) : ℂ) x := by
    intro x hx
    simp only [mem_Ioo, min_eq_left (by norm_num : (-1 : ℝ) ≤ 1),
      max_eq_right (by norm_num : (-1 : ℝ) ≤ 1)] at hx
    obtain ⟨hx1, hx2⟩ := hx
    have hx' : |x| < 1 := abs_lt.mpr ⟨by linarith, by linarith⟩
    have hd := gevreyDeriv_hasDerivAt_of_abs_lt k x hk' hx'
    have hof : HasDerivAt (fun v : ℝ => (v : ℂ)) 1 (gevreyDeriv k x) :=
      Complex.ofRealCLM.hasDerivAt
    have hcomp := hof.scomp x hd
    simpa [Function.comp] using hcomp
  have hu3' : ∀ x ∈ Ioo (min (-1 : ℝ) 1) (max (-1 : ℝ) 1),
      HasDerivAt (fun u : ℝ => (gevreyDeriv2 k u : ℂ)) ((gevreyDeriv3 k x : ℝ) : ℂ) x := by
    intro x hx
    simp only [mem_Ioo, min_eq_left (by norm_num : (-1 : ℝ) ≤ 1),
      max_eq_right (by norm_num : (-1 : ℝ) ≤ 1)] at hx
    obtain ⟨hx1, hx2⟩ := hx
    have hx' : |x| < 1 := abs_lt.mpr ⟨by linarith, by linarith⟩
    have hd := gevreyDeriv2_hasDerivAt_of_abs_lt k x hk' hx'
    have hof : HasDerivAt (fun v : ℝ => (v : ℂ)) 1 (gevreyDeriv2 k x) :=
      Complex.ofRealCLM.hasDerivAt
    have hcomp := hof.scomp x hd
    simpa [Function.comp] using hcomp
  have hintG : IntervalIntegrable (fun u : ℝ => (gevreyInner k u : ℂ)) volume (-1 : ℝ) 1 :=
    hcontF.intervalIntegrable (μ := volume)
  have hintD : IntervalIntegrable (fun u : ℝ => (gevreyDeriv k u : ℂ)) volume (-1 : ℝ) 1 :=
    hcontG.intervalIntegrable (μ := volume)
  have hintD2 : IntervalIntegrable (fun u : ℝ => (gevreyDeriv2 k u : ℂ)) volume (-1 : ℝ) 1 :=
    hcontD.intervalIntegrable (μ := volume)
  have hintD3 : IntervalIntegrable (fun u : ℝ => (gevreyDeriv3 k u : ℂ)) volume (-1 : ℝ) 1 :=
    hcontD3.intervalIntegrable (μ := volume)
  have hintVe : IntervalIntegrable (fun u : ℝ => Complex.exp (w * (u : ℂ)))
      volume (-1 : ℝ) 1 :=
    (by fun_prop : Continuous (fun u : ℝ => Complex.exp (w * (u : ℂ)))).intervalIntegrable
      (-1 : ℝ) 1
  -- first integration by parts
  have hIBP1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := (-1 : ℝ)) (b := (1 : ℝ))
    (u := fun u : ℝ => (gevreyInner k u : ℂ))
    (v := fun u : ℝ => Complex.exp (w * (u : ℂ)) / w)
    (u' := fun x : ℝ => ((gevreyDeriv k x : ℝ) : ℂ))
    (v' := fun u : ℝ => Complex.exp (w * (u : ℂ)))
    hcontF hcontV hu1' hvv' hintD hintVe
  have hb1 : (gevreyInner k 1 : ℂ) = 0 := by
    simp [gevreyInner_of_one_le_abs k 1 abs_one.ge]
  have hb2 : (gevreyInner k (-1) : ℂ) = 0 := by
    simp [gevreyInner_of_one_le_abs k (-1) (by simp)]
  have hprod : (fun u : ℝ =>
        ((gevreyDeriv k u : ℝ) : ℂ) * (Complex.exp (w * (u : ℂ)) / w))
      = fun u : ℝ => (1 / w) * (((gevreyDeriv k u : ℝ) : ℂ) * Complex.exp (w * (u : ℂ))) := by
    funext u
    field_simp
  simp only [hb1, hb2, zero_mul, zero_sub, neg_zero, hprod,
    intervalIntegral.integral_const_mul] at hIBP1
  -- second integration by parts
  have hIBP2 := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := (-1 : ℝ)) (b := (1 : ℝ))
    (u := fun u : ℝ => (gevreyDeriv k u : ℂ))
    (v := fun u : ℝ => Complex.exp (w * (u : ℂ)) / w)
    (u' := fun x : ℝ => ((gevreyDeriv2 k x : ℝ) : ℂ))
    (v' := fun u : ℝ => Complex.exp (w * (u : ℂ)))
    hcontG hcontV hu2' hvv' hintD2 hintVe
  have gb1 : ((gevreyDeriv k 1 : ℝ) : ℂ) = 0 := by
    rw [gevreyDeriv_of_one_le_abs k 1 abs_one.ge]
    exact Complex.ofReal_zero
  have gb2 : ((gevreyDeriv k (-1) : ℝ) : ℂ) = 0 := by
    rw [gevreyDeriv_of_one_le_abs k (-1) (by simp)]
    exact Complex.ofReal_zero
  have hprod2 : (fun u : ℝ =>
        ((gevreyDeriv2 k u : ℝ) : ℂ) * (Complex.exp (w * (u : ℂ)) / w))
      = fun u : ℝ => (1 / w) * (((gevreyDeriv2 k u : ℝ) : ℂ) * Complex.exp (w * (u : ℂ))) := by
    funext u
    field_simp
  simp only [gb1, gb2, zero_mul, zero_sub, neg_zero, hprod2,
    intervalIntegral.integral_const_mul] at hIBP2
  -- third integration by parts
  have hIBP3 := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := (-1 : ℝ)) (b := (1 : ℝ))
    (u := fun u : ℝ => (gevreyDeriv2 k u : ℂ))
    (v := fun u : ℝ => Complex.exp (w * (u : ℂ)) / w)
    (u' := fun x : ℝ => ((gevreyDeriv3 k x : ℝ) : ℂ))
    (v' := fun u : ℝ => Complex.exp (w * (u : ℂ)))
    hcontD hcontV hu3' hvv' hintD3 hintVe
  have gb3 : ((gevreyDeriv2 k 1 : ℝ) : ℂ) = 0 := by
    rw [gevreyDeriv2_of_one_le_abs k 1 abs_one.ge]
    exact Complex.ofReal_zero
  have gb4 : ((gevreyDeriv2 k (-1) : ℝ) : ℂ) = 0 := by
    rw [gevreyDeriv2_of_one_le_abs k (-1) (by simp)]
    exact Complex.ofReal_zero
  have hprod3 : (fun u : ℝ =>
        ((gevreyDeriv3 k u : ℝ) : ℂ) * (Complex.exp (w * (u : ℂ)) / w))
      = fun u : ℝ => (1 / w) * (((gevreyDeriv3 k u : ℝ) : ℂ) * Complex.exp (w * (u : ℂ))) := by
    funext u
    field_simp
  simp only [gb3, gb4, zero_mul, zero_sub, neg_zero, hprod3,
    intervalIntegral.integral_const_mul] at hIBP3
  -- combine the three steps
  rw [hIBP1, hIBP2, hIBP3]
  have hnorm1 : ‖((1 / w : ℂ))‖ = 1 / ‖w‖ := by
    rw [norm_div, norm_one]
  simp only [norm_neg, norm_mul, hnorm1]
  -- pointwise exponential strip bound
  have hre : ∀ x ∈ Icc (-1 : ℝ) 1, (w * (x : ℂ)).re ≤ |w.re| := by
    intro x hx
    simp only [mem_Icc] at hx
    have hx1 : |x| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    have hmain : w.re * x ≤ |w.re * x| := le_abs_self _
    have hrest : |w.re * x| ≤ |w.re| := by
      rw [abs_mul]
      exact le_trans (mul_le_mul_of_nonneg_left hx1 (abs_nonneg w.re)) (by simp)
    exact le_trans hmain hrest
  have hinner : ‖∫ u in (-1 : ℝ)..(1 : ℝ),
        ((gevreyDeriv3 k u : ℝ) : ℂ) * Complex.exp (w * (u : ℂ))‖
      ≤ Real.exp |w.re| * ∫ u in (-1 : ℝ)..(1 : ℝ), |gevreyDeriv3 k u| := by
    have hcprod : Continuous (fun u : ℝ =>
        ((gevreyDeriv3 k u : ℝ) : ℂ) * Complex.exp (w * (u : ℂ))) :=
      (Complex.continuous_ofReal.comp (continuous_gevreyDeriv3 k hk')).mul (by fun_prop)
    have hfx : ∀ x ∈ Icc (-1 : ℝ) 1,
        ‖((gevreyDeriv3 k x : ℝ) : ℂ) * Complex.exp (w * (x : ℂ))‖
          ≤ |gevreyDeriv3 k x| * Real.exp |w.re| := by
      intro x hx
      rw [norm_mul, Complex.norm_exp]
      have h5 : ‖((gevreyDeriv3 k x : ℝ) : ℂ)‖ = |gevreyDeriv3 k x| := by norm_cast
      rw [h5]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hre x hx))
        (abs_nonneg _)
    calc ‖∫ u in (-1 : ℝ)..(1 : ℝ),
          ((gevreyDeriv3 k u : ℝ) : ℂ) * Complex.exp (w * (u : ℂ))‖
        ≤ ∫ u in (-1 : ℝ)..(1 : ℝ),
          ‖((gevreyDeriv3 k u : ℝ) : ℂ) * Complex.exp (w * (u : ℂ))‖ :=
        intervalIntegral.norm_integral_le_integral_norm (by norm_num)
      _ ≤ ∫ u in (-1 : ℝ)..(1 : ℝ), |gevreyDeriv3 k u| * Real.exp |w.re| := by
          refine intervalIntegral.integral_mono_on (by norm_num)
            ((hcprod.norm).intervalIntegrable (-1 : ℝ) 1)
            (((continuous_gevreyDeriv3 k hk').abs.mul
              continuous_const).intervalIntegrable (-1 : ℝ) 1)
            (fun x hx => ?_)
          simp only [mem_Icc] at hx
          exact hfx x hx
      _ = Real.exp |w.re| * ∫ u in (-1 : ℝ)..(1 : ℝ), |gevreyDeriv3 k u| := by
          rw [intervalIntegral.integral_mul_const]
          exact mul_comm _ _
  have hwne : (0 : ℝ) < ‖w‖ := norm_pos_iff.mpr hw
  have hJ3 := integral_abs_gevreyDeriv3_le k hk
  calc (1 / ‖w‖) * ((1 / ‖w‖) * ((1 / ‖w‖) * ‖∫ u in (-1 : ℝ)..(1 : ℝ),
        ((gevreyDeriv3 k u : ℝ) : ℂ) * Complex.exp (w * (u : ℂ))‖))
      ≤ (1 / ‖w‖) * ((1 / ‖w‖) * ((1 / ‖w‖) *
          (Real.exp |w.re| * ∫ u in (-1 : ℝ)..(1 : ℝ), |gevreyDeriv3 k u|))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hinner
            (div_nonneg zero_le_one (norm_nonneg w)))
          (div_nonneg zero_le_one (norm_nonneg w)))
        (div_nonneg zero_le_one (norm_nonneg w))
    _ ≤ (1 / ‖w‖) * ((1 / ‖w‖) * ((1 / ‖w‖) * (Real.exp |w.re| *
          (Real.exp (-k) * (9500 * k ^ 3 + 19400 * k ^ 2 + 6500 * k)
            + 2196115 * (k ^ 4)⁻¹ + 16470860 * (k ^ 5)⁻¹ + 19765032 * (k ^ 6)⁻¹)))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hJ3 (Real.exp_nonneg _))
            (div_nonneg zero_le_one (norm_nonneg w)))
          (div_nonneg zero_le_one (norm_nonneg w)))
        (div_nonneg zero_le_one (norm_nonneg w))
    _ = Real.exp |w.re| * (Real.exp (-k) * (9500 * k ^ 3 + 19400 * k ^ 2 + 6500 * k)
          + 2196115 * (k ^ 4)⁻¹ + 16470860 * (k ^ 5)⁻¹ + 19765032 * (k ^ 6)⁻¹) / ‖w‖ ^ 3 := by
      field_simp

/-- The pipeline form: at the pure-imaginary argument `a * t * I` the strip
factor is exactly `1`. -/
theorem laplace_abs_le_rung3_vertical (k a t : ℝ) (hk : 1 ≤ k) (ha : 0 < a)
    (ht : t ≠ 0) :
    ‖∫ u in (-1 : ℝ)..(1 : ℝ),
        (gevreyInner k u : ℂ) * Complex.exp ((a * t * Complex.I) * (u : ℂ))‖
        ≤ (Real.exp (-k) * (9500 * k ^ 3 + 19400 * k ^ 2 + 6500 * k)
            + 2196115 * (k ^ 4)⁻¹ + 16470860 * (k ^ 5)⁻¹ + 19765032 * (k ^ 6)⁻¹)
          / (a * |t|) ^ 3 := by
  have hnorm : ‖(a * t * Complex.I : ℂ)‖ = a * |t| := by
    have h1 : ‖(a * t * Complex.I : ℂ)‖
        = ‖((a : ℝ) : ℂ) * ((t : ℝ) : ℂ)‖ * ‖(Complex.I : ℂ)‖ := norm_mul _ _
    have h2 : ‖((a : ℝ) : ℂ) * ((t : ℝ) : ℂ)‖ = |a| * |t| := by
      have h3 : ‖((a : ℝ) : ℂ)‖ = |a| := by norm_cast
      have h4 : ‖((t : ℝ) : ℂ)‖ = |t| := by norm_cast
      rw [norm_mul, h3, h4]
    rw [h1, h2, Complex.norm_I, abs_of_pos ha, mul_one]
  have hne : (a * t * Complex.I : ℂ) ≠ 0 := by
    intro hc
    have hpos : (0 : ℝ) < a * |t| := mul_pos ha (abs_pos.mpr ht)
    have h0 : ‖(a * t * Complex.I : ℂ)‖ = 0 := by rw [hc, norm_zero]
    rw [hnorm] at h0
    exact absurd h0 (by linarith [hpos])
  have hmain := laplace_abs_le_rung3 k hk (a * t * Complex.I) hne
  have hre0 : ((a * t * Complex.I : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.I_re]
  rw [hre0, abs_zero, Real.exp_zero, one_mul, hnorm] at hmain
  exact hmain
