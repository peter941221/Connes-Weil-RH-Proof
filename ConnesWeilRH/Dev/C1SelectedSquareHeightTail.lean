/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.CCM25Concrete.UnscaledYoshidaSelectedOwner

/-!
# C1SelectedSquareHeightTail - two-sided height-form tail for the selected square

The assembly's distance-form tail carries `2 * |rho.im| <= |z.im|`; that
hypothesis is the only reason the construction radius tracks the height of
`rho`.  The quadratic frequency bounds on the base and on the correction are
global in the height, so the selected convolution square obeys a HEIGHT-form
tail at every strip point, with no `rho`, `T`, or `epsilon` anywhere.  All
statements are division-free, in the house form consumed by dyadic-shell
summation:

```
‖laplaceAt (selectedOwner b c n).convolutionSquare (z - 1/2)‖
    * ‖z.im / (2*π)‖^(4*(n+2))  <=  C_b^(2*(n+1)) * C_c^2
```

Design record: docs/proofs/1375_two_sided_tail_height_form_design.md.
-/

namespace ConnesWeilRH
namespace Source
namespace C1SelectedSquareHeightTail

open CC20YoshidaConvolution
open CC20YoshidaConvolution.CompactLogTest
open CCM25Concrete.CompactLogConvolution
open CCM25Concrete.UnscaledYoshidaSelectedOwner

noncomputable section

/-- A quadratic frequency bound is global in the height, so it evaluates
directly at any strip point: the frequency factor times the vertical Laplace
value is bounded by `C` with no height floor at all.  This pointwise engine
is the two-sided replacement for the `2 * |rho.im| <= |z.im|` distance
conversion. -/
theorem laplaceAt_heightQuadratic_le_of_quadraticBound
    {f : CompactLogTest} {C : ℝ}
    (hbound : ∀ sigma ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ,
      ‖t / (2 * Real.pi)‖ ^ 2 *
        ‖laplaceAt f ((sigma : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C)
    (z : ℂ) (hzre : z.re ∈ Set.Icc (0 : ℝ) 1) :
    ‖z.im / (2 * Real.pi)‖ ^ 2 * ‖laplaceAt f z‖ ≤ C := by
  have h := hbound z.re hzre z.im
  simpa only [Complex.re_add_im] using h

/-- Multiplicative height decay of the assembled Yoshida source: `(n+1)`
base powers times the correction at every strip point, with the global
frequency factor absorbing exactly `2*(n+2)` powers.  No `rho`, no height
floor. -/
theorem convolved_laplaceAt_heightQuadratic_le
    (base correction : CompactLogTest) (n : ℕ) {C_b C_c : ℝ}
    (hB : ∀ sigma ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ,
      ‖t / (2 * Real.pi)‖ ^ 2 *
        ‖laplaceAt base ((sigma : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C_b)
    (hC : ∀ sigma ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ,
      ‖t / (2 * Real.pi)‖ ^ 2 *
        ‖laplaceAt correction ((sigma : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C_c)
    (z : ℂ) (hzre : z.re ∈ Set.Icc (0 : ℝ) 1) :
    ‖z.im / (2 * Real.pi)‖ ^ (2 * (n + 2)) *
        ‖laplaceAt ((convolutionIterate base n).convolution correction) z‖ ≤
      C_b ^ (n + 1) * C_c := by
  have hb := laplaceAt_heightQuadratic_le_of_quadraticBound hB z hzre
  have hc := laplaceAt_heightQuadratic_le_of_quadraticBound hC z hzre
  have hCb : 0 ≤ C_b :=
    le_trans (mul_nonneg (sq_nonneg _) (norm_nonneg _)) hb
  rw [laplaceAt_convolution, laplaceAt_convolutionIterate, norm_mul, norm_pow]
  calc ‖z.im / (2 * Real.pi)‖ ^ (2 * (n + 2)) *
        (‖laplaceAt base z‖ ^ (n + 1) * ‖laplaceAt correction z‖)
      = (‖z.im / (2 * Real.pi)‖ ^ 2 * ‖laplaceAt base z‖) ^ (n + 1) *
        (‖z.im / (2 * Real.pi)‖ ^ 2 * ‖laplaceAt correction z‖) := by
        rw [mul_pow]
        ring
    _ ≤ C_b ^ (n + 1) * C_c :=
        mul_le_mul
          (pow_le_pow_left₀ (mul_nonneg (sq_nonneg _) (norm_nonneg _)) hb
            (n + 1))
          hc (mul_nonneg (sq_nonneg _) (norm_nonneg _)) (pow_nonneg hCb (n + 1))

/-- The two-sided HEIGHT-form tail for the selected convolution square: at
every strip point the Hermitian square value times the global frequency
factor to the `4*(n+2)` is bounded by an explicit constant.  There is no
`rho`, no `T`, and no `epsilon`; mid heights are covered exactly where the
distance-form tail hypothesis `2 * |rho.im| <= |z.im|` used to fail. -/
theorem selectedOwner_convolutionSquare_heightQuadraticTail
    (base correction : CompactLogTest) (n : ℕ) {C_b C_c : ℝ}
    (hB : ∀ sigma ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ,
      ‖t / (2 * Real.pi)‖ ^ 2 *
        ‖laplaceAt base ((sigma : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C_b)
    (hC : ∀ sigma ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ,
      ‖t / (2 * Real.pi)‖ ^ 2 *
        ‖laplaceAt correction ((sigma : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C_c)
    (z : ℂ) (hzre : z.re ∈ Set.Icc (0 : ℝ) 1) :
    ‖laplaceAt (selectedOwner base correction n).convolutionSquare
        (z - 1 / 2)‖ * ‖z.im / (2 * Real.pi)‖ ^ (4 * (n + 2)) ≤
      C_b ^ (2 * (n + 1)) * C_c ^ 2 := by
  rw [selectedOwner_laplaceAt_convolutionSquare_centered, norm_mul, norm_star]
  have hcompRe : (1 - star z).re ∈ Set.Icc (0 : ℝ) 1 := by
    have hstarRe : (star z).re = z.re := by simp
    rw [Complex.sub_re, Complex.one_re, hstarRe]
    constructor <;> linarith [hzre.1, hzre.2]
  have hcompIm : (1 - star z).im = z.im := by simp
  have hz1 := convolved_laplaceAt_heightQuadratic_le base correction n hB hC z
    hzre
  have hz2 := convolved_laplaceAt_heightQuadratic_le base correction n hB hC
    (1 - star z) hcompRe
  have hz1' : ‖laplaceAt ((convolutionIterate base n).convolution correction) z‖ *
      ‖z.im / (2 * Real.pi)‖ ^ (2 * (n + 2)) ≤ C_b ^ (n + 1) * C_c := by
    rw [mul_comm]
    exact hz1
  have hz2' : ‖laplaceAt ((convolutionIterate base n).convolution correction)
        (1 - star z)‖ *
      ‖(1 - star z).im / (2 * Real.pi)‖ ^ (2 * (n + 2)) ≤
      C_b ^ (n + 1) * C_c := by
    rw [mul_comm]
    exact hz2
  have hCb : 0 ≤ C_b :=
    le_trans (mul_nonneg (sq_nonneg (‖(1 : ℝ) / (2 * Real.pi)‖))
      (norm_nonneg (laplaceAt base ((z.re : ℂ) + (1 : ℝ) * Complex.I))))
      (hB z.re hzre 1)
  have hCc : 0 ≤ C_c :=
    le_trans (mul_nonneg (sq_nonneg (‖(1 : ℝ) / (2 * Real.pi)‖))
      (norm_nonneg (laplaceAt correction ((z.re : ℂ) + (1 : ℝ) * Complex.I))))
      (hC z.re hzre 1)
  have hfreqEq :
      ‖(1 - star z).im / (2 * Real.pi)‖ = ‖z.im / (2 * Real.pi)‖ := by
    rw [hcompIm]
  have hexp : 4 * (n + 2) = 2 * (n + 2) + 2 * (n + 2) := by ring
  calc ‖laplaceAt ((convolutionIterate base n).convolution correction)
          (1 - star z)‖ *
      ‖laplaceAt ((convolutionIterate base n).convolution correction) z‖ *
        ‖z.im / (2 * Real.pi)‖ ^ (4 * (n + 2))
    = (‖laplaceAt ((convolutionIterate base n).convolution correction)
          (1 - star z)‖ * ‖z.im / (2 * Real.pi)‖ ^ (2 * (n + 2))) *
      (‖laplaceAt ((convolutionIterate base n).convolution correction) z‖ *
        ‖z.im / (2 * Real.pi)‖ ^ (2 * (n + 2))) := by
        rw [hexp, pow_add]
        ring
  _ ≤ C_b ^ (n + 1) * C_c * (C_b ^ (n + 1) * C_c) := by
      refine mul_le_mul ?_ hz1'
        (mul_nonneg (norm_nonneg
          (laplaceAt ((convolutionIterate base n).convolution correction) z))
          (pow_nonneg (norm_nonneg (z.im / (2 * Real.pi))) (2 * (n + 2))))
        (mul_nonneg (pow_nonneg hCb (n + 1)) hCc)
      rw [← hfreqEq]
      exact hz2'
  _ = C_b ^ (2 * (n + 1)) * C_c ^ 2 := by
      ring

end

end C1SelectedSquareHeightTail
end Source
end ConnesWeilRH
