/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.CCM25Concrete.UnscaledYoshidaSelectedOwner
import ConnesWeilRH.Dev.C1SpectralTailBound
import ConnesWeilRH.Dev.C1HealthyYoshidaSpectralNegativity

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

The closing section converts this into the spectral currency: a
multiplicity-weighted `spectralNormTerm` bound on every dyadic height shell,
mirroring the fourth-order instance of `C1SpectralTailBound` with the
`2 * |rho.im|` hypothesis replaced by nothing at all.

Design record: docs/proofs/1375_two_sided_tail_height_form_design.md.
-/

namespace ConnesWeilRH
namespace Source
namespace C1SelectedSquareHeightTail

open CC20YoshidaConvolution
open CC20YoshidaConvolution.CompactLogTest
open CC20YoshidaNearZeros
open CCM25Concrete.CompactLogConvolution
open CCM25Concrete.UnscaledYoshidaSelectedOwner
open C1SpectralSummability
open C1SpectralTailBound
open C1SpectralWeil
open C1XiGlobalZeroSum
open C1HealthyYoshidaSpectralNegativity
open C1HealthyYoshidaUnscaledOrbit
open C1HealthyYoshidaDetector

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

/-- Raw-height restatement of the two-sided tail: the global frequency
factor is traded for an explicit `(2*π)` power on the constant, so the
statement compares `|Im z|` directly against dyadic shell heights. -/
theorem selectedOwner_convolutionSquare_heightTail_raw
    (base correction : CompactLogTest) (n : ℕ) {C_b C_c : ℝ}
    (hB : ∀ sigma ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ,
      ‖t / (2 * Real.pi)‖ ^ 2 *
        ‖laplaceAt base ((sigma : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C_b)
    (hC : ∀ sigma ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ,
      ‖t / (2 * Real.pi)‖ ^ 2 *
        ‖laplaceAt correction ((sigma : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C_c)
    (z : ℂ) (hzre : z.re ∈ Set.Icc (0 : ℝ) 1) :
    ‖laplaceAt (selectedOwner base correction n).convolutionSquare
        (z - 1 / 2)‖ * |z.im| ^ (4 * (n + 2)) ≤
      C_b ^ (2 * (n + 1)) * C_c ^ 2 * (2 * Real.pi) ^ (4 * (n + 2)) := by
  have h2pi : 0 < 2 * Real.pi := by positivity
  have h2ne : (2 : ℝ) * Real.pi ≠ 0 := ne_of_gt h2pi
  have hprod : ‖z.im / (2 * Real.pi)‖ * (2 * Real.pi) = |z.im| := by
    rw [Real.norm_eq_abs, abs_div, abs_of_pos h2pi]
    field_simp
  have hfreq : |z.im| ^ (4 * (n + 2)) =
      ‖z.im / (2 * Real.pi)‖ ^ (4 * (n + 2)) *
        (2 * Real.pi) ^ (4 * (n + 2)) := by
    rw [← hprod, mul_pow]
  calc ‖laplaceAt (selectedOwner base correction n).convolutionSquare
          (z - 1 / 2)‖ * |z.im| ^ (4 * (n + 2))
    = ‖laplaceAt (selectedOwner base correction n).convolutionSquare
          (z - 1 / 2)‖ * ‖z.im / (2 * Real.pi)‖ ^ (4 * (n + 2)) *
        (2 * Real.pi) ^ (4 * (n + 2)) := by
        rw [hfreq]
        ring
  _ ≤ C_b ^ (2 * (n + 1)) * C_c ^ 2 * (2 * Real.pi) ^ (4 * (n + 2)) :=
      mul_le_mul_of_nonneg_right
        (selectedOwner_convolutionSquare_heightQuadraticTail base correction n
          hB hC z hzre)
        (pow_nonneg (le_of_lt h2pi) (4 * (n + 2)))

/-- Spectral currency of the height tail: on dyadic height shell `k + 1`
the multiplicity-weighted norm term of the selected square is bounded by
the explicit constant times the shell height decay, with NO `2 * |rho.im|`
hypothesis.  This is the height-form mirror of
`spectralTerm_norm_tail_instance_of_fourthOrderTail`. -/
theorem spectralNormTerm_shell_instance_of_heightTail
    (base correction : CompactLogTest) (n : ℕ) {C_b C_c : ℝ}
    (hB : ∀ sigma ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ,
      ‖t / (2 * Real.pi)‖ ^ 2 *
        ‖laplaceAt base ((sigma : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C_b)
    (hC : ∀ sigma ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ,
      ‖t / (2 * Real.pi)‖ ^ 2 *
        ‖laplaceAt correction ((sigma : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C_c)
    (k : ℕ) (sigma : spectralHeightShell (k + 1)) :
    spectralNormTerm (selectedOwner base correction n).convolutionSquare
        sigma.1 *
      ((2 : Real) ^ (k + 1)) ^ (4 * (n + 2)) ≤
      (xiMultiplicity sigma.1 : ℝ) *
        (C_b ^ (2 * (n + 1)) * C_c ^ 2 * (2 * Real.pi) ^ (4 * (n + 2))) := by
  have hstrip : sigma.1.1.re ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨(sourceNontrivialZero_zero_lt_re sigma.1.2).le,
      (sourceNontrivialZero_re_lt_one sigma.1.2).le⟩
  have hraw := selectedOwner_convolutionSquare_heightTail_raw base correction
    n hB hC sigma.1.1 hstrip
  have hshell : (2 : Real) ^ (k + 1) ≤ |sigma.1.1.im| := shell_lower_im sigma.2
  have hpow : ((2 : Real) ^ (k + 1)) ^ (4 * (n + 2)) ≤
      |sigma.1.1.im| ^ (4 * (n + 2)) :=
    pow_le_pow_left₀ (by norm_num) hshell (4 * (n + 2))
  have hterm :
      spectralNormTerm (selectedOwner base correction n).convolutionSquare
          sigma.1 =
        (xiMultiplicity sigma.1 : ℝ) *
          ‖laplaceAt (selectedOwner base correction n).convolutionSquare
            (sigma.1.1 - 1 / 2)‖ :=
    rfl
  rw [hterm, mul_assoc]
  calc (xiMultiplicity sigma.1 : ℝ) *
        (‖laplaceAt (selectedOwner base correction n).convolutionSquare
            (sigma.1.1 - 1 / 2)‖ * ((2 : Real) ^ (k + 1)) ^ (4 * (n + 2)))
    _ ≤ (xiMultiplicity sigma.1 : ℝ) *
          (‖laplaceAt (selectedOwner base correction n).convolutionSquare
            (sigma.1.1 - 1 / 2)‖ * |sigma.1.1.im| ^ (4 * (n + 2))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hpow (norm_nonneg _))
          (Nat.cast_nonneg _)
    _ ≤ (xiMultiplicity sigma.1 : ℝ) *
          (C_b ^ (2 * (n + 1)) * C_c ^ 2 * (2 * Real.pi) ^ (4 * (n + 2))) :=
        mul_le_mul_of_nonneg_left hraw (Nat.cast_nonneg _)

/-- Shell-summation of the height-form instance: above any dyadic start the
multiplicity-weighted norm term of the selected square sums to an explicit
geometric budget with ratio `3 / 2^(4*(n+2))`, closing value
`1 / (2^(4*(n+2)) - 3)`.  This is the height-form mirror of
`spectralTail_norm_shellSum_le_of_fourthOrderTail` with no `epsilon`, no
`T`, and no `rho` anywhere.  The shell start `N` is the wrapper's knob: the
low-height hypothesis empties the shells below the certificate height, and
larger `N` only shrinks the constant. -/
theorem spectralNormTerm_shellSum_le_of_heightTail
    (base correction : CompactLogTest) (n : ℕ) {C_b C_c : ℝ}
    (hB : ∀ sigma ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ,
      ‖t / (2 * Real.pi)‖ ^ 2 *
        ‖laplaceAt base ((sigma : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C_b)
    (hC : ∀ sigma ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ,
      ‖t / (2 * Real.pi)‖ ^ 2 *
        ‖laplaceAt correction ((sigma : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C_c)
    (N : ℕ) :
    (∑' m : Nat, ∑' sigma : spectralHeightShell (m + N + 1),
        spectralNormTerm (selectedOwner base correction n).convolutionSquare
          sigma.1) ≤
      spectralMultiplicityConstant *
        (C_b ^ (2 * (n + 1)) * C_c ^ 2 * (2 * Real.pi) ^ (4 * (n + 2))) *
        ((3 : Real) / (2 : Real) ^ (4 * (n + 2))) ^ N /
        ((2 : Real) ^ (4 * (n + 2)) - 3) := by
  have h2pi : 0 < 2 * Real.pi := by positivity
  have hzre : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hCb : 0 ≤ C_b :=
    le_trans (mul_nonneg (sq_nonneg _) (norm_nonneg _)) (hB 0 hzre 1)
  have hCc : 0 ≤ C_c :=
    le_trans (mul_nonneg (sq_nonneg _) (norm_nonneg _)) (hC 0 hzre 1)
  have hKc : 0 ≤ C_b ^ (2 * (n + 1)) * C_c ^ 2 * (2 * Real.pi) ^ (4 * (n + 2)) :=
    mul_nonneg (mul_nonneg (pow_nonneg hCb (2 * (n + 1))) (sq_nonneg C_c))
      (pow_nonneg (le_of_lt h2pi) (4 * (n + 2)))
  have hWpos : 0 < (2 : Real) ^ (4 * (n + 2)) := pow_pos (by norm_num) _
  have hWne : (2 : Real) ^ (4 * (n + 2)) ≠ 0 := ne_of_gt hWpos
  have h8 : 8 ≤ 4 * (n + 2) := by omega
  have hW3 : (3 : Real) < (2 : Real) ^ (4 * (n + 2)) :=
    calc (3 : Real) < (2 : Real) ^ 8 := by norm_num
      _ ≤ (2 : Real) ^ (4 * (n + 2)) := pow_le_pow_right₀ (by norm_num) h8
  have hW3ne : (2 : Real) ^ (4 * (n + 2)) - 3 ≠ 0 := ne_of_gt (by linarith)
  have hr0 : 0 ≤ (3 : Real) / (2 : Real) ^ (4 * (n + 2)) :=
    le_of_lt (div_pos (by norm_num) hWpos)
  have hr1 : (3 : Real) / (2 : Real) ^ (4 * (n + 2)) < 1 := by
    rw [div_lt_iff₀ hWpos]
    linarith
  have hperM : ∀ m : ℕ,
      (∑' sigma : spectralHeightShell (m + N + 1),
          spectralNormTerm (selectedOwner base correction n).convolutionSquare
            sigma.1) ≤
        spectralMultiplicityConstant *
          (C_b ^ (2 * (n + 1)) * C_c ^ 2 * (2 * Real.pi) ^ (4 * (n + 2))) /
          (2 : Real) ^ (4 * (n + 2)) *
          ((3 : Real) / (2 : Real) ^ (4 * (n + 2))) ^ (m + N) := by
    intro m
    letI := (spectralHeightShell_finite (m + N + 1)).fintype
    have hmassN' :
        (∑' sigma : spectralHeightShell (m + N + 1),
            (xiMultiplicity sigma.1 : Real)) ≤
          spectralMultiplicityConstant * (3 : Real) ^ (m + N) := by
      simpa [spectralHeightMultiplicity] using
        spectralHeightMultiplicity_geometric_bound (m + N)
    have hmassN :
        (∑ sigma : spectralHeightShell (m + N + 1),
            (xiMultiplicity sigma.1 : Real)) ≤
          spectralMultiplicityConstant * (3 : Real) ^ (m + N) := by
      rw [tsum_fintype] at hmassN'
      exact hmassN'
    have hPpow : ((2 : Real) ^ (m + N + 1)) ^ (4 * (n + 2)) =
        ((2 : Real) ^ (4 * (n + 2))) ^ (m + N + 1) := by
      rw [← pow_mul, ← pow_mul]
      rw [mul_comm (m + N + 1) (4 * (n + 2))]
    have hsum :
        (∑ sigma : spectralHeightShell (m + N + 1),
            spectralNormTerm (selectedOwner base correction n).convolutionSquare
              sigma.1) *
          ((2 : Real) ^ (4 * (n + 2))) ^ (m + N + 1) ≤
        spectralMultiplicityConstant *
          (C_b ^ (2 * (n + 1)) * C_c ^ 2 * (2 * Real.pi) ^ (4 * (n + 2))) *
          (3 : Real) ^ (m + N) := by
      rw [Finset.sum_mul]
      calc (∑ sigma : spectralHeightShell (m + N + 1),
              spectralNormTerm (selectedOwner base correction n).convolutionSquare
                sigma.1 * ((2 : Real) ^ (4 * (n + 2))) ^ (m + N + 1)) ≤
          (∑ sigma : spectralHeightShell (m + N + 1),
              (xiMultiplicity sigma.1 : Real) *
                (C_b ^ (2 * (n + 1)) * C_c ^ 2 * (2 * Real.pi) ^ (4 * (n + 2)))) :=
        Finset.sum_le_sum (fun sigma _sigma => by
          rw [← hPpow]
          exact spectralNormTerm_shell_instance_of_heightTail base correction n
            hB hC (m + N) sigma)
      _ = (C_b ^ (2 * (n + 1)) * C_c ^ 2 * (2 * Real.pi) ^ (4 * (n + 2))) *
            (∑ sigma : spectralHeightShell (m + N + 1),
              (xiMultiplicity sigma.1 : Real)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun sigma _ => mul_comm _ _)
      _ ≤ (C_b ^ (2 * (n + 1)) * C_c ^ 2 * (2 * Real.pi) ^ (4 * (n + 2))) *
            (spectralMultiplicityConstant * (3 : Real) ^ (m + N)) :=
        mul_le_mul_of_nonneg_left hmassN hKc
      _ = spectralMultiplicityConstant *
            (C_b ^ (2 * (n + 1)) * C_c ^ 2 * (2 * Real.pi) ^ (4 * (n + 2))) *
            (3 : Real) ^ (m + N) := by ring
    have hkey : spectralMultiplicityConstant *
          (C_b ^ (2 * (n + 1)) * C_c ^ 2 * (2 * Real.pi) ^ (4 * (n + 2))) /
          (2 : Real) ^ (4 * (n + 2)) *
          ((3 : Real) / (2 : Real) ^ (4 * (n + 2))) ^ (m + N) *
          ((2 : Real) ^ (4 * (n + 2))) ^ (m + N + 1) =
        spectralMultiplicityConstant *
          (C_b ^ (2 * (n + 1)) * C_c ^ 2 * (2 * Real.pi) ^ (4 * (n + 2))) *
          (3 : Real) ^ (m + N) := by
      have hWpowne : ((2 : Real) ^ (4 * (n + 2))) ^ (m + N) ≠ 0 :=
        pow_ne_zero _ hWne
      rw [div_pow, pow_add]
      field_simp
      rw [pow_add, pow_one]
      ring
    have hPPos : 0 < ((2 : Real) ^ (4 * (n + 2))) ^ (m + N + 1) :=
      pow_pos hWpos _
    rw [tsum_fintype]
    refine le_of_mul_le_mul_right ?_ hPPos
    calc (∑ sigma : spectralHeightShell (m + N + 1),
            spectralNormTerm (selectedOwner base correction n).convolutionSquare
              sigma.1) *
          ((2 : Real) ^ (4 * (n + 2))) ^ (m + N + 1) ≤
        spectralMultiplicityConstant *
          (C_b ^ (2 * (n + 1)) * C_c ^ 2 * (2 * Real.pi) ^ (4 * (n + 2))) *
          (3 : Real) ^ (m + N) := hsum
      _ = spectralMultiplicityConstant *
            (C_b ^ (2 * (n + 1)) * C_c ^ 2 * (2 * Real.pi) ^ (4 * (n + 2))) /
            (2 : Real) ^ (4 * (n + 2)) *
            ((3 : Real) / (2 : Real) ^ (4 * (n + 2))) ^ (m + N) *
            ((2 : Real) ^ (4 * (n + 2))) ^ (m + N + 1) := hkey.symm
  have hgeoConst : Summable (fun m : Nat =>
      spectralMultiplicityConstant *
        (C_b ^ (2 * (n + 1)) * C_c ^ 2 * (2 * Real.pi) ^ (4 * (n + 2))) /
        (2 : Real) ^ (4 * (n + 2)) *
        ((3 : Real) / (2 : Real) ^ (4 * (n + 2))) ^ (m + N)) := by
    have hgeo : Summable (fun m : Nat =>
        ((3 : Real) / (2 : Real) ^ (4 * (n + 2))) ^ m) :=
      summable_geometric_of_lt_one hr0 hr1
    refine (hgeo.mul_left (spectralMultiplicityConstant *
      (C_b ^ (2 * (n + 1)) * C_c ^ 2 * (2 * Real.pi) ^ (4 * (n + 2))) /
      (2 : Real) ^ (4 * (n + 2)) *
      ((3 : Real) / (2 : Real) ^ (4 * (n + 2))) ^ N)).congr ?_
    intro m
    rw [pow_add]
    ring
  have hsummable : Summable (fun m : Nat =>
      ∑' sigma : spectralHeightShell (m + N + 1),
        spectralNormTerm (selectedOwner base correction n).convolutionSquare
          sigma.1) :=
    Summable.of_nonneg_of_le
      (fun m => tsum_nonneg (fun sigma => by
        have hterm : spectralNormTerm
            (selectedOwner base correction n).convolutionSquare sigma.1 =
            (xiMultiplicity sigma.1 : ℝ) *
              ‖laplaceAt (selectedOwner base correction n).convolutionSquare
                (sigma.1.1 - 1 / 2)‖ := rfl
        rw [hterm]
        exact mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)))
      (fun m => hperM m) hgeoConst
  calc (∑' m : Nat, ∑' sigma : spectralHeightShell (m + N + 1),
        spectralNormTerm (selectedOwner base correction n).convolutionSquare
          sigma.1) ≤
      ∑' m : Nat, spectralMultiplicityConstant *
        (C_b ^ (2 * (n + 1)) * C_c ^ 2 * (2 * Real.pi) ^ (4 * (n + 2))) /
        (2 : Real) ^ (4 * (n + 2)) *
        ((3 : Real) / (2 : Real) ^ (4 * (n + 2))) ^ (m + N) :=
    hsummable.tsum_le_tsum (fun m => hperM m) hgeoConst
  _ = ∑' m : Nat, (spectralMultiplicityConstant *
        (C_b ^ (2 * (n + 1)) * C_c ^ 2 * (2 * Real.pi) ^ (4 * (n + 2))) /
        (2 : Real) ^ (4 * (n + 2)) *
        ((3 : Real) / (2 : Real) ^ (4 * (n + 2))) ^ N) *
        ((3 : Real) / (2 : Real) ^ (4 * (n + 2))) ^ m := by
    refine tsum_congr (fun m => ?_)
    rw [pow_add]
    ring
  _ = spectralMultiplicityConstant *
        (C_b ^ (2 * (n + 1)) * C_c ^ 2 * (2 * Real.pi) ^ (4 * (n + 2))) /
        (2 : Real) ^ (4 * (n + 2)) *
        ((3 : Real) / (2 : Real) ^ (4 * (n + 2))) ^ N *
        ∑' m : Nat, ((3 : Real) / (2 : Real) ^ (4 * (n + 2))) ^ m := by
    rw [tsum_mul_left]
  _ = spectralMultiplicityConstant *
        (C_b ^ (2 * (n + 1)) * C_c ^ 2 * (2 * Real.pi) ^ (4 * (n + 2))) /
        (2 : Real) ^ (4 * (n + 2)) *
        ((3 : Real) / (2 : Real) ^ (4 * (n + 2))) ^ N *
        (1 / (1 - (3 : Real) / (2 : Real) ^ (4 * (n + 2)))) := by
    rw [tsum_geometric_of_lt_one hr0 hr1]
    ring
  _ = spectralMultiplicityConstant *
        (C_b ^ (2 * (n + 1)) * C_c ^ 2 * (2 * Real.pi) ^ (4 * (n + 2))) *
        ((3 : Real) / (2 : Real) ^ (4 * (n + 2))) ^ N /
        ((2 : Real) ^ (4 * (n + 2)) - 3) := by
    field_simp

/-- The height-form budget composes with the shell-prefix anchor accounting:
a controlled low-shell prefix plus the explicit geometric height budget give
the strictly negative spectral value, with no `2 * |rho.im|` height floor and
no `T` anywhere.  This is the height-tail mirror of
`spectralWeilValue_neg_of_spectralHeightShellPrefix_and_fourthOrderTail`; the
budget inequality is an explicit hypothesis, so the wrapper discharges it by
choosing the construction iterate `n` large enough. -/
theorem spectralWeilValue_neg_of_prefix_and_heightTail
    (base correction : CompactLogTest) (n : ℕ) {C_b C_c : ℝ}
    (hB : ∀ sigma ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ,
      ‖t / (2 * Real.pi)‖ ^ 2 *
        ‖laplaceAt base ((sigma : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C_b)
    (hC : ∀ sigma ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ,
      ‖t / (2 * Real.pi)‖ ^ 2 *
        ‖laplaceAt correction ((sigma : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C_c)
    (rho : sourceNontrivialZeroSet) (N : ℕ)
    (hprefix :
      (∑ k ∈ Finset.range (N + 1), ∑' z : spectralHeightShell k,
          spectralTerm (selectedOwner base correction n).convolutionSquare
            z.1).re ≤
        -(xiMultiplicity rho : Real))
    (hsmall : spectralMultiplicityConstant *
        (C_b ^ (2 * (n + 1)) * C_c ^ 2 * (2 * Real.pi) ^ (4 * (n + 2))) *
        ((3 : Real) / (2 : Real) ^ (4 * (n + 2))) ^ N /
        ((2 : Real) ^ (4 * (n + 2)) - 3) <
          (xiMultiplicity rho : Real)) :
    spectralWeilValue (selectedOwner base correction n).convolutionSquare < 0 := by
  have htail := spectralNormTerm_shellSum_le_of_heightTail base correction n hB hC N
  have htail' :
      (∑' m : Nat, ∑' z : spectralHeightShell (m + (N + 1)),
          ‖spectralTerm (selectedOwner base correction n).convolutionSquare
            z.1‖) ≤
        spectralMultiplicityConstant *
          (C_b ^ (2 * (n + 1)) * C_c ^ 2 * (2 * Real.pi) ^ (4 * (n + 2))) *
          ((3 : Real) / (2 : Real) ^ (4 * (n + 2))) ^ N /
          ((2 : Real) ^ (4 * (n + 2)) - 3) := by
    simpa only [Nat.add_assoc, norm_spectralTerm] using htail
  exact spectralWeilValue_neg_of_spectralHeightShellPrefix_and_tail
    (selectedOwner base correction n).convolutionSquare rho (N + 1) hprefix
    (htail'.trans_lt hsmall)

/-- The N0' assembly variant: the same target and kill interpolation is
available at ANY construction iterate `n` — the base transform is one at
every target and the correction vanishes at every non-target node, so the
assembled values do not depend on `n`.  The distance-form tail is dropped
entirely, and the correction's quadratic frequency bound is exported so the
height-form tail can consume it. -/
theorem exists_nearbyZero_targetValues_assembly_anyIterate
    (base : CompactLogTest) {baseLower baseUpper : ℝ}
    (hbaseSupport : Function.support base.test ⊆ Set.Ioo baseLower baseUpper)
    (targetNodes : Finset ℂ)
    (hbaseTargets : ∀ w : FiniteMellinNode targetNodes,
      laplaceAt base w.1 = 1)
    (targetValues : FiniteMellinNode targetNodes → ℂ)
    (rho : ℂ) (routeNodes : Finset ℂ)
    {lower upper : ℝ} (hlower : lower < 0) (hupper : 0 < upper)
    (R : ℝ) (n : ℕ) :
    ∃ correction : CompactLogTest, ∃ C : ℝ,
      Function.support correction.test ⊆ Set.Ioo lower upper ∧
      Function.support
          ((convolutionIterate base n).convolution correction).test ⊆
        Set.Ioo (((n + 1 : ℕ) : ℝ) * baseLower + lower)
          (((n + 1 : ℕ) : ℝ) * baseUpper + upper) ∧
      (∀ w : FiniteMellinNode targetNodes,
        laplaceAt ((convolutionIterate base n).convolution correction) w.1 =
          targetValues w) ∧
      (∀ z : FiniteMellinNode
          (sourceNontrivialZerosInClosedBallFinset rho R ∪ routeNodes),
        z.1 ∉ targetNodes →
          laplaceAt ((convolutionIterate base n).convolution correction) z.1 = 0) ∧
      0 ≤ C ∧
      (∀ sigma ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ,
        ‖t / (2 * Real.pi)‖ ^ 2 *
          ‖laplaceAt correction ((sigma : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C) := by
  let selectedNodes : Finset ℂ :=
    sourceNontrivialZerosInClosedBallFinset rho R ∪ routeNodes
  let nodes : Finset ℂ := selectedNodes ∪ targetNodes
  let y : FiniteMellinNode nodes → ℂ := fun z =>
    if hz : z.1 ∈ targetNodes then targetValues ⟨z.1, hz⟩ else 0
  obtain ⟨correction, C, hcorrectionSupport, hvalues, hC, hquadratic⟩ :=
    exists_residualWindow_correction_with_quadratic_decay nodes hlower hupper y
  have hassembledSupport := convolution_support_subset_add_Ioo
    (convolutionIterate base n) correction
    (convolutionIterate_support_subset_Ioo base hbaseSupport n)
    hcorrectionSupport
  have hassembledTargets :
      ∀ w : FiniteMellinNode targetNodes,
        laplaceAt
          ((convolutionIterate base n).convolution correction) w.1 =
            targetValues w := by
    intro w
    let wNode : FiniteMellinNode nodes :=
      ⟨w.1, Finset.mem_union_right selectedNodes w.2⟩
    have hcorrectionTarget :
        laplaceAt correction w.1 = targetValues w := by
      simpa [y, wNode, w.2] using hvalues wNode
    rw [laplaceAt_convolution, laplaceAt_convolutionIterate,
      hbaseTargets w, hcorrectionTarget]
    simp
  have hassembledZeros :
      ∀ z : FiniteMellinNode selectedNodes, z.1 ∉ targetNodes →
        laplaceAt
          ((convolutionIterate base n).convolution correction) z.1 = 0 := by
    intro z hz
    let zNode : FiniteMellinNode nodes :=
      ⟨z.1, Finset.mem_union_left targetNodes z.2⟩
    have hcorrectionZero : laplaceAt correction z.1 = 0 := by
      simpa [y, zNode, hz] using hvalues zNode
    rw [laplaceAt_convolution, laplaceAt_convolutionIterate,
      hcorrectionZero]
    simp
  refine ⟨correction, C, hcorrectionSupport, hassembledSupport,
    hassembledTargets, ?_, hC, hquadratic⟩
  intro z hz
  exact hassembledZeros z hz

/-- The N0' small-support wrapper: a healthy construction carrying explicit
quadratic frequency bounds and the height-form budget produces healthy
detector data whose support is the assembled `(n+1)`-fold window.  There is
no `2 * |rho.im|` height floor and no `T` anywhere: the construction iterate
`n` is chosen by the budget, and the prefix kills cover exactly the dyadic
shells below `N + 1`. -/
theorem exists_smallSupport_healthyDetectorData_of_quadraticBounds_and_heightBudget
    (base correction : CompactLogTest) (n : ℕ)
    {baseLower baseUpper lower upper : ℝ}
    (hbaseSupport : Function.support base.test ⊆ Set.Ioo baseLower baseUpper)
    (hcorrSupport : Function.support correction.test ⊆ Set.Ioo lower upper)
    (rho : sourceNontrivialZeroSet) (hoff : rho.1.re ≠ 1 / 2)
    (hright : (1 / 2 : Real) < rho.1.re)
    (routeNodes : Finset Complex)
    (N : ℕ) (hrhoShell : dyadicShellIndex |rho.1.im| < N + 1)
    (htargetValues :
      ∀ w : FiniteMellinNode (healthyUnscaledTargetNodes rho.1),
        laplaceAt ((convolutionIterate base n).convolution correction) w.1 =
          healthyUnscaledTargetValue rho.1 w)
    (hsquareZeros :
      ∀ w : FiniteMellinNode
          (sourceNontrivialZerosInClosedBallFinset rho.1
              ((2 : Real) ^ (N + 1) + 2 + dist (2 : Complex) rho.1) ∪ routeNodes),
        w.1 ∉ healthyUnscaledTargetNodes rho.1 →
          laplaceAt (selectedOwner base correction n).convolutionSquare
            (w.1 - 1 / 2) = 0)
    {C_b C_c : ℝ}
    (hB : ∀ sigma ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ,
      ‖t / (2 * Real.pi)‖ ^ 2 *
        ‖laplaceAt base ((sigma : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C_b)
    (hC : ∀ sigma ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ,
      ‖t / (2 * Real.pi)‖ ^ 2 *
        ‖laplaceAt correction ((sigma : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C_c)
    (hnb : spectralMultiplicityConstant *
        (C_b ^ (2 * (n + 1)) * C_c ^ 2 * (2 * Real.pi) ^ (4 * (n + 2))) *
        ((3 : Real) / (2 : Real) ^ (4 * (n + 2))) ^ N /
        ((2 : Real) ^ (4 * (n + 2)) - 3) <
        (xiMultiplicity rho : Real)) :
    ∃ g : CompactLogTest, HealthyYoshidaDetectorData rho.1 g ∧
      Function.support g.test ⊆
        Set.Ioo (((n + 1 : ℕ) : ℝ) * baseLower + lower)
          (((n + 1 : ℕ) : ℝ) * baseUpper + upper) := by
  refine ⟨(selectedOwner base correction n).sourceTest, ?_, ?_⟩
  · have hhalf :
        laplaceAt ((convolutionIterate base n).convolution correction)
            (1 / 2 : Complex) = 0 := by
      calc laplaceAt ((convolutionIterate base n).convolution correction)
            (1 / 2 : Complex) =
          healthyUnscaledTargetValue rho.1
            ⟨1 / 2, mem_healthyUnscaledTargetNodes_half rho.1⟩ :=
            htargetValues ⟨1 / 2, mem_healthyUnscaledTargetNodes_half rho.1⟩
        _ = 0 := healthyUnscaledTargetValue_half rho.2 hoff
    have hone :
        laplaceAt ((convolutionIterate base n).convolution correction) 1 = 0 := by
      calc laplaceAt ((convolutionIterate base n).convolution correction) 1 =
          healthyUnscaledTargetValue rho.1
            ⟨1, mem_healthyUnscaledTargetNodes_one rho.1⟩ :=
            htargetValues ⟨1, mem_healthyUnscaledTargetNodes_one rho.1⟩
        _ = 0 := healthyUnscaledTargetValue_one rho.2 hoff
    have hthreeHalf :
        laplaceAt ((convolutionIterate base n).convolution correction)
            (3 / 2 : Complex) = 0 := by
      calc laplaceAt ((convolutionIterate base n).convolution correction)
            (3 / 2 : Complex) =
          healthyUnscaledTargetValue rho.1
            ⟨3 / 2, mem_healthyUnscaledTargetNodes_threeHalf rho.1⟩ :=
            htargetValues
              ⟨3 / 2, mem_healthyUnscaledTargetNodes_threeHalf rho.1⟩
        _ = 0 := healthyUnscaledTargetValue_threeHalf rho.2
    have hdetect :
        laplaceAt ((convolutionIterate base n).convolution correction)
          (rho.1 + 1 / 2) ≠ 0 := by
      rw [htargetValues
        ⟨rho.1 + 1 / 2, mem_healthyUnscaledTargetNodes_detector rho.1⟩]
      exact healthyUnscaledTargetValue_detector_ne_zero rho.1 hoff
    have hneg :
        spectralWeilValue (selectedOwner base correction n).convolutionSquare <
          0 := by
      have hprefix :=
        spectralHeightShellPrefix_re_le_neg_xiMultiplicity_of_closedBall_square_zero_control
          base correction n rho hoff hright (N + 1) hrhoShell routeNodes
          htargetValues hsquareZeros
      exact spectralWeilValue_neg_of_prefix_and_heightTail base correction n
        hB hC rho N hprefix hnb
    show HealthyYoshidaDetectorData rho.1
      (halfDensityShift ((convolutionIterate base n).convolution correction))
    refine healthyDetectorData_halfDensityShift_of_raw_values_of_spectral_neg
      hhalf hone hthreeHalf ((bne_iff_ne).mpr hdetect) ?_
    change spectralWeilValue
      (selectedOwner base correction n).convolutionSquare < 0
    exact hneg
  · simp only [selectedOwner_sourceTest]
    exact halfDensityShift_support_subset _
      (convolution_support_subset_add_Ioo (convolutionIterate base n)
        correction (convolutionIterate_support_subset_Ioo base hbaseSupport n)
        hcorrSupport)

/-- E2 (budget discharge, preregistered in 1375 s9): under the height-decay
hypothesis `C_b ^ 2 * (2 * π) ^ 4 < 2 ^ (4 * (N + 1))` the explicit geometric
budget of `spectralNormTerm_shellSum_le_of_heightTail` falls below
`xiMultiplicity rho` for some iterate count `n`.  Route: `budget n ≤ c₀ * q ^ n`
with `q = C_b ^ 2 * (2 * π) ^ 4 / 2 ^ (4 * (N + 1)) < 1` (the `2 / W` fold-in
plus exact exponent bookkeeping), then geometric decay to `0` beats the fixed
positive constant `xiMultiplicity rho`. -/
theorem exists_iterate_heightTail_budget_lt_xiMultiplicity
    (rho : sourceNontrivialZeroSet) (N : ℕ) {C_b C_c : ℝ}
    (hCb : 0 ≤ C_b) (hCc : 0 ≤ C_c)
    (hdecay : C_b ^ 2 * (2 * Real.pi) ^ 4 < (2 : Real) ^ (4 * (N + 1))) :
    ∃ n : ℕ,
      spectralMultiplicityConstant *
        (C_b ^ (2 * (n + 1)) * C_c ^ 2 * (2 * Real.pi) ^ (4 * (n + 2))) *
        ((3 : Real) / (2 : Real) ^ (4 * (n + 2))) ^ N /
        ((2 : Real) ^ (4 * (n + 2)) - 3) <
        (xiMultiplicity rho : Real) := by
  have h2pi : 0 < 2 * Real.pi := by positivity
  have hqden : 0 < (2 : Real) ^ (4 * (N + 1)) := pow_pos (by norm_num) _
  set q : ℝ := C_b ^ 2 * (2 * Real.pi) ^ 4 / (2 : Real) ^ (4 * (N + 1)) with hqdef
  set c0 : ℝ := 2 * spectralMultiplicityConstant *
    (C_b ^ 2 * C_c ^ 2 * (2 * Real.pi) ^ 8) * (3 : Real) ^ N /
    (2 : Real) ^ (8 * (N + 1)) with hc0def
  have hq0 : 0 ≤ q :=
    div_nonneg (mul_nonneg (pow_nonneg hCb 2) (pow_nonneg (le_of_lt h2pi) 4))
      (le_of_lt hqden)
  have hqlt : q < 1 := by
    rw [hqdef, div_lt_iff₀ hqden]
    linarith
  have hgeo : Summable fun m : ℕ => q ^ m :=
    summable_geometric_of_lt_one hq0 hqlt
  have hzero : Filter.Tendsto (fun m : ℕ => c0 * q ^ m) Filter.atTop (nhds 0) :=
    (hgeo.mul_left c0).tendsto_atTop_zero
  have hxi := xiMultiplicity_pos rho
  have hxipos : (0 : ℝ) < (xiMultiplicity rho : Real) :=
    Nat.cast_pos.mpr hxi
  have hmajor : ∀ n : ℕ,
      spectralMultiplicityConstant *
        (C_b ^ (2 * (n + 1)) * C_c ^ 2 * (2 * Real.pi) ^ (4 * (n + 2))) *
        ((3 : Real) / (2 : Real) ^ (4 * (n + 2))) ^ N /
        ((2 : Real) ^ (4 * (n + 2)) - 3) ≤
        c0 * q ^ n := by
    intro n
    have hWpos : 0 < (2 : Real) ^ (4 * (n + 2)) := pow_pos (by norm_num) _
    have hWne : (2 : Real) ^ (4 * (n + 2)) ≠ 0 := ne_of_gt hWpos
    have h8 : 8 ≤ 4 * (n + 2) := by omega
    have hW3 : (3 : Real) < (2 : Real) ^ (4 * (n + 2)) :=
      calc (3 : Real) < (2 : Real) ^ 8 := by norm_num
        _ ≤ (2 : Real) ^ (4 * (n + 2)) := pow_le_pow_right₀ (by norm_num) h8
    have hD1 : 0 < (2 : Real) ^ (4 * (n + 2)) - 3 := by linarith
    have hD1ne : (2 : Real) ^ (4 * (n + 2)) - 3 ≠ 0 := ne_of_gt hD1
    have hW6 : (6 : Real) ≤ (2 : Real) ^ (4 * (n + 2)) := by
      have h1 : (2 : Real) ^ 8 ≤ (2 : Real) ^ (4 * (n + 2)) :=
        pow_le_pow_right₀ (by norm_num) h8
      have h2 : (2 : Real) ^ 8 = 256 := by norm_num
      linarith
    have hK : 0 ≤ spectralMultiplicityConstant :=
      spectralMultiplicityConstant_nonneg
    have hP : 0 ≤ C_b ^ (2 * (n + 1)) * C_c ^ 2 * (2 * Real.pi) ^ (4 * (n + 2)) :=
      mul_nonneg (mul_nonneg (pow_nonneg hCb (2 * (n + 1))) (sq_nonneg C_c))
        (pow_nonneg (le_of_lt h2pi) (4 * (n + 2)))
    have hrn : 0 ≤ ((3 : Real) / (2 : Real) ^ (4 * (n + 2))) ^ N :=
      pow_nonneg (div_nonneg (by norm_num) (le_of_lt hWpos)) N
    have hX : 0 ≤ spectralMultiplicityConstant *
        (C_b ^ (2 * (n + 1)) * C_c ^ 2 * (2 * Real.pi) ^ (4 * (n + 2))) *
        ((3 : Real) / (2 : Real) ^ (4 * (n + 2))) ^ N :=
      mul_nonneg (mul_nonneg hK hP) hrn
    have hDle0 : (2 : Real) ^ (4 * (n + 2)) ≤ 2 * ((2 : Real) ^ (4 * (n + 2)) - 3) := by
      linarith
    have hDle1 :
        spectralMultiplicityConstant *
            (C_b ^ (2 * (n + 1)) * C_c ^ 2 * (2 * Real.pi) ^ (4 * (n + 2))) *
            ((3 : Real) / (2 : Real) ^ (4 * (n + 2))) ^ N *
          (2 : Real) ^ (4 * (n + 2)) ≤
          spectralMultiplicityConstant *
            (C_b ^ (2 * (n + 1)) * C_c ^ 2 * (2 * Real.pi) ^ (4 * (n + 2))) *
            ((3 : Real) / (2 : Real) ^ (4 * (n + 2))) ^ N *
            (2 * ((2 : Real) ^ (4 * (n + 2)) - 3)) :=
      mul_le_mul_of_nonneg_left hDle0 hX
    have hDle :
        spectralMultiplicityConstant *
            (C_b ^ (2 * (n + 1)) * C_c ^ 2 * (2 * Real.pi) ^ (4 * (n + 2))) *
            ((3 : Real) / (2 : Real) ^ (4 * (n + 2))) ^ N *
          (2 : Real) ^ (4 * (n + 2)) ≤
          2 * (spectralMultiplicityConstant *
            (C_b ^ (2 * (n + 1)) * C_c ^ 2 * (2 * Real.pi) ^ (4 * (n + 2))) *
            ((3 : Real) / (2 : Real) ^ (4 * (n + 2))) ^ N) *
            ((2 : Real) ^ (4 * (n + 2)) - 3) :=
      hDle1.trans (le_of_eq (by ring))
    have hstep1 :
        spectralMultiplicityConstant *
            (C_b ^ (2 * (n + 1)) * C_c ^ 2 * (2 * Real.pi) ^ (4 * (n + 2))) *
            ((3 : Real) / (2 : Real) ^ (4 * (n + 2))) ^ N /
          ((2 : Real) ^ (4 * (n + 2)) - 3) ≤
          2 * (spectralMultiplicityConstant *
            (C_b ^ (2 * (n + 1)) * C_c ^ 2 * (2 * Real.pi) ^ (4 * (n + 2))) *
            ((3 : Real) / (2 : Real) ^ (4 * (n + 2))) ^ N) /
          (2 : Real) ^ (4 * (n + 2)) := by
      have e1 :
          (spectralMultiplicityConstant *
              (C_b ^ (2 * (n + 1)) * C_c ^ 2 * (2 * Real.pi) ^ (4 * (n + 2))) *
              ((3 : Real) / (2 : Real) ^ (4 * (n + 2))) ^ N /
            ((2 : Real) ^ (4 * (n + 2)) - 3)) *
            (((2 : Real) ^ (4 * (n + 2)) - 3) * (2 : Real) ^ (4 * (n + 2))) =
            spectralMultiplicityConstant *
              (C_b ^ (2 * (n + 1)) * C_c ^ 2 * (2 * Real.pi) ^ (4 * (n + 2))) *
              ((3 : Real) / (2 : Real) ^ (4 * (n + 2))) ^ N *
            (2 : Real) ^ (4 * (n + 2)) := by
        field_simp
      have e2 :
          (2 * (spectralMultiplicityConstant *
              (C_b ^ (2 * (n + 1)) * C_c ^ 2 * (2 * Real.pi) ^ (4 * (n + 2))) *
              ((3 : Real) / (2 : Real) ^ (4 * (n + 2))) ^ N) /
            (2 : Real) ^ (4 * (n + 2))) *
            (((2 : Real) ^ (4 * (n + 2)) - 3) * (2 : Real) ^ (4 * (n + 2))) =
            2 * (spectralMultiplicityConstant *
              (C_b ^ (2 * (n + 1)) * C_c ^ 2 * (2 * Real.pi) ^ (4 * (n + 2))) *
              ((3 : Real) / (2 : Real) ^ (4 * (n + 2))) ^ N) *
            ((2 : Real) ^ (4 * (n + 2)) - 3) := by
        field_simp
      refine le_of_mul_le_mul_right ?_ (mul_pos hD1 hWpos)
      rw [e1, e2]
      exact hDle
    have he1 : 2 * (n + 1) = 2 * n + 2 := by ring
    have he2 : 4 * (n + 2) = 4 * n + 8 := by ring
    have he3 : 4 * (n + 2) * N + 4 * (n + 2) = 8 * (N + 1) + 4 * (N + 1) * n := by
      ring
    have hDne : (2 : Real) ^ (8 * (N + 1) + 4 * (N + 1) * n) ≠ 0 :=
      pow_ne_zero _ (by norm_num)
    have heq :
        2 * (spectralMultiplicityConstant *
            (C_b ^ (2 * (n + 1)) * C_c ^ 2 * (2 * Real.pi) ^ (4 * (n + 2))) *
            ((3 : Real) / (2 : Real) ^ (4 * (n + 2))) ^ N) /
          (2 : Real) ^ (4 * (n + 2)) =
        c0 * q ^ n := by
      rw [hc0def, hqdef,
        div_pow (3 : Real) ((2 : Real) ^ (4 * (n + 2))) N,
        div_pow (C_b ^ 2 * (2 * Real.pi) ^ 4) ((2 : Real) ^ (4 * (N + 1))) n,
        mul_pow (C_b ^ 2) ((2 * Real.pi) ^ 4) n,
        ← pow_mul C_b 2 n,
        ← pow_mul (2 * Real.pi) 4 n,
        ← pow_mul (2 : Real) (4 * (N + 1)) n,
        ← mul_div_mul_comm,
        ← pow_add (2 : Real) (8 * (N + 1)) (4 * (N + 1) * n),
        mul_div_assoc, mul_div_assoc, mul_div_assoc, div_div,
        ← mul_div_assoc, ← mul_div_assoc, ← mul_div_assoc,
        ← pow_mul (2 : Real) (4 * (n + 2)) N,
        ← pow_add (2 : Real) (4 * (n + 2) * N) (4 * (n + 2)),
        he3,
        he1, pow_add C_b (2 * n) 2,
        he2, pow_add (2 * Real.pi) (4 * n) 8]
      field_simp [hDne] <;> ring
    exact hstep1.trans (le_of_eq heq)
  obtain ⟨n, hn⟩ := (hzero.eventually_lt_const hxipos).exists
  exact ⟨n, lt_of_le_of_lt (hmajor n) hn⟩

/-- F1 (orbit package, preregistered in 1375 s11): the N0' end-to-end
instantiation.  The raw construction data — a base hitting `1` on the
healthy target nodes with quadratic bound `C_b`, and a correction realizing
the healthy target values and killing every non-target node of the
`2^(N+1)`-ball plus the route nodes, with quadratic bound `C_c` — together
with the height-decay hypothesis produces healthy detector data whose
support is the assembled `(n+1)`-fold window.  E2 picks `n`; the assembled
values and the square kills are rebuilt at that `n` from the raw node data
via the product identity `laplaceAt_convolution` / `laplaceAt_convolutionIterate`
and the Hermitian bridge
`selectedOwner_laplaceAt_convolutionSquare_eq_zero_of_source_eq_zero`; E3
closes.  No `2 * |rho.im|`, no `T`, no `epsilon` anywhere. -/
theorem exists_smallSupport_healthyDetectorData_of_heightDecay
    (rho : sourceNontrivialZeroSet) (hoff : rho.1.re ≠ 1 / 2)
    (hright : (1 / 2 : Real) < rho.1.re)
    (routeNodes : Finset Complex)
    {baseLower baseUpper lower upper : ℝ}
    (hlower : lower < 0) (hupper : 0 < upper)
    (N : ℕ) (hrhoShell : dyadicShellIndex |rho.1.im| < N + 1)
    {C_b C_c : ℝ} (hCb : 0 ≤ C_b) (hCc : 0 ≤ C_c)
    (hdecay : C_b ^ 2 * (2 * Real.pi) ^ 4 < (2 : Real) ^ (4 * (N + 1)))
    (hbaseData : ∃ base : CompactLogTest,
      Function.support base.test ⊆ Set.Ioo baseLower baseUpper ∧
      (∀ w : FiniteMellinNode (healthyUnscaledTargetNodes rho.1),
        laplaceAt base w.1 = 1) ∧
      ∀ sigma ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ,
        ‖t / (2 * Real.pi)‖ ^ 2 *
            ‖laplaceAt base ((sigma : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C_b)
    (hcorrData : ∃ correction : CompactLogTest,
      Function.support correction.test ⊆ Set.Ioo lower upper ∧
      (∀ w : FiniteMellinNode (healthyUnscaledTargetNodes rho.1),
        laplaceAt correction w.1 = healthyUnscaledTargetValue rho.1 w) ∧
      (∀ z : FiniteMellinNode
          (sourceNontrivialZerosInClosedBallFinset rho.1
              ((2 : Real) ^ (N + 1) + 2 + dist (2 : Complex) rho.1) ∪
            routeNodes),
        z.1 ∉ healthyUnscaledTargetNodes rho.1 →
          laplaceAt correction z.1 = 0) ∧
      ∀ sigma ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ,
        ‖t / (2 * Real.pi)‖ ^ 2 *
            ‖laplaceAt correction ((sigma : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          C_c) :
    ∃ n : ℕ, ∃ g : CompactLogTest, HealthyYoshidaDetectorData rho.1 g ∧
      Function.support g.test ⊆
        Set.Ioo (((n + 1 : ℕ) : ℝ) * baseLower + lower)
          (((n + 1 : ℕ) : ℝ) * baseUpper + upper) := by
  obtain ⟨base, hbaseSupport, hbaseTargets, hB⟩ := hbaseData
  obtain ⟨correction, hcorrSupport, hcorrTargets, hcorrKills, hC⟩ := hcorrData
  obtain ⟨n, hn⟩ :=
    exists_iterate_heightTail_budget_lt_xiMultiplicity rho N hCb hCc hdecay
  have htargetValues :
      ∀ w : FiniteMellinNode (healthyUnscaledTargetNodes rho.1),
        laplaceAt ((convolutionIterate base n).convolution correction) w.1 =
          healthyUnscaledTargetValue rho.1 w := by
    intro w
    rw [laplaceAt_convolution, laplaceAt_convolutionIterate, hbaseTargets w,
      hcorrTargets w]
    simp
  have hsquareZeros :
      ∀ w : FiniteMellinNode
          (sourceNontrivialZerosInClosedBallFinset rho.1
              ((2 : Real) ^ (N + 1) + 2 + dist (2 : Complex) rho.1) ∪
            routeNodes),
        w.1 ∉ healthyUnscaledTargetNodes rho.1 →
          laplaceAt (selectedOwner base correction n).convolutionSquare
            (w.1 - 1 / 2) = 0 := by
    intro w hw
    refine selectedOwner_laplaceAt_convolutionSquare_eq_zero_of_source_eq_zero
      base correction n w.1 ?_
    rw [laplaceAt_convolution, laplaceAt_convolutionIterate, hcorrKills w hw]
    simp
  exact ⟨n,
    exists_smallSupport_healthyDetectorData_of_quadraticBounds_and_heightBudget
      base correction n hbaseSupport hcorrSupport rho hoff hright routeNodes
      N hrhoShell htargetValues hsquareZeros hB hC hn⟩

/-- F2 (1375 s11): the self-contained instantiation.  The correction engine
`exists_residualWindow_correction_with_quadratic_decay` takes only
n-free inputs — the base is built with value `1` on the healthy targets, the
correction with the healthy values and zero kills over
`killSet ∪ healthyTargets` — so the whole package reduces to the decay
antecedent on the constructed constants.  That antecedent is the open
science interface (the constructed `C_b` versus `16^(N+1)`); nothing
numerical is claimed. -/
theorem exists_smallSupport_healthyDetectorData_heightDecay_construction
    (rho : sourceNontrivialZeroSet) (hoff : rho.1.re ≠ 1 / 2)
    (hright : (1 / 2 : Real) < rho.1.re)
    (routeNodes : Finset Complex)
    {baseLower baseUpper lower upper : ℝ}
    (hbaseLower : baseLower < 0) (hbaseUpper : 0 < baseUpper)
    (hlower : lower < 0) (hupper : 0 < upper)
    (N : ℕ) (hrhoShell : dyadicShellIndex |rho.1.im| < N + 1) :
    ∃ C_b C_c : ℝ, 0 ≤ C_b ∧ 0 ≤ C_c ∧
      (C_b ^ 2 * (2 * Real.pi) ^ 4 < (2 : Real) ^ (4 * (N + 1)) →
        ∃ n : ℕ, ∃ g : CompactLogTest, HealthyYoshidaDetectorData rho.1 g ∧
        Function.support g.test ⊆
          Set.Ioo (((n + 1 : ℕ) : ℝ) * baseLower + lower)
            (((n + 1 : ℕ) : ℝ) * baseUpper + upper)) := by
  obtain ⟨base, C_b, hbaseSupport, hbaseVals, hCb, hbaseB⟩ :=
    exists_residualWindow_correction_with_quadratic_decay
      (healthyUnscaledTargetNodes rho.1) hbaseLower hbaseUpper (fun _ => 1)
  have hbaseTargets :
      ∀ w : FiniteMellinNode (healthyUnscaledTargetNodes rho.1),
        laplaceAt base w.1 = 1 := by
    intro w
    simpa using hbaseVals w
  let killSet : Finset ℂ :=
    sourceNontrivialZerosInClosedBallFinset rho.1
        ((2 : Real) ^ (N + 1) + 2 + dist (2 : Complex) rho.1) ∪ routeNodes
  let y : FiniteMellinNode (killSet ∪ healthyUnscaledTargetNodes rho.1) → ℂ :=
    fun z =>
      if hz : z.1 ∈ healthyUnscaledTargetNodes rho.1 then
        healthyUnscaledTargetValue rho.1 ⟨z.1, hz⟩ else 0
  obtain ⟨correction, C_c, hcorrSupport, hvals, hCc, hcorrB⟩ :=
    exists_residualWindow_correction_with_quadratic_decay
      (killSet ∪ healthyUnscaledTargetNodes rho.1) hlower hupper y
  have hcorrTargets :
      ∀ w : FiniteMellinNode (healthyUnscaledTargetNodes rho.1),
        laplaceAt correction w.1 = healthyUnscaledTargetValue rho.1 w := by
    intro w
    have hwBig : w.1 ∈ killSet ∪ healthyUnscaledTargetNodes rho.1 :=
      Finset.mem_union_right _ w.2
    simpa [y, hwBig, w.2] using hvals ⟨w.1, hwBig⟩
  have hcorrKills :
      ∀ z : FiniteMellinNode killSet,
        z.1 ∉ healthyUnscaledTargetNodes rho.1 →
          laplaceAt correction z.1 = 0 := by
    intro z hz
    have hwBig : z.1 ∈ killSet ∪ healthyUnscaledTargetNodes rho.1 :=
      Finset.mem_union_left _ z.2
    simpa [y, hwBig, hz] using hvals ⟨z.1, hwBig⟩
  refine ⟨C_b, C_c, hCb, hCc, fun hdecay => ?_⟩
  exact exists_smallSupport_healthyDetectorData_of_heightDecay
    rho hoff hright routeNodes hlower hupper N hrhoShell hCb hCc hdecay
    ⟨base, hbaseSupport, hbaseTargets, hbaseB⟩
    ⟨correction, hcorrSupport, hcorrTargets, hcorrKills, hcorrB⟩

end

end C1SelectedSquareHeightTail
end Source
end ConnesWeilRH
