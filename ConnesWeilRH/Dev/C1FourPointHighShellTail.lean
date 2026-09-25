/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Dev.C1FourPointSpectralPrefixTransport
import ConnesWeilRH.Dev.C1HealthyYoshidaUnscaledOrbit

/-!
# Reserved-base decay for the four-point spectral tail

One base factor supplies quartic vertical decay, the correction supplies
quadratic decay, and the other base factors retain geometric contraction.
The resulting sixth-order raw bound is the first quantitative ingredient for
the four-point transformed-square tail on the selected owner.
-/

namespace ConnesWeilRH
namespace Source
namespace C1FourPointHighShellTail

open CC20YoshidaConvolution
open CC20YoshidaConvolution.CompactLogTest
open CCM25Concrete.CompactLogConvolution
open CCM25Concrete.UnscaledYoshidaSelectedOwner
open C1SpectralWeil
open C1FourPointSpectralPrefixTransport
open C1TwoPointSpectralDecomposition
open C1HealthyYoshidaDetector
open C1SpectralTailBound

noncomputable section

/-! The contraction constant is exposed as a parameter for the powered-seed
candidate. The legacy half-contraction theorem below is kept unchanged so
existing consumers retain their original interface. -/
theorem convolutionIterate_convolution_vertical_sextic_bound_of_q
    (base correction : CompactLogTest) (C4 C2 T q : Real) (n : Nat)
    (hq : 0 ≤ q) (hC4 : 0 ≤ C4) (hC2 : 0 ≤ C2)
    (hbaseContract : ∀ sigma ∈ Set.Icc (0 : Real) 1, ∀ t : Real,
      T ≤ |t| →
        ‖laplaceAt base ((sigma : Complex) + (t : Complex) * Complex.I)‖ ≤
          q)
    (hbaseQuartic : ∀ sigma ∈ Set.Icc (0 : Real) 1, ∀ t : Real,
      ‖t / (2 * Real.pi)‖ ^ 4 *
        ‖laplaceAt base ((sigma : Complex) + (t : Complex) * Complex.I)‖ ≤ C4)
    (hcorrectionQuadratic : ∀ sigma ∈ Set.Icc (0 : Real) 1, ∀ t : Real,
      ‖t / (2 * Real.pi)‖ ^ 2 *
        ‖laplaceAt correction
          ((sigma : Complex) + (t : Complex) * Complex.I)‖ ≤ C2) :
    ∀ sigma ∈ Set.Icc (0 : Real) 1, ∀ t : Real, T ≤ |t| →
      ‖t / (2 * Real.pi)‖ ^ 6 *
        ‖laplaceAt ((convolutionIterate base n).convolution correction)
          ((sigma : Complex) + (t : Complex) * Complex.I)‖ ≤
        q ^ n * (C4 * C2) := by
  intro sigma hsigma t hheight
  let s : Complex := (sigma : Complex) + (t : Complex) * Complex.I
  let r : Real := ‖t / (2 * Real.pi)‖
  let b : Real := ‖laplaceAt base s‖
  let c : Real := ‖laplaceAt correction s‖
  have hcontract : b ≤ q := hbaseContract sigma hsigma t hheight
  have hquartic : r ^ 4 * b ≤ C4 := hbaseQuartic sigma hsigma t
  have hquadratic : r ^ 2 * c ≤ C2 :=
    hcorrectionQuadratic sigma hsigma t
  have hpower : b ^ n ≤ q ^ n := by
    exact pow_le_pow_left₀ (norm_nonneg _) hcontract n
  have hproduct : (r ^ 4 * b) * (r ^ 2 * c) ≤ C4 * C2 := by
    exact mul_le_mul hquartic hquadratic (by positivity) hC4
  change r ^ 6 *
      ‖laplaceAt ((convolutionIterate base n).convolution correction) s‖ ≤
    q ^ n * (C4 * C2)
  rw [laplaceAt_convolution, laplaceAt_convolutionIterate, norm_mul, norm_pow]
  calc
    r ^ 6 * (b ^ (n + 1) * c) =
        b ^ n * ((r ^ 4 * b) * (r ^ 2 * c)) := by
          rw [pow_succ]
          ring
    _ ≤ b ^ n * (C4 * C2) :=
      mul_le_mul_of_nonneg_left hproduct (pow_nonneg (norm_nonneg _) _)
    _ ≤ q ^ n * (C4 * C2) :=
      mul_le_mul_of_nonneg_right hpower (mul_nonneg hC4 hC2)

/-- Reserving one base factor gives sixth-order decay of the actual unscaled
Yoshida convolution orbit, with the remaining `n` base factors contracting.
The threshold does not move with the convolution count. -/
theorem convolutionIterate_convolution_vertical_sextic_bound
    (base correction : CompactLogTest) (C4 C2 T : Real) (n : Nat)
    (hC4 : 0 ≤ C4) (hC2 : 0 ≤ C2)
    (hbaseContract : ∀ sigma ∈ Set.Icc (0 : Real) 1, ∀ t : Real,
      T ≤ |t| →
        ‖laplaceAt base ((sigma : Complex) + (t : Complex) * Complex.I)‖ ≤
          1 / 2)
    (hbaseQuartic : ∀ sigma ∈ Set.Icc (0 : Real) 1, ∀ t : Real,
      ‖t / (2 * Real.pi)‖ ^ 4 *
        ‖laplaceAt base ((sigma : Complex) + (t : Complex) * Complex.I)‖ ≤ C4)
    (hcorrectionQuadratic : ∀ sigma ∈ Set.Icc (0 : Real) 1, ∀ t : Real,
      ‖t / (2 * Real.pi)‖ ^ 2 *
        ‖laplaceAt correction
          ((sigma : Complex) + (t : Complex) * Complex.I)‖ ≤ C2) :
    ∀ sigma ∈ Set.Icc (0 : Real) 1, ∀ t : Real, T ≤ |t| →
      ‖t / (2 * Real.pi)‖ ^ 6 *
        ‖laplaceAt ((convolutionIterate base n).convolution correction)
          ((sigma : Complex) + (t : Complex) * Complex.I)‖ ≤
        (1 / 2 : Real) ^ n * (C4 * C2) := by
  intro sigma hsigma t hheight
  let s : Complex := (sigma : Complex) + (t : Complex) * Complex.I
  let r : Real := ‖t / (2 * Real.pi)‖
  let b : Real := ‖laplaceAt base s‖
  let c : Real := ‖laplaceAt correction s‖
  have hcontract : b ≤ 1 / 2 := hbaseContract sigma hsigma t hheight
  have hquartic : r ^ 4 * b ≤ C4 := hbaseQuartic sigma hsigma t
  have hquadratic : r ^ 2 * c ≤ C2 :=
    hcorrectionQuadratic sigma hsigma t
  have hpower : b ^ n ≤ (1 / 2 : Real) ^ n := by
    exact pow_le_pow_left₀ (norm_nonneg _) hcontract n
  have hproduct : (r ^ 4 * b) * (r ^ 2 * c) ≤ C4 * C2 := by
    exact mul_le_mul hquartic hquadratic (by positivity) hC4
  change r ^ 6 *
      ‖laplaceAt ((convolutionIterate base n).convolution correction) s‖ ≤
    (1 / 2 : Real) ^ n * (C4 * C2)
  rw [laplaceAt_convolution, laplaceAt_convolutionIterate, norm_mul, norm_pow]
  calc
    r ^ 6 * (b ^ (n + 1) * c) =
        b ^ n * ((r ^ 4 * b) * (r ^ 2 * c)) := by
          rw [pow_succ]
          ring
    _ ≤ b ^ n * (C4 * C2) :=
      mul_le_mul_of_nonneg_left hproduct (pow_nonneg (norm_nonneg _) _)
    _ ≤ (1 / 2 : Real) ^ n * (C4 * C2) :=
      mul_le_mul_of_nonneg_right hpower (mul_nonneg hC4 hC2)

/-- The actual selected convolution square has twelfth-order vertical decay.
Both factors use the same raw orbit; reflection preserves the imaginary
height and the source strip. -/
theorem selectedOwner_convolutionSquare_vertical_twelfth_bound
    (base correction : CompactLogTest) (C4 C2 T : Real) (n : Nat)
    (hC4 : 0 ≤ C4) (hC2 : 0 ≤ C2)
    (hbaseContract : ∀ sigma ∈ Set.Icc (0 : Real) 1, ∀ t : Real,
      T ≤ |t| →
        ‖laplaceAt base ((sigma : Complex) + (t : Complex) * Complex.I)‖ ≤
          1 / 2)
    (hbaseQuartic : ∀ sigma ∈ Set.Icc (0 : Real) 1, ∀ t : Real,
      ‖t / (2 * Real.pi)‖ ^ 4 *
        ‖laplaceAt base ((sigma : Complex) + (t : Complex) * Complex.I)‖ ≤ C4)
    (hcorrectionQuadratic : ∀ sigma ∈ Set.Icc (0 : Real) 1, ∀ t : Real,
      ‖t / (2 * Real.pi)‖ ^ 2 *
        ‖laplaceAt correction
          ((sigma : Complex) + (t : Complex) * Complex.I)‖ ≤ C2) :
    ∀ z : Complex, z.re ∈ Set.Icc (0 : Real) 1 → T ≤ |z.im| →
      ‖z.im / (2 * Real.pi)‖ ^ 12 *
        ‖laplaceAt (selectedOwner base correction n).convolutionSquare
          (z - 1 / 2)‖ ≤
        ((1 / 2 : Real) ^ n * (C4 * C2)) ^ 2 := by
  intro z hz hheight
  let raw := (convolutionIterate base n).convolution correction
  let r : Real := ‖z.im / (2 * Real.pi)‖
  let M : Real := (1 / 2 : Real) ^ n * (C4 * C2)
  have hfirst : r ^ 6 * ‖laplaceAt raw z‖ ≤ M := by
    have h := convolutionIterate_convolution_vertical_sextic_bound
      base correction C4 C2 T n hC4 hC2 hbaseContract hbaseQuartic
      hcorrectionQuadratic z.re hz z.im hheight
    simpa only [Complex.re_add_im] using h
  have hreflectRe : (1 - star z).re ∈ Set.Icc (0 : Real) 1 := by
    have hstarRe : (star z).re = z.re := by simp
    rw [Complex.sub_re, Complex.one_re, hstarRe]
    constructor <;> linarith [hz.1, hz.2]
  have hreflectIm : (1 - star z).im = z.im := by simp
  have hsecond : r ^ 6 * ‖laplaceAt raw (1 - star z)‖ ≤ M := by
    have h := convolutionIterate_convolution_vertical_sextic_bound
      base correction C4 C2 T n hC4 hC2 hbaseContract hbaseQuartic
      hcorrectionQuadratic (1 - star z).re hreflectRe
      (1 - star z).im (by simpa only [hreflectIm] using hheight)
    have h' :
        ‖(1 - star z).im / (2 * Real.pi)‖ ^ 6 *
          ‖laplaceAt raw (1 - star z)‖ ≤ M := by
      simpa only [Complex.re_add_im] using h
    simpa only [hreflectIm] using h'
  have hM : 0 ≤ M :=
    mul_nonneg (pow_nonneg (by norm_num) _) (mul_nonneg hC4 hC2)
  have hproduct :
      (r ^ 6 * ‖laplaceAt raw (1 - star z)‖) *
          (r ^ 6 * ‖laplaceAt raw z‖) ≤ M * M := by
    exact mul_le_mul hsecond hfirst (by positivity) hM
  change r ^ 12 *
      ‖laplaceAt (selectedOwner base correction n).convolutionSquare
        (z - 1 / 2)‖ ≤ M ^ 2
  rw [selectedOwner_laplaceAt_convolutionSquare_centered, norm_mul, norm_star]
  calc
    r ^ 12 * (‖laplaceAt raw (1 - star z)‖ * ‖laplaceAt raw z‖) =
        (r ^ 6 * ‖laplaceAt raw (1 - star z)‖) *
          (r ^ 6 * ‖laplaceAt raw z‖) := by ring
    _ ≤ M * M := hproduct
    _ = M ^ 2 := by ring

theorem selectedOwner_convolutionSquare_vertical_twelfth_bound_of_q
    (base correction : CompactLogTest) (C4 C2 T q : Real) (n : Nat)
    (hq : 0 ≤ q) (hC4 : 0 ≤ C4) (hC2 : 0 ≤ C2)
    (hbaseContract : ∀ sigma ∈ Set.Icc (0 : Real) 1, ∀ t : Real,
      T ≤ |t| →
        ‖laplaceAt base ((sigma : Complex) + (t : Complex) * Complex.I)‖ ≤
          q)
    (hbaseQuartic : ∀ sigma ∈ Set.Icc (0 : Real) 1, ∀ t : Real,
      ‖t / (2 * Real.pi)‖ ^ 4 *
        ‖laplaceAt base ((sigma : Complex) + (t : Complex) * Complex.I)‖ ≤ C4)
    (hcorrectionQuadratic : ∀ sigma ∈ Set.Icc (0 : Real) 1, ∀ t : Real,
      ‖t / (2 * Real.pi)‖ ^ 2 *
        ‖laplaceAt correction
          ((sigma : Complex) + (t : Complex) * Complex.I)‖ ≤ C2) :
    ∀ z : Complex, z.re ∈ Set.Icc (0 : Real) 1 → T ≤ |z.im| →
      ‖z.im / (2 * Real.pi)‖ ^ 12 *
        ‖laplaceAt (selectedOwner base correction n).convolutionSquare
          (z - 1 / 2)‖ ≤
        (q ^ n * (C4 * C2)) ^ 2 := by
  intro z hz hheight
  let raw := (convolutionIterate base n).convolution correction
  let r : Real := ‖z.im / (2 * Real.pi)‖
  let M : Real := q ^ n * (C4 * C2)
  have hfirst : r ^ 6 * ‖laplaceAt raw z‖ ≤ M := by
    have h := convolutionIterate_convolution_vertical_sextic_bound_of_q
      base correction C4 C2 T q n hq hC4 hC2 hbaseContract hbaseQuartic
      hcorrectionQuadratic z.re hz z.im hheight
    simpa only [Complex.re_add_im] using h
  have hreflectRe : (1 - star z).re ∈ Set.Icc (0 : Real) 1 := by
    have hstarRe : (star z).re = z.re := by simp
    rw [Complex.sub_re, Complex.one_re, hstarRe]
    constructor <;> linarith [hz.1, hz.2]
  have hreflectIm : (1 - star z).im = z.im := by simp
  have hsecond : r ^ 6 * ‖laplaceAt raw (1 - star z)‖ ≤ M := by
    have h := convolutionIterate_convolution_vertical_sextic_bound_of_q
      base correction C4 C2 T q n hq hC4 hC2 hbaseContract hbaseQuartic
      hcorrectionQuadratic (1 - star z).re hreflectRe
      (1 - star z).im (by simpa only [hreflectIm] using hheight)
    have h' :
        ‖(1 - star z).im / (2 * Real.pi)‖ ^ 6 *
          ‖laplaceAt raw (1 - star z)‖ ≤ M := by
      simpa only [Complex.re_add_im] using h
    simpa only [hreflectIm] using h'
  have hM : 0 ≤ M :=
    mul_nonneg (pow_nonneg hq _) (mul_nonneg hC4 hC2)
  have hproduct :
      (r ^ 6 * ‖laplaceAt raw (1 - star z)‖) *
          (r ^ 6 * ‖laplaceAt raw z‖) ≤ M * M := by
    exact mul_le_mul hsecond hfirst (by positivity) hM
  change r ^ 12 *
      ‖laplaceAt (selectedOwner base correction n).convolutionSquare
        (z - 1 / 2)‖ ≤ M ^ 2
  rw [selectedOwner_laplaceAt_convolutionSquare_centered, norm_mul, norm_star]
  calc
    r ^ 12 * (‖laplaceAt raw (1 - star z)‖ * ‖laplaceAt raw z‖) =
        (r ^ 6 * ‖laplaceAt raw (1 - star z)‖) *
          (r ^ 6 * ‖laplaceAt raw z‖) := by ring
    _ ≤ M * M := hproduct
    _ = M ^ 2 := by ring

/-- A source point of norm at most `1 + ‖rho‖` is at most linear in the
vertical height away from a point of the source strip. -/
private theorem orbitPoint_norm_sub_le_height
    (rho w z : Complex)
    (hw : ‖w‖ ≤ 1 + ‖rho‖)
    (hz : z.re ∈ Set.Icc (0 : Real) 1)
    (hheight : 1 ≤ |z.im|) :
    ‖w - z‖ ≤ (3 + ‖rho‖) * |z.im| := by
  have hzNorm : ‖z‖ ≤ 1 + |z.im| := by
    calc
      ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
      _ ≤ 1 + |z.im| := by
        gcongr
        rw [abs_of_nonneg hz.1]
        exact hz.2
  calc
    ‖w - z‖ ≤ ‖w‖ + ‖z‖ := norm_sub_le w z
    _ ≤ (1 + ‖rho‖) + (1 + |z.im|) := add_le_add hw hzNorm
    _ ≤ (3 + ‖rho‖) * |z.im| := by
      have hnonneg : 0 ≤ 2 + ‖rho‖ := by positivity
      nlinarith [mul_nonneg hnonneg (sub_nonneg.mpr hheight)]

/-- The degree-four orbit multiplier has an explicit vertical polynomial
majorant, including the real span coefficient. This is independent of the
Yoshida convolution count. -/
theorem fullOrbit_span_multiplier_norm_le_height_pow_four
    (rho z : Complex) (lambda : Real)
    (hz : z.re ∈ Set.Icc (0 : Real) 1)
    (hheight : 1 ≤ |z.im|) :
    ‖((1 - rho) - 1 / 2 - (z - 1 / 2)) *
          (star rho - 1 / 2 - (z - 1 / 2)) *
          ((1 - star rho) - 1 / 2 - (z - 1 / 2)) *
          (rho - 1 / 2 - (z - 1 / 2)) - (lambda : Complex)‖ ≤
      ((3 + ‖rho‖) ^ 4 + |lambda|) * |z.im| ^ 4 := by
  let K : Real := 3 + ‖rho‖
  let N : Real := |z.im|
  have hnormRho : ‖rho‖ ≤ 1 + ‖rho‖ := by linarith
  have hnormStar : ‖star rho‖ ≤ 1 + ‖rho‖ := by simp
  have hnormOneSub : ‖(1 : Complex) - rho‖ ≤ 1 + ‖rho‖ := by
    simpa using norm_sub_le (1 : Complex) rho
  have hnormOneSubStar : ‖(1 : Complex) - star rho‖ ≤ 1 + ‖rho‖ := by
    simpa using norm_sub_le (1 : Complex) (star rho)
  have h1 := orbitPoint_norm_sub_le_height rho (1 - rho) z
    hnormOneSub hz hheight
  have h2 := orbitPoint_norm_sub_le_height rho (star rho) z
    hnormStar hz hheight
  have h3 := orbitPoint_norm_sub_le_height rho (1 - star rho) z
    hnormOneSubStar hz hheight
  have h4 := orbitPoint_norm_sub_le_height rho rho z
    hnormRho hz hheight
  have hprod :
      ‖((1 - rho) - z) * (star rho - z) *
          ((1 - star rho) - z) * (rho - z)‖ ≤ (K * N) ^ 4 := by
    simp only [norm_mul]
    calc
      ‖(1 - rho) - z‖ * ‖star rho - z‖ *
          ‖(1 - star rho) - z‖ * ‖rho - z‖ ≤
        (K * N) * (K * N) * (K * N) * (K * N) := by
          gcongr
      _ = (K * N) ^ 4 := by ring
  have hN4 : 1 ≤ N ^ 4 := one_le_pow₀ hheight
  have hLambda : |lambda| ≤ |lambda| * N ^ 4 := by
    nlinarith [mul_nonneg (abs_nonneg lambda) (sub_nonneg.mpr hN4)]
  have hpoly :
      ((1 - rho) - 1 / 2 - (z - 1 / 2)) *
            (star rho - 1 / 2 - (z - 1 / 2)) *
            ((1 - star rho) - 1 / 2 - (z - 1 / 2)) *
            (rho - 1 / 2 - (z - 1 / 2)) - (lambda : Complex) =
        ((1 - rho) - z) * (star rho - z) *
          ((1 - star rho) - z) * (rho - z) - (lambda : Complex) := by ring
  rw [hpoly]
  calc
    ‖((1 - rho) - z) * (star rho - z) *
          ((1 - star rho) - z) * (rho - z) - (lambda : Complex)‖ ≤
        ‖((1 - rho) - z) * (star rho - z) *
          ((1 - star rho) - z) * (rho - z)‖ + |lambda| := by
            simpa using norm_sub_le
              (((1 - rho) - z) * (star rho - z) *
                ((1 - star rho) - z) * (rho - z))
              (lambda : Complex)
    _ ≤ (K * N) ^ 4 + |lambda| := add_le_add hprod le_rfl
    _ ≤ (K ^ 4 + |lambda|) * N ^ 4 := by
      nlinarith [hLambda]

/-- On the actual selected orbit, the twelfth-order square bound pays for
the eight powers from the four-point multiplier and leaves four powers for
the two spectral distance weights. The remaining scalar budget is explicit. -/
theorem selectedOwner_fullOrbit_span_doubleDistance_bound
    (base correction : CompactLogTest) (rho : Complex)
    (lambda C4 C2 T : Real) (n : Nat)
    (hC4 : 0 ≤ C4) (hC2 : 0 ≤ C2)
    (hbaseContract : ∀ sigma ∈ Set.Icc (0 : Real) 1, ∀ t : Real,
      T ≤ |t| →
        ‖laplaceAt base ((sigma : Complex) + (t : Complex) * Complex.I)‖ ≤
          1 / 2)
    (hbaseQuartic : ∀ sigma ∈ Set.Icc (0 : Real) 1, ∀ t : Real,
      ‖t / (2 * Real.pi)‖ ^ 4 *
        ‖laplaceAt base ((sigma : Complex) + (t : Complex) * Complex.I)‖ ≤ C4)
    (hcorrectionQuadratic : ∀ sigma ∈ Set.Icc (0 : Real) 1, ∀ t : Real,
      ‖t / (2 * Real.pi)‖ ^ 2 *
        ‖laplaceAt correction
          ((sigma : Complex) + (t : Complex) * Complex.I)‖ ≤ C2) :
    ∀ z : Complex, z.re ∈ Set.Icc (0 : Real) 1 →
      T ≤ |z.im| → 1 ≤ |z.im| →
      ‖z - rho‖ ^ 2 * ‖(1 - star z) - rho‖ ^ 2 *
        ‖laplaceAt
          (annihilatorDetectorSpanVector
            (fullFunctionalEquationOrbitAnnihilator
              (selectedOwner base correction n).sourceTest rho)
            (selectedOwner base correction n).sourceTest lambda).convolutionSquare
          (z - 1 / 2)‖ ≤
        (3 + ‖rho‖) ^ 4 *
          ((3 + ‖rho‖) ^ 4 + |lambda|) ^ 2 *
          (2 * Real.pi) ^ 12 *
          ((1 / 2 : Real) ^ n * (C4 * C2)) ^ 2 := by
  intro z hz hTz hone
  let g := (selectedOwner base correction n).sourceTest
  let v := annihilatorDetectorSpanVector
    (fullFunctionalEquationOrbitAnnihilator g rho) g lambda
  let K : Real := 3 + ‖rho‖
  let L : Real := K ^ 4 + |lambda|
  let N : Real := |z.im|
  let r : Real := ‖z.im / (2 * Real.pi)‖
  let M : Real := (1 / 2 : Real) ^ n * (C4 * C2)
  have hKN : 0 ≤ K * N := by dsimp [K, N]; positivity
  have hLN : 0 ≤ L * N ^ 4 := by dsimp [L, K, N]; positivity
  have hM : 0 ≤ M :=
    mul_nonneg (pow_nonneg (by norm_num) _) (mul_nonneg hC4 hC2)
  have hcompRe : (1 - star z).re ∈ Set.Icc (0 : Real) 1 := by
    have hstarRe : (star z).re = z.re := by simp
    rw [Complex.sub_re, Complex.one_re, hstarRe]
    constructor <;> linarith [hz.1, hz.2]
  have hcompIm : (1 - star z).im = z.im := by simp
  have hcoord : -star (z - 1 / 2) = (1 - star z) - 1 / 2 := by
    apply Complex.ext <;> simp [Complex.star_def] <;> ring
  have hmultAt :
      ‖laplaceAt v (z - 1 / 2)‖ ≤
        (L * N ^ 4) * ‖laplaceAt g (z - 1 / 2)‖ := by
    rw [show v = annihilatorDetectorSpanVector
        (fullFunctionalEquationOrbitAnnihilator g rho) g lambda from rfl,
      laplaceAt_fullOrbitSpanVector, norm_mul]
    exact mul_le_mul_of_nonneg_right
      (fullOrbit_span_multiplier_norm_le_height_pow_four rho z lambda hz hone)
      (norm_nonneg _)
  have hmultComp :
      ‖laplaceAt v ((1 - star z) - 1 / 2)‖ ≤
        (L * N ^ 4) *
          ‖laplaceAt g ((1 - star z) - 1 / 2)‖ := by
    rw [show v = annihilatorDetectorSpanVector
        (fullFunctionalEquationOrbitAnnihilator g rho) g lambda from rfl,
      laplaceAt_fullOrbitSpanVector, norm_mul]
    have hbound := fullOrbit_span_multiplier_norm_le_height_pow_four
      rho (1 - star z) lambda hcompRe
      (by simpa only [hcompIm] using hone)
    exact mul_le_mul_of_nonneg_right
      (by simpa only [hcompIm] using hbound) (norm_nonneg _)
  have hsquare :
      ‖laplaceAt v.convolutionSquare (z - 1 / 2)‖ ≤
        (L * N ^ 4) ^ 2 * ‖laplaceAt g.convolutionSquare (z - 1 / 2)‖ := by
    rw [laplaceAt_convolutionSquare, hcoord, norm_mul, norm_star]
    calc
      ‖laplaceAt v ((1 - star z) - 1 / 2)‖ *
          ‖laplaceAt v (z - 1 / 2)‖ ≤
        ((L * N ^ 4) * ‖laplaceAt g ((1 - star z) - 1 / 2)‖) *
          ((L * N ^ 4) * ‖laplaceAt g (z - 1 / 2)‖) := by
            exact mul_le_mul hmultComp hmultAt (norm_nonneg _) (by positivity)
      _ = (L * N ^ 4) ^ 2 *
          (‖laplaceAt g ((1 - star z) - 1 / 2)‖ *
            ‖laplaceAt g (z - 1 / 2)‖) := by ring
      _ = (L * N ^ 4) ^ 2 *
          ‖laplaceAt g.convolutionSquare (z - 1 / 2)‖ := by
            rw [laplaceAt_convolutionSquare, hcoord, norm_mul, norm_star]
  have hrawSquare :
      r ^ 12 * ‖laplaceAt g.convolutionSquare (z - 1 / 2)‖ ≤ M ^ 2 := by
    exact selectedOwner_convolutionSquare_vertical_twelfth_bound
      base correction C4 C2 T n hC4 hC2 hbaseContract hbaseQuartic
      hcorrectionQuadratic z hz hTz
  have hnrho : ‖rho‖ ≤ 1 + ‖rho‖ := by linarith
  have hdist1 : ‖z - rho‖ ≤ K * N := by
    simpa only [norm_sub_rev] using
      orbitPoint_norm_sub_le_height rho rho z hnrho hz hone
  have hdist2 : ‖(1 - star z) - rho‖ ≤ K * N := by
    have h := orbitPoint_norm_sub_le_height rho rho (1 - star z)
      hnrho hcompRe (by simpa only [hcompIm] using hone)
    simpa only [norm_sub_rev, hcompIm] using h
  have hdist :
      ‖z - rho‖ ^ 2 * ‖(1 - star z) - rho‖ ^ 2 ≤ (K * N) ^ 4 := by
    calc
      ‖z - rho‖ ^ 2 * ‖(1 - star z) - rho‖ ^ 2 ≤
          (K * N) ^ 2 * (K * N) ^ 2 := by
            exact mul_le_mul
              (pow_le_pow_left₀ (norm_nonneg _) hdist1 2)
              (pow_le_pow_left₀ (norm_nonneg _) hdist2 2)
              (sq_nonneg _) (sq_nonneg _)
      _ = (K * N) ^ 4 := by ring
  have hr : r = N / (2 * Real.pi) := by
    dsimp [r, N]
    rw [abs_div,
      abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  have hNpow : N ^ 12 = (2 * Real.pi) ^ 12 * r ^ 12 := by
    rw [hr]
    field_simp [Real.pi_ne_zero]
  change ‖z - rho‖ ^ 2 * ‖(1 - star z) - rho‖ ^ 2 *
      ‖laplaceAt v.convolutionSquare (z - 1 / 2)‖ ≤
    K ^ 4 * L ^ 2 * (2 * Real.pi) ^ 12 * M ^ 2
  calc
    ‖z - rho‖ ^ 2 * ‖(1 - star z) - rho‖ ^ 2 *
        ‖laplaceAt v.convolutionSquare (z - 1 / 2)‖ ≤
      (K * N) ^ 4 *
        ((L * N ^ 4) ^ 2 *
          ‖laplaceAt g.convolutionSquare (z - 1 / 2)‖) := by
            exact mul_le_mul hdist hsquare (by positivity) (by positivity)
    _ = (K ^ 4 * L ^ 2 * (2 * Real.pi) ^ 12) *
          (r ^ 12 * ‖laplaceAt g.convolutionSquare (z - 1 / 2)‖) := by
            calc
              (K * N) ^ 4 *
                  ((L * N ^ 4) ^ 2 *
                    ‖laplaceAt g.convolutionSquare (z - 1 / 2)‖) =
                (K ^ 4 * L ^ 2) *
                  (N ^ 12 * ‖laplaceAt g.convolutionSquare (z - 1 / 2)‖) :=
                    by ring
              _ = (K ^ 4 * L ^ 2) *
                  ((2 * Real.pi) ^ 12 * r ^ 12 *
                    ‖laplaceAt g.convolutionSquare (z - 1 / 2)‖) := by
                      rw [hNpow]
              _ = (K ^ 4 * L ^ 2 * (2 * Real.pi) ^ 12) *
                  (r ^ 12 * ‖laplaceAt g.convolutionSquare (z - 1 / 2)‖) :=
                    by ring
    _ ≤ (K ^ 4 * L ^ 2 * (2 * Real.pi) ^ 12) * M ^ 2 :=
      mul_le_mul_of_nonneg_left hrawSquare (by positivity)
    _ = K ^ 4 * L ^ 2 * (2 * Real.pi) ^ 12 * M ^ 2 := by ring

theorem selectedOwner_fullOrbit_span_doubleDistance_bound_of_q
    (base correction : CompactLogTest) (rho : Complex)
    (lambda C4 C2 T q : Real) (n : Nat)
    (hq : 0 ≤ q) (hC4 : 0 ≤ C4) (hC2 : 0 ≤ C2)
    (hbaseContract : ∀ sigma ∈ Set.Icc (0 : Real) 1, ∀ t : Real,
      T ≤ |t| →
        ‖laplaceAt base ((sigma : Complex) + (t : Complex) * Complex.I)‖ ≤
          q)
    (hbaseQuartic : ∀ sigma ∈ Set.Icc (0 : Real) 1, ∀ t : Real,
      ‖t / (2 * Real.pi)‖ ^ 4 *
        ‖laplaceAt base ((sigma : Complex) + (t : Complex) * Complex.I)‖ ≤ C4)
    (hcorrectionQuadratic : ∀ sigma ∈ Set.Icc (0 : Real) 1, ∀ t : Real,
      ‖t / (2 * Real.pi)‖ ^ 2 *
        ‖laplaceAt correction
          ((sigma : Complex) + (t : Complex) * Complex.I)‖ ≤ C2) :
    ∀ z : Complex, z.re ∈ Set.Icc (0 : Real) 1 →
      T ≤ |z.im| → 1 ≤ |z.im| →
      ‖z - rho‖ ^ 2 * ‖(1 - star z) - rho‖ ^ 2 *
        ‖laplaceAt
          (annihilatorDetectorSpanVector
            (fullFunctionalEquationOrbitAnnihilator
              (selectedOwner base correction n).sourceTest rho)
            (selectedOwner base correction n).sourceTest lambda).convolutionSquare
          (z - 1 / 2)‖ ≤
        (3 + ‖rho‖) ^ 4 *
          ((3 + ‖rho‖) ^ 4 + |lambda|) ^ 2 *
          (2 * Real.pi) ^ 12 *
          ((q ^ n * (C4 * C2)) ^ 2) := by
  intro z hz hTz hone
  let g := (selectedOwner base correction n).sourceTest
  let v := annihilatorDetectorSpanVector
    (fullFunctionalEquationOrbitAnnihilator g rho) g lambda
  let K : Real := 3 + ‖rho‖
  let L : Real := K ^ 4 + |lambda|
  let N : Real := |z.im|
  let r : Real := ‖z.im / (2 * Real.pi)‖
  let M : Real := q ^ n * (C4 * C2)
  have hKN : 0 ≤ K * N := by dsimp [K, N]; positivity
  have hLN : 0 ≤ L * N ^ 4 := by dsimp [L, K, N]; positivity
  have hM : 0 ≤ M :=
    mul_nonneg (pow_nonneg hq _) (mul_nonneg hC4 hC2)
  have hcompRe : (1 - star z).re ∈ Set.Icc (0 : Real) 1 := by
    have hstarRe : (star z).re = z.re := by simp
    rw [Complex.sub_re, Complex.one_re, hstarRe]
    constructor <;> linarith [hz.1, hz.2]
  have hcompIm : (1 - star z).im = z.im := by simp
  have hcoord : -star (z - 1 / 2) = (1 - star z) - 1 / 2 := by
    apply Complex.ext <;> simp [Complex.star_def] <;> ring
  have hmultAt :
      ‖laplaceAt v (z - 1 / 2)‖ ≤
        (L * N ^ 4) * ‖laplaceAt g (z - 1 / 2)‖ := by
    rw [show v = annihilatorDetectorSpanVector
        (fullFunctionalEquationOrbitAnnihilator g rho) g lambda from rfl,
      laplaceAt_fullOrbitSpanVector, norm_mul]
    exact mul_le_mul_of_nonneg_right
      (fullOrbit_span_multiplier_norm_le_height_pow_four rho z lambda hz hone)
      (norm_nonneg _)
  have hmultComp :
      ‖laplaceAt v ((1 - star z) - 1 / 2)‖ ≤
        (L * N ^ 4) * ‖laplaceAt g ((1 - star z) - 1 / 2)‖ := by
    rw [show v = annihilatorDetectorSpanVector
        (fullFunctionalEquationOrbitAnnihilator g rho) g lambda from rfl,
      laplaceAt_fullOrbitSpanVector, norm_mul]
    have hbound := fullOrbit_span_multiplier_norm_le_height_pow_four
      rho (1 - star z) lambda hcompRe
      (by simpa only [hcompIm] using hone)
    exact mul_le_mul_of_nonneg_right
      (by simpa only [hcompIm] using hbound) (norm_nonneg _)
  have hsquare :
      ‖laplaceAt v.convolutionSquare (z - 1 / 2)‖ ≤
        (L * N ^ 4) ^ 2 * ‖laplaceAt g.convolutionSquare (z - 1 / 2)‖ := by
    rw [laplaceAt_convolutionSquare, hcoord, norm_mul, norm_star]
    calc
      ‖laplaceAt v ((1 - star z) - 1 / 2)‖ *
          ‖laplaceAt v (z - 1 / 2)‖ ≤
        ((L * N ^ 4) * ‖laplaceAt g ((1 - star z) - 1 / 2)‖) *
          ((L * N ^ 4) * ‖laplaceAt g (z - 1 / 2)‖) := by
            exact mul_le_mul hmultComp hmultAt (norm_nonneg _) (by positivity)
      _ = (L * N ^ 4) ^ 2 *
          (‖laplaceAt g ((1 - star z) - 1 / 2)‖ *
            ‖laplaceAt g (z - 1 / 2)‖) := by ring
      _ = (L * N ^ 4) ^ 2 *
          ‖laplaceAt g.convolutionSquare (z - 1 / 2)‖ := by
            rw [laplaceAt_convolutionSquare, hcoord, norm_mul, norm_star]
  have hrawSquare :
      r ^ 12 * ‖laplaceAt g.convolutionSquare (z - 1 / 2)‖ ≤ M ^ 2 := by
    exact selectedOwner_convolutionSquare_vertical_twelfth_bound_of_q
      base correction C4 C2 T q n hq hC4 hC2 hbaseContract hbaseQuartic
      hcorrectionQuadratic z hz hTz
  have hnrho : ‖rho‖ ≤ 1 + ‖rho‖ := by linarith
  have hdist1 : ‖z - rho‖ ≤ K * N := by
    simpa only [norm_sub_rev] using
      orbitPoint_norm_sub_le_height rho rho z hnrho hz hone
  have hdist2 : ‖(1 - star z) - rho‖ ≤ K * N := by
    have h := orbitPoint_norm_sub_le_height rho rho (1 - star z)
      hnrho hcompRe (by simpa only [hcompIm] using hone)
    simpa only [norm_sub_rev, hcompIm] using h
  have hdist :
      ‖z - rho‖ ^ 2 * ‖(1 - star z) - rho‖ ^ 2 ≤ (K * N) ^ 4 := by
    calc
      ‖z - rho‖ ^ 2 * ‖(1 - star z) - rho‖ ^ 2 ≤
          (K * N) ^ 2 * (K * N) ^ 2 := by
            exact mul_le_mul
              (pow_le_pow_left₀ (norm_nonneg _) hdist1 2)
              (pow_le_pow_left₀ (norm_nonneg _) hdist2 2)
              (sq_nonneg _) (sq_nonneg _)
      _ = (K * N) ^ 4 := by ring
  have hr : r = N / (2 * Real.pi) := by
    dsimp [r, N]
    rw [abs_div, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  have hNpow : N ^ 12 = (2 * Real.pi) ^ 12 * r ^ 12 := by
    rw [hr]
    field_simp [Real.pi_ne_zero]
  change ‖z - rho‖ ^ 2 * ‖(1 - star z) - rho‖ ^ 2 *
      ‖laplaceAt v.convolutionSquare (z - 1 / 2)‖ ≤
    K ^ 4 * L ^ 2 * (2 * Real.pi) ^ 12 * M ^ 2
  calc
    ‖z - rho‖ ^ 2 * ‖(1 - star z) - rho‖ ^ 2 *
        ‖laplaceAt v.convolutionSquare (z - 1 / 2)‖ ≤
      (K * N) ^ 4 *
        ((L * N ^ 4) ^ 2 *
          ‖laplaceAt g.convolutionSquare (z - 1 / 2)‖) := by
            exact mul_le_mul hdist hsquare (by positivity) (by positivity)
    _ = (K ^ 4 * L ^ 2 * (2 * Real.pi) ^ 12) *
          (r ^ 12 * ‖laplaceAt g.convolutionSquare (z - 1 / 2)‖) := by
            calc
              (K * N) ^ 4 *
                  ((L * N ^ 4) ^ 2 *
                    ‖laplaceAt g.convolutionSquare (z - 1 / 2)‖) =
                (K ^ 4 * L ^ 2) *
                  (N ^ 12 * ‖laplaceAt g.convolutionSquare (z - 1 / 2)‖) :=
                    by ring
              _ = (K ^ 4 * L ^ 2) *
                  ((2 * Real.pi) ^ 12 * r ^ 12 *
                    ‖laplaceAt g.convolutionSquare (z - 1 / 2)‖) := by
                      rw [hNpow]
              _ = (K ^ 4 * L ^ 2 * (2 * Real.pi) ^ 12) *
                  (r ^ 12 * ‖laplaceAt g.convolutionSquare (z - 1 / 2)‖) :=
                    by ring
    _ ≤ (K ^ 4 * L ^ 2 * (2 * Real.pi) ^ 12) * M ^ 2 :=
      mul_le_mul_of_nonneg_left hrawSquare (by positivity)
    _ = K ^ 4 * L ^ 2 * (2 * Real.pi) ^ 12 * M ^ 2 := by ring

/-- The selected four-point span satisfies the existing fourth-order spectral
tail interface whenever its explicit scalar budget is below `epsilon²`.
The `lambda` budget is deliberately exposed: a gate-selected coefficient
may depend on the convolution count. -/
theorem selectedOwner_fullOrbit_span_fourthOrderSpectralTail
    (base correction : CompactLogTest) (rho : Complex)
    (lambda C4 C2 T epsilon : Real) (n : Nat)
    (hC4 : 0 ≤ C4) (hC2 : 0 ≤ C2)
    (hbaseContract : ∀ sigma ∈ Set.Icc (0 : Real) 1, ∀ t : Real,
      T ≤ |t| →
        ‖laplaceAt base ((sigma : Complex) + (t : Complex) * Complex.I)‖ ≤
          1 / 2)
    (hbaseQuartic : ∀ sigma ∈ Set.Icc (0 : Real) 1, ∀ t : Real,
      ‖t / (2 * Real.pi)‖ ^ 4 *
        ‖laplaceAt base ((sigma : Complex) + (t : Complex) * Complex.I)‖ ≤ C4)
    (hcorrectionQuadratic : ∀ sigma ∈ Set.Icc (0 : Real) 1, ∀ t : Real,
      ‖t / (2 * Real.pi)‖ ^ 2 *
        ‖laplaceAt correction
          ((sigma : Complex) + (t : Complex) * Complex.I)‖ ≤ C2)
    (hsmall :
      (3 + ‖rho‖) ^ 4 *
          ((3 + ‖rho‖) ^ 4 + |lambda|) ^ 2 *
          (2 * Real.pi) ^ 12 *
          ((1 / 2 : Real) ^ n * (C4 * C2)) ^ 2 < epsilon ^ 2) :
    FourthOrderSpectralTail
      (annihilatorDetectorSpanVector
        (fullFunctionalEquationOrbitAnnihilator
          (selectedOwner base correction n).sourceTest rho)
        (selectedOwner base correction n).sourceTest lambda).convolutionSquare
      rho T epsilon := by
  intro z hz hTz hone _hrhoHeight
  exact (selectedOwner_fullOrbit_span_doubleDistance_bound
    base correction rho lambda C4 C2 T n hC4 hC2 hbaseContract
    hbaseQuartic hcorrectionQuadratic z hz hTz hone).trans_lt hsmall

theorem selectedOwner_fullOrbit_span_fourthOrderSpectralTail_of_q
    (base correction : CompactLogTest) (rho : Complex)
    (lambda C4 C2 T q epsilon : Real) (n : Nat)
    (hq : 0 ≤ q) (hC4 : 0 ≤ C4) (hC2 : 0 ≤ C2)
    (hbaseContract : ∀ sigma ∈ Set.Icc (0 : Real) 1, ∀ t : Real,
      T ≤ |t| →
        ‖laplaceAt base ((sigma : Complex) + (t : Complex) * Complex.I)‖ ≤
          q)
    (hbaseQuartic : ∀ sigma ∈ Set.Icc (0 : Real) 1, ∀ t : Real,
      ‖t / (2 * Real.pi)‖ ^ 4 *
        ‖laplaceAt base ((sigma : Complex) + (t : Complex) * Complex.I)‖ ≤ C4)
    (hcorrectionQuadratic : ∀ sigma ∈ Set.Icc (0 : Real) 1, ∀ t : Real,
      ‖t / (2 * Real.pi)‖ ^ 2 *
        ‖laplaceAt correction
          ((sigma : Complex) + (t : Complex) * Complex.I)‖ ≤ C2)
    (hsmall :
      (3 + ‖rho‖) ^ 4 *
          ((3 + ‖rho‖) ^ 4 + |lambda|) ^ 2 *
          (2 * Real.pi) ^ 12 *
          ((q ^ n * (C4 * C2)) ^ 2) < epsilon ^ 2) :
    FourthOrderSpectralTail
      (annihilatorDetectorSpanVector
        (fullFunctionalEquationOrbitAnnihilator
          (selectedOwner base correction n).sourceTest rho)
        (selectedOwner base correction n).sourceTest lambda).convolutionSquare
      rho T epsilon := by
  intro z hz hTz hone _hrhoHeight
  exact (selectedOwner_fullOrbit_span_doubleDistance_bound_of_q
    base correction rho lambda C4 C2 T q n hq hC4 hC2 hbaseContract
    hbaseQuartic hcorrectionQuadratic z hz hTz hone).trans_lt hsmall

/-- For fixed base and correction owners, choose the decay constants and the
base contraction threshold before the convolution count and span coefficient.
The resulting tail implication is uniform in both later choices. -/
theorem exists_selectedOwner_fullOrbit_span_fourthOrderSpectralTail_constants
    (base correction : CompactLogTest) (rho : Complex) :
    ∃ C4 C2 T : Real,
      0 ≤ C4 ∧ 0 ≤ C2 ∧ 0 ≤ T ∧
      (∀ sigma ∈ Set.Icc (0 : Real) 1, ∀ t : Real,
        ‖t / (2 * Real.pi)‖ ^ 4 *
          ‖laplaceAt base ((sigma : Complex) + (t : Complex) * Complex.I)‖ ≤ C4) ∧
      (∀ sigma ∈ Set.Icc (0 : Real) 1, ∀ t : Real,
        ‖t / (2 * Real.pi)‖ ^ 2 *
          ‖laplaceAt correction
            ((sigma : Complex) + (t : Complex) * Complex.I)‖ ≤ C2) ∧
      (∀ sigma ∈ Set.Icc (0 : Real) 1, ∀ t : Real, T ≤ |t| →
        ‖laplaceAt base ((sigma : Complex) + (t : Complex) * Complex.I)‖ ≤
          1 / 2) ∧
      ∀ (n : Nat) (lambda epsilon : Real),
        (3 + ‖rho‖) ^ 4 *
            ((3 + ‖rho‖) ^ 4 + |lambda|) ^ 2 *
            (2 * Real.pi) ^ 12 *
            ((1 / 2 : Real) ^ n * (C4 * C2)) ^ 2 < epsilon ^ 2 →
        FourthOrderSpectralTail
          (annihilatorDetectorSpanVector
            (fullFunctionalEquationOrbitAnnihilator
              (selectedOwner base correction n).sourceTest rho)
            (selectedOwner base correction n).sourceTest lambda).convolutionSquare
          rho T epsilon := by
  obtain ⟨C4, hC4, hbaseQuartic⟩ :=
    C1SpectralWeil.exists_uniform_compactLog_laplaceAt_vertical_quartic_decay base
  obtain ⟨C2, hC2, hcorrectionQuadratic⟩ :=
    C1SpectralWeil.exists_uniform_compactLog_laplaceAt_vertical_quadratic_decay
      correction
  obtain ⟨Cbase2, hbase2, hbaseQuadratic⟩ :=
    C1SpectralWeil.exists_uniform_compactLog_laplaceAt_vertical_quadratic_decay
      base
  obtain ⟨T, hT, hbaseContract⟩ :=
    exists_laplaceAt_vertical_half_contraction_of_quadratic_bound
      base Cbase2 hbase2 hbaseQuadratic
  refine ⟨C4, C2, T, hC4, hC2, hT, hbaseQuartic,
    hcorrectionQuadratic, hbaseContract, ?_⟩
  intro n lambda epsilon hsmall
  exact selectedOwner_fullOrbit_span_fourthOrderSpectralTail
    base correction rho lambda C4 C2 T epsilon n hC4 hC2 hbaseContract
    hbaseQuartic hcorrectionQuadratic hsmall

/-! The convolution index can be chosen after a fixed owner, coefficient, and
positive tail budget have been fixed. This removes the former conditional
`hsmall` premise from the producer-facing existence statement. -/
theorem exists_nat_selectedOwner_fullOrbit_span_fourthOrderSpectralTail
    (base correction : CompactLogTest) (rho lambda epsilon : Real)
    (hepsilon : 0 < epsilon) :
    ∃ C4 C2 T : Real, ∃ n : Nat,
      0 ≤ C4 ∧ 0 ≤ C2 ∧ 0 ≤ T ∧
      FourthOrderSpectralTail
        (annihilatorDetectorSpanVector
          (fullFunctionalEquationOrbitAnnihilator
            (selectedOwner base correction n).sourceTest rho)
          (selectedOwner base correction n).sourceTest lambda).convolutionSquare
        rho T epsilon := by
  obtain ⟨C4, C2, T, hC4, hC2, hT, hbaseQuartic,
      hcorrectionQuadratic, hbaseContract, htail⟩ :=
    exists_selectedOwner_fullOrbit_span_fourthOrderSpectralTail_constants
      base correction rho
  let A : Real :=
    (3 + ‖rho‖) ^ 4 *
      ((3 + ‖rho‖) ^ 4 + |lambda|) ^ 2 *
      (2 * Real.pi) ^ 12
  have hpow : Filter.Tendsto (fun n : Nat => (1 / 2 : Real) ^ n)
      Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hsq : Filter.Tendsto
      (fun n : Nat => ((1 / 2 : Real) ^ n) * ((1 / 2 : Real) ^ n))
      Filter.atTop (nhds 0) :=
    by simpa using hpow.mul hpow
  have hscaled : Filter.Tendsto
      (fun n : Nat => A * (((1 / 2 : Real) ^ n * (C4 * C2)) ^ 2))
      Filter.atTop (nhds 0) := by
    have h := hsq.mul_const (A * (C4 * C2) ^ 2)
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using h
  obtain ⟨n, hn⟩ :=
    (hscaled.eventually_lt_const (sq_pos_of_pos hepsilon)).exists
  refine ⟨C4, C2, T, n, hC4, hC2, hT, ?_⟩
  apply htail n lambda epsilon
  simpa [A] using hn

/-! Uniform version: once the span coefficient is restricted to a bounded
interval, one convolution-index threshold works for every later index and
every coefficient in that interval. -/
theorem exists_uniform_nat_selectedOwner_fullOrbit_span_fourthOrderSpectralTail
    (base correction : CompactLogTest) (rho : Complex) (L epsilon : Real)
    (hL : 0 ≤ L) (hepsilon : 0 < epsilon) :
    ∃ C4 C2 T : Real, ∃ N : Nat,
      0 ≤ C4 ∧ 0 ≤ C2 ∧ 0 ≤ T ∧
      ∀ n : Nat, N ≤ n → ∀ lambda : Real, |lambda| ≤ L →
        FourthOrderSpectralTail
          (annihilatorDetectorSpanVector
            (fullFunctionalEquationOrbitAnnihilator
              (selectedOwner base correction n).sourceTest rho)
            (selectedOwner base correction n).sourceTest lambda).convolutionSquare
          rho T epsilon := by
  obtain ⟨C4, C2, T, hC4, hC2, hT, hbaseQuartic,
      hcorrectionQuadratic, hbaseContract, htail⟩ :=
    exists_selectedOwner_fullOrbit_span_fourthOrderSpectralTail_constants
      base correction rho
  let A : Real :=
    (3 + ‖rho‖) ^ 4 *
      ((3 + ‖rho‖) ^ 4 + L) ^ 2 *
      (2 * Real.pi) ^ 12
  have hpow : Filter.Tendsto (fun n : Nat => (1 / 2 : Real) ^ n)
      Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hsq : Filter.Tendsto
      (fun n : Nat => ((1 / 2 : Real) ^ n) * ((1 / 2 : Real) ^ n))
      Filter.atTop (nhds 0) := by simpa using hpow.mul hpow
  have hscaled : Filter.Tendsto
      (fun n : Nat => A * (((1 / 2 : Real) ^ n * (C4 * C2)) ^ 2))
      Filter.atTop (nhds 0) := by
    have h := hsq.mul_const (A * (C4 * C2) ^ 2)
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using h
  obtain ⟨N, hN⟩ :=
    Filter.eventually_atTop.mp
      (hscaled.eventually_lt_const (sq_pos_of_pos hepsilon))
  refine ⟨C4, C2, T, N, hC4, hC2, hT, ?_⟩
  intro n hn lambda hlam
  apply htail n lambda epsilon
  have hbase := hN n hn
  have hbaseCoeff : (3 + ‖rho‖) ^ 4 + |lambda| ≤
      (3 + ‖rho‖) ^ 4 + L := by linarith
  have hsqCoeff : ((3 + ‖rho‖) ^ 4 + |lambda|) ^ 2 ≤
      ((3 + ‖rho‖) ^ 4 + L) ^ 2 := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).2
    exact hbaseCoeff
  have hfactor : 0 ≤
      (3 + ‖rho‖) ^ 4 * (2 * Real.pi) ^ 12 := by positivity
  have htailfactor : 0 ≤ ((1 / 2 : Real) ^ n * (C4 * C2)) ^ 2 := by positivity
  have hbound :
      (3 + ‖rho‖) ^ 4 *
          ((3 + ‖rho‖) ^ 4 + |lambda|) ^ 2 *
          (2 * Real.pi) ^ 12 *
          ((1 / 2 : Real) ^ n * (C4 * C2)) ^ 2 ≤
        A * (((1 / 2 : Real) ^ n * (C4 * C2)) ^ 2) := by
    dsimp [A]
    calc
      (3 + ‖rho‖) ^ 4 *
          ((3 + ‖rho‖) ^ 4 + |lambda|) ^ 2 *
          (2 * Real.pi) ^ 12 *
          ((1 / 2 : Real) ^ n * (C4 * C2)) ^ 2 =
        ((3 + ‖rho‖) ^ 4 * (2 * Real.pi) ^ 12) *
          (((3 + ‖rho‖) ^ 4 + |lambda|) ^ 2 *
            ((1 / 2 : Real) ^ n * (C4 * C2)) ^ 2) := by ring
      _ ≤ ((3 + ‖rho‖) ^ 4 * (2 * Real.pi) ^ 12) *
          (((3 + ‖rho‖) ^ 4 + L) ^ 2 *
            ((1 / 2 : Real) ^ n * (C4 * C2)) ^ 2) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hsqCoeff htailfactor) hfactor
      _ = A * (((1 / 2 : Real) ^ n * (C4 * C2)) ^ 2) := by ring
  exact lt_of_le_of_lt hbound hbase

/-! Uniformity on a bounded rho-region. The decay constants depend only on the
base and correction; the rho-dependence is absorbed by the radius `R`. -/
theorem exists_bounded_rho_uniform_nat_selectedOwner_fullOrbit_span_fourthOrderSpectralTail
    (base correction : CompactLogTest) (R L epsilon : Real)
    (hR : 0 ≤ R) (hL : 0 ≤ L) (hepsilon : 0 < epsilon) :
    ∃ C4 C2 T : Real, ∃ N : Nat,
      0 ≤ C4 ∧ 0 ≤ C2 ∧ 0 ≤ T ∧
      ∀ rho : Complex, ‖rho‖ ≤ R →
        ∀ n : Nat, N ≤ n → ∀ lambda : Real, |lambda| ≤ L →
          FourthOrderSpectralTail
            (annihilatorDetectorSpanVector
              (fullFunctionalEquationOrbitAnnihilator
                (selectedOwner base correction n).sourceTest rho)
              (selectedOwner base correction n).sourceTest lambda).convolutionSquare
            rho T epsilon := by
  obtain ⟨C4, C2, T, hC4, hC2, hT, hbaseQuartic,
      hcorrectionQuadratic, hbaseContract, _⟩ :=
    exists_selectedOwner_fullOrbit_span_fourthOrderSpectralTail_constants
      base correction (0 : Complex)
  let A : Real :=
    (3 + R) ^ 4 *
      ((3 + R) ^ 4 + L) ^ 2 *
      (2 * Real.pi) ^ 12
  have hpow : Filter.Tendsto (fun n : Nat => (1 / 2 : Real) ^ n)
      Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hsq : Filter.Tendsto
      (fun n : Nat => ((1 / 2 : Real) ^ n) * ((1 / 2 : Real) ^ n))
      Filter.atTop (nhds 0) := by simpa using hpow.mul hpow
  have hscaled : Filter.Tendsto
      (fun n : Nat => A * (((1 / 2 : Real) ^ n * (C4 * C2)) ^ 2))
      Filter.atTop (nhds 0) := by
    have h := hsq.mul_const (A * (C4 * C2) ^ 2)
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using h
  obtain ⟨N, hN⟩ :=
    Filter.eventually_atTop.mp
      (hscaled.eventually_lt_const (sq_pos_of_pos hepsilon))
  refine ⟨C4, C2, T, N, hC4, hC2, hT, ?_⟩
  intro rho hrho n hn lambda hlam
  apply selectedOwner_fullOrbit_span_fourthOrderSpectralTail
    (base := base) (correction := correction) (rho := rho)
    (lambda := lambda) (C4 := C4) (C2 := C2) (T := T)
    (epsilon := epsilon) (n := n) hC4 hC2 hbaseContract
    hbaseQuartic hcorrectionQuadratic
  have hK : 3 + ‖rho‖ ≤ 3 + R := by linarith
  have hKpow : (3 + ‖rho‖) ^ 4 ≤ (3 + R) ^ 4 :=
    pow_le_pow_left₀ (by positivity) hK 4
  have hCoeff : (3 + ‖rho‖) ^ 4 + |lambda| ≤
      (3 + R) ^ 4 + L := by linarith
  have hCoeffSq : ((3 + ‖rho‖) ^ 4 + |lambda|) ^ 2 ≤
      ((3 + R) ^ 4 + L) ^ 2 := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).2
    exact hCoeff
  have hfactor : 0 ≤ (3 + ‖rho‖) ^ 4 *
      (2 * Real.pi) ^ 12 := by positivity
  have htailfactor : 0 ≤ ((1 / 2 : Real) ^ n * (C4 * C2)) ^ 2 := by positivity
  have hbound :
      (3 + ‖rho‖) ^ 4 *
          ((3 + ‖rho‖) ^ 4 + |lambda|) ^ 2 *
          (2 * Real.pi) ^ 12 *
          ((1 / 2 : Real) ^ n * (C4 * C2)) ^ 2 ≤
        A * (((1 / 2 : Real) ^ n * (C4 * C2)) ^ 2) := by
    dsimp [A]
    calc
      (3 + ‖rho‖) ^ 4 *
          ((3 + ‖rho‖) ^ 4 + |lambda|) ^ 2 *
          (2 * Real.pi) ^ 12 *
          ((1 / 2 : Real) ^ n * (C4 * C2)) ^ 2 ≤
        (3 + R) ^ 4 *
          ((3 + R) ^ 4 + L) ^ 2 *
          (2 * Real.pi) ^ 12 *
          ((1 / 2 : Real) ^ n * (C4 * C2)) ^ 2 := by
        calc
          _ = ((3 + ‖rho‖) ^ 4 * (2 * Real.pi) ^ 12) *
              (((3 + ‖rho‖) ^ 4 + |lambda|) ^ 2 *
                ((1 / 2 : Real) ^ n * (C4 * C2)) ^ 2) := by ring
          _ ≤ ((3 + ‖rho‖) ^ 4 * (2 * Real.pi) ^ 12) *
              (((3 + R) ^ 4 + L) ^ 2 *
                ((1 / 2 : Real) ^ n * (C4 * C2)) ^ 2) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hCoeffSq htailfactor) hfactor
          _ ≤ ((3 + R) ^ 4 * (2 * Real.pi) ^ 12) *
              (((3 + R) ^ 4 + L) ^ 2 *
                ((1 / 2 : Real) ^ n * (C4 * C2)) ^ 2) := by
            have hRfactor : 0 ≤ ((3 + R) ^ 4 + L) ^ 2 *
                ((1 / 2 : Real) ^ n * (C4 * C2)) ^ 2 := by positivity
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hKpow
                (by positivity : 0 ≤ (2 * Real.pi) ^ 12)) hRfactor
          _ = (3 + R) ^ 4 *
              ((3 + R) ^ 4 + L) ^ 2 *
              (2 * Real.pi) ^ 12 *
              ((1 / 2 : Real) ^ n * (C4 * C2)) ^ 2 := by ring
      _ = A * (((1 / 2 : Real) ^ n * (C4 * C2)) ^ 2) := by ring
  exact lt_of_le_of_lt hbound (hN n hn)

end
end C1FourPointHighShellTail
end Source
end ConnesWeilRH
