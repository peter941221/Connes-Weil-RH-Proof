import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! High-shell geometry only. No gate, analytic tail, or RH claim. -/
namespace ConnesWeilRH.Dev.C1HighShellGeometry2710

theorem distance_sq_le (w z : ℂ)
    (hw : w.re ∈ Set.Icc (0 : ℝ) 1)
    (hz : z.re ∈ Set.Icc (0 : ℝ) 1)
    (hy : 1 ≤ |z.im|) (hsep : 2 * |w.im| ≤ |z.im|) :
    ‖w - z‖ ^ 2 ≤ (13 / 4 : ℝ) * |z.im| ^ 2 := by
  have hrlo : -1 ≤ w.re - z.re := by linarith [hw.1, hz.2]
  have hrhi : w.re - z.re ≤ 1 := by linarith [hw.2, hz.1]
  have hr : (w.re - z.re) ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - (w.re - z.re))
      (by linarith : 0 ≤ 1 + (w.re - z.re))]
  have hi : |w.im - z.im| ≤ (3 / 2 : ℝ) * |z.im| := by
    calc
      |w.im - z.im| ≤ |w.im| + |z.im| := abs_sub _ _
      _ ≤ (3 / 2 : ℝ) * |z.im| := by linarith
  have hi2 : (w.im - z.im) ^ 2 ≤ ((3 / 2 : ℝ) * |z.im|) ^ 2 := by
    have h := mul_self_le_mul_self (abs_nonneg (w.im - z.im)) hi
    simpa only [← sq, sq_abs] using h
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im]
  nlinarith [sq_nonneg (|z.im| - 1)]

private theorem pair_norm_le (a b : ℂ) (c : ℝ) (hc : 0 ≤ c)
    (ha : ‖a‖ ^ 2 ≤ c) (hb : ‖b‖ ^ 2 ≤ c) : ‖a * b‖ ≤ c := by
  have h : ‖a * b‖ ^ 2 ≤ c ^ 2 := by
    calc
      _ = ‖a‖ ^ 2 * ‖b‖ ^ 2 := by simp only [norm_mul, mul_pow]
      _ ≤ c * c := mul_le_mul ha hb (sq_nonneg ‖b‖) hc
      _ = _ := by ring
  nlinarith [norm_nonneg (a * b)]

theorem orbit_product_le (rho z : ℂ)
    (hrho : rho.re ∈ Set.Icc (0 : ℝ) 1)
    (hz : z.re ∈ Set.Icc (0 : ℝ) 1)
    (hy : 1 ≤ |z.im|) (hsep : 2 * |rho.im| ≤ |z.im|) :
    ‖((1 - rho) - z) * (star rho - z) *
      ((1 - star rho) - z) * (rho - z)‖ ≤ (169 / 16 : ℝ) * |z.im| ^ 4 := by
  have h1r : ((1 : ℂ) - rho).re ∈ Set.Icc (0 : ℝ) 1 := by
    simp only [Complex.sub_re, Complex.one_re]
    constructor <;> linarith [hrho.1, hrho.2]
  have h3r : ((1 : ℂ) - star rho).re ∈ Set.Icc (0 : ℝ) 1 := by
    simpa using h1r
  have h1s : 2 * |((1 : ℂ) - rho).im| ≤ |z.im| := by simpa using hsep
  have h2s : 2 * |(star rho).im| ≤ |z.im| := by simpa using hsep
  have h3s : 2 * |((1 : ℂ) - star rho).im| ≤ |z.im| := by simpa using hsep
  have h1 := distance_sq_le (1 - rho) z h1r hz hy h1s
  have h2 := distance_sq_le (star rho) z (by simpa using hrho) hz hy h2s
  have h3 := distance_sq_le (1 - star rho) z h3r hz hy h3s
  have h4 := distance_sq_le rho z hrho hz hy hsep
  have hp := pair_norm_le _ _ _ (by positivity) h1 h2
  have hq := pair_norm_le _ _ _ (by positivity) h3 h4
  calc
    _ = ‖((1 - rho) - z) * (star rho - z)‖ *
        ‖((1 - star rho) - z) * (rho - z)‖ := by simp only [norm_mul]; ring
    _ ≤ ((13 / 4 : ℝ) * |z.im| ^ 2) * ((13 / 4 : ℝ) * |z.im| ^ 2) :=
      mul_le_mul hp hq (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem orbit_multiplier_le (rho z : ℂ) (lam : ℝ)
    (hrho : rho.re ∈ Set.Icc (0 : ℝ) 1)
    (hz : z.re ∈ Set.Icc (0 : ℝ) 1)
    (hy : 1 ≤ |z.im|) (hsep : 2 * |rho.im| ≤ |z.im|) :
    ‖((1 - rho) - z) * (star rho - z) *
      ((1 - star rho) - z) * (rho - z) - (lam : ℂ)‖ ≤
      ((169 / 16 : ℝ) + |lam|) * |z.im| ^ 4 := by
  have hp := orbit_product_le rho z hrho hz hy hsep
  have hpow : 1 ≤ |z.im| ^ 4 := one_le_pow₀ hy
  have hl : |lam| ≤ |lam| * |z.im| ^ 4 := by
    nlinarith [mul_nonneg (abs_nonneg lam) (sub_nonneg.mpr hpow)]
  calc
    _ ≤ ‖((1 - rho) - z) * (star rho - z) *
        ((1 - star rho) - z) * (rho - z)‖ + |lam| := by
      simpa using norm_sub_le
        (((1 - rho) - z) * (star rho - z) * ((1 - star rho) - z) * (rho - z))
        (lam : ℂ)
    _ ≤ (169 / 16 : ℝ) * |z.im| ^ 4 + |lam| := add_le_add hp le_rfl
    _ ≤ _ := by nlinarith

theorem spectral_distance_product_le (rho z : ℂ)
    (hrho : rho.re ∈ Set.Icc (0 : ℝ) 1)
    (hz : z.re ∈ Set.Icc (0 : ℝ) 1)
    (hy : 1 ≤ |z.im|) (hsep : 2 * |rho.im| ≤ |z.im|) :
    ‖z - rho‖ ^ 2 * ‖((1 : ℂ) - star z) - rho‖ ^ 2 ≤
      (169 / 16 : ℝ) * |z.im| ^ 4 := by
  have href : ((1 : ℂ) - star z).re ∈ Set.Icc (0 : ℝ) 1 := by
    simp only [Complex.sub_re, Complex.one_re, Complex.star_def, Complex.conj_re]
    constructor <;> linarith [hz.1, hz.2]
  have hi : |((1 : ℂ) - star z).im| = |z.im| := by simp
  have h1 : ‖z - rho‖ ^ 2 ≤ (13 / 4 : ℝ) * |z.im| ^ 2 := by
    simpa only [norm_sub_rev] using distance_sq_le rho z hrho hz hy hsep
  have h2 : ‖((1 : ℂ) - star z) - rho‖ ^ 2 ≤
      (13 / 4 : ℝ) * |z.im| ^ 2 := by
    have h := distance_sq_le rho (1 - star z) hrho href
      (by simpa only [hi] using hy) (by simpa only [hi] using hsep)
    simpa only [hi, norm_sub_rev] using h
  calc
    _ ≤ ((13 / 4 : ℝ) * |z.im| ^ 2) * ((13 / 4 : ℝ) * |z.im| ^ 2) :=
      mul_le_mul h1 h2 (sq_nonneg _) (by positivity)
    _ = _ := by ring

/-- Exact four-point polynomial, in the uncentered source coordinate. -/
noncomputable def orbitPolynomial (rho z : ℂ) : ℂ :=
  ((1 - rho) - z) * (star rho - z) * ((1 - star rho) - z) * (rho - z)

/-- Geometric transport of a raw-square tail bound. The raw transform bound
remains explicit; no analytic decay or gate sign is manufactured here. -/
theorem weighted_transformed_square_le (rho z : ℂ) (lam R : ℝ) (f : ℂ → ℂ)
    (hrho : rho.re ∈ Set.Icc (0 : ℝ) 1)
    (hz : z.re ∈ Set.Icc (0 : ℝ) 1)
    (hy : 1 ≤ |z.im|) (hsep : 2 * |rho.im| ≤ |z.im|)
    (hraw : |z.im| ^ 12 * (‖f z‖ * ‖f (1 - star z)‖) ≤ R) :
    ‖z - rho‖ ^ 2 * ‖((1 : ℂ) - star z) - rho‖ ^ 2 *
      ‖((orbitPolynomial rho z - (lam : ℂ)) * f z) *
        star ((orbitPolynomial rho (1 - star z) - (lam : ℂ)) * f (1 - star z))‖ ≤
      (169 / 16 : ℝ) * ((169 / 16 : ℝ) + |lam|) ^ 2 * R := by
  have href : ((1 : ℂ) - star z).re ∈ Set.Icc (0 : ℝ) 1 := by
    simp only [Complex.sub_re, Complex.one_re, Complex.star_def, Complex.conj_re]
    constructor <;> linarith [hz.1, hz.2]
  have hi : |((1 : ℂ) - star z).im| = |z.im| := by simp
  have h1 := orbit_multiplier_le rho z lam hrho hz hy hsep
  have h2 := orbit_multiplier_le rho (1 - star z) lam hrho href
    (by simpa only [hi] using hy) (by simpa only [hi] using hsep)
  simp only [hi] at h2
  change ‖orbitPolynomial rho z - (lam : ℂ)‖ ≤ _ at h1
  change ‖orbitPolynomial rho (1 - star z) - (lam : ℂ)‖ ≤ _ at h2
  have hm := mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
  have hd := spectral_distance_product_le rho z hrho hz hy hsep
  have ht := mul_le_mul hd hm (by positivity) (by positivity)
  have h := mul_le_mul_of_nonneg_right ht (mul_nonneg (norm_nonneg (f z))
    (norm_nonneg (f (1 - star z))))
  simp only [norm_mul, norm_star]
  calc
    _ ≤ ((169 / 16 : ℝ) * |z.im| ^ 4) *
        ((((169 / 16 : ℝ) + |lam|) * |z.im| ^ 4) *
          (((169 / 16 : ℝ) + |lam|) * |z.im| ^ 4)) *
        (‖f z‖ * ‖f (1 - star z)‖) := by nlinarith only [h]
    _ = ((169 / 16 : ℝ) * ((169 / 16 : ℝ) + |lam|) ^ 2) *
        (|z.im| ^ 12 * (‖f z‖ * ‖f (1 - star z)‖)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hraw (by positivity)

#print axioms distance_sq_le
#print axioms orbit_product_le
#print axioms orbit_multiplier_le
#print axioms spectral_distance_product_le
#print axioms weighted_transformed_square_le

end ConnesWeilRH.Dev.C1HighShellGeometry2710
