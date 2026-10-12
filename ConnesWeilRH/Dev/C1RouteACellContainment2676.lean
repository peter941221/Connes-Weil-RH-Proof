import ConnesWeilRH.Dev.C1RouteACellIntegralCharge2675
import ConnesWeilRH.Dev.C1RouteAExternalOwnerZeroExtension
import Mathlib.Analysis.Complex.Trigonometric

/-!
# Record 2676: generic containment pins for the repaired-owner cell bridge

Record 2675 left one premise open: the 2242 natural interval evaluator must
contain the actual repaired-owner channel functions pointwise on the whole
cell.  The discharge is split into two layers.  This module carries the
GENERIC layer; every numeric constant stays a hypothesis or an explicit
argument so nothing here is cell-specific:

* two-sided Taylor pins for `Real.exp` (`expTwoSided2676`), the n = 30 pin at
  -1/2 lifted through `exp (-30) = (exp (-1/2)) ^ 60`
  (`expNegHalfPowerPins2676`), and the n = 5 lower addend pin
  (`expAddendLowerPin2676`),
* the bump box lemma: on `0 <= x <= X < radius` the bump
  `widthBump radius x = exp (-30 / (1 - (x/radius)^2))` lies between
  `loBase * pLo` and `hiPin` whenever `loBase <= exp (-30)` and
  `pLo <= exp (30 - 30 / (1 - (X/radius)^2))` (`bumpBoxMem2676`),
* the complex Taylor partial sum `expIPartial2676` with its real and
  imaginary projections onto the even/odd real series
  (`reExpIPartial2676` / `imExpIPartial2676`), and cos/sin endpoint pins via
  `Complex.exp_bound` (`cosPin2676` / `sinPin2676`),
* interval helpers for inverse powers of `q`, the generic family rectangles
  (mid rectangle, k = 0 family, k = 2 family), and the componentwise
  rectangle-subset transfer (`rectSubset2676`).

The per-family literals, the 60 family bridge instances, the four channel
aggregates and their containment inside the exported 2675 rectangles live in
the generated companion module.
-/

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

/-! ## Two-sided Taylor pins for `Real.exp` -/

theorem expTwoSided2676 {x : ℝ} {n : ℕ} (hn : 0 < n) (hx : |x| ≤ 1)
    {S E : ℝ} (hS : ∑ m ∈ Finset.range n, x ^ m / (m.factorial : ℝ) = S)
    (hE : |x| ^ n * (n.succ / (n.factorial * n)) = E) :
    S - E ≤ Real.exp x ∧ Real.exp x ≤ S + E := by
  have h := Real.exp_bound hx hn
  rw [hS, hE] at h
  rcases abs_le.mp h with ⟨h1, h2⟩
  constructor <;> linarith

/-- The n = 30 pin at `-1/2`, lifted to `exp (60 * x) = exp (-30)` through a
monotone 60th power.  `hS2E` is a pure literal side condition giving the pin
enough room that `exp x - E` stays nonnegative. -/
theorem expNegHalfPowerPins2676 (x : ℝ) {S E : ℝ}
    (hxval : x = -(1 / 2 : ℝ))
    (hS : ∑ m ∈ Finset.range 30, x ^ m / (m.factorial : ℝ) = S)
    (hE : |x| ^ 30 * ((30 : Nat).succ / ((30 : Nat).factorial * 30)) = E)
    (hS2E : 0 ≤ S - 2 * E) :
    (Real.exp x - E) ^ 60 ≤ Real.exp ((60 : ℕ) * x)
      ∧ Real.exp ((60 : ℕ) * x) ≤ (Real.exp x + E) ^ 60 := by
  have hx1 : |x| ≤ 1 := by rw [hxval]; norm_num
  have hpin := expTwoSided2676 (n := 30) (by norm_num) hx1 hS hE
  have hpos : 0 ≤ Real.exp x - E := by linarith
  simp only [Real.exp_nat_mul]
  constructor
  · exact pow_le_pow_left₀ hpos (by linarith) 60
  · exact pow_le_pow_left₀ (Real.exp_pos x).le (by linarith) 60

/-- The n = 5 one-sided pin for the exponential addend `s <= -|s| >= -1`:
`sum_{m<5} s^m/m! - |s|^5 * 6/600 <= exp s`. -/
theorem expAddendLowerPin2676 (t : ℝ) (h1 : t ≤ 0) (h2 : -1 ≤ t)
    {S E : ℝ} (hS : ∑ m ∈ Finset.range 5, t ^ m / (m.factorial : ℝ) = S)
    (hE : |t| ^ 5 * ((5 : Nat).succ / ((5 : Nat).factorial * 5)) = E) :
    S - E ≤ Real.exp t := by
  have hx1 : |t| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  exact (expTwoSided2676 (by norm_num) hx1 hS hE).1

/-! ## The bump box lemma -/

theorem bumpBoxMem2676 {x X radius loBase pLo hiPin : ℝ}
    (hx0 : 0 ≤ x) (hxX : x ≤ X) (hXr : X < radius)
    (hloBase : loBase ≤ Real.exp (-30)) (hhiPin : Real.exp (-30) ≤ hiPin)
    (hpLo : pLo ≤ Real.exp (30 - 30 / (1 - (X / radius) ^ 2)))
    (hloPos : 0 ≤ loBase) :
    loBase * pLo ≤ widthBump radius x
      ∧ widthBump radius x ≤ hiPin := by
  have hrpos : 0 < radius := by linarith
  have hinside : |x| < radius := by rw [abs_of_nonneg hx0]; linarith
  have hbump : widthBump radius x
      = Real.exp (-30 / (1 - (x / radius) ^ 2)) := by
    rw [widthBump, if_pos hinside]
  have habsx : |x / radius| < 1 := by
    have hxabs : |x| ≤ X := by rw [abs_of_nonneg hx0]; exact hxX
    calc |x / radius| = |x| / radius := by rw [abs_div, abs_of_pos hrpos]
      _ ≤ X / radius := div_le_div_of_nonneg_right hxabs hrpos.le
      _ < 1 := div_lt_one hrpos |>.mpr hXr
  have hqlo : 0 < 1 - (x / radius) ^ 2 := by
    rcases abs_lt.mp habsx with ⟨hn, hp⟩
    have e1 : (0 : ℝ) < 1 + x / radius := by linarith
    have e2 : (0 : ℝ) < 1 - x / radius := by linarith
    have e4 := mul_pos e2 e1
    rw [show (1 - x / radius) * (1 + x / radius)
        = 1 - (x / radius) ^ 2 from by ring] at e4
    exact e4
  have habsX : |X / radius| < 1 := by
    have hX0 : 0 ≤ X := hx0.trans hxX
    have hXabs : |X| ≤ X := by rw [abs_of_nonneg hX0]
    calc |X / radius| = |X| / radius := by rw [abs_div, abs_of_pos hrpos]
      _ ≤ X / radius := div_le_div_of_nonneg_right hXabs hrpos.le
      _ < 1 := div_lt_one hrpos |>.mpr hXr
  have hqXlo : 0 < 1 - (X / radius) ^ 2 := by
    rcases abs_lt.mp habsX with ⟨hn, hp⟩
    have e1 : (0 : ℝ) < 1 + X / radius := by linarith
    have e2 : (0 : ℝ) < 1 - X / radius := by linarith
    have e4 := mul_pos e2 e1
    rw [show (1 - X / radius) * (1 + X / radius)
        = 1 - (X / radius) ^ 2 from by ring] at e4
    exact e4
  have hqle : (1 : ℝ) - (X / radius) ^ 2 ≤ 1 - (x / radius) ^ 2 := by
    have hpow : (x / radius) ^ 2 ≤ (X / radius) ^ 2 :=
      pow_le_pow_left₀ (div_nonneg hx0 hrpos.le)
        (div_le_div_of_nonneg_right hxX hrpos.le) 2
    linarith
  have hq1 : (1 : ℝ) - (x / radius) ^ 2 ≤ 1 := by
    have := sq_nonneg (x / radius)
    linarith
  have hsUB : 30 - 30 / (1 - (x / radius) ^ 2) ≤ 0 := by
    have hinv := one_div_le_one_div_of_le hqlo hq1
    have h30 := mul_le_mul_of_nonneg_left hinv (by norm_num : (0 : ℝ) ≤ 30)
    simp only [div_one] at h30
    rw [show (30 : ℝ) / (1 - (x / radius) ^ 2)
        = 30 * (1 / (1 - (x / radius) ^ 2)) from by ring]
    linarith
  have hsLB : 30 - 30 / (1 - (X / radius) ^ 2)
      ≤ 30 - 30 / (1 - (x / radius) ^ 2) := by
    have hinv := one_div_le_one_div_of_le hqXlo hqle
    have h30 := mul_le_mul_of_nonneg_left hinv (by norm_num : (0 : ℝ) ≤ 30)
    rw [show (30 : ℝ) / (1 - (x / radius) ^ 2)
        = 30 * (1 / (1 - (x / radius) ^ 2)) from by ring,
      show (30 : ℝ) / (1 - (X / radius) ^ 2)
        = 30 * (1 / (1 - (X / radius) ^ 2)) from by ring]
    linarith
  have hsplit : (-30 : ℝ) / (1 - (x / radius) ^ 2)
      = -30 + (30 - 30 / (1 - (x / radius) ^ 2)) := by ring
  rw [hbump, hsplit, Real.exp_add]
  constructor
  · have htrans : Real.exp (30 - 30 / (1 - (X / radius) ^ 2))
        ≤ Real.exp (30 - 30 / (1 - (x / radius) ^ 2)) :=
      Real.exp_le_exp.mpr hsLB
    calc loBase * pLo
        ≤ loBase * Real.exp (30 - 30 / (1 - (X / radius) ^ 2)) :=
          mul_le_mul_of_nonneg_left hpLo hloPos
      _ ≤ loBase * Real.exp (30 - 30 / (1 - (x / radius) ^ 2)) :=
          mul_le_mul_of_nonneg_left htrans hloPos
      _ ≤ Real.exp (-30) * Real.exp (30 - 30 / (1 - (x / radius) ^ 2)) :=
          mul_le_mul_of_nonneg_right hloBase (Real.exp_pos _).le
  · have hexpUB : Real.exp (30 - 30 / (1 - (x / radius) ^ 2)) ≤ 1 := by
      have hex := Real.exp_le_exp.mpr hsUB
      simpa using hex
    calc Real.exp (-30) * Real.exp (30 - 30 / (1 - (x / radius) ^ 2))
        ≤ Real.exp (-30) * 1 :=
          mul_le_mul_of_nonneg_left hexpUB (Real.exp_pos _).le
      _ ≤ hiPin := by rw [mul_one]; exact hhiPin

/-! ## Complex Taylor partial sums and the cos/sin endpoint pins -/

/-- The n-term Taylor partial sum of `exp (a * I)` at complex precision. -/
noncomputable def expIPartial2676 (a : ℝ) (n : ℕ) : ℂ :=
  ∑ m ∈ Finset.range n, ((a : ℂ) * Complex.I) ^ m / ((m.factorial : ℕ) : ℂ)

theorem sumRangePair2676 (g : ℕ → ℂ) (N : ℕ) :
    ∑ m ∈ Finset.range (2 * N), g m
      = ∑ k ∈ Finset.range N, (g (2 * k) + g (2 * k + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have h2 : 2 * (N + 1) = 2 * N + 1 + 1 := by ring
    rw [h2, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ, add_assoc]

theorem complexIpowEven2676 (a : ℝ) (k : ℕ) :
    ((a : ℂ) * Complex.I) ^ (2 * k) = (((-1 : ℝ) ^ k * a ^ (2 * k) : ℝ) : ℂ) := by
  have h2 : ((a : ℂ) * Complex.I) ^ 2 = (-(a ^ (2 : ℕ)) : ℝ) := by
    rw [pow_two]
    have hr : ((a : ℂ) * Complex.I) * ((a : ℂ) * Complex.I)
        = ((a * a : ℂ) * (Complex.I * Complex.I)) := by ring
    rw [hr, Complex.I_mul_I]
    push_cast
    ring
  calc ((a : ℂ) * Complex.I) ^ (2 * k)
      = (((a : ℂ) * Complex.I) ^ 2) ^ k := by rw [pow_mul]
    _ = ((-(a ^ (2 : ℕ)) : ℝ) : ℂ) ^ k := by rw [h2]
    _ = (((-1 : ℝ) ^ k * a ^ (2 * k) : ℝ) : ℂ) := by
        push_cast
        rw [neg_pow, pow_mul]

theorem complexIpowOdd2676 (a : ℝ) (k : ℕ) :
    ((a : ℂ) * Complex.I) ^ (2 * k + 1)
      = (((-1 : ℝ) ^ k * a ^ (2 * k) * a : ℝ) : ℂ) * Complex.I := by
  rw [pow_succ', complexIpowEven2676]
  push_cast
  ring

theorem termReEven2676 (a : ℝ) (k : ℕ) :
    (((a : ℂ) * Complex.I) ^ (2 * k) / (((2 * k).factorial : ℕ) : ℂ)).re
      = (-1 : ℝ) ^ k * a ^ (2 * k) / ((2 * k).factorial : ℝ) := by
  have hcast : (((2 * k).factorial : ℕ) : ℂ)
      = ((((2 * k).factorial : ℕ) : ℝ) : ℂ) := by norm_cast
  rw [complexIpowEven2676, hcast, ← Complex.ofReal_div, Complex.ofReal_re]

theorem termImEven2676 (a : ℝ) (k : ℕ) :
    (((a : ℂ) * Complex.I) ^ (2 * k) / (((2 * k).factorial : ℕ) : ℂ)).im = 0 := by
  have hcast : (((2 * k).factorial : ℕ) : ℂ)
      = ((((2 * k).factorial : ℕ) : ℝ) : ℂ) := by norm_cast
  rw [complexIpowEven2676, hcast, ← Complex.ofReal_div, Complex.ofReal_im]

theorem termReOdd2676 (a : ℝ) (k : ℕ) :
    (((a : ℂ) * Complex.I) ^ (2 * k + 1) / (((2 * k + 1).factorial : ℕ) : ℂ)).re
      = 0 := by
  have hcast : (((2 * k + 1).factorial : ℕ) : ℂ)
      = ((((2 * k + 1).factorial : ℕ) : ℝ) : ℂ) := by norm_cast
  rw [complexIpowOdd2676, hcast, ← div_mul_eq_mul_div, ← Complex.ofReal_div,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im]
  norm_num

theorem termImOdd2676 (a : ℝ) (k : ℕ) :
    (((a : ℂ) * Complex.I) ^ (2 * k + 1) / (((2 * k + 1).factorial : ℕ) : ℂ)).im
      = (-1 : ℝ) ^ k * a ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ) := by
  have hcast : (((2 * k + 1).factorial : ℕ) : ℂ)
      = ((((2 * k + 1).factorial : ℕ) : ℝ) : ℂ) := by norm_cast
  rw [complexIpowOdd2676, hcast, ← div_mul_eq_mul_div, ← Complex.ofReal_div,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_im, Complex.I_re]
  ring

theorem reExpIPartial2676 (a : ℝ) :
    (expIPartial2676 a 26).re
      = ∑ k ∈ Finset.range 13, (-1 : ℝ) ^ k * a ^ (2 * k) / ((2 * k).factorial : ℝ) := by
  have hsplit : expIPartial2676 a 26 = ∑ k ∈ Finset.range 13,
      (((a : ℂ) * Complex.I) ^ (2 * k) / (((2 * k).factorial : ℕ) : ℂ)
        + ((a : ℂ) * Complex.I) ^ (2 * k + 1) / (((2 * k + 1).factorial : ℕ) : ℂ)) := by
    rw [expIPartial2676]
    have h26 : (26 : ℕ) = 2 * 13 := by norm_num
    rw [h26, sumRangePair2676]
  rw [hsplit, Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.add_re, termReEven2676, termReOdd2676, add_zero]

theorem imExpIPartial2676 (a : ℝ) :
    (expIPartial2676 a 26).im
      = ∑ k ∈ Finset.range 13, (-1 : ℝ) ^ k * a ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ) := by
  have hsplit : expIPartial2676 a 26 = ∑ k ∈ Finset.range 13,
      (((a : ℂ) * Complex.I) ^ (2 * k) / (((2 * k).factorial : ℕ) : ℂ)
        + ((a : ℂ) * Complex.I) ^ (2 * k + 1) / (((2 * k + 1).factorial : ℕ) : ℂ)) := by
    rw [expIPartial2676]
    have h26 : (26 : ℕ) = 2 * 13 := by norm_num
    rw [h26, sumRangePair2676]
  rw [hsplit, Complex.im_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.add_im, termImEven2676, termImOdd2676, zero_add]

/-- Real part of `exp (u * I)` via the ℂ-typed `Complex.exp_mul_I`. -/
theorem expMulIre2676 (u : ℝ) :
    (Complex.exp ((u : ℂ) * Complex.I)).re = Real.cos u := by
  rw [Complex.exp_mul_I, Complex.add_re, Complex.cos_ofReal_re, Complex.mul_re,
    Complex.sin_ofReal_re, Complex.sin_ofReal_im, Complex.I_re, Complex.I_im]
  norm_num

/-- Imaginary part of `exp (u * I)` via the ℂ-typed `Complex.exp_mul_I`. -/
theorem expMulIim2676 (u : ℝ) :
    (Complex.exp ((u : ℂ) * Complex.I)).im = Real.sin u := by
  rw [Complex.exp_mul_I, Complex.add_im, Complex.cos_ofReal_im, Complex.mul_im,
    Complex.sin_ofReal_re, Complex.sin_ofReal_im, Complex.I_im, Complex.I_re]
  norm_num

theorem cosPin2676 (a : ℝ) (h1 : |a| ≤ 1)
    {P E : ℝ} (hP : (expIPartial2676 a 26).re = P)
    (hE : |a| ^ 26 * ((26 : Nat).succ / ((26 : Nat).factorial * 26)) = E) :
    P - E ≤ Real.cos a ∧ Real.cos a ≤ P + E := by
  have hz : ‖((a : ℂ) * Complex.I)‖ ≤ 1 := by
    rw [Complex.norm_mul, Complex.norm_I, Complex.norm_real]
    simpa using h1
  have hb := Complex.exp_bound (x := ((a : ℂ) * Complex.I)) hz (n := 26)
    (by norm_num)
  have hnorm : ‖((a : ℂ) * Complex.I)‖ = |a| := by
    rw [Complex.norm_mul, Complex.norm_I, mul_one]
    exact Complex.norm_real a
  have hb2 : ‖Complex.exp ((a : ℂ) * Complex.I) - expIPartial2676 a 26‖
      ≤ |a| ^ 26 * ((26 : Nat).succ / ((26 : Nat).factorial * 26)) := by
    have hbc := hb
    rw [hnorm] at hbc
    exact hbc
  have hcos : Real.cos a = (Complex.exp ((a : ℂ) * Complex.I)).re :=
    (expMulIre2676 a).symm
  have h1' : |Real.cos a - (expIPartial2676 a 26).re|
      ≤ ‖Complex.exp ((a : ℂ) * Complex.I) - expIPartial2676 a 26‖ := by
    have hshift : (Complex.exp ((a : ℂ) * Complex.I) - expIPartial2676 a 26).re
        = Real.cos a - (expIPartial2676 a 26).re := by
      rw [Complex.sub_re, hcos]
    calc |Real.cos a - (expIPartial2676 a 26).re|
        = |(Complex.exp ((a : ℂ) * Complex.I) - expIPartial2676 a 26).re| := by
          rw [hshift]
      _ ≤ ‖Complex.exp ((a : ℂ) * Complex.I) - expIPartial2676 a 26‖ :=
          Complex.abs_re_le_norm _
  have h2 := h1'.trans hb2
  rw [hP, hE] at h2
  rcases abs_le.mp h2 with ⟨hl, hh⟩
  constructor <;> linarith

theorem sinPin2676 (a : ℝ) (h1 : |a| ≤ 1)
    {P E : ℝ} (hP : (expIPartial2676 a 26).im = P)
    (hE : |a| ^ 26 * ((26 : Nat).succ / ((26 : Nat).factorial * 26)) = E) :
    P - E ≤ Real.sin a ∧ Real.sin a ≤ P + E := by
  have hz : ‖((a : ℂ) * Complex.I)‖ ≤ 1 := by
    rw [Complex.norm_mul, Complex.norm_I, Complex.norm_real]
    simpa using h1
  have hb := Complex.exp_bound (x := ((a : ℂ) * Complex.I)) hz (n := 26)
    (by norm_num)
  have hnorm : ‖((a : ℂ) * Complex.I)‖ = |a| := by
    rw [Complex.norm_mul, Complex.norm_I, mul_one]
    exact Complex.norm_real a
  have hb2 : ‖Complex.exp ((a : ℂ) * Complex.I) - expIPartial2676 a 26‖
      ≤ |a| ^ 26 * ((26 : Nat).succ / ((26 : Nat).factorial * 26)) := by
    have hbc := hb
    rw [hnorm] at hbc
    exact hbc
  have hsin : Real.sin a = (Complex.exp ((a : ℂ) * Complex.I)).im :=
    (expMulIim2676 a).symm
  have h1' : |Real.sin a - (expIPartial2676 a 26).im|
      ≤ ‖Complex.exp ((a : ℂ) * Complex.I) - expIPartial2676 a 26‖ := by
    have hshift : (Complex.exp ((a : ℂ) * Complex.I) - expIPartial2676 a 26).im
        = Real.sin a - (expIPartial2676 a 26).im := by
      rw [Complex.sub_im, hsin]
    calc |Real.sin a - (expIPartial2676 a 26).im|
        = |(Complex.exp ((a : ℂ) * Complex.I) - expIPartial2676 a 26).im| := by
          rw [hshift]
      _ ≤ ‖Complex.exp ((a : ℂ) * Complex.I) - expIPartial2676 a 26‖ :=
          Complex.abs_im_le_norm _
  have h2 := h1'.trans hb2
  rw [hP, hE] at h2
  rcases abs_le.mp h2 with ⟨hl, hh⟩
  constructor <;> linarith

/-! ## Interval helpers and the generic family rectangles -/

theorem mulBoxLoPos2676 {b c : RealInterval2429} (hb : 0 < b.lo) (hbh : 0 < b.hi)
    (hc : 0 < c.lo) (hch : 0 < c.hi) : 0 < (b.mul c).lo := by
  have e1 : 0 < b.lo * c.lo := mul_pos hb hc
  have e2 : 0 < b.lo * c.hi := mul_pos hb hch
  have e3 : 0 < b.hi * c.lo := mul_pos hbh hc
  have e4 : 0 < b.hi * c.hi := mul_pos hbh hch
  have hshape : (b.mul c).lo
      = min (min (b.lo * c.lo) (b.lo * c.hi)) (min (b.hi * c.lo) (b.hi * c.hi)) :=
    rfl
  rw [hshape]
  exact lt_min (lt_min e1 e2) (lt_min e3 e4)

theorem memInvSq2676 {qBox : RealInterval2429} {q : ℝ} (hq : qBox.Mem q)
    (hqlo : 0 < qBox.lo) : (qBox.mul qBox).invPositive.Mem (q⁻¹ ^ 2) := by
  have hqhi : 0 < qBox.hi := by linarith [hq.1, hq.2]
  have hpos := mulBoxLoPos2676 hqlo hqhi hqlo hqhi
  have h1 : (qBox.mul qBox).Mem (q * q) := RealInterval2429.mem_mul hq hq
  have h2 := RealInterval2429.mem_invPositive hpos h1
  rw [mul_inv, ← pow_two] at h2
  exact h2

theorem memInvCube2676 {qBox : RealInterval2429} {q : ℝ} (hq : qBox.Mem q)
    (hqlo : 0 < qBox.lo) :
    ((qBox.mul qBox).mul qBox).invPositive.Mem (q⁻¹ ^ 3) := by
  have hqhi : 0 < qBox.hi := by linarith [hq.1, hq.2]
  have hqpos : 0 < q := lt_of_lt_of_le hqlo hq.1
  have hLpos : 0 < (qBox.mul qBox).lo := mulBoxLoPos2676 hqlo hqhi hqlo hqhi
  have hLhi : 0 < (qBox.mul qBox).hi := by
    have hmem := RealInterval2429.mem_mul hq hq
    exact lt_of_lt_of_le (mul_pos hqpos hqpos) hmem.2
  have hpos := mulBoxLoPos2676 hLpos hLhi hqlo hqhi
  have h1 : ((qBox.mul qBox).mul qBox).Mem (q * q * q) :=
    RealInterval2429.mem_mul (RealInterval2429.mem_mul hq hq) hq
  have h2 := RealInterval2429.mem_invPositive hpos h1
  rw [mul_inv, mul_inv, ← pow_two, ← pow_succ] at h2
  exact h2

theorem familyMidMem2676 {theta radius x : ℝ}
    {phiRect cosRect sinRect : RealInterval2429}
    (hphi : phiRect.Mem (widthBump radius x))
    (hcos : cosRect.Mem (Real.cos (theta * x)))
    (hsin : sinRect.Mem (Real.sin (theta * x))) :
    ({ reLo := (phiRect.mul cosRect).lo, reHi := (phiRect.mul cosRect).hi,
       imLo := (phiRect.mul sinRect).lo, imHi := (phiRect.mul sinRect).hi }
        : ComplexRect2427).Mem
      ((widthBump radius x : ℂ) * Complex.exp ((theta * x : ℝ) * Complex.I)) := by
  have hre : ((widthBump radius x : ℂ) * Complex.exp ((theta * x : ℝ) * Complex.I)).re
      = widthBump radius x * Real.cos (theta * x) := by
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, expMulIre2676,
      expMulIim2676]
    ring
  have him : ((widthBump radius x : ℂ) * Complex.exp ((theta * x : ℝ) * Complex.I)).im
      = widthBump radius x * Real.sin (theta * x) := by
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, expMulIim2676,
      expMulIre2676]
    ring
  have hr := RealInterval2429.mem_mul hphi hcos
  have hi := RealInterval2429.mem_mul hphi hsin
  rw [ComplexRect2427.Mem, hre, him]
  exact ⟨hr.1, hr.2, hi.1, hi.2⟩

theorem familyK0Mem2676 {c : ℂ} {theta radius x : ℝ}
    {midRect : ComplexRect2427}
    (hmid : midRect.Mem
      ((widthBump radius x : ℂ) * Complex.exp ((theta * x : ℝ) * Complex.I))) :
    (ComplexRect2427.mul (ComplexRect2427.point c) midRect).Mem
      (externalFamilyValue2344 c theta radius x) := by
  rw [externalFamilyValue2344_eq_familyTerm, mul_assoc]
  exact ComplexRect2427.mem_mul (ComplexRect2427.point_mem c) hmid

theorem familyK2Mem2676 {c : ℂ} {theta radius x : ℝ}
    {midRect factorRect : ComplexRect2427}
    (hxr : |x| < radius)
    (hmid : midRect.Mem
      ((widthBump radius x : ℂ) * Complex.exp ((theta * x : ℝ) * Complex.I)))
    (hfac : factorRect.Mem (familySecondFactor2345 theta radius x)) :
    (ComplexRect2427.mul (ComplexRect2427.mul (ComplexRect2427.point c) midRect)
      factorRect).Mem (familySecondValue2346 c theta radius x) := by
  have hcmid :
      (ComplexRect2427.mul (ComplexRect2427.point c) midRect).Mem
        (c * ((widthBump radius x : ℂ) *
          Complex.exp ((theta * x : ℝ) * Complex.I))) := by
    exact ComplexRect2427.mem_mul (z := c)
      (w := (widthBump radius x : ℂ) *
        Complex.exp ((theta * x : ℝ) * Complex.I))
      (a := ComplexRect2427.point c) (b := midRect)
      (ComplexRect2427.point_mem c) hmid
  have htotal :
      (ComplexRect2427.mul (ComplexRect2427.mul (ComplexRect2427.point c) midRect)
        factorRect).Mem
        ((c * ((widthBump radius x : ℂ) *
          Complex.exp ((theta * x : ℝ) * Complex.I))) *
          familySecondFactor2345 theta radius x) := by
    exact ComplexRect2427.mem_mul hcmid hfac
  have hvalue :
      (c * ((widthBump radius x : ℂ) *
        Complex.exp ((theta * x : ℝ) * Complex.I))) *
        familySecondFactor2345 theta radius x
      = c * (widthBump radius x : ℂ) *
        Complex.exp ((theta * x : ℝ) * Complex.I) *
        familySecondFactor2345 theta radius x := by
    ring
  rw [hvalue] at htotal
  rw [familySecondValue2346, if_pos hxr,
    externalFamilyValue2344_eq_familyTerm]
  exact htotal

theorem rectSubset2676 {inner outer : ComplexRect2427}
    (h1 : outer.reLo ≤ inner.reLo) (h2 : inner.reHi ≤ outer.reHi)
    (h3 : outer.imLo ≤ inner.imLo) (h4 : inner.imHi ≤ outer.imHi)
    {z : ℂ} (hz : inner.Mem z) : outer.Mem z :=
  ⟨h1.trans hz.1, hz.2.1.trans h2, h3.trans hz.2.2.1, hz.2.2.2.trans h4⟩

/-! ## Endpoint Taylor pins plus whole-interval chord control -/

def endpointHullOfBoxes2676 (left right : RealInterval2429) (radius : ℝ) :
    RealInterval2429 :=
  { lo := min left.lo right.lo - radius
    hi := max left.hi right.hi + radius }

theorem endpointHullOfBoxesSubset2676 {left right : RealInterval2429}
    {leftValue rightValue radius : ℝ}
    (hleft : left.Mem leftValue) (hright : right.Mem rightValue) :
    (endpointHullOfBoxes2676 left right radius).lo ≤
        (RealInterval2429.endpointHull leftValue rightValue radius).lo
      ∧ (RealInterval2429.endpointHull leftValue rightValue radius).hi ≤
        (endpointHullOfBoxes2676 left right radius).hi := by
  constructor
  · dsimp [RealInterval2429.endpointHull, endpointHullOfBoxes2676]
    exact sub_le_sub_right (min_le_min hleft.1 hright.1) radius
  · dsimp [RealInterval2429.endpointHull, endpointHullOfBoxes2676]
    nlinarith [max_le_max hleft.2 hright.2]

theorem memEndpointHullOfBoxes2676 {left right : RealInterval2429}
    {leftValue rightValue value radius : ℝ}
    (hleft : left.Mem leftValue) (hright : right.Mem rightValue)
    (hvalue : (RealInterval2429.endpointHull leftValue rightValue radius).Mem value) :
    (endpointHullOfBoxes2676 left right radius).Mem value := by
  have hsubset := endpointHullOfBoxesSubset2676 (left := left) (right := right)
    (leftValue := leftValue) (rightValue := rightValue) (radius := radius)
    hleft hright
  exact ⟨hsubset.1.trans hvalue.1, hvalue.2.trans hsubset.2⟩

theorem memSinEndpointHullOfBoxes2676 {left right : RealInterval2429}
    {a x b radius : ℝ}
    (hab : a < b) (hax : a ≤ x) (hxb : x ≤ b)
    (hleft : left.Mem (Real.sin a)) (hright : right.Mem (Real.sin b))
    (hradius : (b - a) ^ 2 / 8 ≤ radius) :
    (endpointHullOfBoxes2676 left right radius).Mem (Real.sin x) := by
  have hsin := RealInterval2429.mem_sinEndpointHull hab hax hxb
  have hradle : (RealInterval2429.endpointHull (Real.sin a) (Real.sin b)
      radius).lo ≤
      (RealInterval2429.endpointHull (Real.sin a) (Real.sin b)
        ((b - a) ^ 2 / 8)).lo := by
    dsimp [RealInterval2429.endpointHull]
    linarith
  have hradhi : (RealInterval2429.endpointHull (Real.sin a) (Real.sin b)
      ((b - a) ^ 2 / 8)).hi ≤
      (RealInterval2429.endpointHull (Real.sin a) (Real.sin b) radius).hi := by
    dsimp [RealInterval2429.endpointHull]
    linarith
  have hwide : (RealInterval2429.endpointHull (Real.sin a) (Real.sin b) radius).Mem
      (Real.sin x) := ⟨hradle.trans hsin.1, hsin.2.trans hradhi⟩
  exact memEndpointHullOfBoxes2676 hleft hright hwide

theorem memCosEndpointHullOfBoxes2676 {left right : RealInterval2429}
    {a x b radius : ℝ}
    (hab : a < b) (hax : a ≤ x) (hxb : x ≤ b)
    (hleft : left.Mem (Real.cos a)) (hright : right.Mem (Real.cos b))
    (hradius : (b - a) ^ 2 / 8 ≤ radius) :
    (endpointHullOfBoxes2676 left right radius).Mem (Real.cos x) := by
  have hcos := RealInterval2429.mem_cosEndpointHull hab hax hxb
  have hradle : (RealInterval2429.endpointHull (Real.cos a) (Real.cos b)
      radius).lo ≤
      (RealInterval2429.endpointHull (Real.cos a) (Real.cos b)
        ((b - a) ^ 2 / 8)).lo := by
    dsimp [RealInterval2429.endpointHull]
    linarith
  have hradhi : (RealInterval2429.endpointHull (Real.cos a) (Real.cos b)
      ((b - a) ^ 2 / 8)).hi ≤
      (RealInterval2429.endpointHull (Real.cos a) (Real.cos b) radius).hi := by
    dsimp [RealInterval2429.endpointHull]
    linarith
  have hwide : (RealInterval2429.endpointHull (Real.cos a) (Real.cos b) radius).Mem
      (Real.cos x) := ⟨hradle.trans hcos.1, hcos.2.trans hradhi⟩
  exact memEndpointHullOfBoxes2676 hleft hright hwide

theorem externalPhysicalFamilySumMem2676
    {coefficients : Fin 30 → ℂ} {modulations : Fin 30 → ℝ}
    {rect : Fin 30 → ComplexRect2427} {position : ℝ}
    (hfamily : ∀ index, (rect index).Mem
      (externalFamilyValue2344 (coefficients index) (modulations index)
        (storedWidth index ^ 2) position)) :
    (ComplexRect2427.sumFinset rect Finset.univ).Mem
      (externalPhysical2344 coefficients modulations position) := by
  have hsum := ComplexRect2427.mem_sumFinset (s := Finset.univ)
    (term := fun index => externalFamilyValue2344 (coefficients index)
      (modulations index) (storedWidth index ^ 2) position)
    (rect := rect) (fun index _ => hfamily index)
  simpa [externalPhysical2344, ComplexRect2427.sumFinset] using hsum

theorem correctedPhysicalSecondDerivativeFamilySumMem2676
    {coefficients : Fin 30 → ℂ} {modulations : Fin 30 → ℝ}
    {rect : Fin 30 → ComplexRect2427} {position : ℝ}
    (hfamily : ∀ index, (rect index).Mem
      (familySecondValue2346 (coefficients index) (modulations index)
        (storedWidth index ^ 2) position)) :
    (ComplexRect2427.sumFinset rect Finset.univ).Mem
      (deriv (deriv (correctedPhysical coefficients modulations)) position) := by
  rw [correctedPhysical_secondDerivative_global2346]
  have hsum := ComplexRect2427.mem_sumFinset (s := Finset.univ)
    (term := fun index => familySecondValue2346 (coefficients index)
      (modulations index) (storedWidth index ^ 2) position)
    (rect := rect) (fun index _ => hfamily index)
  simpa [ComplexRect2427.sumFinset] using hsum

end ConnesWeilRH.Dev
