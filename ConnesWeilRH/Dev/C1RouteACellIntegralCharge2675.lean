import ConnesWeilRH.Dev.C1RouteABinary64Bridge2674
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace ConnesWeilRH.Dev

open Set
open scoped Interval

/-- A rational corner-square bound turns the rectangle norm into a scalar
upper bound suitable for pricing a continuous cell. -/
theorem ComplexRect2427.cornerNorm_le_of_sq_le
    {r : ComplexRect2427} {bound : ℝ}
    (hbound : 0 ≤ bound)
    (hsq : r.cornerNormSq ≤ bound ^ 2) :
    r.cornerNorm ≤ bound := by
  rw [ComplexRect2427.cornerNorm]
  exact Real.sqrt_le_iff.mpr ⟨hbound, hsq⟩

/-- If the interval evaluator rectangle contains the actual channel throughout
one cell, and the exponential weight and rectangle norm have certified upper
bounds, then the weighted integral over that cell is bounded by its length
times those bounds.  The rectangle-containment and weight hypotheses are the
proof-carrying inputs supplied by a concrete cell certificate. -/
theorem weightedNormIntegral_le_of_cellRectangle
    {f : ℝ → ℂ} {a b sigma weightBound normBound : ℝ}
    {rect : ComplexRect2427}
    (hab : a ≤ b)
    (hrect : ∀ x ∈ Icc a b, rect.Mem (f x))
    (hnorm : rect.cornerNorm ≤ normBound)
    (hweight_nonneg : 0 ≤ weightBound)
    (hweight : ∀ x ∈ Icc a b, Real.exp (sigma * x) ≤ weightBound)
    (_hintegrable : IntervalIntegrable
      (fun x => Real.exp (sigma * x) * ‖f x‖)
      MeasureTheory.volume a b) :
    (∫ x in a..b, Real.exp (sigma * x) * ‖f x‖) ≤
      (b - a) * (weightBound * normBound) := by
  have hpointwise : ∀ x ∈ Icc a b,
      Real.exp (sigma * x) * ‖f x‖ ≤ weightBound * normBound := by
    intro x hx
    have hxnorm : ‖f x‖ ≤ normBound :=
      (ComplexRect2427.norm_le_cornerNorm (hrect x hx)).trans hnorm
    calc
      Real.exp (sigma * x) * ‖f x‖ ≤ weightBound * ‖f x‖ :=
        mul_le_mul_of_nonneg_right (hweight x hx) (norm_nonneg _)
      _ ≤ weightBound * normBound :=
        mul_le_mul_of_nonneg_left hxnorm hweight_nonneg
  have hmono := intervalIntegral.integral_mono_on hab _hintegrable
    (intervalIntegrable_const (μ := MeasureTheory.volume)
      (c := weightBound * normBound)) hpointwise
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
  exact hmono

def record2675CellRight : ℝ :=
  (binary64Value2674 0x3f5a36e2eb1c4000 : ℚ)

def record2675BaseM0Rect : ComplexRect2427 :=
  { reLo := (binary64Value2674 0x402a7892ea7184b3 : ℚ)
    reHi := (binary64Value2674 0x402c9fa00332e418 : ℚ)
    imLo := (binary64Value2674 0xc00478f8600253f8 : ℚ)
    imHi := (binary64Value2674 0x3ffc678667bdfba1 : ℚ) }

def record2675BaseD2Rect : ComplexRect2427 :=
  { reLo := (binary64Value2674 0xc0dfb7250c5f5a85 : ℚ)
    reHi := (binary64Value2674 0xc0dd553f40944585 : ℚ)
    imLo := (binary64Value2674 0xc0a8266a7ee9025d : ℚ)
    imHi := (binary64Value2674 0x40b931d457be20ae : ℚ) }

def record2675CorrectionM0Rect : ComplexRect2427 :=
  { reLo := (binary64Value2674 0xc0aa32a0069d0708 : ℚ)
    reHi := (binary64Value2674 0x40aa1f3341a8db3a : ℚ)
    imLo := (binary64Value2674 0xc090b2b5df7ba75f : ℚ)
    imHi := (binary64Value2674 0x4091cd591365d2b6 : ℚ) }

def record2675CorrectionD2Rect : ComplexRect2427 :=
  { reLo := (binary64Value2674 0xc153fb4a6ea05f01 : ℚ)
    reHi := (binary64Value2674 0x4153f8bf303b9597 : ℚ)
    imLo := (binary64Value2674 0xc13b4bd15674425a : ℚ)
    imHi := (binary64Value2674 0x4139901a0e1d2cde : ℚ) }

def record2675BaseM0Norm : ℝ :=
  (binary64Value2674 0x402d13d84068257d : ℚ)

def record2675BaseD2Norm : ℝ :=
  (binary64Value2674 0x40e02adb3e1ac432 : ℚ)

def record2675CorrectionM0Norm : ℝ :=
  (binary64Value2674 0x40abab29511e341a : ℚ)

def record2675CorrectionD2Norm : ℝ :=
  (binary64Value2674 0x41551d5f4c4d0816 : ℚ)

theorem record2675BaseM0CornerNorm :
    record2675BaseM0Rect.cornerNorm ≤ record2675BaseM0Norm := by
  apply ComplexRect2427.cornerNorm_le_of_sq_le
  · norm_num [record2675BaseM0Norm, binary64Value2674,
      binary64ExponentBits2674, binary64Significand2674,
      binary64FractionBits2674, binary64Sign2674]
  · norm_num [record2675BaseM0Rect, record2675BaseM0Norm,
      ComplexRect2427.cornerNormSq, binary64Value2674,
      binary64ExponentBits2674, binary64Significand2674,
      binary64FractionBits2674, binary64Sign2674]

theorem record2675BaseD2CornerNorm :
    record2675BaseD2Rect.cornerNorm ≤ record2675BaseD2Norm := by
  apply ComplexRect2427.cornerNorm_le_of_sq_le
  · norm_num [record2675BaseD2Norm, binary64Value2674,
      binary64ExponentBits2674, binary64Significand2674,
      binary64FractionBits2674, binary64Sign2674]
  · norm_num [record2675BaseD2Rect, record2675BaseD2Norm,
      ComplexRect2427.cornerNormSq, binary64Value2674,
      binary64ExponentBits2674, binary64Significand2674,
      binary64FractionBits2674, binary64Sign2674]

theorem record2675CorrectionM0CornerNorm :
    record2675CorrectionM0Rect.cornerNorm ≤ record2675CorrectionM0Norm := by
  apply ComplexRect2427.cornerNorm_le_of_sq_le
  · norm_num [record2675CorrectionM0Norm, binary64Value2674,
      binary64ExponentBits2674, binary64Significand2674,
      binary64FractionBits2674, binary64Sign2674]
  · norm_num [record2675CorrectionM0Rect, record2675CorrectionM0Norm,
      ComplexRect2427.cornerNormSq, binary64Value2674,
      binary64ExponentBits2674, binary64Significand2674,
      binary64FractionBits2674, binary64Sign2674]

theorem record2675CorrectionD2CornerNorm :
    record2675CorrectionD2Rect.cornerNorm ≤ record2675CorrectionD2Norm := by
  apply ComplexRect2427.cornerNorm_le_of_sq_le
  · norm_num [record2675CorrectionD2Norm, binary64Value2674,
      binary64ExponentBits2674, binary64Significand2674,
      binary64FractionBits2674, binary64Sign2674]
  · norm_num [record2675CorrectionD2Rect, record2675CorrectionD2Norm,
      ComplexRect2427.cornerNormSq, binary64Value2674,
      binary64ExponentBits2674, binary64Significand2674,
      binary64FractionBits2674, binary64Sign2674]

theorem record2675CellWeightLeOne {x : ℝ}
    (hx : x ∈ Icc 0 record2675CellRight) :
    Real.exp ((-1 / 2 : ℝ) * x) ≤ 1 := by
  calc
    Real.exp ((-1 / 2 : ℝ) * x) ≤ Real.exp 0 :=
      Real.exp_le_exp.mpr (by nlinarith [hx.1])
    _ = 1 := Real.exp_zero

theorem record2675BaseM0Charge
    {f : ℝ → ℂ}
    (hrect : ∀ x ∈ Icc 0 record2675CellRight,
      record2675BaseM0Rect.Mem (f x))
    (hintegrable : IntervalIntegrable
      (fun x => Real.exp ((-1 / 2 : ℝ) * x) * ‖f x‖)
      MeasureTheory.volume 0 record2675CellRight) :
    (∫ x in (0 : ℝ)..record2675CellRight,
      Real.exp ((-1 / 2 : ℝ) * x) * ‖f x‖) ≤
        (binary64Value2674 0x3f97d1ff630bfcb3 : ℚ) := by
  have hcell := weightedNormIntegral_le_of_cellRectangle
    (a := (0 : ℝ)) (b := record2675CellRight)
    (sigma := (-1 / 2 : ℝ)) (weightBound := 1)
    (normBound := record2675BaseM0Norm)
    (rect := record2675BaseM0Rect)
    (by norm_num [record2675CellRight, binary64Value2674,
      binary64ExponentBits2674, binary64Significand2674,
      binary64FractionBits2674, binary64Sign2674])
    hrect record2675BaseM0CornerNorm (by norm_num)
    (fun x hx => record2675CellWeightLeOne hx) hintegrable
  have hprice : record2675CellRight * (1 * record2675BaseM0Norm) ≤
      (binary64Value2674 0x3f97d1ff630bfcb3 : ℚ) := by
    norm_num [record2675CellRight, record2675BaseM0Norm,
      binary64Value2674, binary64ExponentBits2674,
      binary64Significand2674, binary64FractionBits2674,
      binary64Sign2674]
  exact hcell.trans (by simpa only [sub_zero] using hprice)

theorem record2675BaseD2Charge
    {f : ℝ → ℂ}
    (hrect : ∀ x ∈ Icc 0 record2675CellRight,
      record2675BaseD2Rect.Mem (f x))
    (hintegrable : IntervalIntegrable
      (fun x => Real.exp ((-1 / 2 : ℝ) * x) * ‖f x‖)
      MeasureTheory.volume 0 record2675CellRight) :
    (∫ x in (0 : ℝ)..record2675CellRight,
      Real.exp ((-1 / 2 : ℝ) * x) * ‖f x‖) ≤
        (binary64Value2674 0x404a7d1a33c7e62d : ℚ) := by
  have hcell := weightedNormIntegral_le_of_cellRectangle
    (a := (0 : ℝ)) (b := record2675CellRight)
    (sigma := (-1 / 2 : ℝ)) (weightBound := 1)
    (normBound := record2675BaseD2Norm)
    (rect := record2675BaseD2Rect)
    (by norm_num [record2675CellRight, binary64Value2674,
      binary64ExponentBits2674, binary64Significand2674,
      binary64FractionBits2674, binary64Sign2674])
    hrect record2675BaseD2CornerNorm (by norm_num)
    (fun x hx => record2675CellWeightLeOne hx) hintegrable
  have hprice : record2675CellRight * (1 * record2675BaseD2Norm) ≤
      (binary64Value2674 0x404a7d1a33c7e62d : ℚ) := by
    norm_num [record2675CellRight, record2675BaseD2Norm,
      binary64Value2674, binary64ExponentBits2674,
      binary64Significand2674, binary64FractionBits2674,
      binary64Sign2674]
  exact hcell.trans (by simpa only [sub_zero] using hprice)

theorem record2675CorrectionM0Charge
    {f : ℝ → ℂ}
    (hrect : ∀ x ∈ Icc 0 record2675CellRight,
      record2675CorrectionM0Rect.Mem (f x))
    (hintegrable : IntervalIntegrable
      (fun x => Real.exp ((-1 / 2 : ℝ) * x) * ‖f x‖)
      MeasureTheory.volume 0 record2675CellRight) :
    (∫ x in (0 : ℝ)..record2675CellRight,
      Real.exp ((-1 / 2 : ℝ) * x) * ‖f x‖) ≤
        (binary64Value2674 0x4016aa869bbe9eb9 : ℚ) := by
  have hcell := weightedNormIntegral_le_of_cellRectangle
    (a := (0 : ℝ)) (b := record2675CellRight)
    (sigma := (-1 / 2 : ℝ)) (weightBound := 1)
    (normBound := record2675CorrectionM0Norm)
    (rect := record2675CorrectionM0Rect)
    (by norm_num [record2675CellRight, binary64Value2674,
      binary64ExponentBits2674, binary64Significand2674,
      binary64FractionBits2674, binary64Sign2674])
    hrect record2675CorrectionM0CornerNorm (by norm_num)
    (fun x hx => record2675CellWeightLeOne hx) hintegrable
  have hprice : record2675CellRight * (1 * record2675CorrectionM0Norm) ≤
      (binary64Value2674 0x4016aa869bbe9eb9 : ℚ) := by
    norm_num [record2675CellRight, record2675CorrectionM0Norm,
      binary64Value2674, binary64ExponentBits2674,
      binary64Significand2674, binary64FractionBits2674,
      binary64Sign2674]
  exact hcell.trans (by simpa only [sub_zero] using hprice)

theorem record2675CorrectionD2Charge
    {f : ℝ → ℂ}
    (hrect : ∀ x ∈ Icc 0 record2675CellRight,
      record2675CorrectionD2Rect.Mem (f x))
    (hintegrable : IntervalIntegrable
      (fun x => Real.exp ((-1 / 2 : ℝ) * x) * ‖f x‖)
      MeasureTheory.volume 0 record2675CellRight) :
    (∫ x in (0 : ℝ)..record2675CellRight,
      Real.exp ((-1 / 2 : ℝ) * x) * ‖f x‖) ≤
        (binary64Value2674 0x40c14c14b962bb37 : ℚ) := by
  have hcell := weightedNormIntegral_le_of_cellRectangle
    (a := (0 : ℝ)) (b := record2675CellRight)
    (sigma := (-1 / 2 : ℝ)) (weightBound := 1)
    (normBound := record2675CorrectionD2Norm)
    (rect := record2675CorrectionD2Rect)
    (by norm_num [record2675CellRight, binary64Value2674,
      binary64ExponentBits2674, binary64Significand2674,
      binary64FractionBits2674, binary64Sign2674])
    hrect record2675CorrectionD2CornerNorm (by norm_num)
    (fun x hx => record2675CellWeightLeOne hx) hintegrable
  have hprice : record2675CellRight * (1 * record2675CorrectionD2Norm) ≤
      (binary64Value2674 0x40c14c14b962bb37 : ℚ) := by
    norm_num [record2675CellRight, record2675CorrectionD2Norm,
      binary64Value2674, binary64ExponentBits2674,
      binary64Significand2674, binary64FractionBits2674,
      binary64Sign2674]
  exact hcell.trans (by simpa only [sub_zero] using hprice)

theorem record2675FourChannelCellChargeLeTotal :
    (binary64Value2674 0x3f97d1ff630bfcb3 : ℚ) +
      binary64Value2674 0x404a7d1a33c7e62d +
      binary64Value2674 0x4016aa869bbe9eb9 +
      binary64Value2674 0x40c14c14b962bb37 ≤
        binary64Value2674 0x40c1696a1ea9e753 := by
  norm_num [binary64Value2674, binary64ExponentBits2674,
    binary64Significand2674, binary64FractionBits2674,
    binary64Sign2674]

theorem record2675FourChannelIntegralCharge
    {fBaseM0 fBaseD2 fCorrectionM0 fCorrectionD2 : ℝ → ℂ}
    (hBaseM0Rect : ∀ x ∈ Icc 0 record2675CellRight,
      record2675BaseM0Rect.Mem (fBaseM0 x))
    (hBaseD2Rect : ∀ x ∈ Icc 0 record2675CellRight,
      record2675BaseD2Rect.Mem (fBaseD2 x))
    (hCorrectionM0Rect : ∀ x ∈ Icc 0 record2675CellRight,
      record2675CorrectionM0Rect.Mem (fCorrectionM0 x))
    (hCorrectionD2Rect : ∀ x ∈ Icc 0 record2675CellRight,
      record2675CorrectionD2Rect.Mem (fCorrectionD2 x))
    (hBaseM0Integrable : IntervalIntegrable
      (fun x => Real.exp ((-1 / 2 : ℝ) * x) * ‖fBaseM0 x‖)
      MeasureTheory.volume 0 record2675CellRight)
    (hBaseD2Integrable : IntervalIntegrable
      (fun x => Real.exp ((-1 / 2 : ℝ) * x) * ‖fBaseD2 x‖)
      MeasureTheory.volume 0 record2675CellRight)
    (hCorrectionM0Integrable : IntervalIntegrable
      (fun x => Real.exp ((-1 / 2 : ℝ) * x) * ‖fCorrectionM0 x‖)
      MeasureTheory.volume 0 record2675CellRight)
    (hCorrectionD2Integrable : IntervalIntegrable
      (fun x => Real.exp ((-1 / 2 : ℝ) * x) * ‖fCorrectionD2 x‖)
      MeasureTheory.volume 0 record2675CellRight) :
    (∫ x in (0 : ℝ)..record2675CellRight,
        Real.exp ((-1 / 2 : ℝ) * x) * ‖fBaseM0 x‖) +
      (∫ x in (0 : ℝ)..record2675CellRight,
        Real.exp ((-1 / 2 : ℝ) * x) * ‖fBaseD2 x‖) +
      (∫ x in (0 : ℝ)..record2675CellRight,
        Real.exp ((-1 / 2 : ℝ) * x) * ‖fCorrectionM0 x‖) +
      (∫ x in (0 : ℝ)..record2675CellRight,
        Real.exp ((-1 / 2 : ℝ) * x) * ‖fCorrectionD2 x‖) ≤
      (binary64Value2674 0x40c1696a1ea9e753 : ℚ) := by
  have h0 := record2675BaseM0Charge hBaseM0Rect hBaseM0Integrable
  have h1 := record2675BaseD2Charge hBaseD2Rect hBaseD2Integrable
  have h2 := record2675CorrectionM0Charge
    hCorrectionM0Rect hCorrectionM0Integrable
  have h3 := record2675CorrectionD2Charge
    hCorrectionD2Rect hCorrectionD2Integrable
  have hcharges :
      (∫ x in (0 : ℝ)..record2675CellRight,
          Real.exp ((-1 / 2 : ℝ) * x) * ‖fBaseM0 x‖) +
        (∫ x in (0 : ℝ)..record2675CellRight,
          Real.exp ((-1 / 2 : ℝ) * x) * ‖fBaseD2 x‖) +
        (∫ x in (0 : ℝ)..record2675CellRight,
          Real.exp ((-1 / 2 : ℝ) * x) * ‖fCorrectionM0 x‖) +
        (∫ x in (0 : ℝ)..record2675CellRight,
          Real.exp ((-1 / 2 : ℝ) * x) * ‖fCorrectionD2 x‖) ≤
        (binary64Value2674 0x3f97d1ff630bfcb3 : ℚ) +
          binary64Value2674 0x404a7d1a33c7e62d +
          binary64Value2674 0x4016aa869bbe9eb9 +
          binary64Value2674 0x40c14c14b962bb37 := by
    linarith
  exact hcharges.trans (by exact_mod_cast record2675FourChannelCellChargeLeTotal)

theorem record2675CellTotalBelowKnownError :
    (binary64Value2674 0x40c1696a1ea9e753 : ℚ) ≤ 74601530.30234718 := by
  norm_num [binary64Value2674, binary64ExponentBits2674,
    binary64Significand2674, binary64FractionBits2674,
    binary64Sign2674]

end ConnesWeilRH.Dev
