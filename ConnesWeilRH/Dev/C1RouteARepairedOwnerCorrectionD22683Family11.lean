import ConnesWeilRH.Dev.C1RouteARepairedOwnerCorrectionM02680
import ConnesWeilRH.Dev.C1RouteACellContainment2676Aggregates
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

/- Record 2683: one repaired-owner base-D2 family bridge.  The factor box is
   derived from the analytic log-derivative formulas; it is not a stored
   numerical premise. -/

theorem record2683FirstAbsBound
    (radius position t : ℝ) (hradius : 0 < radius) (hinside : |position| < radius)
    (ht : 0 ≤ t) (htone : t < 1) (hcoord : |position / radius| ≤ t) :
    |familyLogFirst2345 radius position| ≤
      60 * t * (1 - t ^ 2)⁻¹ ^ 2 / radius := by
  have hbase : 0 < 1 - t ^ 2 := by
    nlinarith [sq_nonneg t]
  have hdef : 0 < familyDeficit2345 radius position :=
    familyDeficit2345_pos hradius hinside
  have hlower : 1 - t ^ 2 ≤ familyDeficit2345 radius position := by
    dsimp [familyDeficit2345]
    have hsq : (position / radius) ^ 2 ≤ t ^ 2 := by
      have h := (sq_le_sq₀ (abs_nonneg (position / radius)) ht).2 hcoord
      simpa [sq_abs] using h
    linarith
  have hinv : (familyDeficit2345 radius position)⁻¹ ≤ (1 - t ^ 2)⁻¹ :=
    (inv_le_inv₀ hdef hbase).2 hlower
  have hinvpow : (familyDeficit2345 radius position)⁻¹ ^ 2 ≤
      (1 - t ^ 2)⁻¹ ^ 2 :=
    pow_le_pow_left₀ (by positivity) hinv 2
  calc
    |familyLogFirst2345 radius position| =
        60 * |position / radius| * (familyDeficit2345 radius position)⁻¹ ^ 2 /
          radius := by
      simp only [familyLogFirst2345, abs_div, abs_mul, abs_neg, abs_of_pos hradius]
      rw [abs_of_nonneg (sq_nonneg (familyDeficit2345 radius position)⁻¹)]
      ring
    _ ≤ 60 * t * (familyDeficit2345 radius position)⁻¹ ^ 2 / radius := by
      gcongr
    _ ≤ 60 * t * (1 - t ^ 2)⁻¹ ^ 2 / radius := by
      gcongr

theorem record2683SecondAbsBound
    (radius position t : ℝ) (hradius : 0 < radius) (hinside : |position| < radius)
    (ht : 0 ≤ t) (htone : t < 1) (hcoord : |position / radius| ≤ t) :
    |familyLogSecond2345 radius position| ≤
      60 * ((1 - t ^ 2)⁻¹ ^ 2 + 4 * t ^ 2 * (1 - t ^ 2)⁻¹ ^ 3) / radius ^ 2 := by
  have hbase : 0 < 1 - t ^ 2 := by
    nlinarith [sq_nonneg t]
  have hdef : 0 < familyDeficit2345 radius position :=
    familyDeficit2345_pos hradius hinside
  have hlower : 1 - t ^ 2 ≤ familyDeficit2345 radius position := by
    dsimp [familyDeficit2345]
    have hsq : (position / radius) ^ 2 ≤ t ^ 2 := by
      have h := (sq_le_sq₀ (abs_nonneg (position / radius)) ht).2 hcoord
      simpa [sq_abs] using h
    linarith
  have hinv : (familyDeficit2345 radius position)⁻¹ ≤ (1 - t ^ 2)⁻¹ :=
    (inv_le_inv₀ hdef hbase).2 hlower
  have hinv2 : (familyDeficit2345 radius position)⁻¹ ^ 2 ≤
      (1 - t ^ 2)⁻¹ ^ 2 :=
    pow_le_pow_left₀ (by positivity) hinv 2
  have hinv3 : (familyDeficit2345 radius position)⁻¹ ^ 3 ≤
      (1 - t ^ 2)⁻¹ ^ 3 :=
    pow_le_pow_left₀ (by positivity) hinv 3
  have hsq : (position / radius) ^ 2 ≤ t ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg (position / radius)) ht).2 hcoord
    simpa [sq_abs] using h
  calc
    |familyLogSecond2345 radius position| =
        60 * ((familyDeficit2345 radius position)⁻¹ ^ 2 +
          4 * (position / radius) ^ 2 *
            (familyDeficit2345 radius position)⁻¹ ^ 3) / radius ^ 2 := by
      rw [familyLogSecond2345, abs_div, abs_mul]
      have hsum : 0 ≤ (familyDeficit2345 radius position)⁻¹ ^ 2 +
          4 * (position / radius) ^ 2 *
            (familyDeficit2345 radius position)⁻¹ ^ 3 := by positivity
      rw [show |(-60 : ℝ)| = 60 by norm_num, abs_of_nonneg hsum,
        abs_of_pos (sq_pos_of_pos hradius)]
    _ ≤ 60 * ((familyDeficit2345 radius position)⁻¹ ^ 2 +
          4 * t ^ 2 * (familyDeficit2345 radius position)⁻¹ ^ 3) /
          radius ^ 2 := by
      gcongr
    _ ≤ 60 * ((1 - t ^ 2)⁻¹ ^ 2 +
          4 * t ^ 2 * (1 - t ^ 2)⁻¹ ^ 3) / radius ^ 2 := by
      gcongr

noncomputable def record2683Family11D2FactorRect : ComplexRect2427 :=
  {
    reLo := ((-1128132968706872692043774927357608739134985076683911 : ℚ) / (2 : ℚ) ^ 160 : ℝ)
    reHi := ((-1128132807778150597901202813278697000388862648815790 : ℚ) / (2 : ℚ) ^ 160 : ℝ)
    imLo := ((0 : ℚ) / (2 : ℚ) ^ 160 : ℝ)
    imHi := ((809215713506971506310760222475451254440192836193 : ℚ) / (2 : ℚ) ^ 160 : ℝ)
  }

set_option maxRecDepth 10000 in
theorem record2683Family11D2FactorMem {x : ℝ}
    (hx : x ∈ Set.Icc 0 record2675CellRight) :
    record2683Family11D2FactorRect.Mem
      (familySecondFactor2345 (capturedModulations2584 11)
        (storedWidth 11 ^ 2) x) := by
  let radius : ℝ := storedWidth 11 ^ 2
  let theta : ℝ := capturedModulations2584 11
  let t : ℝ := record2675CellRight / radius
  let firstBound : ℝ :=
    60 * t * (1 - t ^ 2)⁻¹ ^ 2 / radius
  let secondBound : ℝ :=
    60 * ((1 - t ^ 2)⁻¹ ^ 2 + 4 * t ^ 2 * (1 - t ^ 2)⁻¹ ^ 3) /
      radius ^ 2
  have hradius : 0 < radius := by
    norm_num [Matrix.cons_val_11, Matrix.cons_val_zero, radius, storedWidth, binary64Value2674,
      binary64ExponentBits2674, binary64Significand2674,
      binary64FractionBits2674, binary64Sign2674]
  have hright : 0 < record2675CellRight := by
    norm_num [Matrix.cons_val_11, Matrix.cons_val_zero, record2675CellRight, binary64Value2674,
      binary64ExponentBits2674, binary64Significand2674,
      binary64FractionBits2674, binary64Sign2674]
  have hXr : record2675CellRight < radius := by
    norm_num [Matrix.cons_val_11, Matrix.cons_val_zero, radius, record2675CellRight, storedWidth,
      binary64Value2674, binary64ExponentBits2674,
      binary64Significand2674, binary64FractionBits2674,
      binary64Sign2674]
  have hinside : |x| < radius := by
    rw [abs_of_nonneg hx.1]
    exact lt_of_le_of_lt hx.2 hXr
  have ht0 : 0 ≤ t := by
    dsimp [t]
    positivity
  have htone : t < 1 := by
    dsimp [t]
    exact (div_lt_one hradius).2 hXr
  have hcoord : |x / radius| ≤ t := by
    rw [abs_div, abs_of_pos hradius, abs_of_nonneg hx.1]
    dsimp [t]
    exact div_le_div_of_nonneg_right hx.2 hradius.le
  have hfirstAbs := record2683FirstAbsBound
    radius x t hradius hinside ht0 htone hcoord
  have hsecondAbs := record2683SecondAbsBound
    radius x t hradius hinside ht0 htone hcoord
  have hfirstNonpos : familyLogFirst2345 radius x ≤ 0 := by
    have hxratio : 0 ≤ x / radius := div_nonneg hx.1 hradius.le
    have hnonneg : 0 ≤ 60 * (x / radius) *
        (familyDeficit2345 radius x)⁻¹ ^ 2 / radius := by positivity
    have hlog : familyLogFirst2345 radius x =
        -(60 * (x / radius) * (familyDeficit2345 radius x)⁻¹ ^ 2 / radius) := by
      rw [familyLogFirst2345]
      ring
    rw [hlog]
    exact neg_nonpos.mpr hnonneg
  have hfirstLower : -firstBound ≤ familyLogFirst2345 radius x := by
    exact (neg_le_neg hfirstAbs).trans (neg_abs_le _)
  have hqpos : 0 < familyDeficit2345 radius x :=
    familyDeficit2345_pos hradius hinside
  have hqle : familyDeficit2345 radius x ≤ 1 := by
    dsimp [familyDeficit2345]
    nlinarith [sq_nonneg (x / radius)]
  have hqinv : 1 ≤ (familyDeficit2345 radius x)⁻¹ :=
    (one_le_inv₀ hqpos).2 hqle
  have hqinv2 : 1 ≤ (familyDeficit2345 radius x)⁻¹ ^ 2 := by
    nlinarith [sq_nonneg ((familyDeficit2345 radius x)⁻¹ - 1)]
  have hsecondUpper : familyLogSecond2345 radius x ≤ -60 / radius ^ 2 := by
    have hterm : 0 ≤ 4 * (x / radius) ^ 2 *
        (familyDeficit2345 radius x)⁻¹ ^ 3 := by positivity
    have hbracket : 1 ≤ (familyDeficit2345 radius x)⁻¹ ^ 2 +
        4 * (x / radius) ^ 2 * (familyDeficit2345 radius x)⁻¹ ^ 3 :=
      by linarith
    have hscaled : 60 / radius ^ 2 ≤
        60 * ((familyDeficit2345 radius x)⁻¹ ^ 2 +
          4 * (x / radius) ^ 2 * (familyDeficit2345 radius x)⁻¹ ^ 3) /
          radius ^ 2 := by
      have hnum : 60 ≤ 60 * ((familyDeficit2345 radius x)⁻¹ ^ 2 +
          4 * (x / radius) ^ 2 * (familyDeficit2345 radius x)⁻¹ ^ 3) := by
        nlinarith [hbracket]
      exact div_le_div_of_nonneg_right hnum (sq_nonneg radius)
    rw [familyLogSecond2345]
    calc
      -60 * ((familyDeficit2345 radius x)⁻¹ ^ 2 +
          4 * (x / radius) ^ 2 * (familyDeficit2345 radius x)⁻¹ ^ 3) / radius ^ 2
          = -(60 * ((familyDeficit2345 radius x)⁻¹ ^ 2 +
            4 * (x / radius) ^ 2 * (familyDeficit2345 radius x)⁻¹ ^ 3) /
            radius ^ 2) := by ring
      _ ≤ -(60 / radius ^ 2) := neg_le_neg hscaled
      _ = -60 / radius ^ 2 := by ring
  have hsecondLower : -secondBound ≤ familyLogSecond2345 radius x := by
    exact (neg_le_neg hsecondAbs).trans (neg_abs_le _)
  have htheta : theta < 0 := by
    norm_num [Matrix.cons_val_11, Matrix.cons_val_zero, theta, capturedModulations2584]
  have hrealLower :
      -secondBound - theta ^ 2 ≤
        familyLogSecond2345 radius x +
          (familyLogFirst2345 radius x) ^ 2 - theta ^ 2 := by
    have hsq : 0 ≤ (familyLogFirst2345 radius x) ^ 2 := sq_nonneg _
    linarith [hsecondLower]
  have hrealUpper :
      familyLogSecond2345 radius x +
          (familyLogFirst2345 radius x) ^ 2 - theta ^ 2 ≤
        -60 / radius ^ 2 + firstBound ^ 2 - theta ^ 2 := by
    have hfirstSq : (familyLogFirst2345 radius x) ^ 2 ≤ firstBound ^ 2 := by
      have hsquare := (sq_le_sq₀ (abs_nonneg (familyLogFirst2345 radius x))
        (by positivity : 0 ≤ firstBound)).2 hfirstAbs
      simpa [sq_abs] using hsquare
    linarith [hsecondUpper, hfirstSq]
  have himLower : 0 ≤ 2 * theta * familyLogFirst2345 radius x := by
    have hprod : 0 ≤ theta * familyLogFirst2345 radius x :=
      mul_nonneg_of_nonpos_of_nonpos htheta.le hfirstNonpos
    nlinarith
  have himUpper : 2 * theta * familyLogFirst2345 radius x ≤
      -2 * theta * firstBound := by
    nlinarith [mul_le_mul_of_nonpos_left hfirstLower (by linarith : 2 * theta ≤ 0)]
  have hrectLo : record2683Family11D2FactorRect.reLo ≤
      -secondBound - theta ^ 2 := by
    norm_num [Matrix.cons_val_11, Matrix.cons_val_zero, record2683Family11D2FactorRect, radius, theta, t,
      firstBound, secondBound, storedWidth, capturedModulations2584,
      record2675CellRight, binary64Value2674, binary64ExponentBits2674,
      binary64Significand2674, binary64FractionBits2674, binary64Sign2674]
  have hrectReHi : -60 / radius ^ 2 + firstBound ^ 2 - theta ^ 2 ≤
      record2683Family11D2FactorRect.reHi := by
    norm_num [Matrix.cons_val_11, Matrix.cons_val_zero, record2683Family11D2FactorRect, radius, theta, t,
      firstBound, secondBound, storedWidth, capturedModulations2584,
      record2675CellRight, binary64Value2674, binary64ExponentBits2674,
      binary64Significand2674, binary64FractionBits2674, binary64Sign2674]
  have hrectImHi : -2 * theta * firstBound ≤
      record2683Family11D2FactorRect.imHi := by
    norm_num [Matrix.cons_val_11, Matrix.cons_val_zero, record2683Family11D2FactorRect, radius, theta, t,
      firstBound, secondBound, storedWidth, capturedModulations2584,
      record2675CellRight, binary64Value2674, binary64ExponentBits2674,
      binary64Significand2674, binary64FractionBits2674, binary64Sign2674]
  have hrectImLo : record2683Family11D2FactorRect.imLo ≤
      0 := by
    norm_num [Matrix.cons_val_11, Matrix.cons_val_zero, record2683Family11D2FactorRect, radius, theta, t,
      firstBound, secondBound, storedWidth, capturedModulations2584,
      record2675CellRight, binary64Value2674, binary64ExponentBits2674,
      binary64Significand2674, binary64FractionBits2674, binary64Sign2674]
  have hre :
      (familySecondFactor2345 (capturedModulations2584 11)
        (storedWidth 11 ^ 2) x).re =
        familyLogSecond2345 radius x +
          (familyLogFirst2345 radius x) ^ 2 - theta ^ 2 := by
    simp [familySecondFactor2345, radius, theta, pow_two,
      Complex.mul_re, Complex.mul_im]
  have him :
      (familySecondFactor2345 (capturedModulations2584 11)
        (storedWidth 11 ^ 2) x).im =
        2 * theta * familyLogFirst2345 radius x := by
    simp [familySecondFactor2345, radius, theta, pow_two,
      Complex.mul_re, Complex.mul_im]
  rw [ComplexRect2427.Mem, record2683Family11D2FactorRect, hre, him]
  constructor
  · exact hrectLo.trans hrealLower
  constructor
  · exact hrealUpper.trans hrectReHi
  constructor
  · exact hrectImLo.trans himLower
  · exact himUpper.trans hrectImHi

set_option maxRecDepth 10000 in
theorem record2683Family11CorrectionD2CellRectMem {x : ℝ}
    (hx : x ∈ Set.Icc 0 record2675CellRight) :
    (record2676CorrectionD2FamilyRects 11).Mem
      (familySecondValue2346 (record2680CorrectionCoefficient 11)
        (capturedModulations2584 11) (storedWidth 11 ^ 2) x) := by
  have hmid := familyMidMem2676 (record2677Family11PhiMem hx)
    (record2677Family11TrigMem hx).1 (record2677Family11TrigMem hx).2
  have hprod := familyK2Mem2676
    (c := record2680CorrectionCoefficient 11)
    (theta := capturedModulations2584 11) (radius := storedWidth 11 ^ 2)
    (x := x) (by
      simpa [abs_of_nonneg hx.1] using
        (show x < storedWidth 11 ^ 2 from by
          exact lt_of_le_of_lt hx.2 (by
            norm_num [Matrix.cons_val_11, Matrix.cons_val_zero, storedWidth, record2675CellRight, binary64Value2674,
              binary64ExponentBits2674, binary64Significand2674,
              binary64FractionBits2674, binary64Sign2674]))) hmid
    (record2683Family11D2FactorMem hx)
  have hsub :
      (record2676CorrectionD2FamilyRects 11).reLo ≤
          (ComplexRect2427.mul
            (ComplexRect2427.mul (ComplexRect2427.point
              (record2680CorrectionCoefficient 11)) record2677Family11MidRect)
            record2683Family11D2FactorRect).reLo ∧
      (ComplexRect2427.mul
            (ComplexRect2427.mul (ComplexRect2427.point
              (record2680CorrectionCoefficient 11)) record2677Family11MidRect)
            record2683Family11D2FactorRect).reHi ≤
          (record2676CorrectionD2FamilyRects 11).reHi ∧
      (record2676CorrectionD2FamilyRects 11).imLo ≤
          (ComplexRect2427.mul
            (ComplexRect2427.mul (ComplexRect2427.point
              (record2680CorrectionCoefficient 11)) record2677Family11MidRect)
            record2683Family11D2FactorRect).imLo ∧
      (ComplexRect2427.mul
            (ComplexRect2427.mul (ComplexRect2427.point
              (record2680CorrectionCoefficient 11)) record2677Family11MidRect)
            record2683Family11D2FactorRect).imHi ≤
          (record2676CorrectionD2FamilyRects 11).imHi := by
    constructor
    · norm_num [Matrix.cons_val_11, Matrix.cons_val_zero, record2676CorrectionD2FamilyRects, record2683Family11D2FactorRect,
        record2680CorrectionCoefficient, record2677Family11MidRect,
        record2677Family11PhiRect, record2677Family11CosRect,
        record2677Family11SinRect, ComplexRect2427.mul, RealInterval2429.mul,
        RealInterval2429.add, RealInterval2429.sub, ComplexRect2427.point,
        storedWidth, capturedModulations2584, record2675CellRight,
        binary64Value2674, binary64ExponentBits2674,
        binary64Significand2674, binary64FractionBits2674,
        binary64Sign2674]
    constructor
    · norm_num [Matrix.cons_val_11, Matrix.cons_val_zero, record2676CorrectionD2FamilyRects, record2683Family11D2FactorRect,
        record2680CorrectionCoefficient, record2677Family11MidRect,
        record2677Family11PhiRect, record2677Family11CosRect,
        record2677Family11SinRect, ComplexRect2427.mul, RealInterval2429.mul,
        RealInterval2429.add, RealInterval2429.sub, ComplexRect2427.point,
        storedWidth, capturedModulations2584, record2675CellRight,
        binary64Value2674, binary64ExponentBits2674,
        binary64Significand2674, binary64FractionBits2674,
        binary64Sign2674]
    constructor
    · norm_num [Matrix.cons_val_11, Matrix.cons_val_zero, record2676CorrectionD2FamilyRects, record2683Family11D2FactorRect,
        record2680CorrectionCoefficient, record2677Family11MidRect,
        record2677Family11PhiRect, record2677Family11CosRect,
        record2677Family11SinRect, ComplexRect2427.mul, RealInterval2429.mul,
        RealInterval2429.add, RealInterval2429.sub, ComplexRect2427.point,
        storedWidth, capturedModulations2584, record2675CellRight,
        binary64Value2674, binary64ExponentBits2674,
        binary64Significand2674, binary64FractionBits2674,
        binary64Sign2674]
    · norm_num [Matrix.cons_val_11, Matrix.cons_val_zero, record2676CorrectionD2FamilyRects, record2683Family11D2FactorRect,
        record2680CorrectionCoefficient, record2677Family11MidRect,
        record2677Family11PhiRect, record2677Family11CosRect,
        record2677Family11SinRect, ComplexRect2427.mul, RealInterval2429.mul,
        RealInterval2429.add, RealInterval2429.sub, ComplexRect2427.point,
        storedWidth, capturedModulations2584, record2675CellRight,
        binary64Value2674, binary64ExponentBits2674,
        binary64Significand2674, binary64FractionBits2674,
        binary64Sign2674]
  exact rectSubset2676 hsub.1 hsub.2.1 hsub.2.2.1 hsub.2.2.2 hprod

end ConnesWeilRH.Dev