import ConnesWeilRH.Dev.C1RouteACompactExp2542
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541

namespace ConnesWeilRH.Dev

open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def adaptiveN10239MinusPosition2542 : ℝ := ((335478789119 : ℝ) /
        51200000000)

def adaptiveN10239MinusP000Output2542 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem adaptiveN10239MinusP000Zero2542 : weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ adaptiveN10239MinusPosition2542 = 0 := by
  have hx : ¬ |adaptiveN10239MinusPosition2542| < storedWidth ⟨0, by omega⟩ ^ 2 := by
    norm_num [adaptiveN10239MinusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero, weightedFunction2348,
    externalFamilyValue2344, if_neg hx, mul_zero]

theorem adaptiveN10239MinusP000Error2542 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ adaptiveN10239MinusPosition2542 - embedPair2542
            adaptiveN10239MinusP000Output2542.1‖ ≤ (adaptiveN10239MinusP000Output2542.2 : ℝ) := by
  have hz : embedPair2542 adaptiveN10239MinusP000Output2542.1 = 0 := by
    apply Complex.ext <;> norm_num [adaptiveN10239MinusP000Output2542, embedPair2542]
  rw [adaptiveN10239MinusP000Zero2542, hz]
  norm_num [adaptiveN10239MinusP000Output2542]

theorem adaptiveN10239MinusP000Norm2542 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ adaptiveN10239MinusPosition2542‖ ≤ 1 := by
  rw [adaptiveN10239MinusP000Zero2542]
  norm_num

def adaptiveN10239MinusP001Output2542 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem adaptiveN10239MinusP001Zero2542 : weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ adaptiveN10239MinusPosition2542 = 0 := by
  have hx : ¬ |adaptiveN10239MinusPosition2542| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [adaptiveN10239MinusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero, weightedFunction2348,
    externalFamilyValue2344, if_neg hx, mul_zero]

theorem adaptiveN10239MinusP001Error2542 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ adaptiveN10239MinusPosition2542 - embedPair2542
            adaptiveN10239MinusP001Output2542.1‖ ≤ (adaptiveN10239MinusP001Output2542.2 : ℝ) := by
  have hz : embedPair2542 adaptiveN10239MinusP001Output2542.1 = 0 := by
    apply Complex.ext <;> norm_num [adaptiveN10239MinusP001Output2542, embedPair2542]
  rw [adaptiveN10239MinusP001Zero2542, hz]
  norm_num [adaptiveN10239MinusP001Output2542]

theorem adaptiveN10239MinusP001Norm2542 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ adaptiveN10239MinusPosition2542‖ ≤ 1 := by
  rw [adaptiveN10239MinusP001Zero2542]
  norm_num

def adaptiveN10239MinusP002Output2542 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem adaptiveN10239MinusP002Zero2542 : weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ adaptiveN10239MinusPosition2542 = 0 := by
  have hx : ¬ |adaptiveN10239MinusPosition2542| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [adaptiveN10239MinusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero, weightedFunction2348,
    externalFamilyValue2344, if_neg hx, mul_zero]

theorem adaptiveN10239MinusP002Error2542 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ adaptiveN10239MinusPosition2542 - embedPair2542
            adaptiveN10239MinusP002Output2542.1‖ ≤ (adaptiveN10239MinusP002Output2542.2 : ℝ) := by
  have hz : embedPair2542 adaptiveN10239MinusP002Output2542.1 = 0 := by
    apply Complex.ext <;> norm_num [adaptiveN10239MinusP002Output2542, embedPair2542]
  rw [adaptiveN10239MinusP002Zero2542, hz]
  norm_num [adaptiveN10239MinusP002Output2542]

theorem adaptiveN10239MinusP002Norm2542 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ adaptiveN10239MinusPosition2542‖ ≤ 1 := by
  rw [adaptiveN10239MinusP002Zero2542]
  norm_num

def adaptiveN10239MinusP003Output2542 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem adaptiveN10239MinusP003Zero2542 : weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ adaptiveN10239MinusPosition2542 = 0 := by
  have hx : ¬ |adaptiveN10239MinusPosition2542| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [adaptiveN10239MinusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero, weightedFunction2348,
    externalFamilyValue2344, if_neg hx, mul_zero]

theorem adaptiveN10239MinusP003Error2542 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ adaptiveN10239MinusPosition2542 - embedPair2542
            adaptiveN10239MinusP003Output2542.1‖ ≤ (adaptiveN10239MinusP003Output2542.2 : ℝ) := by
  have hz : embedPair2542 adaptiveN10239MinusP003Output2542.1 = 0 := by
    apply Complex.ext <;> norm_num [adaptiveN10239MinusP003Output2542, embedPair2542]
  rw [adaptiveN10239MinusP003Zero2542, hz]
  norm_num [adaptiveN10239MinusP003Output2542]

theorem adaptiveN10239MinusP003Norm2542 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ adaptiveN10239MinusPosition2542‖ ≤ 1 := by
  rw [adaptiveN10239MinusP003Zero2542]
  norm_num

def adaptiveN10239MinusP004Output2542 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

def adaptiveN10239MinusP004Input2542 : RatPair2542 :=
  ((((-((20220 * 10^40
        + 8223985760775046352662199539254491013811) * 10^40
        + 5561935562252393339501278847130390888639)) : ℚ) /
        ((34502 * 10^40
        + 6667990208777211291311779003017294650045) * 10^40
        + 2705343650009835671246640827596800000000)),
    (((-1853282464048842856447326451) : ℚ) /
        944473296573929042739200000000))

theorem adaptiveN10239MinusP004Compute2542 : compactExp2542 adaptiveN10239MinusP004Input2542 17 =
    adaptiveN10239MinusP004Output2542 := by
  cbv

theorem adaptiveN10239MinusP004Owner2542 : weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ adaptiveN10239MinusPosition2542 =
    Complex.exp ((2 : ℂ)^17 * embedPair2542 adaptiveN10239MinusP004Input2542) := by
  have hx : |adaptiveN10239MinusPosition2542| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [adaptiveN10239MinusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN10239MinusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN10239MinusP004Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN10239MinusP004Error2542 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ adaptiveN10239MinusPosition2542 - embedPair2542
            adaptiveN10239MinusP004Output2542.1‖ ≤ (adaptiveN10239MinusP004Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN10239MinusP004Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN10239MinusP004Input2542]
  rw [adaptiveN10239MinusP004Owner2542]
  have h := compactExp_error2542 adaptiveN10239MinusP004Input2542 hz 17
  simpa only [adaptiveN10239MinusP004Compute2542] using h

theorem adaptiveN10239MinusP004Norm2542 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ adaptiveN10239MinusPosition2542‖ ≤ 1 := by
  rw [adaptiveN10239MinusP004Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN10239MinusP004Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN10239MinusP005Output2542 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem adaptiveN10239MinusP005Zero2542 : weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ adaptiveN10239MinusPosition2542 = 0 := by
  have hx : ¬ |adaptiveN10239MinusPosition2542| < storedWidth ⟨5, by omega⟩ ^ 2 := by
    norm_num [adaptiveN10239MinusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero, weightedFunction2348,
    externalFamilyValue2344, if_neg hx, mul_zero]

theorem adaptiveN10239MinusP005Error2542 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ adaptiveN10239MinusPosition2542 - embedPair2542
            adaptiveN10239MinusP005Output2542.1‖ ≤ (adaptiveN10239MinusP005Output2542.2 : ℝ) := by
  have hz : embedPair2542 adaptiveN10239MinusP005Output2542.1 = 0 := by
    apply Complex.ext <;> norm_num [adaptiveN10239MinusP005Output2542, embedPair2542]
  rw [adaptiveN10239MinusP005Zero2542, hz]
  norm_num [adaptiveN10239MinusP005Output2542]

theorem adaptiveN10239MinusP005Norm2542 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ adaptiveN10239MinusPosition2542‖ ≤ 1 := by
  rw [adaptiveN10239MinusP005Zero2542]
  norm_num

def adaptiveN10239MinusP006Output2542 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem adaptiveN10239MinusP006Zero2542 : weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ adaptiveN10239MinusPosition2542 = 0 := by
  have hx : ¬ |adaptiveN10239MinusPosition2542| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [adaptiveN10239MinusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero, weightedFunction2348,
    externalFamilyValue2344, if_neg hx, mul_zero]

theorem adaptiveN10239MinusP006Error2542 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ adaptiveN10239MinusPosition2542 - embedPair2542
            adaptiveN10239MinusP006Output2542.1‖ ≤ (adaptiveN10239MinusP006Output2542.2 : ℝ) := by
  have hz : embedPair2542 adaptiveN10239MinusP006Output2542.1 = 0 := by
    apply Complex.ext <;> norm_num [adaptiveN10239MinusP006Output2542, embedPair2542]
  rw [adaptiveN10239MinusP006Zero2542, hz]
  norm_num [adaptiveN10239MinusP006Output2542]

theorem adaptiveN10239MinusP006Norm2542 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ adaptiveN10239MinusPosition2542‖ ≤ 1 := by
  rw [adaptiveN10239MinusP006Zero2542]
  norm_num

def adaptiveN10239MinusP007Output2542 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem adaptiveN10239MinusP007Zero2542 : weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ adaptiveN10239MinusPosition2542 = 0 := by
  have hx : ¬ |adaptiveN10239MinusPosition2542| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [adaptiveN10239MinusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero, weightedFunction2348,
    externalFamilyValue2344, if_neg hx, mul_zero]

theorem adaptiveN10239MinusP007Error2542 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ adaptiveN10239MinusPosition2542 - embedPair2542
            adaptiveN10239MinusP007Output2542.1‖ ≤ (adaptiveN10239MinusP007Output2542.2 : ℝ) := by
  have hz : embedPair2542 adaptiveN10239MinusP007Output2542.1 = 0 := by
    apply Complex.ext <;> norm_num [adaptiveN10239MinusP007Output2542, embedPair2542]
  rw [adaptiveN10239MinusP007Zero2542, hz]
  norm_num [adaptiveN10239MinusP007Output2542]

theorem adaptiveN10239MinusP007Norm2542 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ adaptiveN10239MinusPosition2542‖ ≤ 1 := by
  rw [adaptiveN10239MinusP007Zero2542]
  norm_num

def adaptiveN10239MinusP008Output2542 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem adaptiveN10239MinusP008Zero2542 : weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ adaptiveN10239MinusPosition2542 = 0 := by
  have hx : ¬ |adaptiveN10239MinusPosition2542| < storedWidth ⟨8, by omega⟩ ^ 2 := by
    norm_num [adaptiveN10239MinusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero, weightedFunction2348,
    externalFamilyValue2344, if_neg hx, mul_zero]

theorem adaptiveN10239MinusP008Error2542 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ adaptiveN10239MinusPosition2542 - embedPair2542
            adaptiveN10239MinusP008Output2542.1‖ ≤ (adaptiveN10239MinusP008Output2542.2 : ℝ) := by
  have hz : embedPair2542 adaptiveN10239MinusP008Output2542.1 = 0 := by
    apply Complex.ext <;> norm_num [adaptiveN10239MinusP008Output2542, embedPair2542]
  rw [adaptiveN10239MinusP008Zero2542, hz]
  norm_num [adaptiveN10239MinusP008Output2542]

theorem adaptiveN10239MinusP008Norm2542 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ adaptiveN10239MinusPosition2542‖ ≤ 1 := by
  rw [adaptiveN10239MinusP008Zero2542]
  norm_num

def adaptiveN10239MinusP009Output2542 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem adaptiveN10239MinusP009Zero2542 : weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ adaptiveN10239MinusPosition2542 = 0 := by
  have hx : ¬ |adaptiveN10239MinusPosition2542| < storedWidth ⟨9, by omega⟩ ^ 2 := by
    norm_num [adaptiveN10239MinusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero, weightedFunction2348,
    externalFamilyValue2344, if_neg hx, mul_zero]

theorem adaptiveN10239MinusP009Error2542 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ adaptiveN10239MinusPosition2542 - embedPair2542
            adaptiveN10239MinusP009Output2542.1‖ ≤ (adaptiveN10239MinusP009Output2542.2 : ℝ) := by
  have hz : embedPair2542 adaptiveN10239MinusP009Output2542.1 = 0 := by
    apply Complex.ext <;> norm_num [adaptiveN10239MinusP009Output2542, embedPair2542]
  rw [adaptiveN10239MinusP009Zero2542, hz]
  norm_num [adaptiveN10239MinusP009Output2542]

theorem adaptiveN10239MinusP009Norm2542 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ adaptiveN10239MinusPosition2542‖ ≤ 1 := by
  rw [adaptiveN10239MinusP009Zero2542]
  norm_num

def adaptiveN10239MinusP010Output2542 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem adaptiveN10239MinusP010Zero2542 : weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ adaptiveN10239MinusPosition2542 = 0 := by
  have hx : ¬ |adaptiveN10239MinusPosition2542| < storedWidth ⟨10, by omega⟩ ^ 2 := by
    norm_num [adaptiveN10239MinusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero, weightedFunction2348,
    externalFamilyValue2344, if_neg hx, mul_zero]

theorem adaptiveN10239MinusP010Error2542 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ adaptiveN10239MinusPosition2542 - embedPair2542
            adaptiveN10239MinusP010Output2542.1‖ ≤ (adaptiveN10239MinusP010Output2542.2 : ℝ) := by
  have hz : embedPair2542 adaptiveN10239MinusP010Output2542.1 = 0 := by
    apply Complex.ext <;> norm_num [adaptiveN10239MinusP010Output2542, embedPair2542]
  rw [adaptiveN10239MinusP010Zero2542, hz]
  norm_num [adaptiveN10239MinusP010Output2542]

theorem adaptiveN10239MinusP010Norm2542 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ adaptiveN10239MinusPosition2542‖ ≤ 1 := by
  rw [adaptiveN10239MinusP010Zero2542]
  norm_num

def adaptiveN10239MinusP011Output2542 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem adaptiveN10239MinusP011Zero2542 : weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ adaptiveN10239MinusPosition2542 = 0 := by
  have hx : ¬ |adaptiveN10239MinusPosition2542| < storedWidth ⟨11, by omega⟩ ^ 2 := by
    norm_num [adaptiveN10239MinusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero, weightedFunction2348,
    externalFamilyValue2344, if_neg hx, mul_zero]

theorem adaptiveN10239MinusP011Error2542 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ adaptiveN10239MinusPosition2542 - embedPair2542
            adaptiveN10239MinusP011Output2542.1‖ ≤ (adaptiveN10239MinusP011Output2542.2 : ℝ) := by
  have hz : embedPair2542 adaptiveN10239MinusP011Output2542.1 = 0 := by
    apply Complex.ext <;> norm_num [adaptiveN10239MinusP011Output2542, embedPair2542]
  rw [adaptiveN10239MinusP011Zero2542, hz]
  norm_num [adaptiveN10239MinusP011Output2542]

theorem adaptiveN10239MinusP011Norm2542 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ adaptiveN10239MinusPosition2542‖ ≤ 1 := by
  rw [adaptiveN10239MinusP011Zero2542]
  norm_num

def adaptiveN10239MinusP012Output2542 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem adaptiveN10239MinusP012Zero2542 : weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ adaptiveN10239MinusPosition2542 = 0 := by
  have hx : ¬ |adaptiveN10239MinusPosition2542| < storedWidth ⟨12, by omega⟩ ^ 2 := by
    norm_num [adaptiveN10239MinusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero, weightedFunction2348,
    externalFamilyValue2344, if_neg hx, mul_zero]

theorem adaptiveN10239MinusP012Error2542 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ adaptiveN10239MinusPosition2542 - embedPair2542
            adaptiveN10239MinusP012Output2542.1‖ ≤ (adaptiveN10239MinusP012Output2542.2 : ℝ) := by
  have hz : embedPair2542 adaptiveN10239MinusP012Output2542.1 = 0 := by
    apply Complex.ext <;> norm_num [adaptiveN10239MinusP012Output2542, embedPair2542]
  rw [adaptiveN10239MinusP012Zero2542, hz]
  norm_num [adaptiveN10239MinusP012Output2542]

theorem adaptiveN10239MinusP012Norm2542 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ adaptiveN10239MinusPosition2542‖ ≤ 1 := by
  rw [adaptiveN10239MinusP012Zero2542]
  norm_num

def adaptiveN10239MinusP013Output2542 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem adaptiveN10239MinusP013Zero2542 : weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ adaptiveN10239MinusPosition2542 = 0 := by
  have hx : ¬ |adaptiveN10239MinusPosition2542| < storedWidth ⟨13, by omega⟩ ^ 2 := by
    norm_num [adaptiveN10239MinusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero, weightedFunction2348,
    externalFamilyValue2344, if_neg hx, mul_zero]

theorem adaptiveN10239MinusP013Error2542 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ adaptiveN10239MinusPosition2542 - embedPair2542
            adaptiveN10239MinusP013Output2542.1‖ ≤ (adaptiveN10239MinusP013Output2542.2 : ℝ) := by
  have hz : embedPair2542 adaptiveN10239MinusP013Output2542.1 = 0 := by
    apply Complex.ext <;> norm_num [adaptiveN10239MinusP013Output2542, embedPair2542]
  rw [adaptiveN10239MinusP013Zero2542, hz]
  norm_num [adaptiveN10239MinusP013Output2542]

theorem adaptiveN10239MinusP013Norm2542 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ adaptiveN10239MinusPosition2542‖ ≤ 1 := by
  rw [adaptiveN10239MinusP013Zero2542]
  norm_num

def adaptiveN10239MinusP014Output2542 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem adaptiveN10239MinusP014Zero2542 : weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ adaptiveN10239MinusPosition2542 = 0 := by
  have hx : ¬ |adaptiveN10239MinusPosition2542| < storedWidth ⟨14, by omega⟩ ^ 2 := by
    norm_num [adaptiveN10239MinusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero, weightedFunction2348,
    externalFamilyValue2344, if_neg hx, mul_zero]

theorem adaptiveN10239MinusP014Error2542 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ adaptiveN10239MinusPosition2542 - embedPair2542
            adaptiveN10239MinusP014Output2542.1‖ ≤ (adaptiveN10239MinusP014Output2542.2 : ℝ) := by
  have hz : embedPair2542 adaptiveN10239MinusP014Output2542.1 = 0 := by
    apply Complex.ext <;> norm_num [adaptiveN10239MinusP014Output2542, embedPair2542]
  rw [adaptiveN10239MinusP014Zero2542, hz]
  norm_num [adaptiveN10239MinusP014Output2542]

theorem adaptiveN10239MinusP014Norm2542 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ adaptiveN10239MinusPosition2542‖ ≤ 1 := by
  rw [adaptiveN10239MinusP014Zero2542]
  norm_num

def adaptiveN10239MinusP015Output2542 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem adaptiveN10239MinusP015Zero2542 : weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ adaptiveN10239MinusPosition2542 = 0 := by
  have hx : ¬ |adaptiveN10239MinusPosition2542| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [adaptiveN10239MinusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero, weightedFunction2348,
    externalFamilyValue2344, if_neg hx, mul_zero]

theorem adaptiveN10239MinusP015Error2542 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ adaptiveN10239MinusPosition2542 - embedPair2542
            adaptiveN10239MinusP015Output2542.1‖ ≤ (adaptiveN10239MinusP015Output2542.2 : ℝ) := by
  have hz : embedPair2542 adaptiveN10239MinusP015Output2542.1 = 0 := by
    apply Complex.ext <;> norm_num [adaptiveN10239MinusP015Output2542, embedPair2542]
  rw [adaptiveN10239MinusP015Zero2542, hz]
  norm_num [adaptiveN10239MinusP015Output2542]

theorem adaptiveN10239MinusP015Norm2542 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ adaptiveN10239MinusPosition2542‖ ≤ 1 := by
  rw [adaptiveN10239MinusP015Zero2542]
  norm_num

def adaptiveN10239MinusP016Output2542 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem adaptiveN10239MinusP016Zero2542 : weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ adaptiveN10239MinusPosition2542 = 0 := by
  have hx : ¬ |adaptiveN10239MinusPosition2542| < storedWidth ⟨16, by omega⟩ ^ 2 := by
    norm_num [adaptiveN10239MinusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero, weightedFunction2348,
    externalFamilyValue2344, if_neg hx, mul_zero]

theorem adaptiveN10239MinusP016Error2542 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ adaptiveN10239MinusPosition2542 - embedPair2542
            adaptiveN10239MinusP016Output2542.1‖ ≤ (adaptiveN10239MinusP016Output2542.2 : ℝ) := by
  have hz : embedPair2542 adaptiveN10239MinusP016Output2542.1 = 0 := by
    apply Complex.ext <;> norm_num [adaptiveN10239MinusP016Output2542, embedPair2542]
  rw [adaptiveN10239MinusP016Zero2542, hz]
  norm_num [adaptiveN10239MinusP016Output2542]

theorem adaptiveN10239MinusP016Norm2542 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ adaptiveN10239MinusPosition2542‖ ≤ 1 := by
  rw [adaptiveN10239MinusP016Zero2542]
  norm_num

def adaptiveN10239MinusP017Output2542 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem adaptiveN10239MinusP017Zero2542 : weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ adaptiveN10239MinusPosition2542 = 0 := by
  have hx : ¬ |adaptiveN10239MinusPosition2542| < storedWidth ⟨17, by omega⟩ ^ 2 := by
    norm_num [adaptiveN10239MinusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero, weightedFunction2348,
    externalFamilyValue2344, if_neg hx, mul_zero]

theorem adaptiveN10239MinusP017Error2542 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ adaptiveN10239MinusPosition2542 - embedPair2542
            adaptiveN10239MinusP017Output2542.1‖ ≤ (adaptiveN10239MinusP017Output2542.2 : ℝ) := by
  have hz : embedPair2542 adaptiveN10239MinusP017Output2542.1 = 0 := by
    apply Complex.ext <;> norm_num [adaptiveN10239MinusP017Output2542, embedPair2542]
  rw [adaptiveN10239MinusP017Zero2542, hz]
  norm_num [adaptiveN10239MinusP017Output2542]

theorem adaptiveN10239MinusP017Norm2542 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ adaptiveN10239MinusPosition2542‖ ≤ 1 := by
  rw [adaptiveN10239MinusP017Zero2542]
  norm_num

def adaptiveN10239MinusP018Output2542 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem adaptiveN10239MinusP018Zero2542 : weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ adaptiveN10239MinusPosition2542 = 0 := by
  have hx : ¬ |adaptiveN10239MinusPosition2542| < storedWidth ⟨18, by omega⟩ ^ 2 := by
    norm_num [adaptiveN10239MinusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero, weightedFunction2348,
    externalFamilyValue2344, if_neg hx, mul_zero]

theorem adaptiveN10239MinusP018Error2542 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ adaptiveN10239MinusPosition2542 - embedPair2542
            adaptiveN10239MinusP018Output2542.1‖ ≤ (adaptiveN10239MinusP018Output2542.2 : ℝ) := by
  have hz : embedPair2542 adaptiveN10239MinusP018Output2542.1 = 0 := by
    apply Complex.ext <;> norm_num [adaptiveN10239MinusP018Output2542, embedPair2542]
  rw [adaptiveN10239MinusP018Zero2542, hz]
  norm_num [adaptiveN10239MinusP018Output2542]

theorem adaptiveN10239MinusP018Norm2542 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ adaptiveN10239MinusPosition2542‖ ≤ 1 := by
  rw [adaptiveN10239MinusP018Zero2542]
  norm_num

def adaptiveN10239MinusP019Output2542 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem adaptiveN10239MinusP019Zero2542 : weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ adaptiveN10239MinusPosition2542 = 0 := by
  have hx : ¬ |adaptiveN10239MinusPosition2542| < storedWidth ⟨19, by omega⟩ ^ 2 := by
    norm_num [adaptiveN10239MinusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero, weightedFunction2348,
    externalFamilyValue2344, if_neg hx, mul_zero]

theorem adaptiveN10239MinusP019Error2542 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ adaptiveN10239MinusPosition2542 - embedPair2542
            adaptiveN10239MinusP019Output2542.1‖ ≤ (adaptiveN10239MinusP019Output2542.2 : ℝ) := by
  have hz : embedPair2542 adaptiveN10239MinusP019Output2542.1 = 0 := by
    apply Complex.ext <;> norm_num [adaptiveN10239MinusP019Output2542, embedPair2542]
  rw [adaptiveN10239MinusP019Zero2542, hz]
  norm_num [adaptiveN10239MinusP019Output2542]

theorem adaptiveN10239MinusP019Norm2542 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ adaptiveN10239MinusPosition2542‖ ≤ 1 := by
  rw [adaptiveN10239MinusP019Zero2542]
  norm_num

def adaptiveN10239MinusP020Output2542 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem adaptiveN10239MinusP020Zero2542 : weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ adaptiveN10239MinusPosition2542 = 0 := by
  have hx : ¬ |adaptiveN10239MinusPosition2542| < storedWidth ⟨20, by omega⟩ ^ 2 := by
    norm_num [adaptiveN10239MinusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero, weightedFunction2348,
    externalFamilyValue2344, if_neg hx, mul_zero]

theorem adaptiveN10239MinusP020Error2542 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ adaptiveN10239MinusPosition2542 - embedPair2542
            adaptiveN10239MinusP020Output2542.1‖ ≤ (adaptiveN10239MinusP020Output2542.2 : ℝ) := by
  have hz : embedPair2542 adaptiveN10239MinusP020Output2542.1 = 0 := by
    apply Complex.ext <;> norm_num [adaptiveN10239MinusP020Output2542, embedPair2542]
  rw [adaptiveN10239MinusP020Zero2542, hz]
  norm_num [adaptiveN10239MinusP020Output2542]

theorem adaptiveN10239MinusP020Norm2542 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ adaptiveN10239MinusPosition2542‖ ≤ 1 := by
  rw [adaptiveN10239MinusP020Zero2542]
  norm_num

def adaptiveN10239MinusP021Output2542 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem adaptiveN10239MinusP021Zero2542 : weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ adaptiveN10239MinusPosition2542 = 0 := by
  have hx : ¬ |adaptiveN10239MinusPosition2542| < storedWidth ⟨21, by omega⟩ ^ 2 := by
    norm_num [adaptiveN10239MinusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero, weightedFunction2348,
    externalFamilyValue2344, if_neg hx, mul_zero]

theorem adaptiveN10239MinusP021Error2542 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ adaptiveN10239MinusPosition2542 - embedPair2542
            adaptiveN10239MinusP021Output2542.1‖ ≤ (adaptiveN10239MinusP021Output2542.2 : ℝ) := by
  have hz : embedPair2542 adaptiveN10239MinusP021Output2542.1 = 0 := by
    apply Complex.ext <;> norm_num [adaptiveN10239MinusP021Output2542, embedPair2542]
  rw [adaptiveN10239MinusP021Zero2542, hz]
  norm_num [adaptiveN10239MinusP021Output2542]

theorem adaptiveN10239MinusP021Norm2542 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ adaptiveN10239MinusPosition2542‖ ≤ 1 := by
  rw [adaptiveN10239MinusP021Zero2542]
  norm_num

def adaptiveN10239MinusP022Output2542 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem adaptiveN10239MinusP022Zero2542 : weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ adaptiveN10239MinusPosition2542 = 0 := by
  have hx : ¬ |adaptiveN10239MinusPosition2542| < storedWidth ⟨22, by omega⟩ ^ 2 := by
    norm_num [adaptiveN10239MinusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero, weightedFunction2348,
    externalFamilyValue2344, if_neg hx, mul_zero]

theorem adaptiveN10239MinusP022Error2542 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ adaptiveN10239MinusPosition2542 - embedPair2542
            adaptiveN10239MinusP022Output2542.1‖ ≤ (adaptiveN10239MinusP022Output2542.2 : ℝ) := by
  have hz : embedPair2542 adaptiveN10239MinusP022Output2542.1 = 0 := by
    apply Complex.ext <;> norm_num [adaptiveN10239MinusP022Output2542, embedPair2542]
  rw [adaptiveN10239MinusP022Zero2542, hz]
  norm_num [adaptiveN10239MinusP022Output2542]

theorem adaptiveN10239MinusP022Norm2542 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ adaptiveN10239MinusPosition2542‖ ≤ 1 := by
  rw [adaptiveN10239MinusP022Zero2542]
  norm_num

def adaptiveN10239MinusP023Output2542 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem adaptiveN10239MinusP023Zero2542 : weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ adaptiveN10239MinusPosition2542 = 0 := by
  have hx : ¬ |adaptiveN10239MinusPosition2542| < storedWidth ⟨23, by omega⟩ ^ 2 := by
    norm_num [adaptiveN10239MinusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero, weightedFunction2348,
    externalFamilyValue2344, if_neg hx, mul_zero]

theorem adaptiveN10239MinusP023Error2542 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ adaptiveN10239MinusPosition2542 - embedPair2542
            adaptiveN10239MinusP023Output2542.1‖ ≤ (adaptiveN10239MinusP023Output2542.2 : ℝ) := by
  have hz : embedPair2542 adaptiveN10239MinusP023Output2542.1 = 0 := by
    apply Complex.ext <;> norm_num [adaptiveN10239MinusP023Output2542, embedPair2542]
  rw [adaptiveN10239MinusP023Zero2542, hz]
  norm_num [adaptiveN10239MinusP023Output2542]

theorem adaptiveN10239MinusP023Norm2542 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ adaptiveN10239MinusPosition2542‖ ≤ 1 := by
  rw [adaptiveN10239MinusP023Zero2542]
  norm_num

def adaptiveN10239MinusP024Output2542 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem adaptiveN10239MinusP024Zero2542 : weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ adaptiveN10239MinusPosition2542 = 0 := by
  have hx : ¬ |adaptiveN10239MinusPosition2542| < storedWidth ⟨24, by omega⟩ ^ 2 := by
    norm_num [adaptiveN10239MinusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero, weightedFunction2348,
    externalFamilyValue2344, if_neg hx, mul_zero]

theorem adaptiveN10239MinusP024Error2542 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ adaptiveN10239MinusPosition2542 - embedPair2542
            adaptiveN10239MinusP024Output2542.1‖ ≤ (adaptiveN10239MinusP024Output2542.2 : ℝ) := by
  have hz : embedPair2542 adaptiveN10239MinusP024Output2542.1 = 0 := by
    apply Complex.ext <;> norm_num [adaptiveN10239MinusP024Output2542, embedPair2542]
  rw [adaptiveN10239MinusP024Zero2542, hz]
  norm_num [adaptiveN10239MinusP024Output2542]

theorem adaptiveN10239MinusP024Norm2542 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ adaptiveN10239MinusPosition2542‖ ≤ 1 := by
  rw [adaptiveN10239MinusP024Zero2542]
  norm_num

def adaptiveN10239MinusP025Output2542 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem adaptiveN10239MinusP025Zero2542 : weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ adaptiveN10239MinusPosition2542 = 0 := by
  have hx : ¬ |adaptiveN10239MinusPosition2542| < storedWidth ⟨25, by omega⟩ ^ 2 := by
    norm_num [adaptiveN10239MinusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero, weightedFunction2348,
    externalFamilyValue2344, if_neg hx, mul_zero]

theorem adaptiveN10239MinusP025Error2542 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ adaptiveN10239MinusPosition2542 - embedPair2542
            adaptiveN10239MinusP025Output2542.1‖ ≤ (adaptiveN10239MinusP025Output2542.2 : ℝ) := by
  have hz : embedPair2542 adaptiveN10239MinusP025Output2542.1 = 0 := by
    apply Complex.ext <;> norm_num [adaptiveN10239MinusP025Output2542, embedPair2542]
  rw [adaptiveN10239MinusP025Zero2542, hz]
  norm_num [adaptiveN10239MinusP025Output2542]

theorem adaptiveN10239MinusP025Norm2542 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ adaptiveN10239MinusPosition2542‖ ≤ 1 := by
  rw [adaptiveN10239MinusP025Zero2542]
  norm_num

def adaptiveN10239MinusP026Output2542 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem adaptiveN10239MinusP026Zero2542 : weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ adaptiveN10239MinusPosition2542 = 0 := by
  have hx : ¬ |adaptiveN10239MinusPosition2542| < storedWidth ⟨26, by omega⟩ ^ 2 := by
    norm_num [adaptiveN10239MinusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero, weightedFunction2348,
    externalFamilyValue2344, if_neg hx, mul_zero]

theorem adaptiveN10239MinusP026Error2542 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ adaptiveN10239MinusPosition2542 - embedPair2542
            adaptiveN10239MinusP026Output2542.1‖ ≤ (adaptiveN10239MinusP026Output2542.2 : ℝ) := by
  have hz : embedPair2542 adaptiveN10239MinusP026Output2542.1 = 0 := by
    apply Complex.ext <;> norm_num [adaptiveN10239MinusP026Output2542, embedPair2542]
  rw [adaptiveN10239MinusP026Zero2542, hz]
  norm_num [adaptiveN10239MinusP026Output2542]

theorem adaptiveN10239MinusP026Norm2542 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ adaptiveN10239MinusPosition2542‖ ≤ 1 := by
  rw [adaptiveN10239MinusP026Zero2542]
  norm_num

def adaptiveN10239MinusP027Output2542 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem adaptiveN10239MinusP027Zero2542 : weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ adaptiveN10239MinusPosition2542 = 0 := by
  have hx : ¬ |adaptiveN10239MinusPosition2542| < storedWidth ⟨27, by omega⟩ ^ 2 := by
    norm_num [adaptiveN10239MinusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero, weightedFunction2348,
    externalFamilyValue2344, if_neg hx, mul_zero]

theorem adaptiveN10239MinusP027Error2542 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ adaptiveN10239MinusPosition2542 - embedPair2542
            adaptiveN10239MinusP027Output2542.1‖ ≤ (adaptiveN10239MinusP027Output2542.2 : ℝ) := by
  have hz : embedPair2542 adaptiveN10239MinusP027Output2542.1 = 0 := by
    apply Complex.ext <;> norm_num [adaptiveN10239MinusP027Output2542, embedPair2542]
  rw [adaptiveN10239MinusP027Zero2542, hz]
  norm_num [adaptiveN10239MinusP027Output2542]

theorem adaptiveN10239MinusP027Norm2542 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ adaptiveN10239MinusPosition2542‖ ≤ 1 := by
  rw [adaptiveN10239MinusP027Zero2542]
  norm_num

def adaptiveN10239MinusP028Output2542 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem adaptiveN10239MinusP028Zero2542 : weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ adaptiveN10239MinusPosition2542 = 0 := by
  have hx : ¬ |adaptiveN10239MinusPosition2542| < storedWidth ⟨28, by omega⟩ ^ 2 := by
    norm_num [adaptiveN10239MinusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero, weightedFunction2348,
    externalFamilyValue2344, if_neg hx, mul_zero]

theorem adaptiveN10239MinusP028Error2542 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ adaptiveN10239MinusPosition2542 - embedPair2542
            adaptiveN10239MinusP028Output2542.1‖ ≤ (adaptiveN10239MinusP028Output2542.2 : ℝ) := by
  have hz : embedPair2542 adaptiveN10239MinusP028Output2542.1 = 0 := by
    apply Complex.ext <;> norm_num [adaptiveN10239MinusP028Output2542, embedPair2542]
  rw [adaptiveN10239MinusP028Zero2542, hz]
  norm_num [adaptiveN10239MinusP028Output2542]

theorem adaptiveN10239MinusP028Norm2542 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ adaptiveN10239MinusPosition2542‖ ≤ 1 := by
  rw [adaptiveN10239MinusP028Zero2542]
  norm_num

def adaptiveN10239MinusP029Output2542 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem adaptiveN10239MinusP029Zero2542 : weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ adaptiveN10239MinusPosition2542 = 0 := by
  have hx : ¬ |adaptiveN10239MinusPosition2542| < storedWidth ⟨29, by omega⟩ ^ 2 := by
    norm_num [adaptiveN10239MinusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero, weightedFunction2348,
    externalFamilyValue2344, if_neg hx, mul_zero]

theorem adaptiveN10239MinusP029Error2542 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ adaptiveN10239MinusPosition2542 - embedPair2542
            adaptiveN10239MinusP029Output2542.1‖ ≤ (adaptiveN10239MinusP029Output2542.2 : ℝ) := by
  have hz : embedPair2542 adaptiveN10239MinusP029Output2542.1 = 0 := by
    apply Complex.ext <;> norm_num [adaptiveN10239MinusP029Output2542, embedPair2542]
  rw [adaptiveN10239MinusP029Zero2542, hz]
  norm_num [adaptiveN10239MinusP029Output2542]

theorem adaptiveN10239MinusP029Norm2542 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ adaptiveN10239MinusPosition2542‖ ≤ 1 := by
  rw [adaptiveN10239MinusP029Zero2542]
  norm_num

noncomputable def adaptiveN10239MinusValue2542 (i : Fin 30) : ℂ :=
  match i.val with
  | 0 => embedPair2542 adaptiveN10239MinusP000Output2542.1
  | 1 => embedPair2542 adaptiveN10239MinusP001Output2542.1
  | 2 => embedPair2542 adaptiveN10239MinusP002Output2542.1
  | 3 => embedPair2542 adaptiveN10239MinusP003Output2542.1
  | 4 => embedPair2542 adaptiveN10239MinusP004Output2542.1
  | 5 => embedPair2542 adaptiveN10239MinusP005Output2542.1
  | 6 => embedPair2542 adaptiveN10239MinusP006Output2542.1
  | 7 => embedPair2542 adaptiveN10239MinusP007Output2542.1
  | 8 => embedPair2542 adaptiveN10239MinusP008Output2542.1
  | 9 => embedPair2542 adaptiveN10239MinusP009Output2542.1
  | 10 => embedPair2542 adaptiveN10239MinusP010Output2542.1
  | 11 => embedPair2542 adaptiveN10239MinusP011Output2542.1
  | 12 => embedPair2542 adaptiveN10239MinusP012Output2542.1
  | 13 => embedPair2542 adaptiveN10239MinusP013Output2542.1
  | 14 => embedPair2542 adaptiveN10239MinusP014Output2542.1
  | 15 => embedPair2542 adaptiveN10239MinusP015Output2542.1
  | 16 => embedPair2542 adaptiveN10239MinusP016Output2542.1
  | 17 => embedPair2542 adaptiveN10239MinusP017Output2542.1
  | 18 => embedPair2542 adaptiveN10239MinusP018Output2542.1
  | 19 => embedPair2542 adaptiveN10239MinusP019Output2542.1
  | 20 => embedPair2542 adaptiveN10239MinusP020Output2542.1
  | 21 => embedPair2542 adaptiveN10239MinusP021Output2542.1
  | 22 => embedPair2542 adaptiveN10239MinusP022Output2542.1
  | 23 => embedPair2542 adaptiveN10239MinusP023Output2542.1
  | 24 => embedPair2542 adaptiveN10239MinusP024Output2542.1
  | 25 => embedPair2542 adaptiveN10239MinusP025Output2542.1
  | 26 => embedPair2542 adaptiveN10239MinusP026Output2542.1
  | 27 => embedPair2542 adaptiveN10239MinusP027Output2542.1
  | 28 => embedPair2542 adaptiveN10239MinusP028Output2542.1
  | 29 => embedPair2542 adaptiveN10239MinusP029Output2542.1
  | _ => 0

noncomputable def adaptiveN10239MinusError2542 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => (adaptiveN10239MinusP000Output2542.2 : ℝ)
  | 1 => (adaptiveN10239MinusP001Output2542.2 : ℝ)
  | 2 => (adaptiveN10239MinusP002Output2542.2 : ℝ)
  | 3 => (adaptiveN10239MinusP003Output2542.2 : ℝ)
  | 4 => (adaptiveN10239MinusP004Output2542.2 : ℝ)
  | 5 => (adaptiveN10239MinusP005Output2542.2 : ℝ)
  | 6 => (adaptiveN10239MinusP006Output2542.2 : ℝ)
  | 7 => (adaptiveN10239MinusP007Output2542.2 : ℝ)
  | 8 => (adaptiveN10239MinusP008Output2542.2 : ℝ)
  | 9 => (adaptiveN10239MinusP009Output2542.2 : ℝ)
  | 10 => (adaptiveN10239MinusP010Output2542.2 : ℝ)
  | 11 => (adaptiveN10239MinusP011Output2542.2 : ℝ)
  | 12 => (adaptiveN10239MinusP012Output2542.2 : ℝ)
  | 13 => (adaptiveN10239MinusP013Output2542.2 : ℝ)
  | 14 => (adaptiveN10239MinusP014Output2542.2 : ℝ)
  | 15 => (adaptiveN10239MinusP015Output2542.2 : ℝ)
  | 16 => (adaptiveN10239MinusP016Output2542.2 : ℝ)
  | 17 => (adaptiveN10239MinusP017Output2542.2 : ℝ)
  | 18 => (adaptiveN10239MinusP018Output2542.2 : ℝ)
  | 19 => (adaptiveN10239MinusP019Output2542.2 : ℝ)
  | 20 => (adaptiveN10239MinusP020Output2542.2 : ℝ)
  | 21 => (adaptiveN10239MinusP021Output2542.2 : ℝ)
  | 22 => (adaptiveN10239MinusP022Output2542.2 : ℝ)
  | 23 => (adaptiveN10239MinusP023Output2542.2 : ℝ)
  | 24 => (adaptiveN10239MinusP024Output2542.2 : ℝ)
  | 25 => (adaptiveN10239MinusP025Output2542.2 : ℝ)
  | 26 => (adaptiveN10239MinusP026Output2542.2 : ℝ)
  | 27 => (adaptiveN10239MinusP027Output2542.2 : ℝ)
  | 28 => (adaptiveN10239MinusP028Output2542.2 : ℝ)
  | 29 => (adaptiveN10239MinusP029Output2542.2 : ℝ)
  | _ => 0

theorem adaptiveN10239MinusExp_error2542 (i : Fin 30) :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 i adaptiveN10239MinusPosition2542 - adaptiveN10239MinusValue2542 i‖
            ≤ adaptiveN10239MinusError2542 i := by
  fin_cases i
  · simpa only [adaptiveN10239MinusValue2542, adaptiveN10239MinusError2542] using
      adaptiveN10239MinusP000Error2542
  · simpa only [adaptiveN10239MinusValue2542, adaptiveN10239MinusError2542] using
      adaptiveN10239MinusP001Error2542
  · simpa only [adaptiveN10239MinusValue2542, adaptiveN10239MinusError2542] using
      adaptiveN10239MinusP002Error2542
  · simpa only [adaptiveN10239MinusValue2542, adaptiveN10239MinusError2542] using
      adaptiveN10239MinusP003Error2542
  · simpa only [adaptiveN10239MinusValue2542, adaptiveN10239MinusError2542] using
      adaptiveN10239MinusP004Error2542
  · simpa only [adaptiveN10239MinusValue2542, adaptiveN10239MinusError2542] using
      adaptiveN10239MinusP005Error2542
  · simpa only [adaptiveN10239MinusValue2542, adaptiveN10239MinusError2542] using
      adaptiveN10239MinusP006Error2542
  · simpa only [adaptiveN10239MinusValue2542, adaptiveN10239MinusError2542] using
      adaptiveN10239MinusP007Error2542
  · simpa only [adaptiveN10239MinusValue2542, adaptiveN10239MinusError2542] using
      adaptiveN10239MinusP008Error2542
  · simpa only [adaptiveN10239MinusValue2542, adaptiveN10239MinusError2542] using
      adaptiveN10239MinusP009Error2542
  · simpa only [adaptiveN10239MinusValue2542, adaptiveN10239MinusError2542] using
      adaptiveN10239MinusP010Error2542
  · simpa only [adaptiveN10239MinusValue2542, adaptiveN10239MinusError2542] using
      adaptiveN10239MinusP011Error2542
  · simpa only [adaptiveN10239MinusValue2542, adaptiveN10239MinusError2542] using
      adaptiveN10239MinusP012Error2542
  · simpa only [adaptiveN10239MinusValue2542, adaptiveN10239MinusError2542] using
      adaptiveN10239MinusP013Error2542
  · simpa only [adaptiveN10239MinusValue2542, adaptiveN10239MinusError2542] using
      adaptiveN10239MinusP014Error2542
  · simpa only [adaptiveN10239MinusValue2542, adaptiveN10239MinusError2542] using
      adaptiveN10239MinusP015Error2542
  · simpa only [adaptiveN10239MinusValue2542, adaptiveN10239MinusError2542] using
      adaptiveN10239MinusP016Error2542
  · simpa only [adaptiveN10239MinusValue2542, adaptiveN10239MinusError2542] using
      adaptiveN10239MinusP017Error2542
  · simpa only [adaptiveN10239MinusValue2542, adaptiveN10239MinusError2542] using
      adaptiveN10239MinusP018Error2542
  · simpa only [adaptiveN10239MinusValue2542, adaptiveN10239MinusError2542] using
      adaptiveN10239MinusP019Error2542
  · simpa only [adaptiveN10239MinusValue2542, adaptiveN10239MinusError2542] using
      adaptiveN10239MinusP020Error2542
  · simpa only [adaptiveN10239MinusValue2542, adaptiveN10239MinusError2542] using
      adaptiveN10239MinusP021Error2542
  · simpa only [adaptiveN10239MinusValue2542, adaptiveN10239MinusError2542] using
      adaptiveN10239MinusP022Error2542
  · simpa only [adaptiveN10239MinusValue2542, adaptiveN10239MinusError2542] using
      adaptiveN10239MinusP023Error2542
  · simpa only [adaptiveN10239MinusValue2542, adaptiveN10239MinusError2542] using
      adaptiveN10239MinusP024Error2542
  · simpa only [adaptiveN10239MinusValue2542, adaptiveN10239MinusError2542] using
      adaptiveN10239MinusP025Error2542
  · simpa only [adaptiveN10239MinusValue2542, adaptiveN10239MinusError2542] using
      adaptiveN10239MinusP026Error2542
  · simpa only [adaptiveN10239MinusValue2542, adaptiveN10239MinusError2542] using
      adaptiveN10239MinusP027Error2542
  · simpa only [adaptiveN10239MinusValue2542, adaptiveN10239MinusError2542] using
      adaptiveN10239MinusP028Error2542
  · simpa only [adaptiveN10239MinusValue2542, adaptiveN10239MinusError2542] using
      adaptiveN10239MinusP029Error2542

theorem adaptiveN10239MinusUnit_norm2542 (i : Fin 30) :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 i adaptiveN10239MinusPosition2542‖ ≤ 1 := by
  fin_cases i
  · simpa only [adaptiveN10239MinusValue2542, adaptiveN10239MinusError2542] using
      adaptiveN10239MinusP000Norm2542
  · simpa only [adaptiveN10239MinusValue2542, adaptiveN10239MinusError2542] using
      adaptiveN10239MinusP001Norm2542
  · simpa only [adaptiveN10239MinusValue2542, adaptiveN10239MinusError2542] using
      adaptiveN10239MinusP002Norm2542
  · simpa only [adaptiveN10239MinusValue2542, adaptiveN10239MinusError2542] using
      adaptiveN10239MinusP003Norm2542
  · simpa only [adaptiveN10239MinusValue2542, adaptiveN10239MinusError2542] using
      adaptiveN10239MinusP004Norm2542
  · simpa only [adaptiveN10239MinusValue2542, adaptiveN10239MinusError2542] using
      adaptiveN10239MinusP005Norm2542
  · simpa only [adaptiveN10239MinusValue2542, adaptiveN10239MinusError2542] using
      adaptiveN10239MinusP006Norm2542
  · simpa only [adaptiveN10239MinusValue2542, adaptiveN10239MinusError2542] using
      adaptiveN10239MinusP007Norm2542
  · simpa only [adaptiveN10239MinusValue2542, adaptiveN10239MinusError2542] using
      adaptiveN10239MinusP008Norm2542
  · simpa only [adaptiveN10239MinusValue2542, adaptiveN10239MinusError2542] using
      adaptiveN10239MinusP009Norm2542
  · simpa only [adaptiveN10239MinusValue2542, adaptiveN10239MinusError2542] using
      adaptiveN10239MinusP010Norm2542
  · simpa only [adaptiveN10239MinusValue2542, adaptiveN10239MinusError2542] using
      adaptiveN10239MinusP011Norm2542
  · simpa only [adaptiveN10239MinusValue2542, adaptiveN10239MinusError2542] using
      adaptiveN10239MinusP012Norm2542
  · simpa only [adaptiveN10239MinusValue2542, adaptiveN10239MinusError2542] using
      adaptiveN10239MinusP013Norm2542
  · simpa only [adaptiveN10239MinusValue2542, adaptiveN10239MinusError2542] using
      adaptiveN10239MinusP014Norm2542
  · simpa only [adaptiveN10239MinusValue2542, adaptiveN10239MinusError2542] using
      adaptiveN10239MinusP015Norm2542
  · simpa only [adaptiveN10239MinusValue2542, adaptiveN10239MinusError2542] using
      adaptiveN10239MinusP016Norm2542
  · simpa only [adaptiveN10239MinusValue2542, adaptiveN10239MinusError2542] using
      adaptiveN10239MinusP017Norm2542
  · simpa only [adaptiveN10239MinusValue2542, adaptiveN10239MinusError2542] using
      adaptiveN10239MinusP018Norm2542
  · simpa only [adaptiveN10239MinusValue2542, adaptiveN10239MinusError2542] using
      adaptiveN10239MinusP019Norm2542
  · simpa only [adaptiveN10239MinusValue2542, adaptiveN10239MinusError2542] using
      adaptiveN10239MinusP020Norm2542
  · simpa only [adaptiveN10239MinusValue2542, adaptiveN10239MinusError2542] using
      adaptiveN10239MinusP021Norm2542
  · simpa only [adaptiveN10239MinusValue2542, adaptiveN10239MinusError2542] using
      adaptiveN10239MinusP022Norm2542
  · simpa only [adaptiveN10239MinusValue2542, adaptiveN10239MinusError2542] using
      adaptiveN10239MinusP023Norm2542
  · simpa only [adaptiveN10239MinusValue2542, adaptiveN10239MinusError2542] using
      adaptiveN10239MinusP024Norm2542
  · simpa only [adaptiveN10239MinusValue2542, adaptiveN10239MinusError2542] using
      adaptiveN10239MinusP025Norm2542
  · simpa only [adaptiveN10239MinusValue2542, adaptiveN10239MinusError2542] using
      adaptiveN10239MinusP026Norm2542
  · simpa only [adaptiveN10239MinusValue2542, adaptiveN10239MinusError2542] using
      adaptiveN10239MinusP027Norm2542
  · simpa only [adaptiveN10239MinusValue2542, adaptiveN10239MinusError2542] using
      adaptiveN10239MinusP028Norm2542
  · simpa only [adaptiveN10239MinusValue2542, adaptiveN10239MinusError2542] using
      adaptiveN10239MinusP029Norm2542

noncomputable def adaptiveN10239MinusSumValue2542 : ℂ := ⟨(0 : ℝ),
    (0 : ℝ)⟩

noncomputable def adaptiveN10239MinusUpper2542 : ℝ := ((1 : ℝ) /
        5000000000)

theorem adaptiveN10239MinusSum_eq2542 :
    (∑ i : Fin 30, baseCoefficientCenter2540 i * adaptiveN10239MinusValue2542 i) =
      adaptiveN10239MinusSumValue2542 := by
  rw [sum30_chain2541]
  apply Complex.ext <;>
    norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, adaptiveN10239MinusValue2542,
      adaptiveN10239MinusSumValue2542, embedPair2542, adaptiveN10239MinusP000Output2542,
      adaptiveN10239MinusP001Output2542,
      adaptiveN10239MinusP002Output2542,
      adaptiveN10239MinusP003Output2542,
      adaptiveN10239MinusP004Output2542,
      adaptiveN10239MinusP005Output2542,
      adaptiveN10239MinusP006Output2542,
      adaptiveN10239MinusP007Output2542,
      adaptiveN10239MinusP008Output2542,
      adaptiveN10239MinusP009Output2542,
      adaptiveN10239MinusP010Output2542,
      adaptiveN10239MinusP011Output2542,
      adaptiveN10239MinusP012Output2542,
      adaptiveN10239MinusP013Output2542,
      adaptiveN10239MinusP014Output2542,
      adaptiveN10239MinusP015Output2542,
      adaptiveN10239MinusP016Output2542,
      adaptiveN10239MinusP017Output2542,
      adaptiveN10239MinusP018Output2542,
      adaptiveN10239MinusP019Output2542,
      adaptiveN10239MinusP020Output2542,
      adaptiveN10239MinusP021Output2542,
      adaptiveN10239MinusP022Output2542,
      adaptiveN10239MinusP023Output2542,
      adaptiveN10239MinusP024Output2542,
      adaptiveN10239MinusP025Output2542,
      adaptiveN10239MinusP026Output2542,
      adaptiveN10239MinusP027Output2542,
      adaptiveN10239MinusP028Output2542,
      adaptiveN10239MinusP029Output2542, Complex.mul_re, Complex.mul_im]

theorem adaptiveN10239MinusSum_norm2542 :
    ‖∑ i : Fin 30, baseCoefficientCenter2540 i * adaptiveN10239MinusValue2542 i‖ ≤
      ((1 : ℝ) /
        10000000000) := by
  rw [adaptiveN10239MinusSum_eq2542]
  apply complex_norm_le_of_sq2541 _ _ (by norm_num)
  norm_num [adaptiveN10239MinusSumValue2542]

theorem adaptiveN10239MinusEvaluation_charge2542 :
    (∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
      |(baseCoefficientCenter2540 i).im|) * adaptiveN10239MinusError2542 i) ≤ (1 : ℝ)/10^12 := by
  rw [sum30_chain2541]
  norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, adaptiveN10239MinusError2542,
      adaptiveN10239MinusP000Output2542,
      adaptiveN10239MinusP001Output2542,
      adaptiveN10239MinusP002Output2542,
      adaptiveN10239MinusP003Output2542,
      adaptiveN10239MinusP004Output2542,
      adaptiveN10239MinusP005Output2542,
      adaptiveN10239MinusP006Output2542,
      adaptiveN10239MinusP007Output2542,
      adaptiveN10239MinusP008Output2542,
      adaptiveN10239MinusP009Output2542,
      adaptiveN10239MinusP010Output2542,
      adaptiveN10239MinusP011Output2542,
      adaptiveN10239MinusP012Output2542,
      adaptiveN10239MinusP013Output2542,
      adaptiveN10239MinusP014Output2542,
      adaptiveN10239MinusP015Output2542,
      adaptiveN10239MinusP016Output2542,
      adaptiveN10239MinusP017Output2542,
      adaptiveN10239MinusP018Output2542,
      adaptiveN10239MinusP019Output2542,
      adaptiveN10239MinusP020Output2542,
      adaptiveN10239MinusP021Output2542,
      adaptiveN10239MinusP022Output2542,
      adaptiveN10239MinusP023Output2542,
      adaptiveN10239MinusP024Output2542,
      adaptiveN10239MinusP025Output2542,
      adaptiveN10239MinusP026Output2542,
      adaptiveN10239MinusP027Output2542,
      adaptiveN10239MinusP028Output2542,
      adaptiveN10239MinusP029Output2542]

theorem adaptiveN10239MinusSigned_le2542 :
    signedJetUpper2539 0 ((((-1) : ℝ) /
        2)) baseCoefficientCenter2540 baseCoefficientError2540
      nodeModulation2541 adaptiveN10239MinusPosition2542 ≤ adaptiveN10239MinusUpper2542 := by
  have hsum :
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i *
        weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 i adaptiveN10239MinusPosition2542‖ ≤
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i * adaptiveN10239MinusValue2542 i‖ +
        ∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
          |(baseCoefficientCenter2540 i).im|) * adaptiveN10239MinusError2542 i := by
    apply norm_sum_le_center_sum_add_error2531
    intro i _
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (Complex.norm_le_abs_re_add_abs_im _) (adaptiveN10239MinusExp_error2542 i)
      (norm_nonneg _) (by positivity)
  have heach : ∀ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 i adaptiveN10239MinusPosition2542‖ ≤
        (1 : ℝ)/10^30 := by
    intro i
    have h := mul_le_mul_of_nonneg_left (adaptiveN10239MinusUnit_norm2542 i)
      (by norm_num [baseCoefficientError2540] : 0 ≤ baseCoefficientError2540 i)
    simpa [baseCoefficientError2540] using h
  have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
  have he' : (∑ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 i adaptiveN10239MinusPosition2542‖) ≤
        (30 : ℝ)/10^30 := by simpa using he
  unfold signedJetUpper2539 adaptiveN10239MinusUpper2542
  linarith [adaptiveN10239MinusSum_norm2542, adaptiveN10239MinusEvaluation_charge2542]

theorem adaptiveN10239MinusPhysical_le2542 (coefficients : Fin 30 → ℂ)
    (hbox : ∀ i, (baseCoefficientBox2540 i).Mem (coefficients i)) :
    ‖weightedPhysical2539 ((((-1) : ℝ) /
        2)) coefficients nodeModulation2541 adaptiveN10239MinusPosition2542‖ ≤
      adaptiveN10239MinusUpper2542 := by
  have h := weightedPhysical2539_jet_le_center_error 0 ((((-1) : ℝ) /
        2)) coefficients
    baseCoefficientCenter2540 baseCoefficientError2540 nodeModulation2541
    (fun i => baseCoefficient_error_of_box2540 i (coefficients i) (hbox i))
        adaptiveN10239MinusPosition2542
  simpa only [iteratedDeriv_zero] using h.trans adaptiveN10239MinusSigned_le2542

theorem adaptiveN10239MinusGrid2542 :
    -stripRadius2303 + (10239 : ℝ)*(2*stripRadius2303/10240) = adaptiveN10239MinusPosition2542 :=
        by
  norm_num [stripRadius2303, adaptiveN10239MinusPosition2542]

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.adaptiveN10239MinusSigned_le2542
#print axioms ConnesWeilRH.Dev.adaptiveN10239MinusPhysical_le2542
