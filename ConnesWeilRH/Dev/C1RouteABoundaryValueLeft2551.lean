import ConnesWeilRH.Dev.C1RouteACompactExp2542
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541

namespace ConnesWeilRH.Dev

open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def adaptiveN02700PlusPosition2542 : ℝ := (((-7929856121) : ℝ) /
        2560000000)

def adaptiveN02700PlusP000Output2542 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem adaptiveN02700PlusP000Zero2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ adaptiveN02700PlusPosition2542 = 0 := by
  have hx : ¬ |adaptiveN02700PlusPosition2542| < storedWidth ⟨0, by omega⟩ ^ 2 := by
    norm_num [adaptiveN02700PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero, weightedFunction2348,
    externalFamilyValue2344, if_neg hx, mul_zero]

theorem adaptiveN02700PlusP000Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ adaptiveN02700PlusPosition2542 - embedPair2542
            adaptiveN02700PlusP000Output2542.1‖ ≤ (adaptiveN02700PlusP000Output2542.2 : ℝ) := by
  have hz : embedPair2542 adaptiveN02700PlusP000Output2542.1 = 0 := by
    apply Complex.ext <;> norm_num [adaptiveN02700PlusP000Output2542, embedPair2542]
  rw [adaptiveN02700PlusP000Zero2542, hz]
  norm_num [adaptiveN02700PlusP000Output2542]

theorem adaptiveN02700PlusP000Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ adaptiveN02700PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN02700PlusP000Zero2542]
  norm_num

def adaptiveN02700PlusP001Output2542 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

def adaptiveN02700PlusP001Input2542 : RatPair2542 :=
  ((((-(6802033789088462436296480399940728088864 * 10^40
        + 8972281175305676998687477935786509916481)) : ℚ) /
        ((1 * 10^40
        + 8752578370474248106975932892819564741070) * 10^40
        + 9992275832742435204355224137891840000000)),
    ((43806833004475480685705509 : ℚ) /
        184467440737095516160000000))

theorem adaptiveN02700PlusP001Compute2542 : compactExp2542 adaptiveN02700PlusP001Input2542 9 =
    adaptiveN02700PlusP001Output2542 := by
  cbv

theorem adaptiveN02700PlusP001Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ adaptiveN02700PlusPosition2542 =
    Complex.exp ((2 : ℂ)^9 * embedPair2542 adaptiveN02700PlusP001Input2542) := by
  have hx : |adaptiveN02700PlusPosition2542| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [adaptiveN02700PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN02700PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN02700PlusP001Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN02700PlusP001Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ adaptiveN02700PlusPosition2542 - embedPair2542
            adaptiveN02700PlusP001Output2542.1‖ ≤ (adaptiveN02700PlusP001Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN02700PlusP001Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN02700PlusP001Input2542]
  rw [adaptiveN02700PlusP001Owner2542]
  have h := compactExp_error2542 adaptiveN02700PlusP001Input2542 hz 9
  simpa only [adaptiveN02700PlusP001Compute2542] using h

theorem adaptiveN02700PlusP001Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ adaptiveN02700PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN02700PlusP001Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN02700PlusP001Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN02700PlusP002Output2542 : RatState2542 :=
  (((((-297) : ℚ) /
        1267650600228229401496703205376),
    (((-401) : ℚ) /
        1267650600228229401496703205376)),
    ((1099511627777 : ℚ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888)))

def adaptiveN02700PlusP002Input2542 : RatPair2542 :=
  ((((-((18 * 10^40
        + 674198634096258458583628358041758074204) * 10^40
        + 9347881399256746042719324903889090304321)) : ℚ) /
        ((73 * 10^40
        + 2973526485978139422317359752257065937823) * 10^40
        + 6716006270187613354841793103134720000000)),
    (((-43806833004475480685705509) : ℚ) /
        92233720368547758080000000))

theorem adaptiveN02700PlusP002Compute2542 : compactExp2542 adaptiveN02700PlusP002Input2542 8 =
    adaptiveN02700PlusP002Output2542 := by
  cbv

theorem adaptiveN02700PlusP002Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ adaptiveN02700PlusPosition2542 =
    Complex.exp ((2 : ℂ)^8 * embedPair2542 adaptiveN02700PlusP002Input2542) := by
  have hx : |adaptiveN02700PlusPosition2542| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [adaptiveN02700PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN02700PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN02700PlusP002Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN02700PlusP002Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ adaptiveN02700PlusPosition2542 - embedPair2542
            adaptiveN02700PlusP002Output2542.1‖ ≤ (adaptiveN02700PlusP002Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN02700PlusP002Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN02700PlusP002Input2542]
  rw [adaptiveN02700PlusP002Owner2542]
  have h := compactExp_error2542 adaptiveN02700PlusP002Input2542 hz 8
  simpa only [adaptiveN02700PlusP002Compute2542] using h

theorem adaptiveN02700PlusP002Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ adaptiveN02700PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN02700PlusP002Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN02700PlusP002Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN02700PlusP003Output2542 : RatState2542 :=
  (((((-1323141729) : ℚ) /
        316912650057057350374175801344),
    (((-3576065449) : ℚ) /
        633825300114114700748351602688)),
    ((549763514509 : ℚ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944)))

def adaptiveN02700PlusP003Input2542 : RatPair2542 :=
  ((((-((2408 * 10^40
        + 369770750836432817481799749086268690782) * 10^40
        + 3306951315371206135663408401255839432267)) : ℚ) /
        ((13284 * 10^40
        + 922703065279921881810676711054660831348) * 10^40
        + 9952512674799299317166344800829440000000)),
    (((-43806833004475480685705509) : ℚ) /
        92233720368547758080000000))

theorem adaptiveN02700PlusP003Compute2542 : compactExp2542 adaptiveN02700PlusP003Input2542 8 =
    adaptiveN02700PlusP003Output2542 := by
  cbv

theorem adaptiveN02700PlusP003Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ adaptiveN02700PlusPosition2542 =
    Complex.exp ((2 : ℂ)^8 * embedPair2542 adaptiveN02700PlusP003Input2542) := by
  have hx : |adaptiveN02700PlusPosition2542| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [adaptiveN02700PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN02700PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN02700PlusP003Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN02700PlusP003Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ adaptiveN02700PlusPosition2542 - embedPair2542
            adaptiveN02700PlusP003Output2542.1‖ ≤ (adaptiveN02700PlusP003Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN02700PlusP003Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN02700PlusP003Input2542]
  rw [adaptiveN02700PlusP003Owner2542]
  have h := compactExp_error2542 adaptiveN02700PlusP003Input2542 hz 8
  simpa only [adaptiveN02700PlusP003Compute2542] using h

theorem adaptiveN02700PlusP003Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ adaptiveN02700PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN02700PlusP003Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN02700PlusP003Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN02700PlusP004Output2542 : RatState2542 :=
  (((((-1339330122569) : ℚ) /
        633825300114114700748351602688),
    ((3619817946177 : ℚ) /
        1267650600228229401496703205376)),
    ((2214238077055 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

def adaptiveN02700PlusP004Input2542 : RatPair2542 :=
  ((((-((42 * 10^40
        + 612804092845883320592175325793232154346) * 10^40
        + 2807937213934500805991847895100027804321)) : ℚ) /
        ((267 * 10^40
        + 9934518708431604868451190036789843840469) * 10^40
        + 7242920599205959594841793103134720000000)),
    ((43806833004475480685705509 : ℚ) /
        92233720368547758080000000))

theorem adaptiveN02700PlusP004Compute2542 : compactExp2542 adaptiveN02700PlusP004Input2542 8 =
    adaptiveN02700PlusP004Output2542 := by
  cbv

theorem adaptiveN02700PlusP004Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ adaptiveN02700PlusPosition2542 =
    Complex.exp ((2 : ℂ)^8 * embedPair2542 adaptiveN02700PlusP004Input2542) := by
  have hx : |adaptiveN02700PlusPosition2542| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [adaptiveN02700PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN02700PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN02700PlusP004Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN02700PlusP004Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ adaptiveN02700PlusPosition2542 - embedPair2542
            adaptiveN02700PlusP004Output2542.1‖ ≤ (adaptiveN02700PlusP004Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN02700PlusP004Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN02700PlusP004Input2542]
  rw [adaptiveN02700PlusP004Owner2542]
  have h := compactExp_error2542 adaptiveN02700PlusP004Input2542 hz 8
  simpa only [adaptiveN02700PlusP004Compute2542] using h

theorem adaptiveN02700PlusP004Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ adaptiveN02700PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN02700PlusP004Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN02700PlusP004Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN02700PlusP005Output2542 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem adaptiveN02700PlusP005Zero2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ adaptiveN02700PlusPosition2542 = 0 := by
  have hx : ¬ |adaptiveN02700PlusPosition2542| < storedWidth ⟨5, by omega⟩ ^ 2 := by
    norm_num [adaptiveN02700PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero, weightedFunction2348,
    externalFamilyValue2344, if_neg hx, mul_zero]

theorem adaptiveN02700PlusP005Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ adaptiveN02700PlusPosition2542 - embedPair2542
            adaptiveN02700PlusP005Output2542.1‖ ≤ (adaptiveN02700PlusP005Output2542.2 : ℝ) := by
  have hz : embedPair2542 adaptiveN02700PlusP005Output2542.1 = 0 := by
    apply Complex.ext <;> norm_num [adaptiveN02700PlusP005Output2542, embedPair2542]
  rw [adaptiveN02700PlusP005Zero2542, hz]
  norm_num [adaptiveN02700PlusP005Output2542]

theorem adaptiveN02700PlusP005Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ adaptiveN02700PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN02700PlusP005Zero2542]
  norm_num

def adaptiveN02700PlusP006Output2542 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

def adaptiveN02700PlusP006Input2542 : RatPair2542 :=
  ((((-5479660975716824374691255046813) : ℚ) /
        9169574712713507276718080000000),
    ((0 : ℚ) /
        1))

theorem adaptiveN02700PlusP006Compute2542 : compactExp2542 adaptiveN02700PlusP006Input2542 7 =
    adaptiveN02700PlusP006Output2542 := by
  cbv

theorem adaptiveN02700PlusP006Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ adaptiveN02700PlusPosition2542 =
    Complex.exp ((2 : ℂ)^7 * embedPair2542 adaptiveN02700PlusP006Input2542) := by
  have hx : |adaptiveN02700PlusPosition2542| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [adaptiveN02700PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN02700PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN02700PlusP006Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN02700PlusP006Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ adaptiveN02700PlusPosition2542 - embedPair2542
            adaptiveN02700PlusP006Output2542.1‖ ≤ (adaptiveN02700PlusP006Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN02700PlusP006Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN02700PlusP006Input2542]
  rw [adaptiveN02700PlusP006Owner2542]
  have h := compactExp_error2542 adaptiveN02700PlusP006Input2542 hz 7
  simpa only [adaptiveN02700PlusP006Compute2542] using h

theorem adaptiveN02700PlusP006Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ adaptiveN02700PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN02700PlusP006Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN02700PlusP006Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN02700PlusP007Output2542 : RatState2542 :=
  ((((4448714447 : ℚ) /
        633825300114114700748351602688),
    ((0 : ℚ) /
        1)),
    ((1099512274383 : ℚ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888)))

def adaptiveN02700PlusP007Input2542 : RatPair2542 :=
  ((((-((2408 * 10^40
        + 369770750836432817481799749086268690782) * 10^40
        + 3306951315371206135663408401255839432267)) : ℚ) /
        ((3321 * 10^40
        + 230675766319980470452669177763665207837) * 10^40
        + 2488128168699824829291586200207360000000)),
    ((0 : ℚ) /
        1))

theorem adaptiveN02700PlusP007Compute2542 : compactExp2542 adaptiveN02700PlusP007Input2542 6 =
    adaptiveN02700PlusP007Output2542 := by
  cbv

theorem adaptiveN02700PlusP007Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ adaptiveN02700PlusPosition2542 =
    Complex.exp ((2 : ℂ)^6 * embedPair2542 adaptiveN02700PlusP007Input2542) := by
  have hx : |adaptiveN02700PlusPosition2542| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [adaptiveN02700PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN02700PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN02700PlusP007Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN02700PlusP007Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ adaptiveN02700PlusPosition2542 - embedPair2542
            adaptiveN02700PlusP007Output2542.1‖ ≤ (adaptiveN02700PlusP007Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN02700PlusP007Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN02700PlusP007Input2542]
  rw [adaptiveN02700PlusP007Owner2542]
  have h := compactExp_error2542 adaptiveN02700PlusP007Input2542 hz 6
  simpa only [adaptiveN02700PlusP007Compute2542] using h

theorem adaptiveN02700PlusP007Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ adaptiveN02700PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN02700PlusP007Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN02700PlusP007Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN02700PlusP008Output2542 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem adaptiveN02700PlusP008Zero2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ adaptiveN02700PlusPosition2542 = 0 := by
  have hx : ¬ |adaptiveN02700PlusPosition2542| < storedWidth ⟨8, by omega⟩ ^ 2 := by
    norm_num [adaptiveN02700PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero, weightedFunction2348,
    externalFamilyValue2344, if_neg hx, mul_zero]

theorem adaptiveN02700PlusP008Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ adaptiveN02700PlusPosition2542 - embedPair2542
            adaptiveN02700PlusP008Output2542.1‖ ≤ (adaptiveN02700PlusP008Output2542.2 : ℝ) := by
  have hz : embedPair2542 adaptiveN02700PlusP008Output2542.1 = 0 := by
    apply Complex.ext <;> norm_num [adaptiveN02700PlusP008Output2542, embedPair2542]
  rw [adaptiveN02700PlusP008Zero2542, hz]
  norm_num [adaptiveN02700PlusP008Output2542]

theorem adaptiveN02700PlusP008Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ adaptiveN02700PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN02700PlusP008Zero2542]
  norm_num

def adaptiveN02700PlusP009Output2542 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem adaptiveN02700PlusP009Zero2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ adaptiveN02700PlusPosition2542 = 0 := by
  have hx : ¬ |adaptiveN02700PlusPosition2542| < storedWidth ⟨9, by omega⟩ ^ 2 := by
    norm_num [adaptiveN02700PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero, weightedFunction2348,
    externalFamilyValue2344, if_neg hx, mul_zero]

theorem adaptiveN02700PlusP009Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ adaptiveN02700PlusPosition2542 - embedPair2542
            adaptiveN02700PlusP009Output2542.1‖ ≤ (adaptiveN02700PlusP009Output2542.2 : ℝ) := by
  have hz : embedPair2542 adaptiveN02700PlusP009Output2542.1 = 0 := by
    apply Complex.ext <;> norm_num [adaptiveN02700PlusP009Output2542, embedPair2542]
  rw [adaptiveN02700PlusP009Zero2542, hz]
  norm_num [adaptiveN02700PlusP009Output2542]

theorem adaptiveN02700PlusP009Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ adaptiveN02700PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN02700PlusP009Zero2542]
  norm_num

def adaptiveN02700PlusP010Output2542 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem adaptiveN02700PlusP010Zero2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ adaptiveN02700PlusPosition2542 = 0 := by
  have hx : ¬ |adaptiveN02700PlusPosition2542| < storedWidth ⟨10, by omega⟩ ^ 2 := by
    norm_num [adaptiveN02700PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero, weightedFunction2348,
    externalFamilyValue2344, if_neg hx, mul_zero]

theorem adaptiveN02700PlusP010Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ adaptiveN02700PlusPosition2542 - embedPair2542
            adaptiveN02700PlusP010Output2542.1‖ ≤ (adaptiveN02700PlusP010Output2542.2 : ℝ) := by
  have hz : embedPair2542 adaptiveN02700PlusP010Output2542.1 = 0 := by
    apply Complex.ext <;> norm_num [adaptiveN02700PlusP010Output2542, embedPair2542]
  rw [adaptiveN02700PlusP010Zero2542, hz]
  norm_num [adaptiveN02700PlusP010Output2542]

theorem adaptiveN02700PlusP010Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ adaptiveN02700PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN02700PlusP010Zero2542]
  norm_num

def adaptiveN02700PlusP011Output2542 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem adaptiveN02700PlusP011Zero2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ adaptiveN02700PlusPosition2542 = 0 := by
  have hx : ¬ |adaptiveN02700PlusPosition2542| < storedWidth ⟨11, by omega⟩ ^ 2 := by
    norm_num [adaptiveN02700PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero, weightedFunction2348,
    externalFamilyValue2344, if_neg hx, mul_zero]

theorem adaptiveN02700PlusP011Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ adaptiveN02700PlusPosition2542 - embedPair2542
            adaptiveN02700PlusP011Output2542.1‖ ≤ (adaptiveN02700PlusP011Output2542.2 : ℝ) := by
  have hz : embedPair2542 adaptiveN02700PlusP011Output2542.1 = 0 := by
    apply Complex.ext <;> norm_num [adaptiveN02700PlusP011Output2542, embedPair2542]
  rw [adaptiveN02700PlusP011Zero2542, hz]
  norm_num [adaptiveN02700PlusP011Output2542]

theorem adaptiveN02700PlusP011Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ adaptiveN02700PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN02700PlusP011Zero2542]
  norm_num

def adaptiveN02700PlusP012Output2542 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem adaptiveN02700PlusP012Zero2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ adaptiveN02700PlusPosition2542 = 0 := by
  have hx : ¬ |adaptiveN02700PlusPosition2542| < storedWidth ⟨12, by omega⟩ ^ 2 := by
    norm_num [adaptiveN02700PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero, weightedFunction2348,
    externalFamilyValue2344, if_neg hx, mul_zero]

theorem adaptiveN02700PlusP012Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ adaptiveN02700PlusPosition2542 - embedPair2542
            adaptiveN02700PlusP012Output2542.1‖ ≤ (adaptiveN02700PlusP012Output2542.2 : ℝ) := by
  have hz : embedPair2542 adaptiveN02700PlusP012Output2542.1 = 0 := by
    apply Complex.ext <;> norm_num [adaptiveN02700PlusP012Output2542, embedPair2542]
  rw [adaptiveN02700PlusP012Zero2542, hz]
  norm_num [adaptiveN02700PlusP012Output2542]

theorem adaptiveN02700PlusP012Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ adaptiveN02700PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN02700PlusP012Zero2542]
  norm_num

def adaptiveN02700PlusP013Output2542 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem adaptiveN02700PlusP013Zero2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ adaptiveN02700PlusPosition2542 = 0 := by
  have hx : ¬ |adaptiveN02700PlusPosition2542| < storedWidth ⟨13, by omega⟩ ^ 2 := by
    norm_num [adaptiveN02700PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero, weightedFunction2348,
    externalFamilyValue2344, if_neg hx, mul_zero]

theorem adaptiveN02700PlusP013Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ adaptiveN02700PlusPosition2542 - embedPair2542
            adaptiveN02700PlusP013Output2542.1‖ ≤ (adaptiveN02700PlusP013Output2542.2 : ℝ) := by
  have hz : embedPair2542 adaptiveN02700PlusP013Output2542.1 = 0 := by
    apply Complex.ext <;> norm_num [adaptiveN02700PlusP013Output2542, embedPair2542]
  rw [adaptiveN02700PlusP013Zero2542, hz]
  norm_num [adaptiveN02700PlusP013Output2542]

theorem adaptiveN02700PlusP013Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ adaptiveN02700PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN02700PlusP013Zero2542]
  norm_num

def adaptiveN02700PlusP014Output2542 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem adaptiveN02700PlusP014Zero2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ adaptiveN02700PlusPosition2542 = 0 := by
  have hx : ¬ |adaptiveN02700PlusPosition2542| < storedWidth ⟨14, by omega⟩ ^ 2 := by
    norm_num [adaptiveN02700PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero, weightedFunction2348,
    externalFamilyValue2344, if_neg hx, mul_zero]

theorem adaptiveN02700PlusP014Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ adaptiveN02700PlusPosition2542 - embedPair2542
            adaptiveN02700PlusP014Output2542.1‖ ≤ (adaptiveN02700PlusP014Output2542.2 : ℝ) := by
  have hz : embedPair2542 adaptiveN02700PlusP014Output2542.1 = 0 := by
    apply Complex.ext <;> norm_num [adaptiveN02700PlusP014Output2542, embedPair2542]
  rw [adaptiveN02700PlusP014Zero2542, hz]
  norm_num [adaptiveN02700PlusP014Output2542]

theorem adaptiveN02700PlusP014Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ adaptiveN02700PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN02700PlusP014Zero2542]
  norm_num

def adaptiveN02700PlusP015Output2542 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem adaptiveN02700PlusP015Zero2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ adaptiveN02700PlusPosition2542 = 0 := by
  have hx : ¬ |adaptiveN02700PlusPosition2542| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [adaptiveN02700PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero, weightedFunction2348,
    externalFamilyValue2344, if_neg hx, mul_zero]

theorem adaptiveN02700PlusP015Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ adaptiveN02700PlusPosition2542 - embedPair2542
            adaptiveN02700PlusP015Output2542.1‖ ≤ (adaptiveN02700PlusP015Output2542.2 : ℝ) := by
  have hz : embedPair2542 adaptiveN02700PlusP015Output2542.1 = 0 := by
    apply Complex.ext <;> norm_num [adaptiveN02700PlusP015Output2542, embedPair2542]
  rw [adaptiveN02700PlusP015Zero2542, hz]
  norm_num [adaptiveN02700PlusP015Output2542]

theorem adaptiveN02700PlusP015Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ adaptiveN02700PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN02700PlusP015Zero2542]
  norm_num

def adaptiveN02700PlusP016Output2542 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem adaptiveN02700PlusP016Zero2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ adaptiveN02700PlusPosition2542 = 0 := by
  have hx : ¬ |adaptiveN02700PlusPosition2542| < storedWidth ⟨16, by omega⟩ ^ 2 := by
    norm_num [adaptiveN02700PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero, weightedFunction2348,
    externalFamilyValue2344, if_neg hx, mul_zero]

theorem adaptiveN02700PlusP016Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ adaptiveN02700PlusPosition2542 - embedPair2542
            adaptiveN02700PlusP016Output2542.1‖ ≤ (adaptiveN02700PlusP016Output2542.2 : ℝ) := by
  have hz : embedPair2542 adaptiveN02700PlusP016Output2542.1 = 0 := by
    apply Complex.ext <;> norm_num [adaptiveN02700PlusP016Output2542, embedPair2542]
  rw [adaptiveN02700PlusP016Zero2542, hz]
  norm_num [adaptiveN02700PlusP016Output2542]

theorem adaptiveN02700PlusP016Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ adaptiveN02700PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN02700PlusP016Zero2542]
  norm_num

def adaptiveN02700PlusP017Output2542 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem adaptiveN02700PlusP017Zero2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ adaptiveN02700PlusPosition2542 = 0 := by
  have hx : ¬ |adaptiveN02700PlusPosition2542| < storedWidth ⟨17, by omega⟩ ^ 2 := by
    norm_num [adaptiveN02700PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero, weightedFunction2348,
    externalFamilyValue2344, if_neg hx, mul_zero]

theorem adaptiveN02700PlusP017Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ adaptiveN02700PlusPosition2542 - embedPair2542
            adaptiveN02700PlusP017Output2542.1‖ ≤ (adaptiveN02700PlusP017Output2542.2 : ℝ) := by
  have hz : embedPair2542 adaptiveN02700PlusP017Output2542.1 = 0 := by
    apply Complex.ext <;> norm_num [adaptiveN02700PlusP017Output2542, embedPair2542]
  rw [adaptiveN02700PlusP017Zero2542, hz]
  norm_num [adaptiveN02700PlusP017Output2542]

theorem adaptiveN02700PlusP017Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ adaptiveN02700PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN02700PlusP017Zero2542]
  norm_num

def adaptiveN02700PlusP018Output2542 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem adaptiveN02700PlusP018Zero2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ adaptiveN02700PlusPosition2542 = 0 := by
  have hx : ¬ |adaptiveN02700PlusPosition2542| < storedWidth ⟨18, by omega⟩ ^ 2 := by
    norm_num [adaptiveN02700PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero, weightedFunction2348,
    externalFamilyValue2344, if_neg hx, mul_zero]

theorem adaptiveN02700PlusP018Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ adaptiveN02700PlusPosition2542 - embedPair2542
            adaptiveN02700PlusP018Output2542.1‖ ≤ (adaptiveN02700PlusP018Output2542.2 : ℝ) := by
  have hz : embedPair2542 adaptiveN02700PlusP018Output2542.1 = 0 := by
    apply Complex.ext <;> norm_num [adaptiveN02700PlusP018Output2542, embedPair2542]
  rw [adaptiveN02700PlusP018Zero2542, hz]
  norm_num [adaptiveN02700PlusP018Output2542]

theorem adaptiveN02700PlusP018Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ adaptiveN02700PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN02700PlusP018Zero2542]
  norm_num

def adaptiveN02700PlusP019Output2542 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem adaptiveN02700PlusP019Zero2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ adaptiveN02700PlusPosition2542 = 0 := by
  have hx : ¬ |adaptiveN02700PlusPosition2542| < storedWidth ⟨19, by omega⟩ ^ 2 := by
    norm_num [adaptiveN02700PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero, weightedFunction2348,
    externalFamilyValue2344, if_neg hx, mul_zero]

theorem adaptiveN02700PlusP019Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ adaptiveN02700PlusPosition2542 - embedPair2542
            adaptiveN02700PlusP019Output2542.1‖ ≤ (adaptiveN02700PlusP019Output2542.2 : ℝ) := by
  have hz : embedPair2542 adaptiveN02700PlusP019Output2542.1 = 0 := by
    apply Complex.ext <;> norm_num [adaptiveN02700PlusP019Output2542, embedPair2542]
  rw [adaptiveN02700PlusP019Zero2542, hz]
  norm_num [adaptiveN02700PlusP019Output2542]

theorem adaptiveN02700PlusP019Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ adaptiveN02700PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN02700PlusP019Zero2542]
  norm_num

def adaptiveN02700PlusP020Output2542 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem adaptiveN02700PlusP020Zero2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ adaptiveN02700PlusPosition2542 = 0 := by
  have hx : ¬ |adaptiveN02700PlusPosition2542| < storedWidth ⟨20, by omega⟩ ^ 2 := by
    norm_num [adaptiveN02700PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero, weightedFunction2348,
    externalFamilyValue2344, if_neg hx, mul_zero]

theorem adaptiveN02700PlusP020Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ adaptiveN02700PlusPosition2542 - embedPair2542
            adaptiveN02700PlusP020Output2542.1‖ ≤ (adaptiveN02700PlusP020Output2542.2 : ℝ) := by
  have hz : embedPair2542 adaptiveN02700PlusP020Output2542.1 = 0 := by
    apply Complex.ext <;> norm_num [adaptiveN02700PlusP020Output2542, embedPair2542]
  rw [adaptiveN02700PlusP020Zero2542, hz]
  norm_num [adaptiveN02700PlusP020Output2542]

theorem adaptiveN02700PlusP020Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ adaptiveN02700PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN02700PlusP020Zero2542]
  norm_num

def adaptiveN02700PlusP021Output2542 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem adaptiveN02700PlusP021Zero2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ adaptiveN02700PlusPosition2542 = 0 := by
  have hx : ¬ |adaptiveN02700PlusPosition2542| < storedWidth ⟨21, by omega⟩ ^ 2 := by
    norm_num [adaptiveN02700PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero, weightedFunction2348,
    externalFamilyValue2344, if_neg hx, mul_zero]

theorem adaptiveN02700PlusP021Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ adaptiveN02700PlusPosition2542 - embedPair2542
            adaptiveN02700PlusP021Output2542.1‖ ≤ (adaptiveN02700PlusP021Output2542.2 : ℝ) := by
  have hz : embedPair2542 adaptiveN02700PlusP021Output2542.1 = 0 := by
    apply Complex.ext <;> norm_num [adaptiveN02700PlusP021Output2542, embedPair2542]
  rw [adaptiveN02700PlusP021Zero2542, hz]
  norm_num [adaptiveN02700PlusP021Output2542]

theorem adaptiveN02700PlusP021Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ adaptiveN02700PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN02700PlusP021Zero2542]
  norm_num

def adaptiveN02700PlusP022Output2542 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem adaptiveN02700PlusP022Zero2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ adaptiveN02700PlusPosition2542 = 0 := by
  have hx : ¬ |adaptiveN02700PlusPosition2542| < storedWidth ⟨22, by omega⟩ ^ 2 := by
    norm_num [adaptiveN02700PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero, weightedFunction2348,
    externalFamilyValue2344, if_neg hx, mul_zero]

theorem adaptiveN02700PlusP022Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ adaptiveN02700PlusPosition2542 - embedPair2542
            adaptiveN02700PlusP022Output2542.1‖ ≤ (adaptiveN02700PlusP022Output2542.2 : ℝ) := by
  have hz : embedPair2542 adaptiveN02700PlusP022Output2542.1 = 0 := by
    apply Complex.ext <;> norm_num [adaptiveN02700PlusP022Output2542, embedPair2542]
  rw [adaptiveN02700PlusP022Zero2542, hz]
  norm_num [adaptiveN02700PlusP022Output2542]

theorem adaptiveN02700PlusP022Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ adaptiveN02700PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN02700PlusP022Zero2542]
  norm_num

def adaptiveN02700PlusP023Output2542 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem adaptiveN02700PlusP023Zero2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ adaptiveN02700PlusPosition2542 = 0 := by
  have hx : ¬ |adaptiveN02700PlusPosition2542| < storedWidth ⟨23, by omega⟩ ^ 2 := by
    norm_num [adaptiveN02700PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero, weightedFunction2348,
    externalFamilyValue2344, if_neg hx, mul_zero]

theorem adaptiveN02700PlusP023Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ adaptiveN02700PlusPosition2542 - embedPair2542
            adaptiveN02700PlusP023Output2542.1‖ ≤ (adaptiveN02700PlusP023Output2542.2 : ℝ) := by
  have hz : embedPair2542 adaptiveN02700PlusP023Output2542.1 = 0 := by
    apply Complex.ext <;> norm_num [adaptiveN02700PlusP023Output2542, embedPair2542]
  rw [adaptiveN02700PlusP023Zero2542, hz]
  norm_num [adaptiveN02700PlusP023Output2542]

theorem adaptiveN02700PlusP023Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ adaptiveN02700PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN02700PlusP023Zero2542]
  norm_num

def adaptiveN02700PlusP024Output2542 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem adaptiveN02700PlusP024Zero2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ adaptiveN02700PlusPosition2542 = 0 := by
  have hx : ¬ |adaptiveN02700PlusPosition2542| < storedWidth ⟨24, by omega⟩ ^ 2 := by
    norm_num [adaptiveN02700PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero, weightedFunction2348,
    externalFamilyValue2344, if_neg hx, mul_zero]

theorem adaptiveN02700PlusP024Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ adaptiveN02700PlusPosition2542 - embedPair2542
            adaptiveN02700PlusP024Output2542.1‖ ≤ (adaptiveN02700PlusP024Output2542.2 : ℝ) := by
  have hz : embedPair2542 adaptiveN02700PlusP024Output2542.1 = 0 := by
    apply Complex.ext <;> norm_num [adaptiveN02700PlusP024Output2542, embedPair2542]
  rw [adaptiveN02700PlusP024Zero2542, hz]
  norm_num [adaptiveN02700PlusP024Output2542]

theorem adaptiveN02700PlusP024Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ adaptiveN02700PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN02700PlusP024Zero2542]
  norm_num

def adaptiveN02700PlusP025Output2542 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem adaptiveN02700PlusP025Zero2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ adaptiveN02700PlusPosition2542 = 0 := by
  have hx : ¬ |adaptiveN02700PlusPosition2542| < storedWidth ⟨25, by omega⟩ ^ 2 := by
    norm_num [adaptiveN02700PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero, weightedFunction2348,
    externalFamilyValue2344, if_neg hx, mul_zero]

theorem adaptiveN02700PlusP025Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ adaptiveN02700PlusPosition2542 - embedPair2542
            adaptiveN02700PlusP025Output2542.1‖ ≤ (adaptiveN02700PlusP025Output2542.2 : ℝ) := by
  have hz : embedPair2542 adaptiveN02700PlusP025Output2542.1 = 0 := by
    apply Complex.ext <;> norm_num [adaptiveN02700PlusP025Output2542, embedPair2542]
  rw [adaptiveN02700PlusP025Zero2542, hz]
  norm_num [adaptiveN02700PlusP025Output2542]

theorem adaptiveN02700PlusP025Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ adaptiveN02700PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN02700PlusP025Zero2542]
  norm_num

def adaptiveN02700PlusP026Output2542 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem adaptiveN02700PlusP026Zero2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ adaptiveN02700PlusPosition2542 = 0 := by
  have hx : ¬ |adaptiveN02700PlusPosition2542| < storedWidth ⟨26, by omega⟩ ^ 2 := by
    norm_num [adaptiveN02700PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero, weightedFunction2348,
    externalFamilyValue2344, if_neg hx, mul_zero]

theorem adaptiveN02700PlusP026Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ adaptiveN02700PlusPosition2542 - embedPair2542
            adaptiveN02700PlusP026Output2542.1‖ ≤ (adaptiveN02700PlusP026Output2542.2 : ℝ) := by
  have hz : embedPair2542 adaptiveN02700PlusP026Output2542.1 = 0 := by
    apply Complex.ext <;> norm_num [adaptiveN02700PlusP026Output2542, embedPair2542]
  rw [adaptiveN02700PlusP026Zero2542, hz]
  norm_num [adaptiveN02700PlusP026Output2542]

theorem adaptiveN02700PlusP026Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ adaptiveN02700PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN02700PlusP026Zero2542]
  norm_num

def adaptiveN02700PlusP027Output2542 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem adaptiveN02700PlusP027Zero2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ adaptiveN02700PlusPosition2542 = 0 := by
  have hx : ¬ |adaptiveN02700PlusPosition2542| < storedWidth ⟨27, by omega⟩ ^ 2 := by
    norm_num [adaptiveN02700PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero, weightedFunction2348,
    externalFamilyValue2344, if_neg hx, mul_zero]

theorem adaptiveN02700PlusP027Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ adaptiveN02700PlusPosition2542 - embedPair2542
            adaptiveN02700PlusP027Output2542.1‖ ≤ (adaptiveN02700PlusP027Output2542.2 : ℝ) := by
  have hz : embedPair2542 adaptiveN02700PlusP027Output2542.1 = 0 := by
    apply Complex.ext <;> norm_num [adaptiveN02700PlusP027Output2542, embedPair2542]
  rw [adaptiveN02700PlusP027Zero2542, hz]
  norm_num [adaptiveN02700PlusP027Output2542]

theorem adaptiveN02700PlusP027Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ adaptiveN02700PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN02700PlusP027Zero2542]
  norm_num

def adaptiveN02700PlusP028Output2542 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem adaptiveN02700PlusP028Zero2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ adaptiveN02700PlusPosition2542 = 0 := by
  have hx : ¬ |adaptiveN02700PlusPosition2542| < storedWidth ⟨28, by omega⟩ ^ 2 := by
    norm_num [adaptiveN02700PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero, weightedFunction2348,
    externalFamilyValue2344, if_neg hx, mul_zero]

theorem adaptiveN02700PlusP028Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ adaptiveN02700PlusPosition2542 - embedPair2542
            adaptiveN02700PlusP028Output2542.1‖ ≤ (adaptiveN02700PlusP028Output2542.2 : ℝ) := by
  have hz : embedPair2542 adaptiveN02700PlusP028Output2542.1 = 0 := by
    apply Complex.ext <;> norm_num [adaptiveN02700PlusP028Output2542, embedPair2542]
  rw [adaptiveN02700PlusP028Zero2542, hz]
  norm_num [adaptiveN02700PlusP028Output2542]

theorem adaptiveN02700PlusP028Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ adaptiveN02700PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN02700PlusP028Zero2542]
  norm_num

def adaptiveN02700PlusP029Output2542 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem adaptiveN02700PlusP029Zero2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ adaptiveN02700PlusPosition2542 = 0 := by
  have hx : ¬ |adaptiveN02700PlusPosition2542| < storedWidth ⟨29, by omega⟩ ^ 2 := by
    norm_num [adaptiveN02700PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero, weightedFunction2348,
    externalFamilyValue2344, if_neg hx, mul_zero]

theorem adaptiveN02700PlusP029Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ adaptiveN02700PlusPosition2542 - embedPair2542
            adaptiveN02700PlusP029Output2542.1‖ ≤ (adaptiveN02700PlusP029Output2542.2 : ℝ) := by
  have hz : embedPair2542 adaptiveN02700PlusP029Output2542.1 = 0 := by
    apply Complex.ext <;> norm_num [adaptiveN02700PlusP029Output2542, embedPair2542]
  rw [adaptiveN02700PlusP029Zero2542, hz]
  norm_num [adaptiveN02700PlusP029Output2542]

theorem adaptiveN02700PlusP029Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ adaptiveN02700PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN02700PlusP029Zero2542]
  norm_num

noncomputable def adaptiveN02700PlusValue2542 (i : Fin 30) : ℂ :=
  match i.val with
  | 0 => embedPair2542 adaptiveN02700PlusP000Output2542.1
  | 1 => embedPair2542 adaptiveN02700PlusP001Output2542.1
  | 2 => embedPair2542 adaptiveN02700PlusP002Output2542.1
  | 3 => embedPair2542 adaptiveN02700PlusP003Output2542.1
  | 4 => embedPair2542 adaptiveN02700PlusP004Output2542.1
  | 5 => embedPair2542 adaptiveN02700PlusP005Output2542.1
  | 6 => embedPair2542 adaptiveN02700PlusP006Output2542.1
  | 7 => embedPair2542 adaptiveN02700PlusP007Output2542.1
  | 8 => embedPair2542 adaptiveN02700PlusP008Output2542.1
  | 9 => embedPair2542 adaptiveN02700PlusP009Output2542.1
  | 10 => embedPair2542 adaptiveN02700PlusP010Output2542.1
  | 11 => embedPair2542 adaptiveN02700PlusP011Output2542.1
  | 12 => embedPair2542 adaptiveN02700PlusP012Output2542.1
  | 13 => embedPair2542 adaptiveN02700PlusP013Output2542.1
  | 14 => embedPair2542 adaptiveN02700PlusP014Output2542.1
  | 15 => embedPair2542 adaptiveN02700PlusP015Output2542.1
  | 16 => embedPair2542 adaptiveN02700PlusP016Output2542.1
  | 17 => embedPair2542 adaptiveN02700PlusP017Output2542.1
  | 18 => embedPair2542 adaptiveN02700PlusP018Output2542.1
  | 19 => embedPair2542 adaptiveN02700PlusP019Output2542.1
  | 20 => embedPair2542 adaptiveN02700PlusP020Output2542.1
  | 21 => embedPair2542 adaptiveN02700PlusP021Output2542.1
  | 22 => embedPair2542 adaptiveN02700PlusP022Output2542.1
  | 23 => embedPair2542 adaptiveN02700PlusP023Output2542.1
  | 24 => embedPair2542 adaptiveN02700PlusP024Output2542.1
  | 25 => embedPair2542 adaptiveN02700PlusP025Output2542.1
  | 26 => embedPair2542 adaptiveN02700PlusP026Output2542.1
  | 27 => embedPair2542 adaptiveN02700PlusP027Output2542.1
  | 28 => embedPair2542 adaptiveN02700PlusP028Output2542.1
  | 29 => embedPair2542 adaptiveN02700PlusP029Output2542.1
  | _ => 0

noncomputable def adaptiveN02700PlusError2542 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => (adaptiveN02700PlusP000Output2542.2 : ℝ)
  | 1 => (adaptiveN02700PlusP001Output2542.2 : ℝ)
  | 2 => (adaptiveN02700PlusP002Output2542.2 : ℝ)
  | 3 => (adaptiveN02700PlusP003Output2542.2 : ℝ)
  | 4 => (adaptiveN02700PlusP004Output2542.2 : ℝ)
  | 5 => (adaptiveN02700PlusP005Output2542.2 : ℝ)
  | 6 => (adaptiveN02700PlusP006Output2542.2 : ℝ)
  | 7 => (adaptiveN02700PlusP007Output2542.2 : ℝ)
  | 8 => (adaptiveN02700PlusP008Output2542.2 : ℝ)
  | 9 => (adaptiveN02700PlusP009Output2542.2 : ℝ)
  | 10 => (adaptiveN02700PlusP010Output2542.2 : ℝ)
  | 11 => (adaptiveN02700PlusP011Output2542.2 : ℝ)
  | 12 => (adaptiveN02700PlusP012Output2542.2 : ℝ)
  | 13 => (adaptiveN02700PlusP013Output2542.2 : ℝ)
  | 14 => (adaptiveN02700PlusP014Output2542.2 : ℝ)
  | 15 => (adaptiveN02700PlusP015Output2542.2 : ℝ)
  | 16 => (adaptiveN02700PlusP016Output2542.2 : ℝ)
  | 17 => (adaptiveN02700PlusP017Output2542.2 : ℝ)
  | 18 => (adaptiveN02700PlusP018Output2542.2 : ℝ)
  | 19 => (adaptiveN02700PlusP019Output2542.2 : ℝ)
  | 20 => (adaptiveN02700PlusP020Output2542.2 : ℝ)
  | 21 => (adaptiveN02700PlusP021Output2542.2 : ℝ)
  | 22 => (adaptiveN02700PlusP022Output2542.2 : ℝ)
  | 23 => (adaptiveN02700PlusP023Output2542.2 : ℝ)
  | 24 => (adaptiveN02700PlusP024Output2542.2 : ℝ)
  | 25 => (adaptiveN02700PlusP025Output2542.2 : ℝ)
  | 26 => (adaptiveN02700PlusP026Output2542.2 : ℝ)
  | 27 => (adaptiveN02700PlusP027Output2542.2 : ℝ)
  | 28 => (adaptiveN02700PlusP028Output2542.2 : ℝ)
  | 29 => (adaptiveN02700PlusP029Output2542.2 : ℝ)
  | _ => 0

theorem adaptiveN02700PlusExp_error2542 (i : Fin 30) :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 i adaptiveN02700PlusPosition2542 - adaptiveN02700PlusValue2542 i‖ ≤
            adaptiveN02700PlusError2542 i := by
  fin_cases i
  · simpa only [adaptiveN02700PlusValue2542, adaptiveN02700PlusError2542] using
      adaptiveN02700PlusP000Error2542
  · simpa only [adaptiveN02700PlusValue2542, adaptiveN02700PlusError2542] using
      adaptiveN02700PlusP001Error2542
  · simpa only [adaptiveN02700PlusValue2542, adaptiveN02700PlusError2542] using
      adaptiveN02700PlusP002Error2542
  · simpa only [adaptiveN02700PlusValue2542, adaptiveN02700PlusError2542] using
      adaptiveN02700PlusP003Error2542
  · simpa only [adaptiveN02700PlusValue2542, adaptiveN02700PlusError2542] using
      adaptiveN02700PlusP004Error2542
  · simpa only [adaptiveN02700PlusValue2542, adaptiveN02700PlusError2542] using
      adaptiveN02700PlusP005Error2542
  · simpa only [adaptiveN02700PlusValue2542, adaptiveN02700PlusError2542] using
      adaptiveN02700PlusP006Error2542
  · simpa only [adaptiveN02700PlusValue2542, adaptiveN02700PlusError2542] using
      adaptiveN02700PlusP007Error2542
  · simpa only [adaptiveN02700PlusValue2542, adaptiveN02700PlusError2542] using
      adaptiveN02700PlusP008Error2542
  · simpa only [adaptiveN02700PlusValue2542, adaptiveN02700PlusError2542] using
      adaptiveN02700PlusP009Error2542
  · simpa only [adaptiveN02700PlusValue2542, adaptiveN02700PlusError2542] using
      adaptiveN02700PlusP010Error2542
  · simpa only [adaptiveN02700PlusValue2542, adaptiveN02700PlusError2542] using
      adaptiveN02700PlusP011Error2542
  · simpa only [adaptiveN02700PlusValue2542, adaptiveN02700PlusError2542] using
      adaptiveN02700PlusP012Error2542
  · simpa only [adaptiveN02700PlusValue2542, adaptiveN02700PlusError2542] using
      adaptiveN02700PlusP013Error2542
  · simpa only [adaptiveN02700PlusValue2542, adaptiveN02700PlusError2542] using
      adaptiveN02700PlusP014Error2542
  · simpa only [adaptiveN02700PlusValue2542, adaptiveN02700PlusError2542] using
      adaptiveN02700PlusP015Error2542
  · simpa only [adaptiveN02700PlusValue2542, adaptiveN02700PlusError2542] using
      adaptiveN02700PlusP016Error2542
  · simpa only [adaptiveN02700PlusValue2542, adaptiveN02700PlusError2542] using
      adaptiveN02700PlusP017Error2542
  · simpa only [adaptiveN02700PlusValue2542, adaptiveN02700PlusError2542] using
      adaptiveN02700PlusP018Error2542
  · simpa only [adaptiveN02700PlusValue2542, adaptiveN02700PlusError2542] using
      adaptiveN02700PlusP019Error2542
  · simpa only [adaptiveN02700PlusValue2542, adaptiveN02700PlusError2542] using
      adaptiveN02700PlusP020Error2542
  · simpa only [adaptiveN02700PlusValue2542, adaptiveN02700PlusError2542] using
      adaptiveN02700PlusP021Error2542
  · simpa only [adaptiveN02700PlusValue2542, adaptiveN02700PlusError2542] using
      adaptiveN02700PlusP022Error2542
  · simpa only [adaptiveN02700PlusValue2542, adaptiveN02700PlusError2542] using
      adaptiveN02700PlusP023Error2542
  · simpa only [adaptiveN02700PlusValue2542, adaptiveN02700PlusError2542] using
      adaptiveN02700PlusP024Error2542
  · simpa only [adaptiveN02700PlusValue2542, adaptiveN02700PlusError2542] using
      adaptiveN02700PlusP025Error2542
  · simpa only [adaptiveN02700PlusValue2542, adaptiveN02700PlusError2542] using
      adaptiveN02700PlusP026Error2542
  · simpa only [adaptiveN02700PlusValue2542, adaptiveN02700PlusError2542] using
      adaptiveN02700PlusP027Error2542
  · simpa only [adaptiveN02700PlusValue2542, adaptiveN02700PlusError2542] using
      adaptiveN02700PlusP028Error2542
  · simpa only [adaptiveN02700PlusValue2542, adaptiveN02700PlusError2542] using
      adaptiveN02700PlusP029Error2542

theorem adaptiveN02700PlusUnit_norm2542 (i : Fin 30) :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 i adaptiveN02700PlusPosition2542‖ ≤ 1 := by
  fin_cases i
  · simpa only [adaptiveN02700PlusValue2542, adaptiveN02700PlusError2542] using
      adaptiveN02700PlusP000Norm2542
  · simpa only [adaptiveN02700PlusValue2542, adaptiveN02700PlusError2542] using
      adaptiveN02700PlusP001Norm2542
  · simpa only [adaptiveN02700PlusValue2542, adaptiveN02700PlusError2542] using
      adaptiveN02700PlusP002Norm2542
  · simpa only [adaptiveN02700PlusValue2542, adaptiveN02700PlusError2542] using
      adaptiveN02700PlusP003Norm2542
  · simpa only [adaptiveN02700PlusValue2542, adaptiveN02700PlusError2542] using
      adaptiveN02700PlusP004Norm2542
  · simpa only [adaptiveN02700PlusValue2542, adaptiveN02700PlusError2542] using
      adaptiveN02700PlusP005Norm2542
  · simpa only [adaptiveN02700PlusValue2542, adaptiveN02700PlusError2542] using
      adaptiveN02700PlusP006Norm2542
  · simpa only [adaptiveN02700PlusValue2542, adaptiveN02700PlusError2542] using
      adaptiveN02700PlusP007Norm2542
  · simpa only [adaptiveN02700PlusValue2542, adaptiveN02700PlusError2542] using
      adaptiveN02700PlusP008Norm2542
  · simpa only [adaptiveN02700PlusValue2542, adaptiveN02700PlusError2542] using
      adaptiveN02700PlusP009Norm2542
  · simpa only [adaptiveN02700PlusValue2542, adaptiveN02700PlusError2542] using
      adaptiveN02700PlusP010Norm2542
  · simpa only [adaptiveN02700PlusValue2542, adaptiveN02700PlusError2542] using
      adaptiveN02700PlusP011Norm2542
  · simpa only [adaptiveN02700PlusValue2542, adaptiveN02700PlusError2542] using
      adaptiveN02700PlusP012Norm2542
  · simpa only [adaptiveN02700PlusValue2542, adaptiveN02700PlusError2542] using
      adaptiveN02700PlusP013Norm2542
  · simpa only [adaptiveN02700PlusValue2542, adaptiveN02700PlusError2542] using
      adaptiveN02700PlusP014Norm2542
  · simpa only [adaptiveN02700PlusValue2542, adaptiveN02700PlusError2542] using
      adaptiveN02700PlusP015Norm2542
  · simpa only [adaptiveN02700PlusValue2542, adaptiveN02700PlusError2542] using
      adaptiveN02700PlusP016Norm2542
  · simpa only [adaptiveN02700PlusValue2542, adaptiveN02700PlusError2542] using
      adaptiveN02700PlusP017Norm2542
  · simpa only [adaptiveN02700PlusValue2542, adaptiveN02700PlusError2542] using
      adaptiveN02700PlusP018Norm2542
  · simpa only [adaptiveN02700PlusValue2542, adaptiveN02700PlusError2542] using
      adaptiveN02700PlusP019Norm2542
  · simpa only [adaptiveN02700PlusValue2542, adaptiveN02700PlusError2542] using
      adaptiveN02700PlusP020Norm2542
  · simpa only [adaptiveN02700PlusValue2542, adaptiveN02700PlusError2542] using
      adaptiveN02700PlusP021Norm2542
  · simpa only [adaptiveN02700PlusValue2542, adaptiveN02700PlusError2542] using
      adaptiveN02700PlusP022Norm2542
  · simpa only [adaptiveN02700PlusValue2542, adaptiveN02700PlusError2542] using
      adaptiveN02700PlusP023Norm2542
  · simpa only [adaptiveN02700PlusValue2542, adaptiveN02700PlusError2542] using
      adaptiveN02700PlusP024Norm2542
  · simpa only [adaptiveN02700PlusValue2542, adaptiveN02700PlusError2542] using
      adaptiveN02700PlusP025Norm2542
  · simpa only [adaptiveN02700PlusValue2542, adaptiveN02700PlusError2542] using
      adaptiveN02700PlusP026Norm2542
  · simpa only [adaptiveN02700PlusValue2542, adaptiveN02700PlusError2542] using
      adaptiveN02700PlusP027Norm2542
  · simpa only [adaptiveN02700PlusValue2542, adaptiveN02700PlusError2542] using
      adaptiveN02700PlusP028Norm2542
  · simpa only [adaptiveN02700PlusValue2542, adaptiveN02700PlusError2542] using
      adaptiveN02700PlusP029Norm2542

noncomputable def adaptiveN02700PlusSumValue2542 : ℂ := ⟨(((((3 * 10^40
        + 6261305251041021615225772764220800640270) * 10^40
        + 8346452814848936073089356349033583840844) * 10^40
        + 6683630567631219230264152968226843256883) : ℝ) /
        (((43322963 * 10^40
        + 9706377321809127216272356828661943293027) * 10^40
        + 4713398703874344710345793446290035999960) * 10^40
        + 95377180907771737671271930809827721216)),
    (((((1 * 10^40
        + 3576088296198276419028758073130164222174) * 10^40
        + 4082813785632845222111684468574054789757) * 10^40
        + 4409315710918172396708936369349830616525) : ℝ) /
        (((43322963 * 10^40
        + 9706377321809127216272356828661943293027) * 10^40
        + 4713398703874344710345793446290035999960) * 10^40
        + 95377180907771737671271930809827721216))⟩

noncomputable def adaptiveN02700PlusUpper2542 : ℝ := ((179 : ℝ) /
        2000000000)

theorem adaptiveN02700PlusSum_eq2542 :
    (∑ i : Fin 30, baseCoefficientCenter2540 i * adaptiveN02700PlusValue2542 i) =
      adaptiveN02700PlusSumValue2542 := by
  rw [sum30_chain2541]
  apply Complex.ext <;>
    norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, adaptiveN02700PlusValue2542,
      adaptiveN02700PlusSumValue2542, embedPair2542, adaptiveN02700PlusP000Output2542,
      adaptiveN02700PlusP001Output2542,
      adaptiveN02700PlusP002Output2542,
      adaptiveN02700PlusP003Output2542,
      adaptiveN02700PlusP004Output2542,
      adaptiveN02700PlusP005Output2542,
      adaptiveN02700PlusP006Output2542,
      adaptiveN02700PlusP007Output2542,
      adaptiveN02700PlusP008Output2542,
      adaptiveN02700PlusP009Output2542,
      adaptiveN02700PlusP010Output2542,
      adaptiveN02700PlusP011Output2542,
      adaptiveN02700PlusP012Output2542,
      adaptiveN02700PlusP013Output2542,
      adaptiveN02700PlusP014Output2542,
      adaptiveN02700PlusP015Output2542,
      adaptiveN02700PlusP016Output2542,
      adaptiveN02700PlusP017Output2542,
      adaptiveN02700PlusP018Output2542,
      adaptiveN02700PlusP019Output2542,
      adaptiveN02700PlusP020Output2542,
      adaptiveN02700PlusP021Output2542,
      adaptiveN02700PlusP022Output2542,
      adaptiveN02700PlusP023Output2542,
      adaptiveN02700PlusP024Output2542,
      adaptiveN02700PlusP025Output2542,
      adaptiveN02700PlusP026Output2542,
      adaptiveN02700PlusP027Output2542,
      adaptiveN02700PlusP028Output2542,
      adaptiveN02700PlusP029Output2542, Complex.mul_re, Complex.mul_im]

theorem adaptiveN02700PlusSum_norm2542 :
    ‖∑ i : Fin 30, baseCoefficientCenter2540 i * adaptiveN02700PlusValue2542 i‖ ≤
      ((447 : ℝ) /
        5000000000) := by
  rw [adaptiveN02700PlusSum_eq2542]
  apply complex_norm_le_of_sq2541 _ _ (by norm_num)
  norm_num [adaptiveN02700PlusSumValue2542]

theorem adaptiveN02700PlusEvaluation_charge2542 :
    (∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
      |(baseCoefficientCenter2540 i).im|) * adaptiveN02700PlusError2542 i) ≤ (1 : ℝ)/10^12 := by
  rw [sum30_chain2541]
  norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, adaptiveN02700PlusError2542,
      adaptiveN02700PlusP000Output2542,
      adaptiveN02700PlusP001Output2542,
      adaptiveN02700PlusP002Output2542,
      adaptiveN02700PlusP003Output2542,
      adaptiveN02700PlusP004Output2542,
      adaptiveN02700PlusP005Output2542,
      adaptiveN02700PlusP006Output2542,
      adaptiveN02700PlusP007Output2542,
      adaptiveN02700PlusP008Output2542,
      adaptiveN02700PlusP009Output2542,
      adaptiveN02700PlusP010Output2542,
      adaptiveN02700PlusP011Output2542,
      adaptiveN02700PlusP012Output2542,
      adaptiveN02700PlusP013Output2542,
      adaptiveN02700PlusP014Output2542,
      adaptiveN02700PlusP015Output2542,
      adaptiveN02700PlusP016Output2542,
      adaptiveN02700PlusP017Output2542,
      adaptiveN02700PlusP018Output2542,
      adaptiveN02700PlusP019Output2542,
      adaptiveN02700PlusP020Output2542,
      adaptiveN02700PlusP021Output2542,
      adaptiveN02700PlusP022Output2542,
      adaptiveN02700PlusP023Output2542,
      adaptiveN02700PlusP024Output2542,
      adaptiveN02700PlusP025Output2542,
      adaptiveN02700PlusP026Output2542,
      adaptiveN02700PlusP027Output2542,
      adaptiveN02700PlusP028Output2542,
      adaptiveN02700PlusP029Output2542]

theorem adaptiveN02700PlusSigned_le2542 :
    signedJetUpper2539 0 (((1 : ℝ) /
        2)) baseCoefficientCenter2540 baseCoefficientError2540
      nodeModulation2541 adaptiveN02700PlusPosition2542 ≤ adaptiveN02700PlusUpper2542 := by
  have hsum :
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i *
        weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 i adaptiveN02700PlusPosition2542‖ ≤
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i * adaptiveN02700PlusValue2542 i‖ +
        ∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
          |(baseCoefficientCenter2540 i).im|) * adaptiveN02700PlusError2542 i := by
    apply norm_sum_le_center_sum_add_error2531
    intro i _
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (Complex.norm_le_abs_re_add_abs_im _) (adaptiveN02700PlusExp_error2542 i)
      (norm_nonneg _) (by positivity)
  have heach : ∀ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 i adaptiveN02700PlusPosition2542‖ ≤
        (1 : ℝ)/10^30 := by
    intro i
    have h := mul_le_mul_of_nonneg_left (adaptiveN02700PlusUnit_norm2542 i)
      (by norm_num [baseCoefficientError2540] : 0 ≤ baseCoefficientError2540 i)
    simpa [baseCoefficientError2540] using h
  have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
  have he' : (∑ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 i adaptiveN02700PlusPosition2542‖) ≤
        (30 : ℝ)/10^30 := by simpa using he
  unfold signedJetUpper2539 adaptiveN02700PlusUpper2542
  linarith [adaptiveN02700PlusSum_norm2542, adaptiveN02700PlusEvaluation_charge2542]

theorem adaptiveN02700PlusPhysical_le2542 (coefficients : Fin 30 → ℂ)
    (hbox : ∀ i, (baseCoefficientBox2540 i).Mem (coefficients i)) :
    ‖weightedPhysical2539 (((1 : ℝ) /
        2)) coefficients nodeModulation2541 adaptiveN02700PlusPosition2542‖ ≤
      adaptiveN02700PlusUpper2542 := by
  have h := weightedPhysical2539_jet_le_center_error 0 (((1 : ℝ) /
        2)) coefficients
    baseCoefficientCenter2540 baseCoefficientError2540 nodeModulation2541
    (fun i => baseCoefficient_error_of_box2540 i (coefficients i) (hbox i))
        adaptiveN02700PlusPosition2542
  simpa only [iteratedDeriv_zero] using h.trans adaptiveN02700PlusSigned_le2542

theorem adaptiveN02700PlusGrid2542 :
    -stripRadius2303 + (2700 : ℝ)*(2*stripRadius2303/10240) = adaptiveN02700PlusPosition2542 := by
  norm_num [stripRadius2303, adaptiveN02700PlusPosition2542]

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.adaptiveN02700PlusSigned_le2542
#print axioms ConnesWeilRH.Dev.adaptiveN02700PlusPhysical_le2542
