import ConnesWeilRH.Dev.C1RouteACompactExp2542
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541

namespace ConnesWeilRH.Dev

open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def adaptiveN05441PlusPosition2542 : ℝ := ((21037056321 : ℝ) /
        51200000000)

def adaptiveN05441PlusP000Output2542 : RatState2542 :=
  (((((-30085212616927361) : ℚ) /
        633825300114114700748351602688),
    ((13438227082181753 : ℚ) /
        633825300114114700748351602688)),
    ((40167273250971 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

def adaptiveN05441PlusP000Input2542 : RatPair2542 :=
  ((((-((784572 * 10^40
        + 6811905081266710236408700291277958317180) * 10^40
        + 9730042723390700240474632798007040790639)) : ℚ) /
        ((1641590 * 10^40
        + 7299889921227587901041435668166425430412) * 10^40
        + 5748789340774106302562410437017600000000)),
    (((-116214821441625035538111309) : ℚ) /
        461168601842738790400000000))

theorem adaptiveN05441PlusP000Compute2542 : compactExp2542 adaptiveN05441PlusP000Input2542 6 =
    adaptiveN05441PlusP000Output2542 := by
  cbv

theorem adaptiveN05441PlusP000Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ adaptiveN05441PlusPosition2542 =
    Complex.exp ((2 : ℂ)^6 * embedPair2542 adaptiveN05441PlusP000Input2542) := by
  have hx : |adaptiveN05441PlusPosition2542| < storedWidth ⟨0, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05441PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05441PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05441PlusP000Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05441PlusP000Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ adaptiveN05441PlusPosition2542 - embedPair2542
            adaptiveN05441PlusP000Output2542.1‖ ≤ (adaptiveN05441PlusP000Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05441PlusP000Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05441PlusP000Input2542]
  rw [adaptiveN05441PlusP000Owner2542]
  have h := compactExp_error2542 adaptiveN05441PlusP000Input2542 hz 6
  simpa only [adaptiveN05441PlusP000Compute2542] using h

theorem adaptiveN05441PlusP000Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ adaptiveN05441PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05441PlusP000Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05441PlusP000Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05441PlusP001Output2542 : RatState2542 :=
  (((((-42470726113974161) : ℚ) /
        633825300114114700748351602688),
    ((37940982444219857 : ℚ) /
        1267650600228229401496703205376)),
    ((55510111139349 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

def adaptiveN05441PlusP001Input2542 : RatPair2542 :=
  ((((-((37 * 10^40
        + 2210872843279052800156387807736435194328) * 10^40
        + 6585212332736148238238202828482993853351)) : ℚ) /
        ((78 * 10^40
        + 7669206969983457920426651219472560969960) * 10^40
        + 6359156146779929224210681488998400000000)),
    (((-116214821441625035538111309) : ℚ) /
        461168601842738790400000000))

theorem adaptiveN05441PlusP001Compute2542 : compactExp2542 adaptiveN05441PlusP001Input2542 6 =
    adaptiveN05441PlusP001Output2542 := by
  cbv

theorem adaptiveN05441PlusP001Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ adaptiveN05441PlusPosition2542 =
    Complex.exp ((2 : ℂ)^6 * embedPair2542 adaptiveN05441PlusP001Input2542) := by
  have hx : |adaptiveN05441PlusPosition2542| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05441PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05441PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05441PlusP001Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05441PlusP001Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ adaptiveN05441PlusPosition2542 - embedPair2542
            adaptiveN05441PlusP001Output2542.1‖ ≤ (adaptiveN05441PlusP001Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05441PlusP001Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05441PlusP001Input2542]
  rw [adaptiveN05441PlusP001Owner2542]
  have h := compactExp_error2542 adaptiveN05441PlusP001Input2542 hz 6
  simpa only [adaptiveN05441PlusP001Compute2542] using h

theorem adaptiveN05441PlusP001Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ adaptiveN05441PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05441PlusP001Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05441PlusP001Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05441PlusP002Output2542 : RatState2542 :=
  (((((-101228313912808433) : ℚ) /
        1267650600228229401496703205376),
    (((-11303967557315125) : ℚ) /
        316912650057057350374175801344)),
    ((65558198693657 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

def adaptiveN05441PlusP002Input2542 : RatPair2542 :=
  ((((-((972 * 10^40
        + 4650254589744882533607086103630523782057) * 10^40
        + 449145224629076769356490527792110637991)) : ℚ) /
        ((2069 * 10^40
        + 9275360438959695706130539090735253425699) * 10^40
        + 327048463036252587370903823974400000000)),
    ((116214821441625035538111309 : ℚ) /
        461168601842738790400000000))

theorem adaptiveN05441PlusP002Compute2542 : compactExp2542 adaptiveN05441PlusP002Input2542 6 =
    adaptiveN05441PlusP002Output2542 := by
  cbv

theorem adaptiveN05441PlusP002Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ adaptiveN05441PlusPosition2542 =
    Complex.exp ((2 : ℂ)^6 * embedPair2542 adaptiveN05441PlusP002Input2542) := by
  have hx : |adaptiveN05441PlusPosition2542| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05441PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05441PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05441PlusP002Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05441PlusP002Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ adaptiveN05441PlusPosition2542 - embedPair2542
            adaptiveN05441PlusP002Output2542.1‖ ≤ (adaptiveN05441PlusP002Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05441PlusP002Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05441PlusP002Input2542]
  rw [adaptiveN05441PlusP002Owner2542]
  have h := compactExp_error2542 adaptiveN05441PlusP002Input2542 hz 6
  simpa only [adaptiveN05441PlusP002Compute2542] using h

theorem adaptiveN05441PlusP002Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ adaptiveN05441PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05441PlusP002Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05441PlusP002Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05441PlusP003Output2542 : RatState2542 :=
  (((((-55780667598372603) : ℚ) /
        633825300114114700748351602688),
    (((-24915671613398283) : ℚ) /
        633825300114114700748351602688)),
    ((17979927593879 : ℚ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944)))

def adaptiveN05441PlusP003Input2542 : RatPair2542 :=
  ((((-((3467731 * 10^40
        + 8511828977644856382439885982238229303076) * 10^40
        + 4074901543573001235591471814120322040639)) : ℚ) /
        ((7405132 * 10^40
        + 3596549542648098448253759473411694208953) * 10^40
        + 3511265881635850302562410437017600000000)),
    ((116214821441625035538111309 : ℚ) /
        461168601842738790400000000))

theorem adaptiveN05441PlusP003Compute2542 : compactExp2542 adaptiveN05441PlusP003Input2542 6 =
    adaptiveN05441PlusP003Output2542 := by
  cbv

theorem adaptiveN05441PlusP003Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ adaptiveN05441PlusPosition2542 =
    Complex.exp ((2 : ℂ)^6 * embedPair2542 adaptiveN05441PlusP003Input2542) := by
  have hx : |adaptiveN05441PlusPosition2542| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05441PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05441PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05441PlusP003Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05441PlusP003Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ adaptiveN05441PlusPosition2542 - embedPair2542
            adaptiveN05441PlusP003Output2542.1‖ ≤ (adaptiveN05441PlusP003Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05441PlusP003Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05441PlusP003Input2542]
  rw [adaptiveN05441PlusP003Owner2542]
  have h := compactExp_error2542 adaptiveN05441PlusP003Input2542 hz 6
  simpa only [adaptiveN05441PlusP003Compute2542] using h

theorem adaptiveN05441PlusP003Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ adaptiveN05441PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05441PlusP003Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05441PlusP003Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05441PlusP004Output2542 : RatState2542 :=
  (((((-118159590386044049) : ℚ) /
        1267650600228229401496703205376),
    ((26389300081792299 : ℚ) /
        633825300114114700748351602688)),
    ((75977044915021 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

def adaptiveN05441PlusP004Input2542 : RatPair2542 :=
  ((((-((2231 * 10^40
        + 3375535476931673290534537883071344715547) * 10^40
        + 6383006085386817160530046997518673137991)) : ℚ) /
        ((4774 * 10^40
        + 400252417480049124655959709246057629116) * 10^40
        + 4311969699402172587370903823974400000000)),
    (((-116214821441625035538111309) : ℚ) /
        461168601842738790400000000))

theorem adaptiveN05441PlusP004Compute2542 : compactExp2542 adaptiveN05441PlusP004Input2542 6 =
    adaptiveN05441PlusP004Output2542 := by
  cbv

theorem adaptiveN05441PlusP004Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ adaptiveN05441PlusPosition2542 =
    Complex.exp ((2 : ℂ)^6 * embedPair2542 adaptiveN05441PlusP004Input2542) := by
  have hx : |adaptiveN05441PlusPosition2542| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05441PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05441PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05441PlusP004Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05441PlusP004Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ adaptiveN05441PlusPosition2542 - embedPair2542
            adaptiveN05441PlusP004Output2542.1‖ ≤ (adaptiveN05441PlusP004Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05441PlusP004Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05441PlusP004Input2542]
  rw [adaptiveN05441PlusP004Owner2542]
  have h := compactExp_error2542 adaptiveN05441PlusP004Input2542 hz 6
  simpa only [adaptiveN05441PlusP004Compute2542] using h

theorem adaptiveN05441PlusP004Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ adaptiveN05441PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05441PlusP004Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05441PlusP004Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05441PlusP005Output2542 : RatState2542 :=
  ((((76083006255940955 : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1)),
    ((9130344602477 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

def adaptiveN05441PlusP005Input2542 : RatPair2542 :=
  ((((-((105958 * 10^40
        + 1078245870052624652491804785029218162688) * 10^40
        + 7127909769652323698197879090457813560071)) : ℚ) /
        ((111373 * 10^40
        + 2246050746979823078836670277118175355916) * 10^40
        + 7617028968325063683475689468723200000000)),
    ((0 : ℚ) /
        1))

theorem adaptiveN05441PlusP005Compute2542 : compactExp2542 adaptiveN05441PlusP005Input2542 5 =
    adaptiveN05441PlusP005Output2542 := by
  cbv

theorem adaptiveN05441PlusP005Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ adaptiveN05441PlusPosition2542 =
    Complex.exp ((2 : ℂ)^5 * embedPair2542 adaptiveN05441PlusP005Input2542) := by
  have hx : |adaptiveN05441PlusPosition2542| < storedWidth ⟨5, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05441PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05441PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05441PlusP005Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05441PlusP005Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ adaptiveN05441PlusPosition2542 - embedPair2542
            adaptiveN05441PlusP005Output2542.1‖ ≤ (adaptiveN05441PlusP005Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05441PlusP005Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05441PlusP005Input2542]
  rw [adaptiveN05441PlusP005Owner2542]
  have h := compactExp_error2542 adaptiveN05441PlusP005Input2542 hz 5
  simpa only [adaptiveN05441PlusP005Compute2542] using h

theorem adaptiveN05441PlusP005Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ adaptiveN05441PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05441PlusP005Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05441PlusP005Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05441PlusP006Output2542 : RatState2542 :=
  ((((6611928741841539 : ℚ) /
        79228162514264337593543950336),
    ((0 : ℚ) /
        1)),
    ((2934505226153 : ℚ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944)))

def adaptiveN05441PlusP006Input2542 : RatPair2542 :=
  ((((-127975970897319380164091345862964161) : ℚ) /
        135988780273982091902841651200000000),
    ((0 : ℚ) /
        1))

theorem adaptiveN05441PlusP006Compute2542 : compactExp2542 adaptiveN05441PlusP006Input2542 5 =
    adaptiveN05441PlusP006Output2542 := by
  cbv

theorem adaptiveN05441PlusP006Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ adaptiveN05441PlusPosition2542 =
    Complex.exp ((2 : ℂ)^5 * embedPair2542 adaptiveN05441PlusP006Input2542) := by
  have hx : |adaptiveN05441PlusPosition2542| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05441PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05441PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05441PlusP006Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05441PlusP006Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ adaptiveN05441PlusPosition2542 - embedPair2542
            adaptiveN05441PlusP006Output2542.1‖ ≤ (adaptiveN05441PlusP006Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05441PlusP006Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05441PlusP006Input2542]
  rw [adaptiveN05441PlusP006Owner2542]
  have h := compactExp_error2542 adaptiveN05441PlusP006Input2542 hz 5
  simpa only [adaptiveN05441PlusP006Compute2542] using h

theorem adaptiveN05441PlusP006Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ adaptiveN05441PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05441PlusP006Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05441PlusP006Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05441PlusP007Output2542 : RatState2542 :=
  ((((122184672846750071 : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1)),
    ((13166735637951 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

def adaptiveN05441PlusP007Input2542 : RatPair2542 :=
  ((((-((3467731 * 10^40
        + 8511828977644856382439885982238229303076) * 10^40
        + 4074901543573001235591471814120322040639)) : ℚ) /
        ((3702566 * 10^40
        + 1798274771324049224126879736705847104476) * 10^40
        + 6755632940817925151281205218508800000000)),
    ((0 : ℚ) /
        1))

theorem adaptiveN05441PlusP007Compute2542 : compactExp2542 adaptiveN05441PlusP007Input2542 5 =
    adaptiveN05441PlusP007Output2542 := by
  cbv

theorem adaptiveN05441PlusP007Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ adaptiveN05441PlusPosition2542 =
    Complex.exp ((2 : ℂ)^5 * embedPair2542 adaptiveN05441PlusP007Input2542) := by
  have hx : |adaptiveN05441PlusPosition2542| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05441PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05441PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05441PlusP007Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05441PlusP007Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ adaptiveN05441PlusPosition2542 - embedPair2542
            adaptiveN05441PlusP007Output2542.1‖ ≤ (adaptiveN05441PlusP007Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05441PlusP007Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05441PlusP007Input2542]
  rw [adaptiveN05441PlusP007Owner2542]
  have h := compactExp_error2542 adaptiveN05441PlusP007Input2542 hz 5
  simpa only [adaptiveN05441PlusP007Compute2542] using h

theorem adaptiveN05441PlusP007Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ adaptiveN05441PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05441PlusP007Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05441PlusP007Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05441PlusP008Output2542 : RatState2542 :=
  ((((75678898124574477 : ℚ) /
        1267650600228229401496703205376),
    ((38968301667069885 : ℚ) /
        1267650600228229401496703205376)),
    ((7984746117365 : ℚ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944)))

def adaptiveN05441PlusP008Input2542 : RatPair2542 :=
  ((((-((1148628 * 10^40
        + 1980583606620428742914120949258198551697) * 10^40
        + 3727227202808030027176920566561728290639)) : ℚ) /
        ((2423597 * 10^40
        + 6830030312889226079875151021067455299232) * 10^40
        + 8720889128251386302562410437017600000000)),
    (((-83697431251741758597728337) : ℚ) /
        922337203685477580800000000))

theorem adaptiveN05441PlusP008Compute2542 : compactExp2542 adaptiveN05441PlusP008Input2542 6 =
    adaptiveN05441PlusP008Output2542 := by
  cbv

theorem adaptiveN05441PlusP008Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ adaptiveN05441PlusPosition2542 =
    Complex.exp ((2 : ℂ)^6 * embedPair2542 adaptiveN05441PlusP008Input2542) := by
  have hx : |adaptiveN05441PlusPosition2542| < storedWidth ⟨8, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05441PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05441PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05441PlusP008Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05441PlusP008Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ adaptiveN05441PlusPosition2542 - embedPair2542
            adaptiveN05441PlusP008Output2542.1‖ ≤ (adaptiveN05441PlusP008Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05441PlusP008Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05441PlusP008Input2542]
  rw [adaptiveN05441PlusP008Owner2542]
  have h := compactExp_error2542 adaptiveN05441PlusP008Input2542 hz 6
  simpa only [adaptiveN05441PlusP008Compute2542] using h

theorem adaptiveN05441PlusP008Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ adaptiveN05441PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05441PlusP008Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05441PlusP008Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05441PlusP009Output2542 : RatState2542 :=
  (((((-30039768110131961) : ℚ) /
        633825300114114700748351602688),
    (((-60301521404716477) : ℚ) /
        1267650600228229401496703205376)),
    ((47043363468949 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

def adaptiveN05441PlusP009Input2542 : RatPair2542 :=
  ((((-((1148628 * 10^40
        + 1980583606620428742914120949258198551697) * 10^40
        + 3727227202808030027176920566561728290639)) : ℚ) /
        ((2423597 * 10^40
        + 6830030312889226079875151021067455299232) * 10^40
        + 8720889128251386302562410437017600000000)),
    (((-124480009324152847187337231) : ℚ) /
        922337203685477580800000000))

theorem adaptiveN05441PlusP009Compute2542 : compactExp2542 adaptiveN05441PlusP009Input2542 6 =
    adaptiveN05441PlusP009Output2542 := by
  cbv

theorem adaptiveN05441PlusP009Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ adaptiveN05441PlusPosition2542 =
    Complex.exp ((2 : ℂ)^6 * embedPair2542 adaptiveN05441PlusP009Input2542) := by
  have hx : |adaptiveN05441PlusPosition2542| < storedWidth ⟨9, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05441PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05441PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05441PlusP009Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05441PlusP009Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ adaptiveN05441PlusPosition2542 - embedPair2542
            adaptiveN05441PlusP009Output2542.1‖ ≤ (adaptiveN05441PlusP009Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05441PlusP009Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05441PlusP009Input2542]
  rw [adaptiveN05441PlusP009Owner2542]
  have h := compactExp_error2542 adaptiveN05441PlusP009Input2542 hz 6
  simpa only [adaptiveN05441PlusP009Compute2542] using h

theorem adaptiveN05441PlusP009Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ adaptiveN05441PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05441PlusP009Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05441PlusP009Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05441PlusP010Output2542 : RatState2542 :=
  (((((-14017905555603873) : ℚ) /
        316912650057057350374175801344),
    ((64045275684567125 : ℚ) /
        1267650600228229401496703205376)),
    ((2911352684741 : ℚ) /
        (8 * 10^40
        + 7112285931760246646623899502532662132736)))

def adaptiveN05441PlusP010Input2542 : RatPair2542 :=
  ((((-((1148628 * 10^40
        + 1980583606620428742914120949258198551697) * 10^40
        + 3727227202808030027176920566561728290639)) : ℚ) /
        ((2423597 * 10^40
        + 6830030312889226079875151021067455299232) * 10^40
        + 8720889128251386302562410437017600000000)),
    (((-74049707789522705117225241) : ℚ) /
        461168601842738790400000000))

theorem adaptiveN05441PlusP010Compute2542 : compactExp2542 adaptiveN05441PlusP010Input2542 6 =
    adaptiveN05441PlusP010Output2542 := by
  cbv

theorem adaptiveN05441PlusP010Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ adaptiveN05441PlusPosition2542 =
    Complex.exp ((2 : ℂ)^6 * embedPair2542 adaptiveN05441PlusP010Input2542) := by
  have hx : |adaptiveN05441PlusPosition2542| < storedWidth ⟨10, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05441PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05441PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05441PlusP010Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05441PlusP010Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ adaptiveN05441PlusPosition2542 - embedPair2542
            adaptiveN05441PlusP010Output2542.1‖ ≤ (adaptiveN05441PlusP010Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05441PlusP010Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05441PlusP010Input2542]
  rw [adaptiveN05441PlusP010Owner2542]
  have h := compactExp_error2542 adaptiveN05441PlusP010Input2542 hz 6
  simpa only [adaptiveN05441PlusP010Compute2542] using h

theorem adaptiveN05441PlusP010Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ adaptiveN05441PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05441PlusP010Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05441PlusP010Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05441PlusP011Output2542 : RatState2542 :=
  ((((31067693906795939 : ℚ) /
        1267650600228229401496703205376),
    ((79250378872779645 : ℚ) /
        1267650600228229401496703205376)),
    ((21117980314573 : ℚ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888)))

def adaptiveN05441PlusP011Input2542 : RatPair2542 :=
  ((((-((1148628 * 10^40
        + 1980583606620428742914120949258198551697) * 10^40
        + 3727227202808030027176920566561728290639)) : ℚ) /
        ((2423597 * 10^40
        + 6830030312889226079875151021067455299232) * 10^40
        + 8720889128251386302562410437017600000000)),
    (((-81923590457429860456094121) : ℚ) /
        461168601842738790400000000))

theorem adaptiveN05441PlusP011Compute2542 : compactExp2542 adaptiveN05441PlusP011Input2542 6 =
    adaptiveN05441PlusP011Output2542 := by
  cbv

theorem adaptiveN05441PlusP011Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ adaptiveN05441PlusPosition2542 =
    Complex.exp ((2 : ℂ)^6 * embedPair2542 adaptiveN05441PlusP011Input2542) := by
  have hx : |adaptiveN05441PlusPosition2542| < storedWidth ⟨11, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05441PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05441PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05441PlusP011Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05441PlusP011Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ adaptiveN05441PlusPosition2542 - embedPair2542
            adaptiveN05441PlusP011Output2542.1‖ ≤ (adaptiveN05441PlusP011Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05441PlusP011Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05441PlusP011Input2542]
  rw [adaptiveN05441PlusP011Owner2542]
  have h := compactExp_error2542 adaptiveN05441PlusP011Input2542 hz 6
  simpa only [adaptiveN05441PlusP011Compute2542] using h

theorem adaptiveN05441PlusP011Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ adaptiveN05441PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05441PlusP011Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05441PlusP011Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05441PlusP012Output2542 : RatState2542 :=
  ((((21235111400005671 : ℚ) /
        316912650057057350374175801344),
    ((1390702552558213 : ℚ) /
        316912650057057350374175801344)),
    ((1516939706649 : ℚ) /
        (8 * 10^40
        + 7112285931760246646623899502532662132736)))

def adaptiveN05441PlusP012Input2542 : RatPair2542 :=
  ((((-((1148628 * 10^40
        + 1980583606620428742914120949258198551697) * 10^40
        + 3727227202808030027176920566561728290639)) : ℚ) /
        ((2423597 * 10^40
        + 6830030312889226079875151021067455299232) * 10^40
        + 8720889128251386302562410437017600000000)),
    (((-1801580117301358815136389) : ℚ) /
        9223372036854775808000000))

theorem adaptiveN05441PlusP012Compute2542 : compactExp2542 adaptiveN05441PlusP012Input2542 6 =
    adaptiveN05441PlusP012Output2542 := by
  cbv

theorem adaptiveN05441PlusP012Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ adaptiveN05441PlusPosition2542 =
    Complex.exp ((2 : ℂ)^6 * embedPair2542 adaptiveN05441PlusP012Input2542) := by
  have hx : |adaptiveN05441PlusPosition2542| < storedWidth ⟨12, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05441PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05441PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05441PlusP012Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05441PlusP012Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ adaptiveN05441PlusPosition2542 - embedPair2542
            adaptiveN05441PlusP012Output2542.1‖ ≤ (adaptiveN05441PlusP012Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05441PlusP012Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05441PlusP012Input2542]
  rw [adaptiveN05441PlusP012Owner2542]
  have h := compactExp_error2542 adaptiveN05441PlusP012Input2542 hz 6
  simpa only [adaptiveN05441PlusP012Compute2542] using h

theorem adaptiveN05441PlusP012Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ adaptiveN05441PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05441PlusP012Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05441PlusP012Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05441PlusP013Output2542 : RatState2542 :=
  ((((24200498752788563 : ℚ) /
        633825300114114700748351602688),
    (((-70022622034815297) : ℚ) /
        1267650600228229401496703205376)),
    ((40989034846297 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

def adaptiveN05441PlusP013Input2542 : RatPair2542 :=
  ((((-((1148628 * 10^40
        + 1980583606620428742914120949258198551697) * 10^40
        + 3727227202808030027176920566561728290639)) : ℚ) /
        ((2423597 * 10^40
        + 6830030312889226079875151021067455299232) * 10^40
        + 8720889128251386302562410437017600000000)),
    (((-19502183631944175412566411) : ℚ) /
        92233720368547758080000000))

theorem adaptiveN05441PlusP013Compute2542 : compactExp2542 adaptiveN05441PlusP013Input2542 6 =
    adaptiveN05441PlusP013Output2542 := by
  cbv

theorem adaptiveN05441PlusP013Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ adaptiveN05441PlusPosition2542 =
    Complex.exp ((2 : ℂ)^6 * embedPair2542 adaptiveN05441PlusP013Input2542) := by
  have hx : |adaptiveN05441PlusPosition2542| < storedWidth ⟨13, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05441PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05441PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05441PlusP013Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05441PlusP013Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ adaptiveN05441PlusPosition2542 - embedPair2542
            adaptiveN05441PlusP013Output2542.1‖ ≤ (adaptiveN05441PlusP013Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05441PlusP013Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05441PlusP013Input2542]
  rw [adaptiveN05441PlusP013Owner2542]
  have h := compactExp_error2542 adaptiveN05441PlusP013Input2542 hz 6
  simpa only [adaptiveN05441PlusP013Compute2542] using h

theorem adaptiveN05441PlusP013Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ adaptiveN05441PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05441PlusP013Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05441PlusP013Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05441PlusP014Output2542 : RatState2542 :=
  (((((-82160928314915089) : ℚ) /
        1267650600228229401496703205376),
    (((-11128859045257829) : ℚ) /
        633825300114114700748351602688)),
    ((46835536846957 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

def adaptiveN05441PlusP014Input2542 : RatPair2542 :=
  ((((-((1148628 * 10^40
        + 1980583606620428742914120949258198551697) * 10^40
        + 3727227202808030027176920566561728290639)) : ℚ) /
        ((2423597 * 10^40
        + 6830030312889226079875151021067455299232) * 10^40
        + 8720889128251386302562410437017600000000)),
    (((-111281490475376521366248531) : ℚ) /
        461168601842738790400000000))

theorem adaptiveN05441PlusP014Compute2542 : compactExp2542 adaptiveN05441PlusP014Input2542 6 =
    adaptiveN05441PlusP014Output2542 := by
  cbv

theorem adaptiveN05441PlusP014Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ adaptiveN05441PlusPosition2542 =
    Complex.exp ((2 : ℂ)^6 * embedPair2542 adaptiveN05441PlusP014Input2542) := by
  have hx : |adaptiveN05441PlusPosition2542| < storedWidth ⟨14, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05441PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05441PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05441PlusP014Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05441PlusP014Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ adaptiveN05441PlusPosition2542 - embedPair2542
            adaptiveN05441PlusP014Output2542.1‖ ≤ (adaptiveN05441PlusP014Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05441PlusP014Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05441PlusP014Input2542]
  rw [adaptiveN05441PlusP014Owner2542]
  have h := compactExp_error2542 adaptiveN05441PlusP014Input2542 hz 6
  simpa only [adaptiveN05441PlusP014Compute2542] using h

theorem adaptiveN05441PlusP014Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ adaptiveN05441PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05441PlusP014Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05441PlusP014Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05441PlusP015Output2542 : RatState2542 :=
  (((((-38252678060581621) : ℚ) /
        1267650600228229401496703205376),
    ((76043124458158487 : ℚ) /
        1267650600228229401496703205376)),
    ((14636194061413 : ℚ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944)))

def adaptiveN05441PlusP015Input2542 : RatPair2542 :=
  ((((-((1148628 * 10^40
        + 1980583606620428742914120949258198551697) * 10^40
        + 3727227202808030027176920566561728290639)) : ℚ) /
        ((2423597 * 10^40
        + 6830030312889226079875151021067455299232) * 10^40
        + 8720889128251386302562410437017600000000)),
    (((-121148152407873549709974087) : ℚ) /
        461168601842738790400000000))

theorem adaptiveN05441PlusP015Compute2542 : compactExp2542 adaptiveN05441PlusP015Input2542 6 =
    adaptiveN05441PlusP015Output2542 := by
  cbv

theorem adaptiveN05441PlusP015Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ adaptiveN05441PlusPosition2542 =
    Complex.exp ((2 : ℂ)^6 * embedPair2542 adaptiveN05441PlusP015Input2542) := by
  have hx : |adaptiveN05441PlusPosition2542| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05441PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05441PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05441PlusP015Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05441PlusP015Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ adaptiveN05441PlusPosition2542 - embedPair2542
            adaptiveN05441PlusP015Output2542.1‖ ≤ (adaptiveN05441PlusP015Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05441PlusP015Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05441PlusP015Input2542]
  rw [adaptiveN05441PlusP015Owner2542]
  have h := compactExp_error2542 adaptiveN05441PlusP015Input2542 hz 6
  simpa only [adaptiveN05441PlusP015Compute2542] using h

theorem adaptiveN05441PlusP015Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ adaptiveN05441PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05441PlusP015Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05441PlusP015Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05441PlusP016Output2542 : RatState2542 :=
  ((((5318950355279571 : ℚ) /
        158456325028528675187087900672),
    ((73723708884741065 : ℚ) /
        1267650600228229401496703205376)),
    ((53659945627381 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

def adaptiveN05441PlusP016Input2542 : RatPair2542 :=
  ((((-((1148628 * 10^40
        + 1980583606620428742914120949258198551697) * 10^40
        + 3727227202808030027176920566561728290639)) : ℚ) /
        ((2423597 * 10^40
        + 6830030312889226079875151021067455299232) * 10^40
        + 8720889128251386302562410437017600000000)),
    (((-64139286418828663293690489) : ℚ) /
        230584300921369395200000000))

theorem adaptiveN05441PlusP016Compute2542 : compactExp2542 adaptiveN05441PlusP016Input2542 6 =
    adaptiveN05441PlusP016Output2542 := by
  cbv

theorem adaptiveN05441PlusP016Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ adaptiveN05441PlusPosition2542 =
    Complex.exp ((2 : ℂ)^6 * embedPair2542 adaptiveN05441PlusP016Input2542) := by
  have hx : |adaptiveN05441PlusPosition2542| < storedWidth ⟨16, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05441PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05441PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05441PlusP016Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05441PlusP016Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ adaptiveN05441PlusPosition2542 - embedPair2542
            adaptiveN05441PlusP016Output2542.1‖ ≤ (adaptiveN05441PlusP016Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05441PlusP016Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05441PlusP016Input2542]
  rw [adaptiveN05441PlusP016Owner2542]
  have h := compactExp_error2542 adaptiveN05441PlusP016Input2542 hz 6
  simpa only [adaptiveN05441PlusP016Compute2542] using h

theorem adaptiveN05441PlusP016Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ adaptiveN05441PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05441PlusP016Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05441PlusP016Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05441PlusP017Output2542 : RatState2542 :=
  ((((3411013174531863 : ℚ) /
        79228162514264337593543950336),
    (((-4082767411106281) : ℚ) /
        79228162514264337593543950336)),
    ((25052858391699 : ℚ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888)))

def adaptiveN05441PlusP017Input2542 : RatPair2542 :=
  ((((-((1148628 * 10^40
        + 1980583606620428742914120949258198551697) * 10^40
        + 3727227202808030027176920566561728290639)) : ℚ) /
        ((2423597 * 10^40
        + 6830030312889226079875151021067455299232) * 10^40
        + 8720889128251386302562410437017600000000)),
    (((-142128968738930782070534667) : ℚ) /
        461168601842738790400000000))

theorem adaptiveN05441PlusP017Compute2542 : compactExp2542 adaptiveN05441PlusP017Input2542 6 =
    adaptiveN05441PlusP017Output2542 := by
  cbv

theorem adaptiveN05441PlusP017Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ adaptiveN05441PlusPosition2542 =
    Complex.exp ((2 : ℂ)^6 * embedPair2542 adaptiveN05441PlusP017Input2542) := by
  have hx : |adaptiveN05441PlusPosition2542| < storedWidth ⟨17, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05441PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05441PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05441PlusP017Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05441PlusP017Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ adaptiveN05441PlusPosition2542 - embedPair2542
            adaptiveN05441PlusP017Output2542.1‖ ≤ (adaptiveN05441PlusP017Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05441PlusP017Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05441PlusP017Input2542]
  rw [adaptiveN05441PlusP017Owner2542]
  have h := compactExp_error2542 adaptiveN05441PlusP017Input2542 hz 6
  simpa only [adaptiveN05441PlusP017Compute2542] using h

theorem adaptiveN05441PlusP017Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ adaptiveN05441PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05441PlusP017Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05441PlusP017Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05441PlusP018Output2542 : RatState2542 :=
  (((((-1307289511708849) : ℚ) /
        633825300114114700748351602688),
    (((-85082243345458329) : ℚ) /
        1267650600228229401496703205376)),
    ((56636079998407 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

def adaptiveN05441PlusP018Input2542 : RatPair2542 :=
  ((((-((1148628 * 10^40
        + 1980583606620428742914120949258198551697) * 10^40
        + 3727227202808030027176920566561728290639)) : ℚ) /
        ((2423597 * 10^40
        + 6830030312889226079875151021067455299232) * 10^40
        + 8720889128251386302562410437017600000000)),
    (((-36841377177147749391625773) : ℚ) /
        115292150460684697600000000))

theorem adaptiveN05441PlusP018Compute2542 : compactExp2542 adaptiveN05441PlusP018Input2542 6 =
    adaptiveN05441PlusP018Output2542 := by
  cbv

theorem adaptiveN05441PlusP018Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ adaptiveN05441PlusPosition2542 =
    Complex.exp ((2 : ℂ)^6 * embedPair2542 adaptiveN05441PlusP018Input2542) := by
  have hx : |adaptiveN05441PlusPosition2542| < storedWidth ⟨18, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05441PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05441PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05441PlusP018Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05441PlusP018Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ adaptiveN05441PlusPosition2542 - embedPair2542
            adaptiveN05441PlusP018Output2542.1‖ ≤ (adaptiveN05441PlusP018Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05441PlusP018Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05441PlusP018Input2542]
  rw [adaptiveN05441PlusP018Owner2542]
  have h := compactExp_error2542 adaptiveN05441PlusP018Input2542 hz 6
  simpa only [adaptiveN05441PlusP018Compute2542] using h

theorem adaptiveN05441PlusP018Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ adaptiveN05441PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05441PlusP018Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05441PlusP018Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05441PlusP019Output2542 : RatState2542 :=
  (((((-41472183286353791) : ℚ) /
        633825300114114700748351602688),
    (((-19132595485657273) : ℚ) /
        1267650600228229401496703205376)),
    ((44522606514041 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

def adaptiveN05441PlusP019Input2542 : RatPair2542 :=
  ((((-((1148628 * 10^40
        + 1980583606620428742914120949258198551697) * 10^40
        + 3727227202808030027176920566561728290639)) : ℚ) /
        ((2423597 * 10^40
        + 6830030312889226079875151021067455299232) * 10^40
        + 8720889128251386302562410437017600000000)),
    (((-7841468079158496015368511) : ℚ) /
        23058430092136939520000000))

theorem adaptiveN05441PlusP019Compute2542 : compactExp2542 adaptiveN05441PlusP019Input2542 6 =
    adaptiveN05441PlusP019Output2542 := by
  cbv

theorem adaptiveN05441PlusP019Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ adaptiveN05441PlusPosition2542 =
    Complex.exp ((2 : ℂ)^6 * embedPair2542 adaptiveN05441PlusP019Input2542) := by
  have hx : |adaptiveN05441PlusPosition2542| < storedWidth ⟨19, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05441PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05441PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05441PlusP019Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05441PlusP019Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ adaptiveN05441PlusPosition2542 - embedPair2542
            adaptiveN05441PlusP019Output2542.1‖ ≤ (adaptiveN05441PlusP019Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05441PlusP019Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05441PlusP019Input2542]
  rw [adaptiveN05441PlusP019Owner2542]
  have h := compactExp_error2542 adaptiveN05441PlusP019Input2542 hz 6
  simpa only [adaptiveN05441PlusP019Compute2542] using h

theorem adaptiveN05441PlusP019Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ adaptiveN05441PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05441PlusP019Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05441PlusP019Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05441PlusP020Output2542 : RatState2542 :=
  (((((-30726832232824155) : ℚ) /
        1267650600228229401496703205376),
    ((79383159026970969 : ℚ) /
        1267650600228229401496703205376)),
    ((11638332541593 : ℚ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944)))

def adaptiveN05441PlusP020Input2542 : RatPair2542 :=
  ((((-((1148628 * 10^40
        + 1980583606620428742914120949258198551697) * 10^40
        + 3727227202808030027176920566561728290639)) : ℚ) /
        ((2423597 * 10^40
        + 6830030312889226079875151021067455299232) * 10^40
        + 8720889128251386302562410437017600000000)),
    (((-167120544922882863756005499) : ℚ) /
        461168601842738790400000000))

theorem adaptiveN05441PlusP020Compute2542 : compactExp2542 adaptiveN05441PlusP020Input2542 6 =
    adaptiveN05441PlusP020Output2542 := by
  cbv

theorem adaptiveN05441PlusP020Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ adaptiveN05441PlusPosition2542 =
    Complex.exp ((2 : ℂ)^6 * embedPair2542 adaptiveN05441PlusP020Input2542) := by
  have hx : |adaptiveN05441PlusPosition2542| < storedWidth ⟨20, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05441PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05441PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05441PlusP020Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05441PlusP020Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ adaptiveN05441PlusPosition2542 - embedPair2542
            adaptiveN05441PlusP020Output2542.1‖ ≤ (adaptiveN05441PlusP020Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05441PlusP020Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05441PlusP020Input2542]
  rw [adaptiveN05441PlusP020Owner2542]
  have h := compactExp_error2542 adaptiveN05441PlusP020Input2542 hz 6
  simpa only [adaptiveN05441PlusP020Compute2542] using h

theorem adaptiveN05441PlusP020Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ adaptiveN05441PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05441PlusP020Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05441PlusP020Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05441PlusP021Output2542 : RatState2542 :=
  ((((15596467458466339 : ℚ) /
        316912650057057350374175801344),
    ((57912238786266003 : ℚ) /
        1267650600228229401496703205376)),
    ((32706087005659 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

def adaptiveN05441PlusP021Input2542 : RatPair2542 :=
  ((((-((1148628 * 10^40
        + 1980583606620428742914120949258198551697) * 10^40
        + 3727227202808030027176920566561728290639)) : ℚ) /
        ((2423597 * 10^40
        + 6830030312889226079875151021067455299232) * 10^40
        + 8720889128251386302562410437017600000000)),
    (((-175708939706778788195515227) : ℚ) /
        461168601842738790400000000))

theorem adaptiveN05441PlusP021Compute2542 : compactExp2542 adaptiveN05441PlusP021Input2542 6 =
    adaptiveN05441PlusP021Output2542 := by
  cbv

theorem adaptiveN05441PlusP021Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ adaptiveN05441PlusPosition2542 =
    Complex.exp ((2 : ℂ)^6 * embedPair2542 adaptiveN05441PlusP021Input2542) := by
  have hx : |adaptiveN05441PlusPosition2542| < storedWidth ⟨21, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05441PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05441PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05441PlusP021Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05441PlusP021Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ adaptiveN05441PlusPosition2542 - embedPair2542
            adaptiveN05441PlusP021Output2542.1‖ ≤ (adaptiveN05441PlusP021Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05441PlusP021Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05441PlusP021Input2542]
  rw [adaptiveN05441PlusP021Owner2542]
  have h := compactExp_error2542 adaptiveN05441PlusP021Input2542 hz 6
  simpa only [adaptiveN05441PlusP021Compute2542] using h

theorem adaptiveN05441PlusP021Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ adaptiveN05441PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05441PlusP021Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05441PlusP021Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05441PlusP022Output2542 : RatState2542 :=
  ((((84311051410122179 : ℚ) /
        1267650600228229401496703205376),
    ((11724792803509099 : ℚ) /
        1267650600228229401496703205376)),
    ((22295137333103 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

def adaptiveN05441PlusP022Input2542 : RatPair2542 :=
  ((((-((1148628 * 10^40
        + 1980583606620428742914120949258198551697) * 10^40
        + 3727227202808030027176920566561728290639)) : ℚ) /
        ((2423597 * 10^40
        + 6830030312889226079875151021067455299232) * 10^40
        + 8720889128251386302562410437017600000000)),
    (((-36020959374381273657830793) : ℚ) /
        92233720368547758080000000))

theorem adaptiveN05441PlusP022Compute2542 : compactExp2542 adaptiveN05441PlusP022Input2542 6 =
    adaptiveN05441PlusP022Output2542 := by
  cbv

theorem adaptiveN05441PlusP022Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ adaptiveN05441PlusPosition2542 =
    Complex.exp ((2 : ℂ)^6 * embedPair2542 adaptiveN05441PlusP022Input2542) := by
  have hx : |adaptiveN05441PlusPosition2542| < storedWidth ⟨22, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05441PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05441PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05441PlusP022Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05441PlusP022Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ adaptiveN05441PlusPosition2542 - embedPair2542
            adaptiveN05441PlusP022Output2542.1‖ ≤ (adaptiveN05441PlusP022Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05441PlusP022Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05441PlusP022Input2542]
  rw [adaptiveN05441PlusP022Owner2542]
  have h := compactExp_error2542 adaptiveN05441PlusP022Input2542 hz 6
  simpa only [adaptiveN05441PlusP022Compute2542] using h

theorem adaptiveN05441PlusP022Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ adaptiveN05441PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05441PlusP022Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05441PlusP022Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05441PlusP023Output2542 : RatState2542 :=
  (((((-1061566622896829) : ℚ) /
        316912650057057350374175801344),
    (((-42508215020887159) : ℚ) /
        633825300114114700748351602688)),
    ((1415403270485 : ℚ) /
        (4 * 10^40
        + 3556142965880123323311949751266331066368)))

def adaptiveN05441PlusP023Input2542 : RatPair2542 :=
  ((((-((1148628 * 10^40
        + 1980583606620428742914120949258198551697) * 10^40
        + 3727227202808030027176920566561728290639)) : ℚ) /
        ((2423597 * 10^40
        + 6830030312889226079875151021067455299232) * 10^40
        + 8720889128251386302562410437017600000000)),
    (((-96389434963244923910950893) : ℚ) /
        230584300921369395200000000))

theorem adaptiveN05441PlusP023Compute2542 : compactExp2542 adaptiveN05441PlusP023Input2542 6 =
    adaptiveN05441PlusP023Output2542 := by
  cbv

theorem adaptiveN05441PlusP023Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ adaptiveN05441PlusPosition2542 =
    Complex.exp ((2 : ℂ)^6 * embedPair2542 adaptiveN05441PlusP023Input2542) := by
  have hx : |adaptiveN05441PlusPosition2542| < storedWidth ⟨23, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05441PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05441PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05441PlusP023Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05441PlusP023Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ adaptiveN05441PlusPosition2542 - embedPair2542
            adaptiveN05441PlusP023Output2542.1‖ ≤ (adaptiveN05441PlusP023Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05441PlusP023Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05441PlusP023Input2542]
  rw [adaptiveN05441PlusP023Owner2542]
  have h := compactExp_error2542 adaptiveN05441PlusP023Input2542 hz 6
  simpa only [adaptiveN05441PlusP023Compute2542] using h

theorem adaptiveN05441PlusP023Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ adaptiveN05441PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05441PlusP023Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05441PlusP023Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05441PlusP024Output2542 : RatState2542 :=
  (((((-64410169773694499) : ℚ) /
        1267650600228229401496703205376),
    (((-13913020398823667) : ℚ) /
        316912650057057350374175801344)),
    ((48200538787461 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

def adaptiveN05441PlusP024Input2542 : RatPair2542 :=
  ((((-((1148628 * 10^40
        + 1980583606620428742914120949258198551697) * 10^40
        + 3727227202808030027176920566561728290639)) : ℚ) /
        ((2423597 * 10^40
        + 6830030312889226079875151021067455299232) * 10^40
        + 8720889128251386302562410437017600000000)),
    (((-99301680327601486613435187) : ℚ) /
        230584300921369395200000000))

theorem adaptiveN05441PlusP024Compute2542 : compactExp2542 adaptiveN05441PlusP024Input2542 6 =
    adaptiveN05441PlusP024Output2542 := by
  cbv

theorem adaptiveN05441PlusP024Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ adaptiveN05441PlusPosition2542 =
    Complex.exp ((2 : ℂ)^6 * embedPair2542 adaptiveN05441PlusP024Input2542) := by
  have hx : |adaptiveN05441PlusPosition2542| < storedWidth ⟨24, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05441PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05441PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05441PlusP024Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05441PlusP024Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ adaptiveN05441PlusPosition2542 - embedPair2542
            adaptiveN05441PlusP024Output2542.1‖ ≤ (adaptiveN05441PlusP024Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05441PlusP024Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05441PlusP024Input2542]
  rw [adaptiveN05441PlusP024Owner2542]
  have h := compactExp_error2542 adaptiveN05441PlusP024Input2542 hz 6
  simpa only [adaptiveN05441PlusP024Compute2542] using h

theorem adaptiveN05441PlusP024Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ adaptiveN05441PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05441PlusP024Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05441PlusP024Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05441PlusP025Output2542 : RatState2542 :=
  (((((-40649034076960087) : ℚ) /
        633825300114114700748351602688),
    ((12613963201607519 : ℚ) /
        633825300114114700748351602688)),
    ((23965893802661 : ℚ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888)))

def adaptiveN05441PlusP025Input2542 : RatPair2542 :=
  ((((-((1148628 * 10^40
        + 1980583606620428742914120949258198551697) * 10^40
        + 3727227202808030027176920566561728290639)) : ℚ) /
        ((2423597 * 10^40
        + 6830030312889226079875151021067455299232) * 10^40
        + 8720889128251386302562410437017600000000)),
    (((-3217284425888024839257393) : ℚ) /
        7205759403792793600000000))

theorem adaptiveN05441PlusP025Compute2542 : compactExp2542 adaptiveN05441PlusP025Input2542 6 =
    adaptiveN05441PlusP025Output2542 := by
  cbv

theorem adaptiveN05441PlusP025Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ adaptiveN05441PlusPosition2542 =
    Complex.exp ((2 : ℂ)^6 * embedPair2542 adaptiveN05441PlusP025Input2542) := by
  have hx : |adaptiveN05441PlusPosition2542| < storedWidth ⟨25, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05441PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05441PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05441PlusP025Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05441PlusP025Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ adaptiveN05441PlusPosition2542 - embedPair2542
            adaptiveN05441PlusP025Output2542.1‖ ≤ (adaptiveN05441PlusP025Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05441PlusP025Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05441PlusP025Input2542]
  rw [adaptiveN05441PlusP025Owner2542]
  have h := compactExp_error2542 adaptiveN05441PlusP025Input2542 hz 6
  simpa only [adaptiveN05441PlusP025Compute2542] using h

theorem adaptiveN05441PlusP025Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ adaptiveN05441PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05441PlusP025Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05441PlusP025Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05441PlusP026Output2542 : RatState2542 :=
  (((((-19751936632082831) : ℚ) /
        1267650600228229401496703205376),
    ((82799064943075705 : ℚ) /
        1267650600228229401496703205376)),
    ((15008208047897 : ℚ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944)))

def adaptiveN05441PlusP026Input2542 : RatPair2542 :=
  ((((-((1148628 * 10^40
        + 1980583606620428742914120949258198551697) * 10^40
        + 3727227202808030027176920566561728290639)) : ℚ) /
        ((2423597 * 10^40
        + 6830030312889226079875151021067455299232) * 10^40
        + 8720889128251386302562410437017600000000)),
    (((-6667794114411367544987277) : ℚ) /
        14411518807585587200000000))

theorem adaptiveN05441PlusP026Compute2542 : compactExp2542 adaptiveN05441PlusP026Input2542 6 =
    adaptiveN05441PlusP026Output2542 := by
  cbv

theorem adaptiveN05441PlusP026Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ adaptiveN05441PlusPosition2542 =
    Complex.exp ((2 : ℂ)^6 * embedPair2542 adaptiveN05441PlusP026Input2542) := by
  have hx : |adaptiveN05441PlusPosition2542| < storedWidth ⟨26, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05441PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05441PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05441PlusP026Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05441PlusP026Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ adaptiveN05441PlusPosition2542 - embedPair2542
            adaptiveN05441PlusP026Output2542.1‖ ≤ (adaptiveN05441PlusP026Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05441PlusP026Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05441PlusP026Input2542]
  rw [adaptiveN05441PlusP026Owner2542]
  have h := compactExp_error2542 adaptiveN05441PlusP026Input2542 hz 6
  simpa only [adaptiveN05441PlusP026Compute2542] using h

theorem adaptiveN05441PlusP026Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ adaptiveN05441PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05441PlusP026Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05441PlusP026Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05441PlusP027Output2542 : RatState2542 :=
  ((((10131872598729435 : ℚ) /
        158456325028528675187087900672),
    ((6499587704832155 : ℚ) /
        316912650057057350374175801344)),
    ((2676132222099 : ℚ) /
        (8 * 10^40
        + 7112285931760246646623899502532662132736)))

def adaptiveN05441PlusP027Input2542 : RatPair2542 :=
  ((((-((1148628 * 10^40
        + 1980583606620428742914120949258198551697) * 10^40
        + 3727227202808030027176920566561728290639)) : ℚ) /
        ((2423597 * 10^40
        + 6830030312889226079875151021067455299232) * 10^40
        + 8720889128251386302562410437017600000000)),
    (((-14008691541762368185839267) : ℚ) /
        28823037615171174400000000))

theorem adaptiveN05441PlusP027Compute2542 : compactExp2542 adaptiveN05441PlusP027Input2542 6 =
    adaptiveN05441PlusP027Output2542 := by
  cbv

theorem adaptiveN05441PlusP027Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ adaptiveN05441PlusPosition2542 =
    Complex.exp ((2 : ℂ)^6 * embedPair2542 adaptiveN05441PlusP027Input2542) := by
  have hx : |adaptiveN05441PlusPosition2542| < storedWidth ⟨27, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05441PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05441PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05441PlusP027Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05441PlusP027Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ adaptiveN05441PlusPosition2542 - embedPair2542
            adaptiveN05441PlusP027Output2542.1‖ ≤ (adaptiveN05441PlusP027Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05441PlusP027Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05441PlusP027Input2542]
  rw [adaptiveN05441PlusP027Owner2542]
  have h := compactExp_error2542 adaptiveN05441PlusP027Input2542 hz 6
  simpa only [adaptiveN05441PlusP027Compute2542] using h

theorem adaptiveN05441PlusP027Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ adaptiveN05441PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05441PlusP027Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05441PlusP027Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05441PlusP028Output2542 : RatState2542 :=
  ((((81775618486861615 : ℚ) /
        1267650600228229401496703205376),
    (((-11817067923735785) : ℚ) /
        633825300114114700748351602688)),
    ((42721615969753 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

def adaptiveN05441PlusP028Input2542 : RatPair2542 :=
  ((((-((1148628 * 10^40
        + 1980583606620428742914120949258198551697) * 10^40
        + 3727227202808030027176920566561728290639)) : ℚ) /
        ((2423597 * 10^40
        + 6830030312889226079875151021067455299232) * 10^40
        + 8720889128251386302562410437017600000000)),
    (((-57100729615769193262781367) : ℚ) /
        115292150460684697600000000))

theorem adaptiveN05441PlusP028Compute2542 : compactExp2542 adaptiveN05441PlusP028Input2542 6 =
    adaptiveN05441PlusP028Output2542 := by
  cbv

theorem adaptiveN05441PlusP028Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ adaptiveN05441PlusPosition2542 =
    Complex.exp ((2 : ℂ)^6 * embedPair2542 adaptiveN05441PlusP028Input2542) := by
  have hx : |adaptiveN05441PlusPosition2542| < storedWidth ⟨28, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05441PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05441PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05441PlusP028Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05441PlusP028Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ adaptiveN05441PlusPosition2542 - embedPair2542
            adaptiveN05441PlusP028Output2542.1‖ ≤ (adaptiveN05441PlusP028Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05441PlusP028Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05441PlusP028Input2542]
  rw [adaptiveN05441PlusP028Owner2542]
  have h := compactExp_error2542 adaptiveN05441PlusP028Input2542 hz 6
  simpa only [adaptiveN05441PlusP028Compute2542] using h

theorem adaptiveN05441PlusP028Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ adaptiveN05441PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05441PlusP028Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05441PlusP028Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05441PlusP029Output2542 : RatState2542 :=
  ((((8062714586698767 : ℚ) /
        316912650057057350374175801344),
    (((-39388152698687339) : ℚ) /
        633825300114114700748351602688)),
    ((60793450727817 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

def adaptiveN05441PlusP029Input2542 : RatPair2542 :=
  ((((-((1148628 * 10^40
        + 1980583606620428742914120949258198551697) * 10^40
        + 3727227202808030027176920566561728290639)) : ℚ) /
        ((2423597 * 10^40
        + 6830030312889226079875151021067455299232) * 10^40
        + 8720889128251386302562410437017600000000)),
    (((-58723590526748964315538539) : ℚ) /
        115292150460684697600000000))

theorem adaptiveN05441PlusP029Compute2542 : compactExp2542 adaptiveN05441PlusP029Input2542 6 =
    adaptiveN05441PlusP029Output2542 := by
  cbv

theorem adaptiveN05441PlusP029Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ adaptiveN05441PlusPosition2542 =
    Complex.exp ((2 : ℂ)^6 * embedPair2542 adaptiveN05441PlusP029Input2542) := by
  have hx : |adaptiveN05441PlusPosition2542| < storedWidth ⟨29, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05441PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05441PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05441PlusP029Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05441PlusP029Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ adaptiveN05441PlusPosition2542 - embedPair2542
            adaptiveN05441PlusP029Output2542.1‖ ≤ (adaptiveN05441PlusP029Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05441PlusP029Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05441PlusP029Input2542]
  rw [adaptiveN05441PlusP029Owner2542]
  have h := compactExp_error2542 adaptiveN05441PlusP029Input2542 hz 6
  simpa only [adaptiveN05441PlusP029Compute2542] using h

theorem adaptiveN05441PlusP029Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ adaptiveN05441PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05441PlusP029Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05441PlusP029Input2542, Complex.mul_re, Complex.mul_im]

noncomputable def adaptiveN05441PlusValue2542 (i : Fin 30) : ℂ :=
  match i.val with
  | 0 => embedPair2542 adaptiveN05441PlusP000Output2542.1
  | 1 => embedPair2542 adaptiveN05441PlusP001Output2542.1
  | 2 => embedPair2542 adaptiveN05441PlusP002Output2542.1
  | 3 => embedPair2542 adaptiveN05441PlusP003Output2542.1
  | 4 => embedPair2542 adaptiveN05441PlusP004Output2542.1
  | 5 => embedPair2542 adaptiveN05441PlusP005Output2542.1
  | 6 => embedPair2542 adaptiveN05441PlusP006Output2542.1
  | 7 => embedPair2542 adaptiveN05441PlusP007Output2542.1
  | 8 => embedPair2542 adaptiveN05441PlusP008Output2542.1
  | 9 => embedPair2542 adaptiveN05441PlusP009Output2542.1
  | 10 => embedPair2542 adaptiveN05441PlusP010Output2542.1
  | 11 => embedPair2542 adaptiveN05441PlusP011Output2542.1
  | 12 => embedPair2542 adaptiveN05441PlusP012Output2542.1
  | 13 => embedPair2542 adaptiveN05441PlusP013Output2542.1
  | 14 => embedPair2542 adaptiveN05441PlusP014Output2542.1
  | 15 => embedPair2542 adaptiveN05441PlusP015Output2542.1
  | 16 => embedPair2542 adaptiveN05441PlusP016Output2542.1
  | 17 => embedPair2542 adaptiveN05441PlusP017Output2542.1
  | 18 => embedPair2542 adaptiveN05441PlusP018Output2542.1
  | 19 => embedPair2542 adaptiveN05441PlusP019Output2542.1
  | 20 => embedPair2542 adaptiveN05441PlusP020Output2542.1
  | 21 => embedPair2542 adaptiveN05441PlusP021Output2542.1
  | 22 => embedPair2542 adaptiveN05441PlusP022Output2542.1
  | 23 => embedPair2542 adaptiveN05441PlusP023Output2542.1
  | 24 => embedPair2542 adaptiveN05441PlusP024Output2542.1
  | 25 => embedPair2542 adaptiveN05441PlusP025Output2542.1
  | 26 => embedPair2542 adaptiveN05441PlusP026Output2542.1
  | 27 => embedPair2542 adaptiveN05441PlusP027Output2542.1
  | 28 => embedPair2542 adaptiveN05441PlusP028Output2542.1
  | 29 => embedPair2542 adaptiveN05441PlusP029Output2542.1
  | _ => 0

noncomputable def adaptiveN05441PlusError2542 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => (adaptiveN05441PlusP000Output2542.2 : ℝ)
  | 1 => (adaptiveN05441PlusP001Output2542.2 : ℝ)
  | 2 => (adaptiveN05441PlusP002Output2542.2 : ℝ)
  | 3 => (adaptiveN05441PlusP003Output2542.2 : ℝ)
  | 4 => (adaptiveN05441PlusP004Output2542.2 : ℝ)
  | 5 => (adaptiveN05441PlusP005Output2542.2 : ℝ)
  | 6 => (adaptiveN05441PlusP006Output2542.2 : ℝ)
  | 7 => (adaptiveN05441PlusP007Output2542.2 : ℝ)
  | 8 => (adaptiveN05441PlusP008Output2542.2 : ℝ)
  | 9 => (adaptiveN05441PlusP009Output2542.2 : ℝ)
  | 10 => (adaptiveN05441PlusP010Output2542.2 : ℝ)
  | 11 => (adaptiveN05441PlusP011Output2542.2 : ℝ)
  | 12 => (adaptiveN05441PlusP012Output2542.2 : ℝ)
  | 13 => (adaptiveN05441PlusP013Output2542.2 : ℝ)
  | 14 => (adaptiveN05441PlusP014Output2542.2 : ℝ)
  | 15 => (adaptiveN05441PlusP015Output2542.2 : ℝ)
  | 16 => (adaptiveN05441PlusP016Output2542.2 : ℝ)
  | 17 => (adaptiveN05441PlusP017Output2542.2 : ℝ)
  | 18 => (adaptiveN05441PlusP018Output2542.2 : ℝ)
  | 19 => (adaptiveN05441PlusP019Output2542.2 : ℝ)
  | 20 => (adaptiveN05441PlusP020Output2542.2 : ℝ)
  | 21 => (adaptiveN05441PlusP021Output2542.2 : ℝ)
  | 22 => (adaptiveN05441PlusP022Output2542.2 : ℝ)
  | 23 => (adaptiveN05441PlusP023Output2542.2 : ℝ)
  | 24 => (adaptiveN05441PlusP024Output2542.2 : ℝ)
  | 25 => (adaptiveN05441PlusP025Output2542.2 : ℝ)
  | 26 => (adaptiveN05441PlusP026Output2542.2 : ℝ)
  | 27 => (adaptiveN05441PlusP027Output2542.2 : ℝ)
  | 28 => (adaptiveN05441PlusP028Output2542.2 : ℝ)
  | 29 => (adaptiveN05441PlusP029Output2542.2 : ℝ)
  | _ => 0

theorem adaptiveN05441PlusExp_error2542 (i : Fin 30) :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 i adaptiveN05441PlusPosition2542 - adaptiveN05441PlusValue2542 i‖ ≤
            adaptiveN05441PlusError2542 i := by
  fin_cases i
  · simpa only [adaptiveN05441PlusValue2542, adaptiveN05441PlusError2542] using
      adaptiveN05441PlusP000Error2542
  · simpa only [adaptiveN05441PlusValue2542, adaptiveN05441PlusError2542] using
      adaptiveN05441PlusP001Error2542
  · simpa only [adaptiveN05441PlusValue2542, adaptiveN05441PlusError2542] using
      adaptiveN05441PlusP002Error2542
  · simpa only [adaptiveN05441PlusValue2542, adaptiveN05441PlusError2542] using
      adaptiveN05441PlusP003Error2542
  · simpa only [adaptiveN05441PlusValue2542, adaptiveN05441PlusError2542] using
      adaptiveN05441PlusP004Error2542
  · simpa only [adaptiveN05441PlusValue2542, adaptiveN05441PlusError2542] using
      adaptiveN05441PlusP005Error2542
  · simpa only [adaptiveN05441PlusValue2542, adaptiveN05441PlusError2542] using
      adaptiveN05441PlusP006Error2542
  · simpa only [adaptiveN05441PlusValue2542, adaptiveN05441PlusError2542] using
      adaptiveN05441PlusP007Error2542
  · simpa only [adaptiveN05441PlusValue2542, adaptiveN05441PlusError2542] using
      adaptiveN05441PlusP008Error2542
  · simpa only [adaptiveN05441PlusValue2542, adaptiveN05441PlusError2542] using
      adaptiveN05441PlusP009Error2542
  · simpa only [adaptiveN05441PlusValue2542, adaptiveN05441PlusError2542] using
      adaptiveN05441PlusP010Error2542
  · simpa only [adaptiveN05441PlusValue2542, adaptiveN05441PlusError2542] using
      adaptiveN05441PlusP011Error2542
  · simpa only [adaptiveN05441PlusValue2542, adaptiveN05441PlusError2542] using
      adaptiveN05441PlusP012Error2542
  · simpa only [adaptiveN05441PlusValue2542, adaptiveN05441PlusError2542] using
      adaptiveN05441PlusP013Error2542
  · simpa only [adaptiveN05441PlusValue2542, adaptiveN05441PlusError2542] using
      adaptiveN05441PlusP014Error2542
  · simpa only [adaptiveN05441PlusValue2542, adaptiveN05441PlusError2542] using
      adaptiveN05441PlusP015Error2542
  · simpa only [adaptiveN05441PlusValue2542, adaptiveN05441PlusError2542] using
      adaptiveN05441PlusP016Error2542
  · simpa only [adaptiveN05441PlusValue2542, adaptiveN05441PlusError2542] using
      adaptiveN05441PlusP017Error2542
  · simpa only [adaptiveN05441PlusValue2542, adaptiveN05441PlusError2542] using
      adaptiveN05441PlusP018Error2542
  · simpa only [adaptiveN05441PlusValue2542, adaptiveN05441PlusError2542] using
      adaptiveN05441PlusP019Error2542
  · simpa only [adaptiveN05441PlusValue2542, adaptiveN05441PlusError2542] using
      adaptiveN05441PlusP020Error2542
  · simpa only [adaptiveN05441PlusValue2542, adaptiveN05441PlusError2542] using
      adaptiveN05441PlusP021Error2542
  · simpa only [adaptiveN05441PlusValue2542, adaptiveN05441PlusError2542] using
      adaptiveN05441PlusP022Error2542
  · simpa only [adaptiveN05441PlusValue2542, adaptiveN05441PlusError2542] using
      adaptiveN05441PlusP023Error2542
  · simpa only [adaptiveN05441PlusValue2542, adaptiveN05441PlusError2542] using
      adaptiveN05441PlusP024Error2542
  · simpa only [adaptiveN05441PlusValue2542, adaptiveN05441PlusError2542] using
      adaptiveN05441PlusP025Error2542
  · simpa only [adaptiveN05441PlusValue2542, adaptiveN05441PlusError2542] using
      adaptiveN05441PlusP026Error2542
  · simpa only [adaptiveN05441PlusValue2542, adaptiveN05441PlusError2542] using
      adaptiveN05441PlusP027Error2542
  · simpa only [adaptiveN05441PlusValue2542, adaptiveN05441PlusError2542] using
      adaptiveN05441PlusP028Error2542
  · simpa only [adaptiveN05441PlusValue2542, adaptiveN05441PlusError2542] using
      adaptiveN05441PlusP029Error2542

theorem adaptiveN05441PlusUnit_norm2542 (i : Fin 30) :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 i adaptiveN05441PlusPosition2542‖ ≤ 1 := by
  fin_cases i
  · simpa only [adaptiveN05441PlusValue2542, adaptiveN05441PlusError2542] using
      adaptiveN05441PlusP000Norm2542
  · simpa only [adaptiveN05441PlusValue2542, adaptiveN05441PlusError2542] using
      adaptiveN05441PlusP001Norm2542
  · simpa only [adaptiveN05441PlusValue2542, adaptiveN05441PlusError2542] using
      adaptiveN05441PlusP002Norm2542
  · simpa only [adaptiveN05441PlusValue2542, adaptiveN05441PlusError2542] using
      adaptiveN05441PlusP003Norm2542
  · simpa only [adaptiveN05441PlusValue2542, adaptiveN05441PlusError2542] using
      adaptiveN05441PlusP004Norm2542
  · simpa only [adaptiveN05441PlusValue2542, adaptiveN05441PlusError2542] using
      adaptiveN05441PlusP005Norm2542
  · simpa only [adaptiveN05441PlusValue2542, adaptiveN05441PlusError2542] using
      adaptiveN05441PlusP006Norm2542
  · simpa only [adaptiveN05441PlusValue2542, adaptiveN05441PlusError2542] using
      adaptiveN05441PlusP007Norm2542
  · simpa only [adaptiveN05441PlusValue2542, adaptiveN05441PlusError2542] using
      adaptiveN05441PlusP008Norm2542
  · simpa only [adaptiveN05441PlusValue2542, adaptiveN05441PlusError2542] using
      adaptiveN05441PlusP009Norm2542
  · simpa only [adaptiveN05441PlusValue2542, adaptiveN05441PlusError2542] using
      adaptiveN05441PlusP010Norm2542
  · simpa only [adaptiveN05441PlusValue2542, adaptiveN05441PlusError2542] using
      adaptiveN05441PlusP011Norm2542
  · simpa only [adaptiveN05441PlusValue2542, adaptiveN05441PlusError2542] using
      adaptiveN05441PlusP012Norm2542
  · simpa only [adaptiveN05441PlusValue2542, adaptiveN05441PlusError2542] using
      adaptiveN05441PlusP013Norm2542
  · simpa only [adaptiveN05441PlusValue2542, adaptiveN05441PlusError2542] using
      adaptiveN05441PlusP014Norm2542
  · simpa only [adaptiveN05441PlusValue2542, adaptiveN05441PlusError2542] using
      adaptiveN05441PlusP015Norm2542
  · simpa only [adaptiveN05441PlusValue2542, adaptiveN05441PlusError2542] using
      adaptiveN05441PlusP016Norm2542
  · simpa only [adaptiveN05441PlusValue2542, adaptiveN05441PlusError2542] using
      adaptiveN05441PlusP017Norm2542
  · simpa only [adaptiveN05441PlusValue2542, adaptiveN05441PlusError2542] using
      adaptiveN05441PlusP018Norm2542
  · simpa only [adaptiveN05441PlusValue2542, adaptiveN05441PlusError2542] using
      adaptiveN05441PlusP019Norm2542
  · simpa only [adaptiveN05441PlusValue2542, adaptiveN05441PlusError2542] using
      adaptiveN05441PlusP020Norm2542
  · simpa only [adaptiveN05441PlusValue2542, adaptiveN05441PlusError2542] using
      adaptiveN05441PlusP021Norm2542
  · simpa only [adaptiveN05441PlusValue2542, adaptiveN05441PlusError2542] using
      adaptiveN05441PlusP022Norm2542
  · simpa only [adaptiveN05441PlusValue2542, adaptiveN05441PlusError2542] using
      adaptiveN05441PlusP023Norm2542
  · simpa only [adaptiveN05441PlusValue2542, adaptiveN05441PlusError2542] using
      adaptiveN05441PlusP024Norm2542
  · simpa only [adaptiveN05441PlusValue2542, adaptiveN05441PlusError2542] using
      adaptiveN05441PlusP025Norm2542
  · simpa only [adaptiveN05441PlusValue2542, adaptiveN05441PlusError2542] using
      adaptiveN05441PlusP026Norm2542
  · simpa only [adaptiveN05441PlusValue2542, adaptiveN05441PlusError2542] using
      adaptiveN05441PlusP027Norm2542
  · simpa only [adaptiveN05441PlusValue2542, adaptiveN05441PlusError2542] using
      adaptiveN05441PlusP028Norm2542
  · simpa only [adaptiveN05441PlusValue2542, adaptiveN05441PlusError2542] using
      adaptiveN05441PlusP029Norm2542

noncomputable def adaptiveN05441PlusSumValue2542 : ℂ := ⟨(((((4829072 * 10^40
        + 546208695144341111563291571028419457255) * 10^40
        + 5977860088350514075520591071508303357873) * 10^40
        + 2507512592239738090944294669414529073313) : ℝ) /
        (((10830740 * 10^40
        + 9926594330452281804068089207165485823256) * 10^40
        + 8678349675968586177586448361572508999990) * 10^40
        + 23844295226942934417817982702456930304)),
    (((-(((17792678 * 10^40
        + 8730230025930925462713326536899753079315) * 10^40
        + 8382253706232277748448224305176697970474) * 10^40
        + 9220872385200477341435105044853031378499)) : ℝ) /
        (((43322963 * 10^40
        + 9706377321809127216272356828661943293027) * 10^40
        + 4713398703874344710345793446290035999960) * 10^40
        + 95377180907771737671271930809827721216))⟩

noncomputable def adaptiveN05441PlusUpper2542 : ℝ := ((6061937461 : ℝ) /
        10000000000)

theorem adaptiveN05441PlusSum_eq2542 :
    (∑ i : Fin 30, baseCoefficientCenter2540 i * adaptiveN05441PlusValue2542 i) =
      adaptiveN05441PlusSumValue2542 := by
  rw [sum30_chain2541]
  apply Complex.ext <;>
    norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, adaptiveN05441PlusValue2542,
      adaptiveN05441PlusSumValue2542, embedPair2542, adaptiveN05441PlusP000Output2542,
      adaptiveN05441PlusP001Output2542,
      adaptiveN05441PlusP002Output2542,
      adaptiveN05441PlusP003Output2542,
      adaptiveN05441PlusP004Output2542,
      adaptiveN05441PlusP005Output2542,
      adaptiveN05441PlusP006Output2542,
      adaptiveN05441PlusP007Output2542,
      adaptiveN05441PlusP008Output2542,
      adaptiveN05441PlusP009Output2542,
      adaptiveN05441PlusP010Output2542,
      adaptiveN05441PlusP011Output2542,
      adaptiveN05441PlusP012Output2542,
      adaptiveN05441PlusP013Output2542,
      adaptiveN05441PlusP014Output2542,
      adaptiveN05441PlusP015Output2542,
      adaptiveN05441PlusP016Output2542,
      adaptiveN05441PlusP017Output2542,
      adaptiveN05441PlusP018Output2542,
      adaptiveN05441PlusP019Output2542,
      adaptiveN05441PlusP020Output2542,
      adaptiveN05441PlusP021Output2542,
      adaptiveN05441PlusP022Output2542,
      adaptiveN05441PlusP023Output2542,
      adaptiveN05441PlusP024Output2542,
      adaptiveN05441PlusP025Output2542,
      adaptiveN05441PlusP026Output2542,
      adaptiveN05441PlusP027Output2542,
      adaptiveN05441PlusP028Output2542,
      adaptiveN05441PlusP029Output2542, Complex.mul_re, Complex.mul_im]

theorem adaptiveN05441PlusSum_norm2542 :
    ‖∑ i : Fin 30, baseCoefficientCenter2540 i * adaptiveN05441PlusValue2542 i‖ ≤
      ((303096873 : ℝ) /
        500000000) := by
  rw [adaptiveN05441PlusSum_eq2542]
  apply complex_norm_le_of_sq2541 _ _ (by norm_num)
  norm_num [adaptiveN05441PlusSumValue2542]

theorem adaptiveN05441PlusEvaluation_charge2542 :
    (∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
      |(baseCoefficientCenter2540 i).im|) * adaptiveN05441PlusError2542 i) ≤ (1 : ℝ)/10^12 := by
  rw [sum30_chain2541]
  norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, adaptiveN05441PlusError2542,
      adaptiveN05441PlusP000Output2542,
      adaptiveN05441PlusP001Output2542,
      adaptiveN05441PlusP002Output2542,
      adaptiveN05441PlusP003Output2542,
      adaptiveN05441PlusP004Output2542,
      adaptiveN05441PlusP005Output2542,
      adaptiveN05441PlusP006Output2542,
      adaptiveN05441PlusP007Output2542,
      adaptiveN05441PlusP008Output2542,
      adaptiveN05441PlusP009Output2542,
      adaptiveN05441PlusP010Output2542,
      adaptiveN05441PlusP011Output2542,
      adaptiveN05441PlusP012Output2542,
      adaptiveN05441PlusP013Output2542,
      adaptiveN05441PlusP014Output2542,
      adaptiveN05441PlusP015Output2542,
      adaptiveN05441PlusP016Output2542,
      adaptiveN05441PlusP017Output2542,
      adaptiveN05441PlusP018Output2542,
      adaptiveN05441PlusP019Output2542,
      adaptiveN05441PlusP020Output2542,
      adaptiveN05441PlusP021Output2542,
      adaptiveN05441PlusP022Output2542,
      adaptiveN05441PlusP023Output2542,
      adaptiveN05441PlusP024Output2542,
      adaptiveN05441PlusP025Output2542,
      adaptiveN05441PlusP026Output2542,
      adaptiveN05441PlusP027Output2542,
      adaptiveN05441PlusP028Output2542,
      adaptiveN05441PlusP029Output2542]

theorem adaptiveN05441PlusSigned_le2542 :
    signedJetUpper2539 0 (((1 : ℝ) /
        2)) baseCoefficientCenter2540 baseCoefficientError2540
      nodeModulation2541 adaptiveN05441PlusPosition2542 ≤ adaptiveN05441PlusUpper2542 := by
  have hsum :
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i *
        weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 i adaptiveN05441PlusPosition2542‖ ≤
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i * adaptiveN05441PlusValue2542 i‖ +
        ∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
          |(baseCoefficientCenter2540 i).im|) * adaptiveN05441PlusError2542 i := by
    apply norm_sum_le_center_sum_add_error2531
    intro i _
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (Complex.norm_le_abs_re_add_abs_im _) (adaptiveN05441PlusExp_error2542 i)
      (norm_nonneg _) (by positivity)
  have heach : ∀ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 i adaptiveN05441PlusPosition2542‖ ≤
        (1 : ℝ)/10^30 := by
    intro i
    have h := mul_le_mul_of_nonneg_left (adaptiveN05441PlusUnit_norm2542 i)
      (by norm_num [baseCoefficientError2540] : 0 ≤ baseCoefficientError2540 i)
    simpa [baseCoefficientError2540] using h
  have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
  have he' : (∑ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 i adaptiveN05441PlusPosition2542‖) ≤
        (30 : ℝ)/10^30 := by simpa using he
  unfold signedJetUpper2539 adaptiveN05441PlusUpper2542
  linarith [adaptiveN05441PlusSum_norm2542, adaptiveN05441PlusEvaluation_charge2542]

theorem adaptiveN05441PlusPhysical_le2542 (coefficients : Fin 30 → ℂ)
    (hbox : ∀ i, (baseCoefficientBox2540 i).Mem (coefficients i)) :
    ‖weightedPhysical2539 (((1 : ℝ) /
        2)) coefficients nodeModulation2541 adaptiveN05441PlusPosition2542‖ ≤
      adaptiveN05441PlusUpper2542 := by
  have h := weightedPhysical2539_jet_le_center_error 0 (((1 : ℝ) /
        2)) coefficients
    baseCoefficientCenter2540 baseCoefficientError2540 nodeModulation2541
    (fun i => baseCoefficient_error_of_box2540 i (coefficients i) (hbox i))
        adaptiveN05441PlusPosition2542
  simpa only [iteratedDeriv_zero] using h.trans adaptiveN05441PlusSigned_le2542

theorem adaptiveN05441PlusGrid2542 :
    -stripRadius2303 + (5441 : ℝ)*(2*stripRadius2303/10240) = adaptiveN05441PlusPosition2542 := by
  norm_num [stripRadius2303, adaptiveN05441PlusPosition2542]

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.adaptiveN05441PlusSigned_le2542
#print axioms ConnesWeilRH.Dev.adaptiveN05441PlusPhysical_le2542
