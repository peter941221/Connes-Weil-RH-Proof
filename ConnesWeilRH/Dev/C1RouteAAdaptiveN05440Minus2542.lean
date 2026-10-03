import ConnesWeilRH.Dev.C1RouteACompactExp2542
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541

namespace ConnesWeilRH.Dev

open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def adaptiveN05440MinusPosition2542 : ℝ := ((65536001 : ℝ) /
        160000000)

def adaptiveN05440MinusP000Output2542 : RatState2542 :=
  (((((-40974711010205085) : ℚ) /
        1267650600228229401496703205376),
    ((7942517672949573 : ℚ) /
        633825300114114700748351602688)),
    ((27225769980587 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

def adaptiveN05440MinusP000Input2542 : RatPair2542 :=
  ((((-((33 * 10^40
        + 1290059165262451568566309402597100238574) * 10^40
        + 58407946859350584659335737862549108307)) : ℚ) /
        ((68 * 10^40
        + 4108646130446117391380318820003814069094) * 10^40
        + 5827290179342624543465749633167360000000)),
    (((-362039942185747774262029) : ℚ) /
        1441151880758558720000000))

theorem adaptiveN05440MinusP000Compute2542 : compactExp2542 adaptiveN05440MinusP000Input2542 6 =
    adaptiveN05440MinusP000Output2542 := by
  cbv

theorem adaptiveN05440MinusP000Owner2542 : weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ adaptiveN05440MinusPosition2542 =
    Complex.exp ((2 : ℂ)^6 * embedPair2542 adaptiveN05440MinusP000Input2542) := by
  have hx : |adaptiveN05440MinusPosition2542| < storedWidth ⟨0, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05440MinusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05440MinusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05440MinusP000Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05440MinusP000Error2542 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ adaptiveN05440MinusPosition2542 - embedPair2542
            adaptiveN05440MinusP000Output2542.1‖ ≤ (adaptiveN05440MinusP000Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05440MinusP000Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05440MinusP000Input2542]
  rw [adaptiveN05440MinusP000Owner2542]
  have h := compactExp_error2542 adaptiveN05440MinusP000Input2542 hz 6
  simpa only [adaptiveN05440MinusP000Compute2542] using h

theorem adaptiveN05440MinusP000Norm2542 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ adaptiveN05440MinusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05440MinusP000Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05440MinusP000Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05440MinusP001Output2542 : RatState2542 :=
  (((((-14428550937086301) : ℚ) /
        316912650057057350374175801344),
    ((22374585296637089 : ℚ) /
        1267650600228229401496703205376)),
    ((37261833685291 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

def adaptiveN05440MinusP001Input2542 : RatPair2542 :=
  ((((-(424417575296239745199154000011321411027 * 10^40
        + 7930567342231968039510139851389362216201)) : ℚ) /
        (886210261626655755083735189233369746668 * 10^40
        + 3797746372915947800471746154516480000000)),
    (((-362039942185747774262029) : ℚ) /
        1441151880758558720000000))

theorem adaptiveN05440MinusP001Compute2542 : compactExp2542 adaptiveN05440MinusP001Input2542 6 =
    adaptiveN05440MinusP001Output2542 := by
  cbv

theorem adaptiveN05440MinusP001Owner2542 : weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ adaptiveN05440MinusPosition2542 =
    Complex.exp ((2 : ℂ)^6 * embedPair2542 adaptiveN05440MinusP001Input2542) := by
  have hx : |adaptiveN05440MinusPosition2542| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05440MinusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05440MinusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05440MinusP001Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05440MinusP001Error2542 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ adaptiveN05440MinusPosition2542 - embedPair2542
            adaptiveN05440MinusP001Output2542.1‖ ≤ (adaptiveN05440MinusP001Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05440MinusP001Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05440MinusP001Input2542]
  rw [adaptiveN05440MinusP001Owner2542]
  have h := compactExp_error2542 adaptiveN05440MinusP001Input2542 hz 6
  simpa only [adaptiveN05440MinusP001Compute2542] using h

theorem adaptiveN05440MinusP001Norm2542 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ adaptiveN05440MinusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05440MinusP001Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05440MinusP001Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05440MinusP002Output2542 : RatState2542 :=
  (((((-68703646355652623) : ℚ) /
        1267650600228229401496703205376),
    (((-6658740378180367) : ℚ) /
        316912650057057350374175801344)),
    ((21912336934161 : ℚ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888)))

def adaptiveN05440MinusP002Input2542 : RatPair2542 :=
  ((((-((1 * 10^40
        + 1089503407207950123102807654511471321419) * 10^40
        + 1225280447109717097189589041083555224841)) : ℚ) /
        ((2 * 10^40
        + 3288003241060619496441480162260487009338) * 10^40
        + 6963595085534041865672938472263680000000)),
    ((362039942185747774262029 : ℚ) /
        1441151880758558720000000))

theorem adaptiveN05440MinusP002Compute2542 : compactExp2542 adaptiveN05440MinusP002Input2542 6 =
    adaptiveN05440MinusP002Output2542 := by
  cbv

theorem adaptiveN05440MinusP002Owner2542 : weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ adaptiveN05440MinusPosition2542 =
    Complex.exp ((2 : ℂ)^6 * embedPair2542 adaptiveN05440MinusP002Input2542) := by
  have hx : |adaptiveN05440MinusPosition2542| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05440MinusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05440MinusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05440MinusP002Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05440MinusP002Error2542 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ adaptiveN05440MinusPosition2542 - embedPair2542
            adaptiveN05440MinusP002Output2542.1‖ ≤ (adaptiveN05440MinusP002Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05440MinusP002Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05440MinusP002Input2542]
  rw [adaptiveN05440MinusP002Owner2542]
  have h := compactExp_error2542 adaptiveN05440MinusP002Input2542 hz 6
  simpa only [adaptiveN05440MinusP002Compute2542] using h

theorem adaptiveN05440MinusP002Norm2542 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ adaptiveN05440MinusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05440MinusP002Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05440MinusP002Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05440MinusP003Output2542 : RatState2542 :=
  (((((-9458777387197523) : ℚ) /
        158456325028528675187087900672),
    (((-1833484720456021) : ℚ) /
        79228162514264337593543950336)),
    ((47976393930171 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

def adaptiveN05440MinusP003Input2542 : RatPair2542 :=
  ((((-((146 * 10^40
        + 4666505999543186600661552487163202263838) * 10^40
        + 5198120859216655713919987686397705358307)) : ℚ) /
        ((308 * 10^40
        + 5584325157930343245986452666829032621960) * 10^40
        + 3552613615865160449465749633167360000000)),
    ((362039942185747774262029 : ℚ) /
        1441151880758558720000000))

theorem adaptiveN05440MinusP003Compute2542 : compactExp2542 adaptiveN05440MinusP003Input2542 6 =
    adaptiveN05440MinusP003Output2542 := by
  cbv

theorem adaptiveN05440MinusP003Owner2542 : weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ adaptiveN05440MinusPosition2542 =
    Complex.exp ((2 : ℂ)^6 * embedPair2542 adaptiveN05440MinusP003Input2542) := by
  have hx : |adaptiveN05440MinusPosition2542| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05440MinusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05440MinusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05440MinusP003Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05440MinusP003Error2542 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ adaptiveN05440MinusPosition2542 - embedPair2542
            adaptiveN05440MinusP003Output2542.1‖ ≤ (adaptiveN05440MinusP003Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05440MinusP003Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05440MinusP003Input2542]
  rw [adaptiveN05440MinusP003Owner2542]
  have h := compactExp_error2542 adaptiveN05440MinusP003Input2542 hz 6
  simpa only [adaptiveN05440MinusP003Compute2542] using h

theorem adaptiveN05440MinusP003Norm2542 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ adaptiveN05440MinusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05440MinusP003Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05440MinusP003Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05440MinusP004Output2542 : RatState2542 :=
  (((((-80116784298837343) : ℚ) /
        1267650600228229401496703205376),
    ((31059595516606405 : ℚ) /
        1267650600228229401496703205376)),
    ((50623159761603 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

def adaptiveN05440MinusP004Input2542 : RatPair2542 :=
  ((((-((2 * 10^40
        + 5446819663058783993660070886078225195841) * 10^40
        + 2437251345453047163544114024481992724841)) : ℚ) /
        ((5 * 10^40
        + 3709268744536454894037321260456311664067) * 10^40
        + 5409328121924953525672938472263680000000)),
    (((-362039942185747774262029) : ℚ) /
        1441151880758558720000000))

theorem adaptiveN05440MinusP004Compute2542 : compactExp2542 adaptiveN05440MinusP004Input2542 6 =
    adaptiveN05440MinusP004Output2542 := by
  cbv

theorem adaptiveN05440MinusP004Owner2542 : weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ adaptiveN05440MinusPosition2542 =
    Complex.exp ((2 : ℂ)^6 * embedPair2542 adaptiveN05440MinusP004Input2542) := by
  have hx : |adaptiveN05440MinusPosition2542| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05440MinusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05440MinusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05440MinusP004Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05440MinusP004Error2542 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ adaptiveN05440MinusPosition2542 - embedPair2542
            adaptiveN05440MinusP004Output2542.1‖ ≤ (adaptiveN05440MinusP004Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05440MinusP004Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05440MinusP004Input2542]
  rw [adaptiveN05440MinusP004Owner2542]
  have h := compactExp_error2542 adaptiveN05440MinusP004Input2542 hz 6
  simpa only [adaptiveN05440MinusP004Compute2542] using h

theorem adaptiveN05440MinusP004Norm2542 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ adaptiveN05440MinusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05440MinusP004Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05440MinusP004Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05440MinusP005Output2542 : RatState2542 :=
  ((((50689188268019505 : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1)),
    ((6875893870241 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

def adaptiveN05440MinusP005Input2542 : RatPair2542 :=
  ((((-((120 * 10^40
        + 8092596673282430104202541543593795555768) * 10^40
        + 1336442834775297158451777459193116074921)) : ℚ) /
        ((125 * 10^40
        + 3117539759639451663790354394338218649327) * 10^40
        + 8796645127269504130198624449751040000000)),
    ((0 : ℚ) /
        1))

theorem adaptiveN05440MinusP005Compute2542 : compactExp2542 adaptiveN05440MinusP005Input2542 5 =
    adaptiveN05440MinusP005Output2542 := by
  cbv

theorem adaptiveN05440MinusP005Owner2542 : weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ adaptiveN05440MinusPosition2542 =
    Complex.exp ((2 : ℂ)^5 * embedPair2542 adaptiveN05440MinusP005Input2542) := by
  have hx : |adaptiveN05440MinusPosition2542| < storedWidth ⟨5, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05440MinusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05440MinusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05440MinusP005Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05440MinusP005Error2542 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ adaptiveN05440MinusPosition2542 - embedPair2542
            adaptiveN05440MinusP005Output2542.1‖ ≤ (adaptiveN05440MinusP005Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05440MinusP005Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05440MinusP005Input2542]
  rw [adaptiveN05440MinusP005Owner2542]
  have h := compactExp_error2542 adaptiveN05440MinusP005Input2542 hz 5
  simpa only [adaptiveN05440MinusP005Compute2542] using h

theorem adaptiveN05440MinusP005Norm2542 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ adaptiveN05440MinusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05440MinusP005Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05440MinusP005Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05440MinusP006Output2542 : RatState2542 :=
  ((((70332595842747643 : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1)),
    ((8622225740805 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

def adaptiveN05440MinusP006Input2542 : RatPair2542 :=
  ((((-1319574023673334813971797333) : ℚ) /
        1383441177848927569920000000),
    ((0 : ℚ) /
        1))

theorem adaptiveN05440MinusP006Compute2542 : compactExp2542 adaptiveN05440MinusP006Input2542 5 =
    adaptiveN05440MinusP006Output2542 := by
  cbv

theorem adaptiveN05440MinusP006Owner2542 : weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ adaptiveN05440MinusPosition2542 =
    Complex.exp ((2 : ℂ)^5 * embedPair2542 adaptiveN05440MinusP006Input2542) := by
  have hx : |adaptiveN05440MinusPosition2542| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05440MinusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05440MinusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05440MinusP006Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05440MinusP006Error2542 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ adaptiveN05440MinusPosition2542 - embedPair2542
            adaptiveN05440MinusP006Output2542.1‖ ≤ (adaptiveN05440MinusP006Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05440MinusP006Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05440MinusP006Input2542]
  rw [adaptiveN05440MinusP006Owner2542]
  have h := compactExp_error2542 adaptiveN05440MinusP006Input2542 hz 5
  simpa only [adaptiveN05440MinusP006Compute2542] using h

theorem adaptiveN05440MinusP006Norm2542 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ adaptiveN05440MinusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05440MinusP006Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05440MinusP006Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05440MinusP007Output2542 : RatState2542 :=
  ((((81157677459579177 : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1)),
    ((9577754063895 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

def adaptiveN05440MinusP007Input2542 : RatPair2542 :=
  ((((-((146 * 10^40
        + 4666505999543186600661552487163202263838) * 10^40
        + 5198120859216655713919987686397705358307)) : ℚ) /
        ((154 * 10^40
        + 2792162578965171622993226333414516310980) * 10^40
        + 1776306807932580224732874816583680000000)),
    ((0 : ℚ) /
        1))

theorem adaptiveN05440MinusP007Compute2542 : compactExp2542 adaptiveN05440MinusP007Input2542 5 =
    adaptiveN05440MinusP007Output2542 := by
  cbv

theorem adaptiveN05440MinusP007Owner2542 : weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ adaptiveN05440MinusPosition2542 =
    Complex.exp ((2 : ℂ)^5 * embedPair2542 adaptiveN05440MinusP007Input2542) := by
  have hx : |adaptiveN05440MinusPosition2542| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05440MinusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05440MinusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05440MinusP007Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05440MinusP007Error2542 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ adaptiveN05440MinusPosition2542 - embedPair2542
            adaptiveN05440MinusP007Output2542.1‖ ≤ (adaptiveN05440MinusP007Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05440MinusP007Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05440MinusP007Input2542]
  rw [adaptiveN05440MinusP007Owner2542]
  have h := compactExp_error2542 adaptiveN05440MinusP007Input2542 hz 5
  simpa only [adaptiveN05440MinusP007Compute2542] using h

theorem adaptiveN05440MinusP007Norm2542 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ adaptiveN05440MinusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05440MinusP007Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05440MinusP007Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05440MinusP008Output2542 : RatState2542 :=
  ((((49905777083256443 : ℚ) /
        1267650600228229401496703205376),
    ((1678155352085625 : ℚ) /
        79228162514264337593543950336)),
    ((11139676833527 : ℚ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888)))

def adaptiveN05440MinusP008Input2542 : RatPair2542 :=
  ((((-((48 * 10^40
        + 5068468129079000620088176576571579509659) * 10^40
        + 5914912058239751028382499713448486608307)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-260739661220379310273297) : ℚ) /
        2882303761517117440000000))

theorem adaptiveN05440MinusP008Compute2542 : compactExp2542 adaptiveN05440MinusP008Input2542 6 =
    adaptiveN05440MinusP008Output2542 := by
  cbv

theorem adaptiveN05440MinusP008Owner2542 : weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ adaptiveN05440MinusPosition2542 =
    Complex.exp ((2 : ℂ)^6 * embedPair2542 adaptiveN05440MinusP008Input2542) := by
  have hx : |adaptiveN05440MinusPosition2542| < storedWidth ⟨8, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05440MinusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05440MinusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05440MinusP008Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05440MinusP008Error2542 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ adaptiveN05440MinusPosition2542 - embedPair2542
            adaptiveN05440MinusP008Output2542.1‖ ≤ (adaptiveN05440MinusP008Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05440MinusP008Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05440MinusP008Input2542]
  rw [adaptiveN05440MinusP008Owner2542]
  have h := compactExp_error2542 adaptiveN05440MinusP008Input2542 hz 6
  simpa only [adaptiveN05440MinusP008Compute2542] using h

theorem adaptiveN05440MinusP008Norm2542 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ adaptiveN05440MinusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05440MinusP008Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05440MinusP008Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05440MinusP009Output2542 : RatState2542 :=
  (((((-38903466002202859) : ℚ) /
        1267650600228229401496703205376),
    (((-20603734479742617) : ℚ) /
        633825300114114700748351602688)),
    ((16180731248423 : ℚ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888)))

def adaptiveN05440MinusP009Input2542 : RatPair2542 :=
  ((((-((48 * 10^40
        + 5068468129079000620088176576571579509659) * 10^40
        + 5914912058239751028382499713448486608307)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-387788191040974601829711) : ℚ) /
        2882303761517117440000000))

theorem adaptiveN05440MinusP009Compute2542 : compactExp2542 adaptiveN05440MinusP009Input2542 6 =
    adaptiveN05440MinusP009Output2542 := by
  cbv

theorem adaptiveN05440MinusP009Owner2542 : weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ adaptiveN05440MinusPosition2542 =
    Complex.exp ((2 : ℂ)^6 * embedPair2542 adaptiveN05440MinusP009Input2542) := by
  have hx : |adaptiveN05440MinusPosition2542| < storedWidth ⟨9, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05440MinusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05440MinusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05440MinusP009Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05440MinusP009Error2542 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ adaptiveN05440MinusPosition2542 - embedPair2542
            adaptiveN05440MinusP009Output2542.1‖ ≤ (adaptiveN05440MinusP009Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05440MinusP009Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05440MinusP009Input2542]
  rw [adaptiveN05440MinusP009Owner2542]
  have h := compactExp_error2542 adaptiveN05440MinusP009Input2542 hz 6
  simpa only [adaptiveN05440MinusP009Compute2542] using h

theorem adaptiveN05440MinusP009Norm2542 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ adaptiveN05440MinusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05440MinusP009Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05440MinusP009Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05440MinusP010Output2542 : RatState2542 :=
  (((((-19337723936491801) : ℚ) /
        633825300114114700748351602688),
    ((41421551116002657 : ℚ) /
        1267650600228229401496703205376)),
    ((15916450541837 : ℚ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888)))

def adaptiveN05440MinusP010Input2542 : RatPair2542 :=
  ((((-((48 * 10^40
        + 5068468129079000620088176576571579509659) * 10^40
        + 5914912058239751028382499713448486608307)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-230684447942438333698521) : ℚ) /
        1441151880758558720000000))

theorem adaptiveN05440MinusP010Compute2542 : compactExp2542 adaptiveN05440MinusP010Input2542 6 =
    adaptiveN05440MinusP010Output2542 := by
  cbv

theorem adaptiveN05440MinusP010Owner2542 : weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ adaptiveN05440MinusPosition2542 =
    Complex.exp ((2 : ℂ)^6 * embedPair2542 adaptiveN05440MinusP010Input2542) := by
  have hx : |adaptiveN05440MinusPosition2542| < storedWidth ⟨10, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05440MinusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05440MinusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05440MinusP010Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05440MinusP010Error2542 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ adaptiveN05440MinusPosition2542 - embedPair2542
            adaptiveN05440MinusP010Output2542.1‖ ≤ (adaptiveN05440MinusP010Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05440MinusP010Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05440MinusP010Input2542]
  rw [adaptiveN05440MinusP010Owner2542]
  have h := compactExp_error2542 adaptiveN05440MinusP010Input2542 hz 6
  simpa only [adaptiveN05440MinusP010Compute2542] using h

theorem adaptiveN05440MinusP010Norm2542 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ adaptiveN05440MinusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05440MinusP010Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05440MinusP010Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05440MinusP011Output2542 : RatState2542 :=
  ((((18802103677661491 : ℚ) /
        1267650600228229401496703205376),
    ((53460415845052691 : ℚ) /
        1267650600228229401496703205376)),
    ((29293363584939 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

def adaptiveN05440MinusP011Input2542 : RatPair2542 :=
  ((((-((48 * 10^40
        + 5068468129079000620088176576571579509659) * 10^40
        + 5914912058239751028382499713448486608307)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-255213677437476200797801) : ℚ) /
        1441151880758558720000000))

theorem adaptiveN05440MinusP011Compute2542 : compactExp2542 adaptiveN05440MinusP011Input2542 6 =
    adaptiveN05440MinusP011Output2542 := by
  cbv

theorem adaptiveN05440MinusP011Owner2542 : weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ adaptiveN05440MinusPosition2542 =
    Complex.exp ((2 : ℂ)^6 * embedPair2542 adaptiveN05440MinusP011Input2542) := by
  have hx : |adaptiveN05440MinusPosition2542| < storedWidth ⟨11, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05440MinusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05440MinusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05440MinusP011Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05440MinusP011Error2542 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ adaptiveN05440MinusPosition2542 - embedPair2542
            adaptiveN05440MinusP011Output2542.1‖ ≤ (adaptiveN05440MinusP011Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05440MinusP011Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05440MinusP011Input2542]
  rw [adaptiveN05440MinusP011Owner2542]
  have h := compactExp_error2542 adaptiveN05440MinusP011Input2542 hz 6
  simpa only [adaptiveN05440MinusP011Compute2542] using h

theorem adaptiveN05440MinusP011Norm2542 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ adaptiveN05440MinusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05440MinusP011Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05440MinusP011Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05440MinusP012Output2542 : RatState2542 :=
  ((((28181100192677863 : ℚ) /
        633825300114114700748351602688),
    ((5902332822918367 : ℚ) /
        1267650600228229401496703205376)),
    ((8726838324309 : ℚ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888)))

def adaptiveN05440MinusP012Input2542 : RatPair2542 :=
  ((((-((48 * 10^40
        + 5068468129079000620088176576571579509659) * 10^40
        + 5914912058239751028382499713448486608307)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-5612399119318874813509) : ℚ) /
        28823037615171174400000))

theorem adaptiveN05440MinusP012Compute2542 : compactExp2542 adaptiveN05440MinusP012Input2542 6 =
    adaptiveN05440MinusP012Output2542 := by
  cbv

theorem adaptiveN05440MinusP012Owner2542 : weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ adaptiveN05440MinusPosition2542 =
    Complex.exp ((2 : ℂ)^6 * embedPair2542 adaptiveN05440MinusP012Input2542) := by
  have hx : |adaptiveN05440MinusPosition2542| < storedWidth ⟨12, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05440MinusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05440MinusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05440MinusP012Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05440MinusP012Error2542 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ adaptiveN05440MinusPosition2542 - embedPair2542
            adaptiveN05440MinusP012Output2542.1‖ ≤ (adaptiveN05440MinusP012Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05440MinusP012Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05440MinusP012Input2542]
  rw [adaptiveN05440MinusP012Owner2542]
  have h := compactExp_error2542 adaptiveN05440MinusP012Input2542 hz 6
  simpa only [adaptiveN05440MinusP012Compute2542] using h

theorem adaptiveN05440MinusP012Norm2542 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ adaptiveN05440MinusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05440MinusP012Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05440MinusP012Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05440MinusP013Output2542 : RatState2542 :=
  ((((8539775933109667 : ℚ) /
        316912650057057350374175801344),
    (((-45218257343997539) : ℚ) /
        1267650600228229401496703205376)),
    ((27719683342671 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

def adaptiveN05440MinusP013Input2542 : RatPair2542 :=
  ((((-((48 * 10^40
        + 5068468129079000620088176576571579509659) * 10^40
        + 5914912058239751028382499713448486608307)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-60754466143128272313291) : ℚ) /
        288230376151711744000000))

theorem adaptiveN05440MinusP013Compute2542 : compactExp2542 adaptiveN05440MinusP013Input2542 6 =
    adaptiveN05440MinusP013Output2542 := by
  cbv

theorem adaptiveN05440MinusP013Owner2542 : weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ adaptiveN05440MinusPosition2542 =
    Complex.exp ((2 : ℂ)^6 * embedPair2542 adaptiveN05440MinusP013Input2542) := by
  have hx : |adaptiveN05440MinusPosition2542| < storedWidth ⟨13, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05440MinusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05440MinusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05440MinusP013Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05440MinusP013Error2542 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ adaptiveN05440MinusPosition2542 - embedPair2542
            adaptiveN05440MinusP013Output2542.1‖ ≤ (adaptiveN05440MinusP013Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05440MinusP013Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05440MinusP013Input2542]
  rw [adaptiveN05440MinusP013Owner2542]
  have h := compactExp_error2542 adaptiveN05440MinusP013Input2542 hz 6
  simpa only [adaptiveN05440MinusP013Compute2542] using h

theorem adaptiveN05440MinusP013Norm2542 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ adaptiveN05440MinusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05440MinusP013Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05440MinusP013Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05440MinusP014Output2542 : RatState2542 :=
  (((((-53922877994898033) : ℚ) /
        1267650600228229401496703205376),
    (((-17431534464264307) : ℚ) /
        1267650600228229401496703205376)),
    ((32525484933857 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

def adaptiveN05440MinusP014Input2542 : RatPair2542 :=
  ((((-((48 * 10^40
        + 5068468129079000620088176576571579509659) * 10^40
        + 5914912058239751028382499713448486608307)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-346671309892138695845011) : ℚ) /
        1441151880758558720000000))

theorem adaptiveN05440MinusP014Compute2542 : compactExp2542 adaptiveN05440MinusP014Input2542 6 =
    adaptiveN05440MinusP014Output2542 := by
  cbv

theorem adaptiveN05440MinusP014Owner2542 : weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ adaptiveN05440MinusPosition2542 =
    Complex.exp ((2 : ℂ)^6 * embedPair2542 adaptiveN05440MinusP014Input2542) := by
  have hx : |adaptiveN05440MinusPosition2542| < storedWidth ⟨14, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05440MinusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05440MinusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05440MinusP014Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05440MinusP014Error2542 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ adaptiveN05440MinusPosition2542 - embedPair2542
            adaptiveN05440MinusP014Output2542.1‖ ≤ (adaptiveN05440MinusP014Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05440MinusP014Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05440MinusP014Input2542]
  rw [adaptiveN05440MinusP014Owner2542]
  have h := compactExp_error2542 adaptiveN05440MinusP014Input2542 hz 6
  simpa only [adaptiveN05440MinusP014Compute2542] using h

theorem adaptiveN05440MinusP014Norm2542 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ adaptiveN05440MinusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05440MinusP014Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05440MinusP014Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05440MinusP015Output2542 : RatState2542 :=
  (((((-28082237960145599) : ℚ) /
        1267650600228229401496703205376),
    ((24611598262715743 : ℚ) /
        633825300114114700748351602688)),
    ((39773057727481 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

def adaptiveN05440MinusP015Input2542 : RatPair2542 :=
  ((((-((48 * 10^40
        + 5068468129079000620088176576571579509659) * 10^40
        + 5914912058239751028382499713448486608307)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-377408574479356852679047) : ℚ) /
        1441151880758558720000000))

theorem adaptiveN05440MinusP015Compute2542 : compactExp2542 adaptiveN05440MinusP015Input2542 6 =
    adaptiveN05440MinusP015Output2542 := by
  cbv

theorem adaptiveN05440MinusP015Owner2542 : weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ adaptiveN05440MinusPosition2542 =
    Complex.exp ((2 : ℂ)^6 * embedPair2542 adaptiveN05440MinusP015Input2542) := by
  have hx : |adaptiveN05440MinusPosition2542| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05440MinusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05440MinusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05440MinusP015Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05440MinusP015Error2542 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ adaptiveN05440MinusPosition2542 - embedPair2542
            adaptiveN05440MinusP015Output2542.1‖ ≤ (adaptiveN05440MinusP015Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05440MinusP015Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05440MinusP015Input2542]
  rw [adaptiveN05440MinusP015Owner2542]
  have h := compactExp_error2542 adaptiveN05440MinusP015Input2542 hz 6
  simpa only [adaptiveN05440MinusP015Compute2542] using h

theorem adaptiveN05440MinusP015Norm2542 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ adaptiveN05440MinusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05440MinusP015Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05440MinusP015Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05440MinusP016Output2542 : RatState2542 :=
  ((((25564648617501253 : ℚ) /
        1267650600228229401496703205376),
    ((50576515361333307 : ℚ) /
        1267650600228229401496703205376)),
    ((37172189466759 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

def adaptiveN05440MinusP016Input2542 : RatPair2542 :=
  ((((-((48 * 10^40
        + 5068468129079000620088176576571579509659) * 10^40
        + 5914912058239751028382499713448486608307)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-199810861117846303095609) : ℚ) /
        720575940379279360000000))

theorem adaptiveN05440MinusP016Compute2542 : compactExp2542 adaptiveN05440MinusP016Input2542 6 =
    adaptiveN05440MinusP016Output2542 := by
  cbv

theorem adaptiveN05440MinusP016Owner2542 : weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ adaptiveN05440MinusPosition2542 =
    Complex.exp ((2 : ℂ)^6 * embedPair2542 adaptiveN05440MinusP016Input2542) := by
  have hx : |adaptiveN05440MinusPosition2542| < storedWidth ⟨16, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05440MinusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05440MinusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05440MinusP016Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05440MinusP016Error2542 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ adaptiveN05440MinusPosition2542 - embedPair2542
            adaptiveN05440MinusP016Output2542.1‖ ≤ (adaptiveN05440MinusP016Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05440MinusP016Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05440MinusP016Input2542]
  rw [adaptiveN05440MinusP016Owner2542]
  have h := compactExp_error2542 adaptiveN05440MinusP016Input2542 hz 6
  simpa only [adaptiveN05440MinusP016Compute2542] using h

theorem adaptiveN05440MinusP016Norm2542 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ adaptiveN05440MinusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05440MinusP016Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05440MinusP016Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05440MinusP017Output2542 : RatState2542 :=
  ((((19468131813814611 : ℚ) /
        633825300114114700748351602688),
    (((-10294120104916843) : ℚ) /
        316912650057057350374175801344)),
    ((33666964800321 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

def adaptiveN05440MinusP017Input2542 : RatPair2542 :=
  ((((-((48 * 10^40
        + 5068468129079000620088176576571579509659) * 10^40
        + 5914912058239751028382499713448486608307)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-442769373018475956606027) : ℚ) /
        1441151880758558720000000))

theorem adaptiveN05440MinusP017Compute2542 : compactExp2542 adaptiveN05440MinusP017Input2542 6 =
    adaptiveN05440MinusP017Output2542 := by
  cbv

theorem adaptiveN05440MinusP017Owner2542 : weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ adaptiveN05440MinusPosition2542 =
    Complex.exp ((2 : ℂ)^6 * embedPair2542 adaptiveN05440MinusP017Input2542) := by
  have hx : |adaptiveN05440MinusPosition2542| < storedWidth ⟨17, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05440MinusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05440MinusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05440MinusP017Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05440MinusP017Error2542 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ adaptiveN05440MinusPosition2542 - embedPair2542
            adaptiveN05440MinusP017Output2542.1‖ ≤ (adaptiveN05440MinusP017Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05440MinusP017Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05440MinusP017Input2542]
  rw [adaptiveN05440MinusP017Owner2542]
  have h := compactExp_error2542 adaptiveN05440MinusP017Input2542 hz 6
  simpa only [adaptiveN05440MinusP017Compute2542] using h

theorem adaptiveN05440MinusP017Norm2542 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ adaptiveN05440MinusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05440MinusP017Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05440MinusP017Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05440MinusP018Output2542 : RatState2542 :=
  ((((1869226410618573 : ℚ) /
        1267650600228229401496703205376),
    (((-28319786182355521) : ℚ) /
        633825300114114700748351602688)),
    ((19268389507989 : ℚ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888)))

def adaptiveN05440MinusP018Input2542 : RatPair2542 :=
  ((((-((48 * 10^40
        + 5068468129079000620088176576571579509659) * 10^40
        + 5914912058239751028382499713448486608307)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-114770645411675231749613) : ℚ) /
        360287970189639680000000))

theorem adaptiveN05440MinusP018Compute2542 : compactExp2542 adaptiveN05440MinusP018Input2542 6 =
    adaptiveN05440MinusP018Output2542 := by
  cbv

theorem adaptiveN05440MinusP018Owner2542 : weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ adaptiveN05440MinusPosition2542 =
    Complex.exp ((2 : ℂ)^6 * embedPair2542 adaptiveN05440MinusP018Input2542) := by
  have hx : |adaptiveN05440MinusPosition2542| < storedWidth ⟨18, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05440MinusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05440MinusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05440MinusP018Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05440MinusP018Error2542 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ adaptiveN05440MinusPosition2542 - embedPair2542
            adaptiveN05440MinusP018Output2542.1‖ ≤ (adaptiveN05440MinusP018Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05440MinusP018Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05440MinusP018Input2542]
  rw [adaptiveN05440MinusP018Owner2542]
  have h := compactExp_error2542 adaptiveN05440MinusP018Input2542 hz 6
  simpa only [adaptiveN05440MinusP018Compute2542] using h

theorem adaptiveN05440MinusP018Norm2542 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ adaptiveN05440MinusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05440MinusP018Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05440MinusP018Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05440MinusP019Output2542 : RatState2542 :=
  (((((-13557631060402587) : ℚ) /
        316912650057057350374175801344),
    (((-8224740201240481) : ℚ) /
        633825300114114700748351602688)),
    ((15711626783115 : ℚ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888)))

def adaptiveN05440MinusP019Input2542 : RatPair2542 :=
  ((((-((48 * 10^40
        + 5068468129079000620088176576571579509659) * 10^40
        + 5914912058239751028382499713448486608307)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-24428249467783476683391) : ℚ) /
        72057594037927936000000))

theorem adaptiveN05440MinusP019Compute2542 : compactExp2542 adaptiveN05440MinusP019Input2542 6 =
    adaptiveN05440MinusP019Output2542 := by
  cbv

theorem adaptiveN05440MinusP019Owner2542 : weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ adaptiveN05440MinusPosition2542 =
    Complex.exp ((2 : ℂ)^6 * embedPair2542 adaptiveN05440MinusP019Input2542) := by
  have hx : |adaptiveN05440MinusPosition2542| < storedWidth ⟨19, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05440MinusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05440MinusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05440MinusP019Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05440MinusP019Error2542 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ adaptiveN05440MinusPosition2542 - embedPair2542
            adaptiveN05440MinusP019Output2542.1‖ ≤ (adaptiveN05440MinusP019Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05440MinusP019Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05440MinusP019Input2542]
  rw [adaptiveN05440MinusP019Owner2542]
  have h := compactExp_error2542 adaptiveN05440MinusP019Input2542 hz 6
  simpa only [adaptiveN05440MinusP019Compute2542] using h

theorem adaptiveN05440MinusP019Norm2542 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ adaptiveN05440MinusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05440MinusP019Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05440MinusP019Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05440MinusP020Output2542 : RatState2542 :=
  (((((-24218195739792927) : ℚ) /
        1267650600228229401496703205376),
    ((25617446009216885 : ℚ) /
        633825300114114700748351602688)),
    ((32102732821811 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

def adaptiveN05440MinusP020Input2542 : RatPair2542 :=
  ((((-((48 * 10^40
        + 5068468129079000620088176576571579509659) * 10^40
        + 5914912058239751028382499713448486608307)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-520624750538575899551419) : ℚ) /
        1441151880758558720000000))

theorem adaptiveN05440MinusP020Compute2542 : compactExp2542 adaptiveN05440MinusP020Input2542 6 =
    adaptiveN05440MinusP020Output2542 := by
  cbv

theorem adaptiveN05440MinusP020Owner2542 : weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ adaptiveN05440MinusPosition2542 =
    Complex.exp ((2 : ℂ)^6 * embedPair2542 adaptiveN05440MinusP020Input2542) := by
  have hx : |adaptiveN05440MinusPosition2542| < storedWidth ⟨20, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05440MinusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05440MinusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05440MinusP020Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05440MinusP020Error2542 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ adaptiveN05440MinusPosition2542 - embedPair2542
            adaptiveN05440MinusP020Output2542.1‖ ≤ (adaptiveN05440MinusP020Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05440MinusP020Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05440MinusP020Input2542]
  rw [adaptiveN05440MinusP020Owner2542]
  have h := compactExp_error2542 adaptiveN05440MinusP020Input2542 hz 6
  simpa only [adaptiveN05440MinusP020Compute2542] using h

theorem adaptiveN05440MinusP020Norm2542 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ adaptiveN05440MinusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05440MinusP020Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05440MinusP020Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05440MinusP021Output2542 : RatState2542 :=
  ((((1202741799837633 : ℚ) /
        39614081257132168796771975168),
    ((5199503010903097 : ℚ) /
        158456325028528675187087900672)),
    ((11735654166425 : ℚ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888)))

def adaptiveN05440MinusP021Input2542 : RatPair2542 :=
  ((((-((48 * 10^40
        + 5068468129079000620088176576571579509659) * 10^40
        + 5914912058239751028382499713448486608307)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-547379874475946380671387) : ℚ) /
        1441151880758558720000000))

theorem adaptiveN05440MinusP021Compute2542 : compactExp2542 adaptiveN05440MinusP021Input2542 6 =
    adaptiveN05440MinusP021Output2542 := by
  cbv

theorem adaptiveN05440MinusP021Owner2542 : weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ adaptiveN05440MinusPosition2542 =
    Complex.exp ((2 : ℂ)^6 * embedPair2542 adaptiveN05440MinusP021Input2542) := by
  have hx : |adaptiveN05440MinusPosition2542| < storedWidth ⟨21, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05440MinusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05440MinusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05440MinusP021Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05440MinusP021Error2542 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ adaptiveN05440MinusPosition2542 - embedPair2542
            adaptiveN05440MinusP021Output2542.1‖ ≤ (adaptiveN05440MinusP021Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05440MinusP021Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05440MinusP021Input2542]
  rw [adaptiveN05440MinusP021Owner2542]
  have h := compactExp_error2542 adaptiveN05440MinusP021Input2542 hz 6
  simpa only [adaptiveN05440MinusP021Compute2542] using h

theorem adaptiveN05440MinusP021Norm2542 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ adaptiveN05440MinusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05440MinusP021Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05440MinusP021Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05440MinusP022Output2542 : RatState2542 :=
  ((((55352993987341561 : ℚ) /
        1267650600228229401496703205376),
    ((6074150592239659 : ℚ) /
        633825300114114700748351602688)),
    ((4138154524739 : ℚ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944)))

def adaptiveN05440MinusP022Input2542 : RatPair2542 :=
  ((((-((48 * 10^40
        + 5068468129079000620088176576571579509659) * 10^40
        + 5914912058239751028382499713448486608307)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-112214826711468142236233) : ℚ) /
        288230376151711744000000))

theorem adaptiveN05440MinusP022Compute2542 : compactExp2542 adaptiveN05440MinusP022Input2542 6 =
    adaptiveN05440MinusP022Output2542 := by
  cbv

theorem adaptiveN05440MinusP022Owner2542 : weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ adaptiveN05440MinusPosition2542 =
    Complex.exp ((2 : ℂ)^6 * embedPair2542 adaptiveN05440MinusP022Input2542) := by
  have hx : |adaptiveN05440MinusPosition2542| < storedWidth ⟨22, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05440MinusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05440MinusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05440MinusP022Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05440MinusP022Error2542 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ adaptiveN05440MinusPosition2542 - embedPair2542
            adaptiveN05440MinusP022Output2542.1‖ ≤ (adaptiveN05440MinusP022Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05440MinusP022Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05440MinusP022Input2542]
  rw [adaptiveN05440MinusP022Owner2542]
  have h := compactExp_error2542 adaptiveN05440MinusP022Input2542 hz 6
  simpa only [adaptiveN05440MinusP022Compute2542] using h

theorem adaptiveN05440MinusP022Norm2542 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ adaptiveN05440MinusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05440MinusP022Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05440MinusP022Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05440MinusP023Output2542 : RatState2542 :=
  ((((1894654674811975 : ℚ) /
        1267650600228229401496703205376),
    (((-56638727463588957) : ℚ) /
        1267650600228229401496703205376)),
    ((15250065435635 : ℚ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888)))

def adaptiveN05440MinusP023Input2542 : RatPair2542 :=
  ((((-((48 * 10^40
        + 5068468129079000620088176576571579509659) * 10^40
        + 5914912058239751028382499713448486608307)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-300278613592663314364333) : ℚ) /
        720575940379279360000000))

theorem adaptiveN05440MinusP023Compute2542 : compactExp2542 adaptiveN05440MinusP023Input2542 6 =
    adaptiveN05440MinusP023Output2542 := by
  cbv

theorem adaptiveN05440MinusP023Owner2542 : weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ adaptiveN05440MinusPosition2542 =
    Complex.exp ((2 : ℂ)^6 * embedPair2542 adaptiveN05440MinusP023Input2542) := by
  have hx : |adaptiveN05440MinusPosition2542| < storedWidth ⟨23, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05440MinusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05440MinusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05440MinusP023Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05440MinusP023Error2542 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ adaptiveN05440MinusPosition2542 - embedPair2542
            adaptiveN05440MinusP023Output2542.1‖ ≤ (adaptiveN05440MinusP023Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05440MinusP023Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05440MinusP023Input2542]
  rw [adaptiveN05440MinusP023Owner2542]
  have h := compactExp_error2542 adaptiveN05440MinusP023Input2542 hz 6
  simpa only [adaptiveN05440MinusP023Compute2542] using h

theorem adaptiveN05440MinusP023Norm2542 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ adaptiveN05440MinusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05440MinusP023Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05440MinusP023Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05440MinusP024Output2542 : RatState2542 :=
  (((((-39545899385971705) : ℚ) /
        1267650600228229401496703205376),
    (((-5073917690604839) : ℚ) /
        158456325028528675187087900672)),
    ((16579333641141 : ℚ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888)))

def adaptiveN05440MinusP024Input2542 : RatPair2542 :=
  ((((-((48 * 10^40
        + 5068468129079000620088176576571579509659) * 10^40
        + 5914912058239751028382499713448486608307)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-309351029057948556428147) : ℚ) /
        720575940379279360000000))

theorem adaptiveN05440MinusP024Compute2542 : compactExp2542 adaptiveN05440MinusP024Input2542 6 =
    adaptiveN05440MinusP024Output2542 := by
  cbv

theorem adaptiveN05440MinusP024Owner2542 : weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ adaptiveN05440MinusPosition2542 =
    Complex.exp ((2 : ℂ)^6 * embedPair2542 adaptiveN05440MinusP024Input2542) := by
  have hx : |adaptiveN05440MinusPosition2542| < storedWidth ⟨24, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05440MinusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05440MinusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05440MinusP024Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05440MinusP024Error2542 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ adaptiveN05440MinusPosition2542 - embedPair2542
            adaptiveN05440MinusP024Output2542.1‖ ≤ (adaptiveN05440MinusP024Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05440MinusP024Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05440MinusP024Input2542]
  rw [adaptiveN05440MinusP024Owner2542]
  have h := compactExp_error2542 adaptiveN05440MinusP024Input2542 hz 6
  simpa only [adaptiveN05440MinusP024Compute2542] using h

theorem adaptiveN05440MinusP024Norm2542 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ adaptiveN05440MinusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05440MinusP024Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05440MinusP024Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05440MinusP025Output2542 : RatState2542 :=
  (((((-55403190914160447) : ℚ) /
        1267650600228229401496703205376),
    ((11917281634692621 : ℚ) /
        1267650600228229401496703205376)),
    ((15805855028149 : ℚ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888)))

def adaptiveN05440MinusP025Input2542 : RatPair2542 :=
  ((((-((48 * 10^40
        + 5068468129079000620088176576571579509659) * 10^40
        + 5914912058239751028382499713448486608307)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-10022692915539018190833) : ℚ) /
        22517998136852480000000))

theorem adaptiveN05440MinusP025Compute2542 : compactExp2542 adaptiveN05440MinusP025Input2542 6 =
    adaptiveN05440MinusP025Output2542 := by
  cbv

theorem adaptiveN05440MinusP025Owner2542 : weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ adaptiveN05440MinusPosition2542 =
    Complex.exp ((2 : ℂ)^6 * embedPair2542 adaptiveN05440MinusP025Input2542) := by
  have hx : |adaptiveN05440MinusPosition2542| < storedWidth ⟨25, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05440MinusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05440MinusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05440MinusP025Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05440MinusP025Error2542 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ adaptiveN05440MinusPosition2542 - embedPair2542
            adaptiveN05440MinusP025Output2542.1‖ ≤ (adaptiveN05440MinusP025Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05440MinusP025Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05440MinusP025Input2542]
  rw [adaptiveN05440MinusP025Owner2542]
  have h := compactExp_error2542 adaptiveN05440MinusP025Input2542 hz 6
  simpa only [adaptiveN05440MinusP025Compute2542] using h

theorem adaptiveN05440MinusP025Norm2542 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ adaptiveN05440MinusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05440MinusP025Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05440MinusP025Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05440MinusP026Output2542 : RatState2542 :=
  (((((-18171706321072569) : ℚ) /
        1267650600228229401496703205376),
    ((13419492013513831 : ℚ) /
        316912650057057350374175801344)),
    ((20380821283677 : ℚ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888)))

def adaptiveN05440MinusP026Input2542 : RatPair2542 :=
  ((((-((48 * 10^40
        + 5068468129079000620088176576571579509659) * 10^40
        + 5914912058239751028382499713448486608307)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-20771944281655350607437) : ℚ) /
        45035996273704960000000))

theorem adaptiveN05440MinusP026Compute2542 : compactExp2542 adaptiveN05440MinusP026Input2542 6 =
    adaptiveN05440MinusP026Output2542 := by
  cbv

theorem adaptiveN05440MinusP026Owner2542 : weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ adaptiveN05440MinusPosition2542 =
    Complex.exp ((2 : ℂ)^6 * embedPair2542 adaptiveN05440MinusP026Input2542) := by
  have hx : |adaptiveN05440MinusPosition2542| < storedWidth ⟨26, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05440MinusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05440MinusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05440MinusP026Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05440MinusP026Error2542 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ adaptiveN05440MinusPosition2542 - embedPair2542
            adaptiveN05440MinusP026Output2542.1‖ ≤ (adaptiveN05440MinusP026Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05440MinusP026Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05440MinusP026Input2542]
  rw [adaptiveN05440MinusP026Owner2542]
  have h := compactExp_error2542 adaptiveN05440MinusP026Input2542 hz 6
  simpa only [adaptiveN05440MinusP026Compute2542] using h

theorem adaptiveN05440MinusP026Norm2542 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ adaptiveN05440MinusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05440MinusP026Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05440MinusP026Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05440MinusP027Output2542 : RatState2542 :=
  ((((52034755416156523 : ℚ) /
        1267650600228229401496703205376),
    ((5612037251592899 : ℚ) /
        316912650057057350374175801344)),
    ((15414513008267 : ℚ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888)))

def adaptiveN05440MinusP027Input2542 : RatPair2542 :=
  ((((-((48 * 10^40
        + 5068468129079000620088176576571579509659) * 10^40
        + 5914912058239751028382499713448486608307)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-43640783619197408678627) : ℚ) /
        90071992547409920000000))

theorem adaptiveN05440MinusP027Compute2542 : compactExp2542 adaptiveN05440MinusP027Input2542 6 =
    adaptiveN05440MinusP027Output2542 := by
  cbv

theorem adaptiveN05440MinusP027Owner2542 : weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ adaptiveN05440MinusPosition2542 =
    Complex.exp ((2 : ℂ)^6 * embedPair2542 adaptiveN05440MinusP027Input2542) := by
  have hx : |adaptiveN05440MinusPosition2542| < storedWidth ⟨27, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05440MinusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05440MinusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05440MinusP027Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05440MinusP027Error2542 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ adaptiveN05440MinusPosition2542 - embedPair2542
            adaptiveN05440MinusP027Output2542.1‖ ≤ (adaptiveN05440MinusP027Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05440MinusP027Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05440MinusP027Input2542]
  rw [adaptiveN05440MinusP027Owner2542]
  have h := compactExp_error2542 adaptiveN05440MinusP027Input2542 hz 6
  simpa only [adaptiveN05440MinusP027Compute2542] using h

theorem adaptiveN05440MinusP027Norm2542 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ adaptiveN05440MinusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05440MinusP027Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05440MinusP027Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05440MinusP028Output2542 : RatState2542 :=
  ((((55728251971754459 : ℚ) /
        1267650600228229401496703205376),
    (((-643164470375707) : ℚ) /
        79228162514264337593543950336)),
    ((27691895472287 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

def adaptiveN05440MinusP028Input2542 : RatPair2542 :=
  ((((-((48 * 10^40
        + 5068468129079000620088176576571579509659) * 10^40
        + 5914912058239751028382499713448486608307)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-177883892884016178388727) : ℚ) /
        360287970189639680000000))

theorem adaptiveN05440MinusP028Compute2542 : compactExp2542 adaptiveN05440MinusP028Input2542 6 =
    adaptiveN05440MinusP028Output2542 := by
  cbv

theorem adaptiveN05440MinusP028Owner2542 : weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ adaptiveN05440MinusPosition2542 =
    Complex.exp ((2 : ℂ)^6 * embedPair2542 adaptiveN05440MinusP028Input2542) := by
  have hx : |adaptiveN05440MinusPosition2542| < storedWidth ⟨28, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05440MinusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05440MinusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05440MinusP028Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05440MinusP028Error2542 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ adaptiveN05440MinusPosition2542 - embedPair2542
            adaptiveN05440MinusP028Output2542.1‖ ≤ (adaptiveN05440MinusP028Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05440MinusP028Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05440MinusP028Input2542]
  rw [adaptiveN05440MinusP028Owner2542]
  have h := compactExp_error2542 adaptiveN05440MinusP028Input2542 hz 6
  simpa only [adaptiveN05440MinusP028Compute2542] using h

theorem adaptiveN05440MinusP028Norm2542 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ adaptiveN05440MinusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05440MinusP028Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05440MinusP028Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05440MinusP029Output2542 : RatState2542 :=
  ((((26677239168008587 : ℚ) /
        1267650600228229401496703205376),
    (((-12499650183616043) : ℚ) /
        316912650057057350374175801344)),
    ((40476134981187 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

def adaptiveN05440MinusP029Input2542 : RatPair2542 :=
  ((((-((48 * 10^40
        + 5068468129079000620088176576571579509659) * 10^40
        + 5914912058239751028382499713448486608307)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-182939534351242879487659) : ℚ) /
        360287970189639680000000))

theorem adaptiveN05440MinusP029Compute2542 : compactExp2542 adaptiveN05440MinusP029Input2542 6 =
    adaptiveN05440MinusP029Output2542 := by
  cbv

theorem adaptiveN05440MinusP029Owner2542 : weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ adaptiveN05440MinusPosition2542 =
    Complex.exp ((2 : ℂ)^6 * embedPair2542 adaptiveN05440MinusP029Input2542) := by
  have hx : |adaptiveN05440MinusPosition2542| < storedWidth ⟨29, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05440MinusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05440MinusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05440MinusP029Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05440MinusP029Error2542 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ adaptiveN05440MinusPosition2542 - embedPair2542
            adaptiveN05440MinusP029Output2542.1‖ ≤ (adaptiveN05440MinusP029Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05440MinusP029Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05440MinusP029Input2542]
  rw [adaptiveN05440MinusP029Owner2542]
  have h := compactExp_error2542 adaptiveN05440MinusP029Input2542 hz 6
  simpa only [adaptiveN05440MinusP029Compute2542] using h

theorem adaptiveN05440MinusP029Norm2542 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ adaptiveN05440MinusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05440MinusP029Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05440MinusP029Input2542, Complex.mul_re, Complex.mul_im]

noncomputable def adaptiveN05440MinusValue2542 (i : Fin 30) : ℂ :=
  match i.val with
  | 0 => embedPair2542 adaptiveN05440MinusP000Output2542.1
  | 1 => embedPair2542 adaptiveN05440MinusP001Output2542.1
  | 2 => embedPair2542 adaptiveN05440MinusP002Output2542.1
  | 3 => embedPair2542 adaptiveN05440MinusP003Output2542.1
  | 4 => embedPair2542 adaptiveN05440MinusP004Output2542.1
  | 5 => embedPair2542 adaptiveN05440MinusP005Output2542.1
  | 6 => embedPair2542 adaptiveN05440MinusP006Output2542.1
  | 7 => embedPair2542 adaptiveN05440MinusP007Output2542.1
  | 8 => embedPair2542 adaptiveN05440MinusP008Output2542.1
  | 9 => embedPair2542 adaptiveN05440MinusP009Output2542.1
  | 10 => embedPair2542 adaptiveN05440MinusP010Output2542.1
  | 11 => embedPair2542 adaptiveN05440MinusP011Output2542.1
  | 12 => embedPair2542 adaptiveN05440MinusP012Output2542.1
  | 13 => embedPair2542 adaptiveN05440MinusP013Output2542.1
  | 14 => embedPair2542 adaptiveN05440MinusP014Output2542.1
  | 15 => embedPair2542 adaptiveN05440MinusP015Output2542.1
  | 16 => embedPair2542 adaptiveN05440MinusP016Output2542.1
  | 17 => embedPair2542 adaptiveN05440MinusP017Output2542.1
  | 18 => embedPair2542 adaptiveN05440MinusP018Output2542.1
  | 19 => embedPair2542 adaptiveN05440MinusP019Output2542.1
  | 20 => embedPair2542 adaptiveN05440MinusP020Output2542.1
  | 21 => embedPair2542 adaptiveN05440MinusP021Output2542.1
  | 22 => embedPair2542 adaptiveN05440MinusP022Output2542.1
  | 23 => embedPair2542 adaptiveN05440MinusP023Output2542.1
  | 24 => embedPair2542 adaptiveN05440MinusP024Output2542.1
  | 25 => embedPair2542 adaptiveN05440MinusP025Output2542.1
  | 26 => embedPair2542 adaptiveN05440MinusP026Output2542.1
  | 27 => embedPair2542 adaptiveN05440MinusP027Output2542.1
  | 28 => embedPair2542 adaptiveN05440MinusP028Output2542.1
  | 29 => embedPair2542 adaptiveN05440MinusP029Output2542.1
  | _ => 0

noncomputable def adaptiveN05440MinusError2542 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => (adaptiveN05440MinusP000Output2542.2 : ℝ)
  | 1 => (adaptiveN05440MinusP001Output2542.2 : ℝ)
  | 2 => (adaptiveN05440MinusP002Output2542.2 : ℝ)
  | 3 => (adaptiveN05440MinusP003Output2542.2 : ℝ)
  | 4 => (adaptiveN05440MinusP004Output2542.2 : ℝ)
  | 5 => (adaptiveN05440MinusP005Output2542.2 : ℝ)
  | 6 => (adaptiveN05440MinusP006Output2542.2 : ℝ)
  | 7 => (adaptiveN05440MinusP007Output2542.2 : ℝ)
  | 8 => (adaptiveN05440MinusP008Output2542.2 : ℝ)
  | 9 => (adaptiveN05440MinusP009Output2542.2 : ℝ)
  | 10 => (adaptiveN05440MinusP010Output2542.2 : ℝ)
  | 11 => (adaptiveN05440MinusP011Output2542.2 : ℝ)
  | 12 => (adaptiveN05440MinusP012Output2542.2 : ℝ)
  | 13 => (adaptiveN05440MinusP013Output2542.2 : ℝ)
  | 14 => (adaptiveN05440MinusP014Output2542.2 : ℝ)
  | 15 => (adaptiveN05440MinusP015Output2542.2 : ℝ)
  | 16 => (adaptiveN05440MinusP016Output2542.2 : ℝ)
  | 17 => (adaptiveN05440MinusP017Output2542.2 : ℝ)
  | 18 => (adaptiveN05440MinusP018Output2542.2 : ℝ)
  | 19 => (adaptiveN05440MinusP019Output2542.2 : ℝ)
  | 20 => (adaptiveN05440MinusP020Output2542.2 : ℝ)
  | 21 => (adaptiveN05440MinusP021Output2542.2 : ℝ)
  | 22 => (adaptiveN05440MinusP022Output2542.2 : ℝ)
  | 23 => (adaptiveN05440MinusP023Output2542.2 : ℝ)
  | 24 => (adaptiveN05440MinusP024Output2542.2 : ℝ)
  | 25 => (adaptiveN05440MinusP025Output2542.2 : ℝ)
  | 26 => (adaptiveN05440MinusP026Output2542.2 : ℝ)
  | 27 => (adaptiveN05440MinusP027Output2542.2 : ℝ)
  | 28 => (adaptiveN05440MinusP028Output2542.2 : ℝ)
  | 29 => (adaptiveN05440MinusP029Output2542.2 : ℝ)
  | _ => 0

theorem adaptiveN05440MinusExp_error2542 (i : Fin 30) :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 i adaptiveN05440MinusPosition2542 - adaptiveN05440MinusValue2542 i‖
            ≤ adaptiveN05440MinusError2542 i := by
  fin_cases i
  · simpa only [adaptiveN05440MinusValue2542, adaptiveN05440MinusError2542] using
      adaptiveN05440MinusP000Error2542
  · simpa only [adaptiveN05440MinusValue2542, adaptiveN05440MinusError2542] using
      adaptiveN05440MinusP001Error2542
  · simpa only [adaptiveN05440MinusValue2542, adaptiveN05440MinusError2542] using
      adaptiveN05440MinusP002Error2542
  · simpa only [adaptiveN05440MinusValue2542, adaptiveN05440MinusError2542] using
      adaptiveN05440MinusP003Error2542
  · simpa only [adaptiveN05440MinusValue2542, adaptiveN05440MinusError2542] using
      adaptiveN05440MinusP004Error2542
  · simpa only [adaptiveN05440MinusValue2542, adaptiveN05440MinusError2542] using
      adaptiveN05440MinusP005Error2542
  · simpa only [adaptiveN05440MinusValue2542, adaptiveN05440MinusError2542] using
      adaptiveN05440MinusP006Error2542
  · simpa only [adaptiveN05440MinusValue2542, adaptiveN05440MinusError2542] using
      adaptiveN05440MinusP007Error2542
  · simpa only [adaptiveN05440MinusValue2542, adaptiveN05440MinusError2542] using
      adaptiveN05440MinusP008Error2542
  · simpa only [adaptiveN05440MinusValue2542, adaptiveN05440MinusError2542] using
      adaptiveN05440MinusP009Error2542
  · simpa only [adaptiveN05440MinusValue2542, adaptiveN05440MinusError2542] using
      adaptiveN05440MinusP010Error2542
  · simpa only [adaptiveN05440MinusValue2542, adaptiveN05440MinusError2542] using
      adaptiveN05440MinusP011Error2542
  · simpa only [adaptiveN05440MinusValue2542, adaptiveN05440MinusError2542] using
      adaptiveN05440MinusP012Error2542
  · simpa only [adaptiveN05440MinusValue2542, adaptiveN05440MinusError2542] using
      adaptiveN05440MinusP013Error2542
  · simpa only [adaptiveN05440MinusValue2542, adaptiveN05440MinusError2542] using
      adaptiveN05440MinusP014Error2542
  · simpa only [adaptiveN05440MinusValue2542, adaptiveN05440MinusError2542] using
      adaptiveN05440MinusP015Error2542
  · simpa only [adaptiveN05440MinusValue2542, adaptiveN05440MinusError2542] using
      adaptiveN05440MinusP016Error2542
  · simpa only [adaptiveN05440MinusValue2542, adaptiveN05440MinusError2542] using
      adaptiveN05440MinusP017Error2542
  · simpa only [adaptiveN05440MinusValue2542, adaptiveN05440MinusError2542] using
      adaptiveN05440MinusP018Error2542
  · simpa only [adaptiveN05440MinusValue2542, adaptiveN05440MinusError2542] using
      adaptiveN05440MinusP019Error2542
  · simpa only [adaptiveN05440MinusValue2542, adaptiveN05440MinusError2542] using
      adaptiveN05440MinusP020Error2542
  · simpa only [adaptiveN05440MinusValue2542, adaptiveN05440MinusError2542] using
      adaptiveN05440MinusP021Error2542
  · simpa only [adaptiveN05440MinusValue2542, adaptiveN05440MinusError2542] using
      adaptiveN05440MinusP022Error2542
  · simpa only [adaptiveN05440MinusValue2542, adaptiveN05440MinusError2542] using
      adaptiveN05440MinusP023Error2542
  · simpa only [adaptiveN05440MinusValue2542, adaptiveN05440MinusError2542] using
      adaptiveN05440MinusP024Error2542
  · simpa only [adaptiveN05440MinusValue2542, adaptiveN05440MinusError2542] using
      adaptiveN05440MinusP025Error2542
  · simpa only [adaptiveN05440MinusValue2542, adaptiveN05440MinusError2542] using
      adaptiveN05440MinusP026Error2542
  · simpa only [adaptiveN05440MinusValue2542, adaptiveN05440MinusError2542] using
      adaptiveN05440MinusP027Error2542
  · simpa only [adaptiveN05440MinusValue2542, adaptiveN05440MinusError2542] using
      adaptiveN05440MinusP028Error2542
  · simpa only [adaptiveN05440MinusValue2542, adaptiveN05440MinusError2542] using
      adaptiveN05440MinusP029Error2542

theorem adaptiveN05440MinusUnit_norm2542 (i : Fin 30) :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 i adaptiveN05440MinusPosition2542‖ ≤ 1 := by
  fin_cases i
  · simpa only [adaptiveN05440MinusValue2542, adaptiveN05440MinusError2542] using
      adaptiveN05440MinusP000Norm2542
  · simpa only [adaptiveN05440MinusValue2542, adaptiveN05440MinusError2542] using
      adaptiveN05440MinusP001Norm2542
  · simpa only [adaptiveN05440MinusValue2542, adaptiveN05440MinusError2542] using
      adaptiveN05440MinusP002Norm2542
  · simpa only [adaptiveN05440MinusValue2542, adaptiveN05440MinusError2542] using
      adaptiveN05440MinusP003Norm2542
  · simpa only [adaptiveN05440MinusValue2542, adaptiveN05440MinusError2542] using
      adaptiveN05440MinusP004Norm2542
  · simpa only [adaptiveN05440MinusValue2542, adaptiveN05440MinusError2542] using
      adaptiveN05440MinusP005Norm2542
  · simpa only [adaptiveN05440MinusValue2542, adaptiveN05440MinusError2542] using
      adaptiveN05440MinusP006Norm2542
  · simpa only [adaptiveN05440MinusValue2542, adaptiveN05440MinusError2542] using
      adaptiveN05440MinusP007Norm2542
  · simpa only [adaptiveN05440MinusValue2542, adaptiveN05440MinusError2542] using
      adaptiveN05440MinusP008Norm2542
  · simpa only [adaptiveN05440MinusValue2542, adaptiveN05440MinusError2542] using
      adaptiveN05440MinusP009Norm2542
  · simpa only [adaptiveN05440MinusValue2542, adaptiveN05440MinusError2542] using
      adaptiveN05440MinusP010Norm2542
  · simpa only [adaptiveN05440MinusValue2542, adaptiveN05440MinusError2542] using
      adaptiveN05440MinusP011Norm2542
  · simpa only [adaptiveN05440MinusValue2542, adaptiveN05440MinusError2542] using
      adaptiveN05440MinusP012Norm2542
  · simpa only [adaptiveN05440MinusValue2542, adaptiveN05440MinusError2542] using
      adaptiveN05440MinusP013Norm2542
  · simpa only [adaptiveN05440MinusValue2542, adaptiveN05440MinusError2542] using
      adaptiveN05440MinusP014Norm2542
  · simpa only [adaptiveN05440MinusValue2542, adaptiveN05440MinusError2542] using
      adaptiveN05440MinusP015Norm2542
  · simpa only [adaptiveN05440MinusValue2542, adaptiveN05440MinusError2542] using
      adaptiveN05440MinusP016Norm2542
  · simpa only [adaptiveN05440MinusValue2542, adaptiveN05440MinusError2542] using
      adaptiveN05440MinusP017Norm2542
  · simpa only [adaptiveN05440MinusValue2542, adaptiveN05440MinusError2542] using
      adaptiveN05440MinusP018Norm2542
  · simpa only [adaptiveN05440MinusValue2542, adaptiveN05440MinusError2542] using
      adaptiveN05440MinusP019Norm2542
  · simpa only [adaptiveN05440MinusValue2542, adaptiveN05440MinusError2542] using
      adaptiveN05440MinusP020Norm2542
  · simpa only [adaptiveN05440MinusValue2542, adaptiveN05440MinusError2542] using
      adaptiveN05440MinusP021Norm2542
  · simpa only [adaptiveN05440MinusValue2542, adaptiveN05440MinusError2542] using
      adaptiveN05440MinusP022Norm2542
  · simpa only [adaptiveN05440MinusValue2542, adaptiveN05440MinusError2542] using
      adaptiveN05440MinusP023Norm2542
  · simpa only [adaptiveN05440MinusValue2542, adaptiveN05440MinusError2542] using
      adaptiveN05440MinusP024Norm2542
  · simpa only [adaptiveN05440MinusValue2542, adaptiveN05440MinusError2542] using
      adaptiveN05440MinusP025Norm2542
  · simpa only [adaptiveN05440MinusValue2542, adaptiveN05440MinusError2542] using
      adaptiveN05440MinusP026Norm2542
  · simpa only [adaptiveN05440MinusValue2542, adaptiveN05440MinusError2542] using
      adaptiveN05440MinusP027Norm2542
  · simpa only [adaptiveN05440MinusValue2542, adaptiveN05440MinusError2542] using
      adaptiveN05440MinusP028Norm2542
  · simpa only [adaptiveN05440MinusValue2542, adaptiveN05440MinusError2542] using
      adaptiveN05440MinusP029Norm2542

noncomputable def adaptiveN05440MinusSumValue2542 : ℂ := ⟨(((((3308863 * 10^40
        + 1457526202056050565370770699042711683614) * 10^40
        + 3274567882976662725472565310651598716783) * 10^40
        + 3969581876902298473435917725672662335445) : ℝ) /
        (((10830740 * 10^40
        + 9926594330452281804068089207165485823256) * 10^40
        + 8678349675968586177586448361572508999990) * 10^40
        + 23844295226942934417817982702456930304)),
    (((-(((10026258 * 10^40
        + 908462726282454835498420668289821246246) * 10^40
        + 3719598386632679148105343040242987080120) * 10^40
        + 1367401390754665866014458452395176729669)) : ℝ) /
        (((43322963 * 10^40
        + 9706377321809127216272356828661943293027) * 10^40
        + 4713398703874344710345793446290035999960) * 10^40
        + 95377180907771737671271930809827721216))⟩

noncomputable def adaptiveN05440MinusUpper2542 : ℝ := ((766536121 : ℝ) /
        2000000000)

theorem adaptiveN05440MinusSum_eq2542 :
    (∑ i : Fin 30, baseCoefficientCenter2540 i * adaptiveN05440MinusValue2542 i) =
      adaptiveN05440MinusSumValue2542 := by
  rw [sum30_chain2541]
  apply Complex.ext <;>
    norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, adaptiveN05440MinusValue2542,
      adaptiveN05440MinusSumValue2542, embedPair2542, adaptiveN05440MinusP000Output2542,
      adaptiveN05440MinusP001Output2542,
      adaptiveN05440MinusP002Output2542,
      adaptiveN05440MinusP003Output2542,
      adaptiveN05440MinusP004Output2542,
      adaptiveN05440MinusP005Output2542,
      adaptiveN05440MinusP006Output2542,
      adaptiveN05440MinusP007Output2542,
      adaptiveN05440MinusP008Output2542,
      adaptiveN05440MinusP009Output2542,
      adaptiveN05440MinusP010Output2542,
      adaptiveN05440MinusP011Output2542,
      adaptiveN05440MinusP012Output2542,
      adaptiveN05440MinusP013Output2542,
      adaptiveN05440MinusP014Output2542,
      adaptiveN05440MinusP015Output2542,
      adaptiveN05440MinusP016Output2542,
      adaptiveN05440MinusP017Output2542,
      adaptiveN05440MinusP018Output2542,
      adaptiveN05440MinusP019Output2542,
      adaptiveN05440MinusP020Output2542,
      adaptiveN05440MinusP021Output2542,
      adaptiveN05440MinusP022Output2542,
      adaptiveN05440MinusP023Output2542,
      adaptiveN05440MinusP024Output2542,
      adaptiveN05440MinusP025Output2542,
      adaptiveN05440MinusP026Output2542,
      adaptiveN05440MinusP027Output2542,
      adaptiveN05440MinusP028Output2542,
      adaptiveN05440MinusP029Output2542, Complex.mul_re, Complex.mul_im]

theorem adaptiveN05440MinusSum_norm2542 :
    ‖∑ i : Fin 30, baseCoefficientCenter2540 i * adaptiveN05440MinusValue2542 i‖ ≤
      ((958170151 : ℝ) /
        2500000000) := by
  rw [adaptiveN05440MinusSum_eq2542]
  apply complex_norm_le_of_sq2541 _ _ (by norm_num)
  norm_num [adaptiveN05440MinusSumValue2542]

theorem adaptiveN05440MinusEvaluation_charge2542 :
    (∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
      |(baseCoefficientCenter2540 i).im|) * adaptiveN05440MinusError2542 i) ≤ (1 : ℝ)/10^12 := by
  rw [sum30_chain2541]
  norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, adaptiveN05440MinusError2542,
      adaptiveN05440MinusP000Output2542,
      adaptiveN05440MinusP001Output2542,
      adaptiveN05440MinusP002Output2542,
      adaptiveN05440MinusP003Output2542,
      adaptiveN05440MinusP004Output2542,
      adaptiveN05440MinusP005Output2542,
      adaptiveN05440MinusP006Output2542,
      adaptiveN05440MinusP007Output2542,
      adaptiveN05440MinusP008Output2542,
      adaptiveN05440MinusP009Output2542,
      adaptiveN05440MinusP010Output2542,
      adaptiveN05440MinusP011Output2542,
      adaptiveN05440MinusP012Output2542,
      adaptiveN05440MinusP013Output2542,
      adaptiveN05440MinusP014Output2542,
      adaptiveN05440MinusP015Output2542,
      adaptiveN05440MinusP016Output2542,
      adaptiveN05440MinusP017Output2542,
      adaptiveN05440MinusP018Output2542,
      adaptiveN05440MinusP019Output2542,
      adaptiveN05440MinusP020Output2542,
      adaptiveN05440MinusP021Output2542,
      adaptiveN05440MinusP022Output2542,
      adaptiveN05440MinusP023Output2542,
      adaptiveN05440MinusP024Output2542,
      adaptiveN05440MinusP025Output2542,
      adaptiveN05440MinusP026Output2542,
      adaptiveN05440MinusP027Output2542,
      adaptiveN05440MinusP028Output2542,
      adaptiveN05440MinusP029Output2542]

theorem adaptiveN05440MinusSigned_le2542 :
    signedJetUpper2539 0 ((((-1) : ℝ) /
        2)) baseCoefficientCenter2540 baseCoefficientError2540
      nodeModulation2541 adaptiveN05440MinusPosition2542 ≤ adaptiveN05440MinusUpper2542 := by
  have hsum :
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i *
        weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 i adaptiveN05440MinusPosition2542‖ ≤
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i * adaptiveN05440MinusValue2542 i‖ +
        ∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
          |(baseCoefficientCenter2540 i).im|) * adaptiveN05440MinusError2542 i := by
    apply norm_sum_le_center_sum_add_error2531
    intro i _
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (Complex.norm_le_abs_re_add_abs_im _) (adaptiveN05440MinusExp_error2542 i)
      (norm_nonneg _) (by positivity)
  have heach : ∀ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 i adaptiveN05440MinusPosition2542‖ ≤
        (1 : ℝ)/10^30 := by
    intro i
    have h := mul_le_mul_of_nonneg_left (adaptiveN05440MinusUnit_norm2542 i)
      (by norm_num [baseCoefficientError2540] : 0 ≤ baseCoefficientError2540 i)
    simpa [baseCoefficientError2540] using h
  have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
  have he' : (∑ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 i adaptiveN05440MinusPosition2542‖) ≤
        (30 : ℝ)/10^30 := by simpa using he
  unfold signedJetUpper2539 adaptiveN05440MinusUpper2542
  linarith [adaptiveN05440MinusSum_norm2542, adaptiveN05440MinusEvaluation_charge2542]

theorem adaptiveN05440MinusPhysical_le2542 (coefficients : Fin 30 → ℂ)
    (hbox : ∀ i, (baseCoefficientBox2540 i).Mem (coefficients i)) :
    ‖weightedPhysical2539 ((((-1) : ℝ) /
        2)) coefficients nodeModulation2541 adaptiveN05440MinusPosition2542‖ ≤
      adaptiveN05440MinusUpper2542 := by
  have h := weightedPhysical2539_jet_le_center_error 0 ((((-1) : ℝ) /
        2)) coefficients
    baseCoefficientCenter2540 baseCoefficientError2540 nodeModulation2541
    (fun i => baseCoefficient_error_of_box2540 i (coefficients i) (hbox i))
        adaptiveN05440MinusPosition2542
  simpa only [iteratedDeriv_zero] using h.trans adaptiveN05440MinusSigned_le2542

theorem adaptiveN05440MinusGrid2542 :
    -stripRadius2303 + (5440 : ℝ)*(2*stripRadius2303/10240) = adaptiveN05440MinusPosition2542 :=
        by
  norm_num [stripRadius2303, adaptiveN05440MinusPosition2542]

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.adaptiveN05440MinusSigned_le2542
#print axioms ConnesWeilRH.Dev.adaptiveN05440MinusPhysical_le2542
