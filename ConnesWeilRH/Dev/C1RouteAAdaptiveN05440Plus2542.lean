import ConnesWeilRH.Dev.C1RouteACompactExp2542
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541

namespace ConnesWeilRH.Dev

open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def adaptiveN05440PlusPosition2542 : ℝ := ((65536001 : ℝ) /
        160000000)

def adaptiveN05440PlusP000Output2542 : RatState2542 :=
  (((((-30858366022552697) : ℚ) /
        633825300114114700748351602688),
    ((23926281498988875 : ℚ) /
        1267650600228229401496703205376)),
    ((39654207116799 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

def adaptiveN05440PlusP000Input2542 : RatPair2542 :=
  ((((-((32 * 10^40
        + 6911763763220111443585096710647091568765) * 10^40
        + 8030436439533111481004726762137450891693)) : ℚ) /
        ((68 * 10^40
        + 4108646130446117391380318820003814069094) * 10^40
        + 5827290179342624543465749633167360000000)),
    (((-362039942185747774262029) : ℚ) /
        1441151880758558720000000))

theorem adaptiveN05440PlusP000Compute2542 : compactExp2542 adaptiveN05440PlusP000Input2542 6 =
    adaptiveN05440PlusP000Output2542 := by
  cbv

theorem adaptiveN05440PlusP000Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ adaptiveN05440PlusPosition2542 =
    Complex.exp ((2 : ℂ)^6 * embedPair2542 adaptiveN05440PlusP000Input2542) := by
  have hx : |adaptiveN05440PlusPosition2542| < storedWidth ⟨0, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05440PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05440PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05440PlusP000Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05440PlusP000Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ adaptiveN05440PlusPosition2542 - embedPair2542
            adaptiveN05440PlusP000Output2542.1‖ ≤ (adaptiveN05440PlusP000Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05440PlusP000Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05440PlusP000Input2542]
  rw [adaptiveN05440PlusP000Owner2542]
  have h := compactExp_error2542 adaptiveN05440PlusP000Input2542 hz 6
  simpa only [adaptiveN05440PlusP000Compute2542] using h

theorem adaptiveN05440PlusP000Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ adaptiveN05440PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05440PlusP000Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05440PlusP000Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05440PlusP001Output2542 : RatState2542 :=
  (((((-86930010245736943) : ℚ) /
        1267650600228229401496703205376),
    ((1053154381178083 : ℚ) /
        39614081257132168796771975168)),
    ((54674242154227 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

def adaptiveN05440PlusP001Input2542 : RatPair2542 :=
  ((((-(418745829535285177504639993717831830075 * 10^40
        + 5441618534605682304357047648610637783799)) : ℚ) /
        (886210261626655755083735189233369746668 * 10^40
        + 3797746372915947800471746154516480000000)),
    (((-362039942185747774262029) : ℚ) /
        1441151880758558720000000))

theorem adaptiveN05440PlusP001Compute2542 : compactExp2542 adaptiveN05440PlusP001Input2542 6 =
    adaptiveN05440PlusP001Output2542 := by
  cbv

theorem adaptiveN05440PlusP001Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ adaptiveN05440PlusPosition2542 =
    Complex.exp ((2 : ℂ)^6 * embedPair2542 adaptiveN05440PlusP001Input2542) := by
  have hx : |adaptiveN05440PlusPosition2542| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05440PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05440PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05440PlusP001Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05440PlusP001Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ adaptiveN05440PlusPosition2542 - embedPair2542
            adaptiveN05440PlusP001Output2542.1‖ ≤ (adaptiveN05440PlusP001Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05440PlusP001Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05440PlusP001Input2542]
  rw [adaptiveN05440PlusP001Owner2542]
  have h := compactExp_error2542 adaptiveN05440PlusP001Input2542 hz 6
  simpa only [adaptiveN05440PlusP001Compute2542] using h

theorem adaptiveN05440PlusP001Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ adaptiveN05440PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05440PlusP001Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05440PlusP001Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05440PlusP002Output2542 : RatState2542 :=
  (((((-25870618901970091) : ℚ) /
        316912650057057350374175801344),
    (((-10029495890177959) : ℚ) /
        316912650057057350374175801344)),
    ((64496229382583 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

def adaptiveN05440PlusP002Input2542 : RatPair2542 :=
  ((((-((1 * 10^40
        + 940460184190943091815756058773640907463) * 10^40
        + 6041868381241635646677598458916444775159)) : ℚ) /
        ((2 * 10^40
        + 3288003241060619496441480162260487009338) * 10^40
        + 6963595085534041865672938472263680000000)),
    ((362039942185747774262029 : ℚ) /
        1441151880758558720000000))

theorem adaptiveN05440PlusP002Compute2542 : compactExp2542 adaptiveN05440PlusP002Input2542 6 =
    adaptiveN05440PlusP002Output2542 := by
  cbv

theorem adaptiveN05440PlusP002Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ adaptiveN05440PlusPosition2542 =
    Complex.exp ((2 : ℂ)^6 * embedPair2542 adaptiveN05440PlusP002Input2542) := by
  have hx : |adaptiveN05440PlusPosition2542| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05440PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05440PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05440PlusP002Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05440PlusP002Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ adaptiveN05440PlusPosition2542 - embedPair2542
            adaptiveN05440PlusP002Output2542.1‖ ≤ (adaptiveN05440PlusP002Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05440PlusP002Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05440PlusP002Input2542]
  rw [adaptiveN05440PlusP002Owner2542]
  have h := compactExp_error2542 adaptiveN05440PlusP002Input2542 hz 6
  simpa only [adaptiveN05440PlusP002Compute2542] using h

theorem adaptiveN05440PlusP002Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ adaptiveN05440PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05440PlusP002Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05440PlusP002Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05440PlusP003Output2542 : RatState2542 :=
  (((((-56987816639837217) : ℚ) /
        633825300114114700748351602688),
    (((-44185960524967363) : ℚ) /
        1267650600228229401496703205376)),
    ((70709719318829 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

def adaptiveN05440PlusP003Input2542 : RatPair2542 :=
  ((((-((144 * 10^40
        + 4918766017205838150183104107479631936812) * 10^40
        + 9508214248915683763619074813602294641693)) : ℚ) /
        ((308 * 10^40
        + 5584325157930343245986452666829032621960) * 10^40
        + 3552613615865160449465749633167360000000)),
    ((362039942185747774262029 : ℚ) /
        1441151880758558720000000))

theorem adaptiveN05440PlusP003Compute2542 : compactExp2542 adaptiveN05440PlusP003Input2542 6 =
    adaptiveN05440PlusP003Output2542 := by
  cbv

theorem adaptiveN05440PlusP003Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ adaptiveN05440PlusPosition2542 =
    Complex.exp ((2 : ℂ)^6 * embedPair2542 adaptiveN05440PlusP003Input2542) := by
  have hx : |adaptiveN05440PlusPosition2542| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05440PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05440PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05440PlusP003Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05440PlusP003Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ adaptiveN05440PlusPosition2542 - embedPair2542
            adaptiveN05440PlusP003Output2542.1‖ ≤ (adaptiveN05440PlusP003Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05440PlusP003Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05440PlusP003Input2542]
  rw [adaptiveN05440PlusP003Owner2542]
  have h := compactExp_error2542 adaptiveN05440PlusP003Input2542 hz 6
  simpa only [adaptiveN05440PlusP003Compute2542] using h

theorem adaptiveN05440PlusP003Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ adaptiveN05440PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05440PlusP003Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05440PlusP003Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05440PlusP004Output2542 : RatState2542 :=
  (((((-60336558659991183) : ℚ) /
        633825300114114700748351602688),
    ((46782434498447973 : ℚ) /
        1267650600228229401496703205376)),
    ((37335442720627 : ℚ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888)))

def adaptiveN05440PlusP004Input2542 : RatPair2542 :=
  ((((-((2 * 10^40
        + 5103080337848704906504593856765472646849) * 10^40
        + 7747772204514785261573073475518007275159)) : ℚ) /
        ((5 * 10^40
        + 3709268744536454894037321260456311664067) * 10^40
        + 5409328121924953525672938472263680000000)),
    (((-362039942185747774262029) : ℚ) /
        1441151880758558720000000))

theorem adaptiveN05440PlusP004Compute2542 : compactExp2542 adaptiveN05440PlusP004Input2542 6 =
    adaptiveN05440PlusP004Output2542 := by
  cbv

theorem adaptiveN05440PlusP004Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ adaptiveN05440PlusPosition2542 =
    Complex.exp ((2 : ℂ)^6 * embedPair2542 adaptiveN05440PlusP004Input2542) := by
  have hx : |adaptiveN05440PlusPosition2542| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05440PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05440PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05440PlusP004Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05440PlusP004Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ adaptiveN05440PlusPosition2542 - embedPair2542
            adaptiveN05440PlusP004Output2542.1‖ ≤ (adaptiveN05440PlusP004Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05440PlusP004Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05440PlusP004Input2542]
  rw [adaptiveN05440PlusP004Owner2542]
  have h := compactExp_error2542 adaptiveN05440PlusP004Input2542 hz 6
  simpa only [adaptiveN05440PlusP004Compute2542] using h

theorem adaptiveN05440PlusP004Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ adaptiveN05440PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05440PlusP004Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05440PlusP004Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05440PlusP005Output2542 : RatState2542 :=
  ((((19087206308435669 : ℚ) /
        316912650057057350374175801344),
    ((0 : ℚ) /
        1)),
    ((9153803216799 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

def adaptiveN05440PlusP005Input2542 : RatPair2542 :=
  ((((-((119 * 10^40
        + 2052691919609525638601444604262212764412) * 10^40
        + 5534546308631277754165410040806883925079)) : ℚ) /
        ((125 * 10^40
        + 3117539759639451663790354394338218649327) * 10^40
        + 8796645127269504130198624449751040000000)),
    ((0 : ℚ) /
        1))

theorem adaptiveN05440PlusP005Compute2542 : compactExp2542 adaptiveN05440PlusP005Input2542 5 =
    adaptiveN05440PlusP005Output2542 := by
  cbv

theorem adaptiveN05440PlusP005Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ adaptiveN05440PlusPosition2542 =
    Complex.exp ((2 : ℂ)^5 * embedPair2542 adaptiveN05440PlusP005Input2542) := by
  have hx : |adaptiveN05440PlusPosition2542| < storedWidth ⟨5, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05440PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05440PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05440PlusP005Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05440PlusP005Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ adaptiveN05440PlusPosition2542 - embedPair2542
            adaptiveN05440PlusP005Output2542.1‖ ≤ (adaptiveN05440PlusP005Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05440PlusP005Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05440PlusP005Input2542]
  rw [adaptiveN05440PlusP005Owner2542]
  have h := compactExp_error2542 adaptiveN05440PlusP005Input2542 hz 5
  simpa only [adaptiveN05440PlusP005Compute2542] using h

theorem adaptiveN05440PlusP005Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ adaptiveN05440PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05440PlusP005Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05440PlusP005Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05440PlusP006Output2542 : RatState2542 :=
  ((((105936024065733223 : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1)),
    ((5875350411947 : ℚ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888)))

def adaptiveN05440PlusP006Input2542 : RatPair2542 :=
  ((((-1301865976326665186028202667) : ℚ) /
        1383441177848927569920000000),
    ((0 : ℚ) /
        1))

theorem adaptiveN05440PlusP006Compute2542 : compactExp2542 adaptiveN05440PlusP006Input2542 5 =
    adaptiveN05440PlusP006Output2542 := by
  cbv

theorem adaptiveN05440PlusP006Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ adaptiveN05440PlusPosition2542 =
    Complex.exp ((2 : ℂ)^5 * embedPair2542 adaptiveN05440PlusP006Input2542) := by
  have hx : |adaptiveN05440PlusPosition2542| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05440PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05440PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05440PlusP006Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05440PlusP006Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ adaptiveN05440PlusPosition2542 - embedPair2542
            adaptiveN05440PlusP006Output2542.1‖ ≤ (adaptiveN05440PlusP006Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05440PlusP006Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05440PlusP006Input2542]
  rw [adaptiveN05440PlusP006Owner2542]
  have h := compactExp_error2542 adaptiveN05440PlusP006Input2542 hz 5
  simpa only [adaptiveN05440PlusP006Compute2542] using h

theorem adaptiveN05440PlusP006Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ adaptiveN05440PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05440PlusP006Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05440PlusP006Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05440PlusP007Output2542 : RatState2542 :=
  ((((122240926407716675 : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1)),
    ((1646453414559 : ℚ) /
        (17 * 10^40
        + 4224571863520493293247799005065324265472)))

def adaptiveN05440PlusP007Input2542 : RatPair2542 :=
  ((((-((144 * 10^40
        + 4918766017205838150183104107479631936812) * 10^40
        + 9508214248915683763619074813602294641693)) : ℚ) /
        ((154 * 10^40
        + 2792162578965171622993226333414516310980) * 10^40
        + 1776306807932580224732874816583680000000)),
    ((0 : ℚ) /
        1))

theorem adaptiveN05440PlusP007Compute2542 : compactExp2542 adaptiveN05440PlusP007Input2542 5 =
    adaptiveN05440PlusP007Output2542 := by
  cbv

theorem adaptiveN05440PlusP007Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ adaptiveN05440PlusPosition2542 =
    Complex.exp ((2 : ℂ)^5 * embedPair2542 adaptiveN05440PlusP007Input2542) := by
  have hx : |adaptiveN05440PlusPosition2542| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05440PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05440PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05440PlusP007Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05440PlusP007Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ adaptiveN05440PlusPosition2542 - embedPair2542
            adaptiveN05440PlusP007Output2542.1‖ ≤ (adaptiveN05440PlusP007Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05440PlusP007Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05440PlusP007Input2542]
  rw [adaptiveN05440PlusP007Owner2542]
  have h := compactExp_error2542 adaptiveN05440PlusP007Input2542 hz 5
  simpa only [adaptiveN05440PlusP007Compute2542] using h

theorem adaptiveN05440PlusP007Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ adaptiveN05440PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05440PlusP007Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05440PlusP007Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05440PlusP008Output2542 : RatState2542 :=
  ((((37584419704424455 : ℚ) /
        633825300114114700748351602688),
    ((10110652316150125 : ℚ) /
        316912650057057350374175801344)),
    ((32251369786171 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

def adaptiveN05440PlusP008Input2542 : RatPair2542 :=
  ((((-((47 * 10^40
        + 8604820820512611674804590228678584994159) * 10^40
        + 4681860925800659368531562786551513391693)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-260739661220379310273297) : ℚ) /
        2882303761517117440000000))

theorem adaptiveN05440PlusP008Compute2542 : compactExp2542 adaptiveN05440PlusP008Input2542 6 =
    adaptiveN05440PlusP008Output2542 := by
  cbv

theorem adaptiveN05440PlusP008Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ adaptiveN05440PlusPosition2542 =
    Complex.exp ((2 : ℂ)^6 * embedPair2542 adaptiveN05440PlusP008Input2542) := by
  have hx : |adaptiveN05440PlusPosition2542| < storedWidth ⟨8, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05440PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05440PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05440PlusP008Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05440PlusP008Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ adaptiveN05440PlusPosition2542 - embedPair2542
            adaptiveN05440PlusP008Output2542.1‖ ≤ (adaptiveN05440PlusP008Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05440PlusP008Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05440PlusP008Input2542]
  rw [adaptiveN05440PlusP008Owner2542]
  have h := compactExp_error2542 adaptiveN05440PlusP008Input2542 hz 6
  simpa only [adaptiveN05440PlusP008Compute2542] using h

theorem adaptiveN05440PlusP008Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ adaptiveN05440PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05440PlusP008Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05440PlusP008Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05440PlusP009Output2542 : RatState2542 :=
  (((((-29298495678051691) : ℚ) /
        633825300114114700748351602688),
    (((-31033657801712695) : ℚ) /
        633825300114114700748351602688)),
    ((23670158132947 : ℚ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888)))

def adaptiveN05440PlusP009Input2542 : RatPair2542 :=
  ((((-((47 * 10^40
        + 8604820820512611674804590228678584994159) * 10^40
        + 4681860925800659368531562786551513391693)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-387788191040974601829711) : ℚ) /
        2882303761517117440000000))

theorem adaptiveN05440PlusP009Compute2542 : compactExp2542 adaptiveN05440PlusP009Input2542 6 =
    adaptiveN05440PlusP009Output2542 := by
  cbv

theorem adaptiveN05440PlusP009Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ adaptiveN05440PlusPosition2542 =
    Complex.exp ((2 : ℂ)^6 * embedPair2542 adaptiveN05440PlusP009Input2542) := by
  have hx : |adaptiveN05440PlusPosition2542| < storedWidth ⟨9, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05440PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05440PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05440PlusP009Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05440PlusP009Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ adaptiveN05440PlusPosition2542 - embedPair2542
            adaptiveN05440PlusP009Output2542.1‖ ≤ (adaptiveN05440PlusP009Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05440PlusP009Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05440PlusP009Input2542]
  rw [adaptiveN05440PlusP009Owner2542]
  have h := compactExp_error2542 adaptiveN05440PlusP009Input2542 hz 6
  simpa only [adaptiveN05440PlusP009Compute2542] using h

theorem adaptiveN05440PlusP009Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ adaptiveN05440PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05440PlusP009Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05440PlusP009Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05440PlusP010Output2542 : RatState2542 :=
  (((((-29126773493373607) : ℚ) /
        633825300114114700748351602688),
    ((31194884699519655 : ℚ) /
        633825300114114700748351602688)),
    ((46549267981635 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

def adaptiveN05440PlusP010Input2542 : RatPair2542 :=
  ((((-((47 * 10^40
        + 8604820820512611674804590228678584994159) * 10^40
        + 4681860925800659368531562786551513391693)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-230684447942438333698521) : ℚ) /
        1441151880758558720000000))

theorem adaptiveN05440PlusP010Compute2542 : compactExp2542 adaptiveN05440PlusP010Input2542 6 =
    adaptiveN05440PlusP010Output2542 := by
  cbv

theorem adaptiveN05440PlusP010Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ adaptiveN05440PlusPosition2542 =
    Complex.exp ((2 : ℂ)^6 * embedPair2542 adaptiveN05440PlusP010Input2542) := by
  have hx : |adaptiveN05440PlusPosition2542| < storedWidth ⟨10, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05440PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05440PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05440PlusP010Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05440PlusP010Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ adaptiveN05440PlusPosition2542 - embedPair2542
            adaptiveN05440PlusP010Output2542.1‖ ≤ (adaptiveN05440PlusP010Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05440PlusP010Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05440PlusP010Input2542]
  rw [adaptiveN05440PlusP010Owner2542]
  have h := compactExp_error2542 adaptiveN05440PlusP010Input2542 hz 6
  simpa only [adaptiveN05440PlusP010Compute2542] using h

theorem adaptiveN05440PlusP010Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ adaptiveN05440PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05440PlusP010Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05440PlusP010Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05440PlusP011Output2542 : RatState2542 :=
  ((((28320014124553967 : ℚ) /
        1267650600228229401496703205376),
    ((80522890299513783 : ℚ) /
        1267650600228229401496703205376)),
    ((42748580416135 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

def adaptiveN05440PlusP011Input2542 : RatPair2542 :=
  ((((-((47 * 10^40
        + 8604820820512611674804590228678584994159) * 10^40
        + 4681860925800659368531562786551513391693)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-255213677437476200797801) : ℚ) /
        1441151880758558720000000))

theorem adaptiveN05440PlusP011Compute2542 : compactExp2542 adaptiveN05440PlusP011Input2542 6 =
    adaptiveN05440PlusP011Output2542 := by
  cbv

theorem adaptiveN05440PlusP011Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ adaptiveN05440PlusPosition2542 =
    Complex.exp ((2 : ℂ)^6 * embedPair2542 adaptiveN05440PlusP011Input2542) := by
  have hx : |adaptiveN05440PlusPosition2542| < storedWidth ⟨11, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05440PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05440PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05440PlusP011Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05440PlusP011Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ adaptiveN05440PlusPosition2542 - embedPair2542
            adaptiveN05440PlusP011Output2542.1‖ ≤ (adaptiveN05440PlusP011Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05440PlusP011Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05440PlusP011Input2542]
  rw [adaptiveN05440PlusP011Owner2542]
  have h := compactExp_error2542 adaptiveN05440PlusP011Input2542 hz 6
  simpa only [adaptiveN05440PlusP011Compute2542] using h

theorem adaptiveN05440PlusP011Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ adaptiveN05440PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05440PlusP011Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05440PlusP011Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05440PlusP012Output2542 : RatState2542 :=
  ((((84893602246253523 : ℚ) /
        1267650600228229401496703205376),
    ((8890183342168253 : ℚ) /
        1267650600228229401496703205376)),
    ((12514615859921 : ℚ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888)))

def adaptiveN05440PlusP012Input2542 : RatPair2542 :=
  ((((-((47 * 10^40
        + 8604820820512611674804590228678584994159) * 10^40
        + 4681860925800659368531562786551513391693)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-5612399119318874813509) : ℚ) /
        28823037615171174400000))

theorem adaptiveN05440PlusP012Compute2542 : compactExp2542 adaptiveN05440PlusP012Input2542 6 =
    adaptiveN05440PlusP012Output2542 := by
  cbv

theorem adaptiveN05440PlusP012Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ adaptiveN05440PlusPosition2542 =
    Complex.exp ((2 : ℂ)^6 * embedPair2542 adaptiveN05440PlusP012Input2542) := by
  have hx : |adaptiveN05440PlusPosition2542| < storedWidth ⟨12, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05440PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05440PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05440PlusP012Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05440PlusP012Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ adaptiveN05440PlusPosition2542 - embedPair2542
            adaptiveN05440PlusP012Output2542.1‖ ≤ (adaptiveN05440PlusP012Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05440PlusP012Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05440PlusP012Input2542]
  rw [adaptiveN05440PlusP012Owner2542]
  have h := compactExp_error2542 adaptiveN05440PlusP012Input2542 hz 6
  simpa only [adaptiveN05440PlusP012Compute2542] using h

theorem adaptiveN05440PlusP012Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ adaptiveN05440PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05440PlusP012Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05440PlusP012Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05440PlusP013Output2542 : RatState2542 :=
  ((((25725480424142777 : ℚ) /
        633825300114114700748351602688),
    (((-34054212991899601) : ℚ) /
        633825300114114700748351602688)),
    ((2524587552149 : ℚ) /
        (8 * 10^40
        + 7112285931760246646623899502532662132736)))

def adaptiveN05440PlusP013Input2542 : RatPair2542 :=
  ((((-((47 * 10^40
        + 8604820820512611674804590228678584994159) * 10^40
        + 4681860925800659368531562786551513391693)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-60754466143128272313291) : ℚ) /
        288230376151711744000000))

theorem adaptiveN05440PlusP013Compute2542 : compactExp2542 adaptiveN05440PlusP013Input2542 6 =
    adaptiveN05440PlusP013Output2542 := by
  cbv

theorem adaptiveN05440PlusP013Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ adaptiveN05440PlusPosition2542 =
    Complex.exp ((2 : ℂ)^6 * embedPair2542 adaptiveN05440PlusP013Input2542) := by
  have hx : |adaptiveN05440PlusPosition2542| < storedWidth ⟨13, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05440PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05440PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05440PlusP013Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05440PlusP013Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ adaptiveN05440PlusPosition2542 - embedPair2542
            adaptiveN05440PlusP013Output2542.1‖ ≤ (adaptiveN05440PlusP013Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05440PlusP013Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05440PlusP013Input2542]
  rw [adaptiveN05440PlusP013Owner2542]
  have h := compactExp_error2542 adaptiveN05440PlusP013Input2542 hz 6
  simpa only [adaptiveN05440PlusP013Compute2542] using h

theorem adaptiveN05440PlusP013Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ adaptiveN05440PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05440PlusP013Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05440PlusP013Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05440PlusP014Output2542 : RatState2542 :=
  (((((-81219457813459147) : ℚ) /
        1267650600228229401496703205376),
    (((-26255641959209401) : ℚ) /
        1267650600228229401496703205376)),
    ((5948224162945 : ℚ) /
        (17 * 10^40
        + 4224571863520493293247799005065324265472)))

def adaptiveN05440PlusP014Input2542 : RatPair2542 :=
  ((((-((47 * 10^40
        + 8604820820512611674804590228678584994159) * 10^40
        + 4681860925800659368531562786551513391693)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-346671309892138695845011) : ℚ) /
        1441151880758558720000000))

theorem adaptiveN05440PlusP014Compute2542 : compactExp2542 adaptiveN05440PlusP014Input2542 6 =
    adaptiveN05440PlusP014Output2542 := by
  cbv

theorem adaptiveN05440PlusP014Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ adaptiveN05440PlusPosition2542 =
    Complex.exp ((2 : ℂ)^6 * embedPair2542 adaptiveN05440PlusP014Input2542) := by
  have hx : |adaptiveN05440PlusPosition2542| < storedWidth ⟨14, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05440PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05440PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05440PlusP014Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05440PlusP014Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ adaptiveN05440PlusPosition2542 - embedPair2542
            adaptiveN05440PlusP014Output2542.1‖ ≤ (adaptiveN05440PlusP014Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05440PlusP014Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05440PlusP014Input2542]
  rw [adaptiveN05440PlusP014Owner2542]
  have h := compactExp_error2542 adaptiveN05440PlusP014Input2542 hz 6
  simpa only [adaptiveN05440PlusP014Compute2542] using h

theorem adaptiveN05440PlusP014Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ adaptiveN05440PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05440PlusP014Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05440PlusP014Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05440PlusP015Output2542 : RatState2542 :=
  (((((-21148946663486405) : ℚ) /
        633825300114114700748351602688),
    ((37070363102829517 : ℚ) /
        633825300114114700748351602688)),
    ((58432555568759 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

def adaptiveN05440PlusP015Input2542 : RatPair2542 :=
  ((((-((47 * 10^40
        + 8604820820512611674804590228678584994159) * 10^40
        + 4681860925800659368531562786551513391693)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-377408574479356852679047) : ℚ) /
        1441151880758558720000000))

theorem adaptiveN05440PlusP015Compute2542 : compactExp2542 adaptiveN05440PlusP015Input2542 6 =
    adaptiveN05440PlusP015Output2542 := by
  cbv

theorem adaptiveN05440PlusP015Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ adaptiveN05440PlusPosition2542 =
    Complex.exp ((2 : ℂ)^6 * embedPair2542 adaptiveN05440PlusP015Input2542) := by
  have hx : |adaptiveN05440PlusPosition2542| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05440PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05440PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05440PlusP015Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05440PlusP015Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ adaptiveN05440PlusPosition2542 - embedPair2542
            adaptiveN05440PlusP015Output2542.1‖ ≤ (adaptiveN05440PlusP015Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05440PlusP015Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05440PlusP015Input2542]
  rw [adaptiveN05440PlusP015Owner2542]
  have h := compactExp_error2542 adaptiveN05440PlusP015Input2542 hz 6
  simpa only [adaptiveN05440PlusP015Compute2542] using h

theorem adaptiveN05440PlusP015Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ adaptiveN05440PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05440PlusP015Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05440PlusP015Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05440PlusP016Output2542 : RatState2542 :=
  ((((38505862022080969 : ℚ) /
        1267650600228229401496703205376),
    ((76179115590422351 : ℚ) /
        1267650600228229401496703205376)),
    ((13635020005641 : ℚ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944)))

def adaptiveN05440PlusP016Input2542 : RatPair2542 :=
  ((((-((47 * 10^40
        + 8604820820512611674804590228678584994159) * 10^40
        + 4681860925800659368531562786551513391693)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-199810861117846303095609) : ℚ) /
        720575940379279360000000))

theorem adaptiveN05440PlusP016Compute2542 : compactExp2542 adaptiveN05440PlusP016Input2542 6 =
    adaptiveN05440PlusP016Output2542 := by
  cbv

theorem adaptiveN05440PlusP016Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ adaptiveN05440PlusPosition2542 =
    Complex.exp ((2 : ℂ)^6 * embedPair2542 adaptiveN05440PlusP016Input2542) := by
  have hx : |adaptiveN05440PlusPosition2542| < storedWidth ⟨16, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05440PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05440PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05440PlusP016Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05440PlusP016Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ adaptiveN05440PlusPosition2542 - embedPair2542
            adaptiveN05440PlusP016Output2542.1‖ ≤ (adaptiveN05440PlusP016Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05440PlusP016Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05440PlusP016Input2542]
  rw [adaptiveN05440PlusP016Owner2542]
  have h := compactExp_error2542 adaptiveN05440PlusP016Input2542 hz 6
  simpa only [adaptiveN05440PlusP016Compute2542] using h

theorem adaptiveN05440PlusP016Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ adaptiveN05440PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05440PlusP016Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05440PlusP016Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05440PlusP017Output2542 : RatState2542 :=
  ((((58646391637649003 : ℚ) /
        1267650600228229401496703205376),
    (((-15505160048524895) : ℚ) /
        316912650057057350374175801344)),
    ((49294139097261 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

def adaptiveN05440PlusP017Input2542 : RatPair2542 :=
  ((((-((47 * 10^40
        + 8604820820512611674804590228678584994159) * 10^40
        + 4681860925800659368531562786551513391693)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-442769373018475956606027) : ℚ) /
        1441151880758558720000000))

theorem adaptiveN05440PlusP017Compute2542 : compactExp2542 adaptiveN05440PlusP017Input2542 6 =
    adaptiveN05440PlusP017Output2542 := by
  cbv

theorem adaptiveN05440PlusP017Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ adaptiveN05440PlusPosition2542 =
    Complex.exp ((2 : ℂ)^6 * embedPair2542 adaptiveN05440PlusP017Input2542) := by
  have hx : |adaptiveN05440PlusPosition2542| < storedWidth ⟨17, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05440PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05440PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05440PlusP017Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05440PlusP017Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ adaptiveN05440PlusPosition2542 - embedPair2542
            adaptiveN05440PlusP017Output2542.1‖ ≤ (adaptiveN05440PlusP017Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05440PlusP017Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05440PlusP017Input2542]
  rw [adaptiveN05440PlusP017Owner2542]
  have h := compactExp_error2542 adaptiveN05440PlusP017Input2542 hz 6
  simpa only [adaptiveN05440PlusP017Compute2542] using h

theorem adaptiveN05440PlusP017Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ adaptiveN05440PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05440PlusP017Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05440PlusP017Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05440PlusP018Output2542 : RatState2542 :=
  ((((1407728604688007 : ℚ) /
        633825300114114700748351602688),
    (((-21327846033567009) : ℚ) /
        316912650057057350374175801344)),
    ((14145583295521 : ℚ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944)))

def adaptiveN05440PlusP018Input2542 : RatPair2542 :=
  ((((-((47 * 10^40
        + 8604820820512611674804590228678584994159) * 10^40
        + 4681860925800659368531562786551513391693)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-114770645411675231749613) : ℚ) /
        360287970189639680000000))

theorem adaptiveN05440PlusP018Compute2542 : compactExp2542 adaptiveN05440PlusP018Input2542 6 =
    adaptiveN05440PlusP018Output2542 := by
  cbv

theorem adaptiveN05440PlusP018Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ adaptiveN05440PlusPosition2542 =
    Complex.exp ((2 : ℂ)^6 * embedPair2542 adaptiveN05440PlusP018Input2542) := by
  have hx : |adaptiveN05440PlusPosition2542| < storedWidth ⟨18, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05440PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05440PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05440PlusP018Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05440PlusP018Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ adaptiveN05440PlusPosition2542 - embedPair2542
            adaptiveN05440PlusP018Output2542.1‖ ≤ (adaptiveN05440PlusP018Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05440PlusP018Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05440PlusP018Input2542]
  rw [adaptiveN05440PlusP018Owner2542]
  have h := compactExp_error2542 adaptiveN05440PlusP018Input2542 hz 6
  simpa only [adaptiveN05440PlusP018Compute2542] using h

theorem adaptiveN05440PlusP018Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ adaptiveN05440PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05440PlusP018Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05440PlusP018Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05440PlusP019Output2542 : RatState2542 :=
  (((((-81682839262770589) : ℚ) /
        1267650600228229401496703205376),
    (((-24776457215971191) : ℚ) /
        1267650600228229401496703205376)),
    ((22968093507731 : ℚ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888)))

def adaptiveN05440PlusP019Input2542 : RatPair2542 :=
  ((((-((47 * 10^40
        + 8604820820512611674804590228678584994159) * 10^40
        + 4681860925800659368531562786551513391693)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-24428249467783476683391) : ℚ) /
        72057594037927936000000))

theorem adaptiveN05440PlusP019Compute2542 : compactExp2542 adaptiveN05440PlusP019Input2542 6 =
    adaptiveN05440PlusP019Output2542 := by
  cbv

theorem adaptiveN05440PlusP019Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ adaptiveN05440PlusPosition2542 =
    Complex.exp ((2 : ℂ)^6 * embedPair2542 adaptiveN05440PlusP019Input2542) := by
  have hx : |adaptiveN05440PlusPosition2542| < storedWidth ⟨19, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05440PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05440PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05440PlusP019Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05440PlusP019Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ adaptiveN05440PlusPosition2542 - embedPair2542
            adaptiveN05440PlusP019Output2542.1‖ ≤ (adaptiveN05440PlusP019Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05440PlusP019Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05440PlusP019Input2542]
  rw [adaptiveN05440PlusP019Owner2542]
  have h := compactExp_error2542 adaptiveN05440PlusP019Input2542 hz 6
  simpa only [adaptiveN05440PlusP019Compute2542] using h

theorem adaptiveN05440PlusP019Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ adaptiveN05440PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05440PlusP019Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05440PlusP019Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05440PlusP020Output2542 : RatState2542 :=
  (((((-9119453561957117) : ℚ) /
        316912650057057350374175801344),
    ((77170772510733555 : ℚ) /
        1267650600228229401496703205376)),
    ((23476549907841 : ℚ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888)))

def adaptiveN05440PlusP020Input2542 : RatPair2542 :=
  ((((-((47 * 10^40
        + 8604820820512611674804590228678584994159) * 10^40
        + 4681860925800659368531562786551513391693)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-520624750538575899551419) : ℚ) /
        1441151880758558720000000))

theorem adaptiveN05440PlusP020Compute2542 : compactExp2542 adaptiveN05440PlusP020Input2542 6 =
    adaptiveN05440PlusP020Output2542 := by
  cbv

theorem adaptiveN05440PlusP020Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ adaptiveN05440PlusPosition2542 =
    Complex.exp ((2 : ℂ)^6 * embedPair2542 adaptiveN05440PlusP020Input2542) := by
  have hx : |adaptiveN05440PlusPosition2542| < storedWidth ⟨20, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05440PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05440PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05440PlusP020Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05440PlusP020Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ adaptiveN05440PlusPosition2542 - embedPair2542
            adaptiveN05440PlusP020Output2542.1‖ ≤ (adaptiveN05440PlusP020Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05440PlusP020Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05440PlusP020Input2542]
  rw [adaptiveN05440PlusP020Owner2542]
  have h := compactExp_error2542 adaptiveN05440PlusP020Input2542 hz 6
  simpa only [adaptiveN05440PlusP020Compute2542] using h

theorem adaptiveN05440PlusP020Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ adaptiveN05440PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05440PlusP020Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05440PlusP020Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05440PlusP021Output2542 : RatState2542 :=
  ((((28985407457410333 : ℚ) /
        633825300114114700748351602688),
    ((31326281619089717 : ℚ) /
        633825300114114700748351602688)),
    ((4254407061753 : ℚ) /
        (17 * 10^40
        + 4224571863520493293247799005065324265472)))

def adaptiveN05440PlusP021Input2542 : RatPair2542 :=
  ((((-((47 * 10^40
        + 8604820820512611674804590228678584994159) * 10^40
        + 4681860925800659368531562786551513391693)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-547379874475946380671387) : ℚ) /
        1441151880758558720000000))

theorem adaptiveN05440PlusP021Compute2542 : compactExp2542 adaptiveN05440PlusP021Input2542 6 =
    adaptiveN05440PlusP021Output2542 := by
  cbv

theorem adaptiveN05440PlusP021Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ adaptiveN05440PlusPosition2542 =
    Complex.exp ((2 : ℂ)^6 * embedPair2542 adaptiveN05440PlusP021Input2542) := by
  have hx : |adaptiveN05440PlusPosition2542| < storedWidth ⟨21, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05440PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05440PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05440PlusP021Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05440PlusP021Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ adaptiveN05440PlusPosition2542 - embedPair2542
            adaptiveN05440PlusP021Output2542.1‖ ≤ (adaptiveN05440PlusP021Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05440PlusP021Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05440PlusP021Input2542]
  rw [adaptiveN05440PlusP021Owner2542]
  have h := compactExp_error2542 adaptiveN05440PlusP021Input2542 hz 6
  simpa only [adaptiveN05440PlusP021Compute2542] using h

theorem adaptiveN05440PlusP021Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ adaptiveN05440PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05440PlusP021Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05440PlusP021Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05440PlusP022Output2542 : RatState2542 :=
  ((((10421690030224543 : ℚ) /
        158456325028528675187087900672),
    ((18297955751756599 : ℚ) /
        1267650600228229401496703205376)),
    ((2960087737759 : ℚ) /
        (17 * 10^40
        + 4224571863520493293247799005065324265472)))

def adaptiveN05440PlusP022Input2542 : RatPair2542 :=
  ((((-((47 * 10^40
        + 8604820820512611674804590228678584994159) * 10^40
        + 4681860925800659368531562786551513391693)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-112214826711468142236233) : ℚ) /
        288230376151711744000000))

theorem adaptiveN05440PlusP022Compute2542 : compactExp2542 adaptiveN05440PlusP022Input2542 6 =
    adaptiveN05440PlusP022Output2542 := by
  cbv

theorem adaptiveN05440PlusP022Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ adaptiveN05440PlusPosition2542 =
    Complex.exp ((2 : ℂ)^6 * embedPair2542 adaptiveN05440PlusP022Input2542) := by
  have hx : |adaptiveN05440PlusPosition2542| < storedWidth ⟨22, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05440PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05440PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05440PlusP022Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05440PlusP022Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ adaptiveN05440PlusPosition2542 - embedPair2542
            adaptiveN05440PlusP022Output2542.1‖ ≤ (adaptiveN05440PlusP022Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05440PlusP022Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05440PlusP022Input2542]
  rw [adaptiveN05440PlusP022Owner2542]
  have h := compactExp_error2542 adaptiveN05440PlusP022Input2542 hz 6
  simpa only [adaptiveN05440PlusP022Compute2542] using h

theorem adaptiveN05440PlusP022Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ adaptiveN05440PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05440PlusP022Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05440PlusP022Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05440PlusP023Output2542 : RatState2542 :=
  ((((2853757647107117 : ℚ) /
        1267650600228229401496703205376),
    (((-42655055765682821) : ℚ) /
        633825300114114700748351602688)),
    ((22277317902181 : ℚ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888)))

def adaptiveN05440PlusP023Input2542 : RatPair2542 :=
  ((((-((47 * 10^40
        + 8604820820512611674804590228678584994159) * 10^40
        + 4681860925800659368531562786551513391693)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-300278613592663314364333) : ℚ) /
        720575940379279360000000))

theorem adaptiveN05440PlusP023Compute2542 : compactExp2542 adaptiveN05440PlusP023Input2542 6 =
    adaptiveN05440PlusP023Output2542 := by
  cbv

theorem adaptiveN05440PlusP023Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ adaptiveN05440PlusPosition2542 =
    Complex.exp ((2 : ℂ)^6 * embedPair2542 adaptiveN05440PlusP023Input2542) := by
  have hx : |adaptiveN05440PlusPosition2542| < storedWidth ⟨23, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05440PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05440PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05440PlusP023Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05440PlusP023Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ adaptiveN05440PlusPosition2542 - embedPair2542
            adaptiveN05440PlusP023Output2542.1‖ ≤ (adaptiveN05440PlusP023Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05440PlusP023Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05440PlusP023Input2542]
  rw [adaptiveN05440PlusP023Owner2542]
  have h := compactExp_error2542 adaptiveN05440PlusP023Input2542 hz 6
  simpa only [adaptiveN05440PlusP023Compute2542] using h

theorem adaptiveN05440PlusP023Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ adaptiveN05440PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05440PlusP023Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05440PlusP023Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05440PlusP024Output2542 : RatState2542 :=
  (((((-59564634275976993) : ℚ) /
        1267650600228229401496703205376),
    (((-61139295103653053) : ℚ) /
        1267650600228229401496703205376)),
    ((48533417885251 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

def adaptiveN05440PlusP024Input2542 : RatPair2542 :=
  ((((-((47 * 10^40
        + 8604820820512611674804590228678584994159) * 10^40
        + 4681860925800659368531562786551513391693)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-309351029057948556428147) : ℚ) /
        720575940379279360000000))

theorem adaptiveN05440PlusP024Compute2542 : compactExp2542 adaptiveN05440PlusP024Input2542 6 =
    adaptiveN05440PlusP024Output2542 := by
  cbv

theorem adaptiveN05440PlusP024Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ adaptiveN05440PlusPosition2542 =
    Complex.exp ((2 : ℂ)^6 * embedPair2542 adaptiveN05440PlusP024Input2542) := by
  have hx : |adaptiveN05440PlusPosition2542| < storedWidth ⟨24, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05440PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05440PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05440PlusP024Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05440PlusP024Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ adaptiveN05440PlusPosition2542 - embedPair2542
            adaptiveN05440PlusP024Output2542.1‖ ≤ (adaptiveN05440PlusP024Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05440PlusP024Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05440PlusP024Input2542]
  rw [adaptiveN05440PlusP024Owner2542]
  have h := compactExp_error2542 adaptiveN05440PlusP024Input2542 hz 6
  simpa only [adaptiveN05440PlusP024Compute2542] using h

theorem adaptiveN05440PlusP024Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ adaptiveN05440PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05440PlusP024Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05440PlusP024Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05440PlusP025Output2542 : RatState2542 :=
  (((((-83449127615358963) : ℚ) /
        1267650600228229401496703205376),
    ((17949990597156351 : ℚ) /
        1267650600228229401496703205376)),
    ((46218232174417 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

def adaptiveN05440PlusP025Input2542 : RatPair2542 :=
  ((((-((47 * 10^40
        + 8604820820512611674804590228678584994159) * 10^40
        + 4681860925800659368531562786551513391693)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-10022692915539018190833) : ℚ) /
        22517998136852480000000))

theorem adaptiveN05440PlusP025Compute2542 : compactExp2542 adaptiveN05440PlusP025Input2542 6 =
    adaptiveN05440PlusP025Output2542 := by
  cbv

theorem adaptiveN05440PlusP025Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ adaptiveN05440PlusPosition2542 =
    Complex.exp ((2 : ℂ)^6 * embedPair2542 adaptiveN05440PlusP025Input2542) := by
  have hx : |adaptiveN05440PlusPosition2542| < storedWidth ⟨25, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05440PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05440PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05440PlusP025Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05440PlusP025Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ adaptiveN05440PlusPosition2542 - embedPair2542
            adaptiveN05440PlusP025Output2542.1‖ ≤ (adaptiveN05440PlusP025Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05440PlusP025Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05440PlusP025Input2542]
  rw [adaptiveN05440PlusP025Owner2542]
  have h := compactExp_error2542 adaptiveN05440PlusP025Input2542 hz 6
  simpa only [adaptiveN05440PlusP025Compute2542] using h

theorem adaptiveN05440PlusP025Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ adaptiveN05440PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05440PlusP025Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05440PlusP025Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05440PlusP026Output2542 : RatState2542 :=
  (((((-27370500051621241) : ℚ) /
        1267650600228229401496703205376),
    ((40425285370441941 : ℚ) /
        633825300114114700748351602688)),
    ((59912077754477 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

def adaptiveN05440PlusP026Input2542 : RatPair2542 :=
  ((((-((47 * 10^40
        + 8604820820512611674804590228678584994159) * 10^40
        + 4681860925800659368531562786551513391693)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-20771944281655350607437) : ℚ) /
        45035996273704960000000))

theorem adaptiveN05440PlusP026Compute2542 : compactExp2542 adaptiveN05440PlusP026Input2542 6 =
    adaptiveN05440PlusP026Output2542 := by
  cbv

theorem adaptiveN05440PlusP026Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ adaptiveN05440PlusPosition2542 =
    Complex.exp ((2 : ℂ)^6 * embedPair2542 adaptiveN05440PlusP026Input2542) := by
  have hx : |adaptiveN05440PlusPosition2542| < storedWidth ⟨26, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05440PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05440PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05440PlusP026Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05440PlusP026Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ adaptiveN05440PlusPosition2542 - embedPair2542
            adaptiveN05440PlusP026Output2542.1‖ ≤ (adaptiveN05440PlusP026Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05440PlusP026Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05440PlusP026Input2542]
  rw [adaptiveN05440PlusP026Owner2542]
  have h := compactExp_error2542 adaptiveN05440PlusP026Input2542 hz 6
  simpa only [adaptiveN05440PlusP026Compute2542] using h

theorem adaptiveN05440PlusP026Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ adaptiveN05440PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05440PlusP026Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05440PlusP026Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05440PlusP027Output2542 : RatState2542 :=
  ((((78375538908662461 : ℚ) /
        1267650600228229401496703205376),
    ((33811742974582127 : ℚ) /
        1267650600228229401496703205376)),
    ((22523431186811 : ℚ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888)))

def adaptiveN05440PlusP027Input2542 : RatPair2542 :=
  ((((-((47 * 10^40
        + 8604820820512611674804590228678584994159) * 10^40
        + 4681860925800659368531562786551513391693)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-43640783619197408678627) : ℚ) /
        90071992547409920000000))

theorem adaptiveN05440PlusP027Compute2542 : compactExp2542 adaptiveN05440PlusP027Input2542 6 =
    adaptiveN05440PlusP027Output2542 := by
  cbv

theorem adaptiveN05440PlusP027Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ adaptiveN05440PlusPosition2542 =
    Complex.exp ((2 : ℂ)^6 * embedPair2542 adaptiveN05440PlusP027Input2542) := by
  have hx : |adaptiveN05440PlusPosition2542| < storedWidth ⟨27, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05440PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05440PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05440PlusP027Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05440PlusP027Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ adaptiveN05440PlusPosition2542 - embedPair2542
            adaptiveN05440PlusP027Output2542.1‖ ≤ (adaptiveN05440PlusP027Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05440PlusP027Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05440PlusP027Input2542]
  rw [adaptiveN05440PlusP027Owner2542]
  have h := compactExp_error2542 adaptiveN05440PlusP027Input2542 hz 6
  simpa only [adaptiveN05440PlusP027Compute2542] using h

theorem adaptiveN05440PlusP027Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ adaptiveN05440PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05440PlusP027Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05440PlusP027Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05440PlusP028Output2542 : RatState2542 :=
  ((((83938739517315555 : ℚ) /
        1267650600228229401496703205376),
    (((-15499905497993049) : ℚ) /
        1267650600228229401496703205376)),
    ((40351813399135 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

def adaptiveN05440PlusP028Input2542 : RatPair2542 :=
  ((((-((47 * 10^40
        + 8604820820512611674804590228678584994159) * 10^40
        + 4681860925800659368531562786551513391693)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-177883892884016178388727) : ℚ) /
        360287970189639680000000))

theorem adaptiveN05440PlusP028Compute2542 : compactExp2542 adaptiveN05440PlusP028Input2542 6 =
    adaptiveN05440PlusP028Output2542 := by
  cbv

theorem adaptiveN05440PlusP028Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ adaptiveN05440PlusPosition2542 =
    Complex.exp ((2 : ℂ)^6 * embedPair2542 adaptiveN05440PlusP028Input2542) := by
  have hx : |adaptiveN05440PlusPosition2542| < storedWidth ⟨28, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05440PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05440PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05440PlusP028Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05440PlusP028Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ adaptiveN05440PlusPosition2542 - embedPair2542
            adaptiveN05440PlusP028Output2542.1‖ ≤ (adaptiveN05440PlusP028Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05440PlusP028Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05440PlusP028Input2542]
  rw [adaptiveN05440PlusP028Owner2542]
  have h := compactExp_error2542 adaptiveN05440PlusP028Input2542 hz 6
  simpa only [adaptiveN05440PlusP028Compute2542] using h

theorem adaptiveN05440PlusP028Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ adaptiveN05440PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05440PlusP028Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05440PlusP028Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN05440PlusP029Output2542 : RatState2542 :=
  ((((40181662807215871 : ℚ) /
        1267650600228229401496703205376),
    (((-4706790737631139) : ℚ) /
        79228162514264337593543950336)),
    ((59484785339005 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

def adaptiveN05440PlusP029Input2542 : RatPair2542 :=
  ((((-((47 * 10^40
        + 8604820820512611674804590228678584994159) * 10^40
        + 4681860925800659368531562786551513391693)) : ℚ) /
        ((100 * 10^40
        + 9944876552962436626304436891476851612005) * 10^40
        + 7835747350167102763465749633167360000000)),
    (((-182939534351242879487659) : ℚ) /
        360287970189639680000000))

theorem adaptiveN05440PlusP029Compute2542 : compactExp2542 adaptiveN05440PlusP029Input2542 6 =
    adaptiveN05440PlusP029Output2542 := by
  cbv

theorem adaptiveN05440PlusP029Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ adaptiveN05440PlusPosition2542 =
    Complex.exp ((2 : ℂ)^6 * embedPair2542 adaptiveN05440PlusP029Input2542) := by
  have hx : |adaptiveN05440PlusPosition2542| < storedWidth ⟨29, by omega⟩ ^ 2 := by
    norm_num [adaptiveN05440PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN05440PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN05440PlusP029Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN05440PlusP029Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ adaptiveN05440PlusPosition2542 - embedPair2542
            adaptiveN05440PlusP029Output2542.1‖ ≤ (adaptiveN05440PlusP029Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN05440PlusP029Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN05440PlusP029Input2542]
  rw [adaptiveN05440PlusP029Owner2542]
  have h := compactExp_error2542 adaptiveN05440PlusP029Input2542 hz 6
  simpa only [adaptiveN05440PlusP029Compute2542] using h

theorem adaptiveN05440PlusP029Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ adaptiveN05440PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN05440PlusP029Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN05440PlusP029Input2542, Complex.mul_re, Complex.mul_im]

noncomputable def adaptiveN05440PlusValue2542 (i : Fin 30) : ℂ :=
  match i.val with
  | 0 => embedPair2542 adaptiveN05440PlusP000Output2542.1
  | 1 => embedPair2542 adaptiveN05440PlusP001Output2542.1
  | 2 => embedPair2542 adaptiveN05440PlusP002Output2542.1
  | 3 => embedPair2542 adaptiveN05440PlusP003Output2542.1
  | 4 => embedPair2542 adaptiveN05440PlusP004Output2542.1
  | 5 => embedPair2542 adaptiveN05440PlusP005Output2542.1
  | 6 => embedPair2542 adaptiveN05440PlusP006Output2542.1
  | 7 => embedPair2542 adaptiveN05440PlusP007Output2542.1
  | 8 => embedPair2542 adaptiveN05440PlusP008Output2542.1
  | 9 => embedPair2542 adaptiveN05440PlusP009Output2542.1
  | 10 => embedPair2542 adaptiveN05440PlusP010Output2542.1
  | 11 => embedPair2542 adaptiveN05440PlusP011Output2542.1
  | 12 => embedPair2542 adaptiveN05440PlusP012Output2542.1
  | 13 => embedPair2542 adaptiveN05440PlusP013Output2542.1
  | 14 => embedPair2542 adaptiveN05440PlusP014Output2542.1
  | 15 => embedPair2542 adaptiveN05440PlusP015Output2542.1
  | 16 => embedPair2542 adaptiveN05440PlusP016Output2542.1
  | 17 => embedPair2542 adaptiveN05440PlusP017Output2542.1
  | 18 => embedPair2542 adaptiveN05440PlusP018Output2542.1
  | 19 => embedPair2542 adaptiveN05440PlusP019Output2542.1
  | 20 => embedPair2542 adaptiveN05440PlusP020Output2542.1
  | 21 => embedPair2542 adaptiveN05440PlusP021Output2542.1
  | 22 => embedPair2542 adaptiveN05440PlusP022Output2542.1
  | 23 => embedPair2542 adaptiveN05440PlusP023Output2542.1
  | 24 => embedPair2542 adaptiveN05440PlusP024Output2542.1
  | 25 => embedPair2542 adaptiveN05440PlusP025Output2542.1
  | 26 => embedPair2542 adaptiveN05440PlusP026Output2542.1
  | 27 => embedPair2542 adaptiveN05440PlusP027Output2542.1
  | 28 => embedPair2542 adaptiveN05440PlusP028Output2542.1
  | 29 => embedPair2542 adaptiveN05440PlusP029Output2542.1
  | _ => 0

noncomputable def adaptiveN05440PlusError2542 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => (adaptiveN05440PlusP000Output2542.2 : ℝ)
  | 1 => (adaptiveN05440PlusP001Output2542.2 : ℝ)
  | 2 => (adaptiveN05440PlusP002Output2542.2 : ℝ)
  | 3 => (adaptiveN05440PlusP003Output2542.2 : ℝ)
  | 4 => (adaptiveN05440PlusP004Output2542.2 : ℝ)
  | 5 => (adaptiveN05440PlusP005Output2542.2 : ℝ)
  | 6 => (adaptiveN05440PlusP006Output2542.2 : ℝ)
  | 7 => (adaptiveN05440PlusP007Output2542.2 : ℝ)
  | 8 => (adaptiveN05440PlusP008Output2542.2 : ℝ)
  | 9 => (adaptiveN05440PlusP009Output2542.2 : ℝ)
  | 10 => (adaptiveN05440PlusP010Output2542.2 : ℝ)
  | 11 => (adaptiveN05440PlusP011Output2542.2 : ℝ)
  | 12 => (adaptiveN05440PlusP012Output2542.2 : ℝ)
  | 13 => (adaptiveN05440PlusP013Output2542.2 : ℝ)
  | 14 => (adaptiveN05440PlusP014Output2542.2 : ℝ)
  | 15 => (adaptiveN05440PlusP015Output2542.2 : ℝ)
  | 16 => (adaptiveN05440PlusP016Output2542.2 : ℝ)
  | 17 => (adaptiveN05440PlusP017Output2542.2 : ℝ)
  | 18 => (adaptiveN05440PlusP018Output2542.2 : ℝ)
  | 19 => (adaptiveN05440PlusP019Output2542.2 : ℝ)
  | 20 => (adaptiveN05440PlusP020Output2542.2 : ℝ)
  | 21 => (adaptiveN05440PlusP021Output2542.2 : ℝ)
  | 22 => (adaptiveN05440PlusP022Output2542.2 : ℝ)
  | 23 => (adaptiveN05440PlusP023Output2542.2 : ℝ)
  | 24 => (adaptiveN05440PlusP024Output2542.2 : ℝ)
  | 25 => (adaptiveN05440PlusP025Output2542.2 : ℝ)
  | 26 => (adaptiveN05440PlusP026Output2542.2 : ℝ)
  | 27 => (adaptiveN05440PlusP027Output2542.2 : ℝ)
  | 28 => (adaptiveN05440PlusP028Output2542.2 : ℝ)
  | 29 => (adaptiveN05440PlusP029Output2542.2 : ℝ)
  | _ => 0

theorem adaptiveN05440PlusExp_error2542 (i : Fin 30) :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 i adaptiveN05440PlusPosition2542 - adaptiveN05440PlusValue2542 i‖ ≤
            adaptiveN05440PlusError2542 i := by
  fin_cases i
  · simpa only [adaptiveN05440PlusValue2542, adaptiveN05440PlusError2542] using
      adaptiveN05440PlusP000Error2542
  · simpa only [adaptiveN05440PlusValue2542, adaptiveN05440PlusError2542] using
      adaptiveN05440PlusP001Error2542
  · simpa only [adaptiveN05440PlusValue2542, adaptiveN05440PlusError2542] using
      adaptiveN05440PlusP002Error2542
  · simpa only [adaptiveN05440PlusValue2542, adaptiveN05440PlusError2542] using
      adaptiveN05440PlusP003Error2542
  · simpa only [adaptiveN05440PlusValue2542, adaptiveN05440PlusError2542] using
      adaptiveN05440PlusP004Error2542
  · simpa only [adaptiveN05440PlusValue2542, adaptiveN05440PlusError2542] using
      adaptiveN05440PlusP005Error2542
  · simpa only [adaptiveN05440PlusValue2542, adaptiveN05440PlusError2542] using
      adaptiveN05440PlusP006Error2542
  · simpa only [adaptiveN05440PlusValue2542, adaptiveN05440PlusError2542] using
      adaptiveN05440PlusP007Error2542
  · simpa only [adaptiveN05440PlusValue2542, adaptiveN05440PlusError2542] using
      adaptiveN05440PlusP008Error2542
  · simpa only [adaptiveN05440PlusValue2542, adaptiveN05440PlusError2542] using
      adaptiveN05440PlusP009Error2542
  · simpa only [adaptiveN05440PlusValue2542, adaptiveN05440PlusError2542] using
      adaptiveN05440PlusP010Error2542
  · simpa only [adaptiveN05440PlusValue2542, adaptiveN05440PlusError2542] using
      adaptiveN05440PlusP011Error2542
  · simpa only [adaptiveN05440PlusValue2542, adaptiveN05440PlusError2542] using
      adaptiveN05440PlusP012Error2542
  · simpa only [adaptiveN05440PlusValue2542, adaptiveN05440PlusError2542] using
      adaptiveN05440PlusP013Error2542
  · simpa only [adaptiveN05440PlusValue2542, adaptiveN05440PlusError2542] using
      adaptiveN05440PlusP014Error2542
  · simpa only [adaptiveN05440PlusValue2542, adaptiveN05440PlusError2542] using
      adaptiveN05440PlusP015Error2542
  · simpa only [adaptiveN05440PlusValue2542, adaptiveN05440PlusError2542] using
      adaptiveN05440PlusP016Error2542
  · simpa only [adaptiveN05440PlusValue2542, adaptiveN05440PlusError2542] using
      adaptiveN05440PlusP017Error2542
  · simpa only [adaptiveN05440PlusValue2542, adaptiveN05440PlusError2542] using
      adaptiveN05440PlusP018Error2542
  · simpa only [adaptiveN05440PlusValue2542, adaptiveN05440PlusError2542] using
      adaptiveN05440PlusP019Error2542
  · simpa only [adaptiveN05440PlusValue2542, adaptiveN05440PlusError2542] using
      adaptiveN05440PlusP020Error2542
  · simpa only [adaptiveN05440PlusValue2542, adaptiveN05440PlusError2542] using
      adaptiveN05440PlusP021Error2542
  · simpa only [adaptiveN05440PlusValue2542, adaptiveN05440PlusError2542] using
      adaptiveN05440PlusP022Error2542
  · simpa only [adaptiveN05440PlusValue2542, adaptiveN05440PlusError2542] using
      adaptiveN05440PlusP023Error2542
  · simpa only [adaptiveN05440PlusValue2542, adaptiveN05440PlusError2542] using
      adaptiveN05440PlusP024Error2542
  · simpa only [adaptiveN05440PlusValue2542, adaptiveN05440PlusError2542] using
      adaptiveN05440PlusP025Error2542
  · simpa only [adaptiveN05440PlusValue2542, adaptiveN05440PlusError2542] using
      adaptiveN05440PlusP026Error2542
  · simpa only [adaptiveN05440PlusValue2542, adaptiveN05440PlusError2542] using
      adaptiveN05440PlusP027Error2542
  · simpa only [adaptiveN05440PlusValue2542, adaptiveN05440PlusError2542] using
      adaptiveN05440PlusP028Error2542
  · simpa only [adaptiveN05440PlusValue2542, adaptiveN05440PlusError2542] using
      adaptiveN05440PlusP029Error2542

theorem adaptiveN05440PlusUnit_norm2542 (i : Fin 30) :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 i adaptiveN05440PlusPosition2542‖ ≤ 1 := by
  fin_cases i
  · simpa only [adaptiveN05440PlusValue2542, adaptiveN05440PlusError2542] using
      adaptiveN05440PlusP000Norm2542
  · simpa only [adaptiveN05440PlusValue2542, adaptiveN05440PlusError2542] using
      adaptiveN05440PlusP001Norm2542
  · simpa only [adaptiveN05440PlusValue2542, adaptiveN05440PlusError2542] using
      adaptiveN05440PlusP002Norm2542
  · simpa only [adaptiveN05440PlusValue2542, adaptiveN05440PlusError2542] using
      adaptiveN05440PlusP003Norm2542
  · simpa only [adaptiveN05440PlusValue2542, adaptiveN05440PlusError2542] using
      adaptiveN05440PlusP004Norm2542
  · simpa only [adaptiveN05440PlusValue2542, adaptiveN05440PlusError2542] using
      adaptiveN05440PlusP005Norm2542
  · simpa only [adaptiveN05440PlusValue2542, adaptiveN05440PlusError2542] using
      adaptiveN05440PlusP006Norm2542
  · simpa only [adaptiveN05440PlusValue2542, adaptiveN05440PlusError2542] using
      adaptiveN05440PlusP007Norm2542
  · simpa only [adaptiveN05440PlusValue2542, adaptiveN05440PlusError2542] using
      adaptiveN05440PlusP008Norm2542
  · simpa only [adaptiveN05440PlusValue2542, adaptiveN05440PlusError2542] using
      adaptiveN05440PlusP009Norm2542
  · simpa only [adaptiveN05440PlusValue2542, adaptiveN05440PlusError2542] using
      adaptiveN05440PlusP010Norm2542
  · simpa only [adaptiveN05440PlusValue2542, adaptiveN05440PlusError2542] using
      adaptiveN05440PlusP011Norm2542
  · simpa only [adaptiveN05440PlusValue2542, adaptiveN05440PlusError2542] using
      adaptiveN05440PlusP012Norm2542
  · simpa only [adaptiveN05440PlusValue2542, adaptiveN05440PlusError2542] using
      adaptiveN05440PlusP013Norm2542
  · simpa only [adaptiveN05440PlusValue2542, adaptiveN05440PlusError2542] using
      adaptiveN05440PlusP014Norm2542
  · simpa only [adaptiveN05440PlusValue2542, adaptiveN05440PlusError2542] using
      adaptiveN05440PlusP015Norm2542
  · simpa only [adaptiveN05440PlusValue2542, adaptiveN05440PlusError2542] using
      adaptiveN05440PlusP016Norm2542
  · simpa only [adaptiveN05440PlusValue2542, adaptiveN05440PlusError2542] using
      adaptiveN05440PlusP017Norm2542
  · simpa only [adaptiveN05440PlusValue2542, adaptiveN05440PlusError2542] using
      adaptiveN05440PlusP018Norm2542
  · simpa only [adaptiveN05440PlusValue2542, adaptiveN05440PlusError2542] using
      adaptiveN05440PlusP019Norm2542
  · simpa only [adaptiveN05440PlusValue2542, adaptiveN05440PlusError2542] using
      adaptiveN05440PlusP020Norm2542
  · simpa only [adaptiveN05440PlusValue2542, adaptiveN05440PlusError2542] using
      adaptiveN05440PlusP021Norm2542
  · simpa only [adaptiveN05440PlusValue2542, adaptiveN05440PlusError2542] using
      adaptiveN05440PlusP022Norm2542
  · simpa only [adaptiveN05440PlusValue2542, adaptiveN05440PlusError2542] using
      adaptiveN05440PlusP023Norm2542
  · simpa only [adaptiveN05440PlusValue2542, adaptiveN05440PlusError2542] using
      adaptiveN05440PlusP024Norm2542
  · simpa only [adaptiveN05440PlusValue2542, adaptiveN05440PlusError2542] using
      adaptiveN05440PlusP025Norm2542
  · simpa only [adaptiveN05440PlusValue2542, adaptiveN05440PlusError2542] using
      adaptiveN05440PlusP026Norm2542
  · simpa only [adaptiveN05440PlusValue2542, adaptiveN05440PlusError2542] using
      adaptiveN05440PlusP027Norm2542
  · simpa only [adaptiveN05440PlusValue2542, adaptiveN05440PlusError2542] using
      adaptiveN05440PlusP028Norm2542
  · simpa only [adaptiveN05440PlusValue2542, adaptiveN05440PlusError2542] using
      adaptiveN05440PlusP029Norm2542

noncomputable def adaptiveN05440PlusSumValue2542 : ℂ := ⟨(((((2491929 * 10^40
        + 9624770783735339919990625973839050026984) * 10^40
        + 1792567356600965027701481636873375414114) * 10^40
        + 6411029779039899566501762795821736160369) : ℝ) /
        (((5415370 * 10^40
        + 4963297165226140902034044603582742911628) * 10^40
        + 4339174837984293088793224180786254499995) * 10^40
        + 11922147613471467208908991351228465152)),
    (((-(((3775425 * 10^40
        + 5536647665030467530343974684205802994623) * 10^40
        + 1505676124309338947165463527000420048880) * 10^40
        + 397544844622642790809925619220028124775)) : ℝ) /
        (((10830740 * 10^40
        + 9926594330452281804068089207165485823256) * 10^40
        + 8678349675968586177586448361572508999990) * 10^40
        + 23844295226942934417817982702456930304))⟩

noncomputable def adaptiveN05440PlusUpper2542 : ℝ := ((721605217 : ℝ) /
        1250000000)

theorem adaptiveN05440PlusSum_eq2542 :
    (∑ i : Fin 30, baseCoefficientCenter2540 i * adaptiveN05440PlusValue2542 i) =
      adaptiveN05440PlusSumValue2542 := by
  rw [sum30_chain2541]
  apply Complex.ext <;>
    norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, adaptiveN05440PlusValue2542,
      adaptiveN05440PlusSumValue2542, embedPair2542, adaptiveN05440PlusP000Output2542,
      adaptiveN05440PlusP001Output2542,
      adaptiveN05440PlusP002Output2542,
      adaptiveN05440PlusP003Output2542,
      adaptiveN05440PlusP004Output2542,
      adaptiveN05440PlusP005Output2542,
      adaptiveN05440PlusP006Output2542,
      adaptiveN05440PlusP007Output2542,
      adaptiveN05440PlusP008Output2542,
      adaptiveN05440PlusP009Output2542,
      adaptiveN05440PlusP010Output2542,
      adaptiveN05440PlusP011Output2542,
      adaptiveN05440PlusP012Output2542,
      adaptiveN05440PlusP013Output2542,
      adaptiveN05440PlusP014Output2542,
      adaptiveN05440PlusP015Output2542,
      adaptiveN05440PlusP016Output2542,
      adaptiveN05440PlusP017Output2542,
      adaptiveN05440PlusP018Output2542,
      adaptiveN05440PlusP019Output2542,
      adaptiveN05440PlusP020Output2542,
      adaptiveN05440PlusP021Output2542,
      adaptiveN05440PlusP022Output2542,
      adaptiveN05440PlusP023Output2542,
      adaptiveN05440PlusP024Output2542,
      adaptiveN05440PlusP025Output2542,
      adaptiveN05440PlusP026Output2542,
      adaptiveN05440PlusP027Output2542,
      adaptiveN05440PlusP028Output2542,
      adaptiveN05440PlusP029Output2542, Complex.mul_re, Complex.mul_im]

theorem adaptiveN05440PlusSum_norm2542 :
    ‖∑ i : Fin 30, baseCoefficientCenter2540 i * adaptiveN05440PlusValue2542 i‖ ≤
      ((1154568347 : ℝ) /
        2000000000) := by
  rw [adaptiveN05440PlusSum_eq2542]
  apply complex_norm_le_of_sq2541 _ _ (by norm_num)
  norm_num [adaptiveN05440PlusSumValue2542]

theorem adaptiveN05440PlusEvaluation_charge2542 :
    (∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
      |(baseCoefficientCenter2540 i).im|) * adaptiveN05440PlusError2542 i) ≤ (1 : ℝ)/10^12 := by
  rw [sum30_chain2541]
  norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, adaptiveN05440PlusError2542,
      adaptiveN05440PlusP000Output2542,
      adaptiveN05440PlusP001Output2542,
      adaptiveN05440PlusP002Output2542,
      adaptiveN05440PlusP003Output2542,
      adaptiveN05440PlusP004Output2542,
      adaptiveN05440PlusP005Output2542,
      adaptiveN05440PlusP006Output2542,
      adaptiveN05440PlusP007Output2542,
      adaptiveN05440PlusP008Output2542,
      adaptiveN05440PlusP009Output2542,
      adaptiveN05440PlusP010Output2542,
      adaptiveN05440PlusP011Output2542,
      adaptiveN05440PlusP012Output2542,
      adaptiveN05440PlusP013Output2542,
      adaptiveN05440PlusP014Output2542,
      adaptiveN05440PlusP015Output2542,
      adaptiveN05440PlusP016Output2542,
      adaptiveN05440PlusP017Output2542,
      adaptiveN05440PlusP018Output2542,
      adaptiveN05440PlusP019Output2542,
      adaptiveN05440PlusP020Output2542,
      adaptiveN05440PlusP021Output2542,
      adaptiveN05440PlusP022Output2542,
      adaptiveN05440PlusP023Output2542,
      adaptiveN05440PlusP024Output2542,
      adaptiveN05440PlusP025Output2542,
      adaptiveN05440PlusP026Output2542,
      adaptiveN05440PlusP027Output2542,
      adaptiveN05440PlusP028Output2542,
      adaptiveN05440PlusP029Output2542]

theorem adaptiveN05440PlusSigned_le2542 :
    signedJetUpper2539 0 (((1 : ℝ) /
        2)) baseCoefficientCenter2540 baseCoefficientError2540
      nodeModulation2541 adaptiveN05440PlusPosition2542 ≤ adaptiveN05440PlusUpper2542 := by
  have hsum :
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i *
        weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 i adaptiveN05440PlusPosition2542‖ ≤
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i * adaptiveN05440PlusValue2542 i‖ +
        ∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
          |(baseCoefficientCenter2540 i).im|) * adaptiveN05440PlusError2542 i := by
    apply norm_sum_le_center_sum_add_error2531
    intro i _
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (Complex.norm_le_abs_re_add_abs_im _) (adaptiveN05440PlusExp_error2542 i)
      (norm_nonneg _) (by positivity)
  have heach : ∀ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 i adaptiveN05440PlusPosition2542‖ ≤
        (1 : ℝ)/10^30 := by
    intro i
    have h := mul_le_mul_of_nonneg_left (adaptiveN05440PlusUnit_norm2542 i)
      (by norm_num [baseCoefficientError2540] : 0 ≤ baseCoefficientError2540 i)
    simpa [baseCoefficientError2540] using h
  have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
  have he' : (∑ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 i adaptiveN05440PlusPosition2542‖) ≤
        (30 : ℝ)/10^30 := by simpa using he
  unfold signedJetUpper2539 adaptiveN05440PlusUpper2542
  linarith [adaptiveN05440PlusSum_norm2542, adaptiveN05440PlusEvaluation_charge2542]

theorem adaptiveN05440PlusPhysical_le2542 (coefficients : Fin 30 → ℂ)
    (hbox : ∀ i, (baseCoefficientBox2540 i).Mem (coefficients i)) :
    ‖weightedPhysical2539 (((1 : ℝ) /
        2)) coefficients nodeModulation2541 adaptiveN05440PlusPosition2542‖ ≤
      adaptiveN05440PlusUpper2542 := by
  have h := weightedPhysical2539_jet_le_center_error 0 (((1 : ℝ) /
        2)) coefficients
    baseCoefficientCenter2540 baseCoefficientError2540 nodeModulation2541
    (fun i => baseCoefficient_error_of_box2540 i (coefficients i) (hbox i))
        adaptiveN05440PlusPosition2542
  simpa only [iteratedDeriv_zero] using h.trans adaptiveN05440PlusSigned_le2542

theorem adaptiveN05440PlusGrid2542 :
    -stripRadius2303 + (5440 : ℝ)*(2*stripRadius2303/10240) = adaptiveN05440PlusPosition2542 := by
  norm_num [stripRadius2303, adaptiveN05440PlusPosition2542]

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.adaptiveN05440PlusSigned_le2542
#print axioms ConnesWeilRH.Dev.adaptiveN05440PlusPhysical_le2542
