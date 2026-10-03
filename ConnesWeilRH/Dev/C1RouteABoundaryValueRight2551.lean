import ConnesWeilRH.Dev.C1RouteACompactExp2542
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541

namespace ConnesWeilRH.Dev

open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def adaptiveN02701PlusPosition2542 : ℝ := (((-158531586419) : ℝ) /
        51200000000)

def adaptiveN02701PlusP000Output2542 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem adaptiveN02701PlusP000Zero2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ adaptiveN02701PlusPosition2542 = 0 := by
  have hx : ¬ |adaptiveN02701PlusPosition2542| < storedWidth ⟨0, by omega⟩ ^ 2 := by
    norm_num [adaptiveN02701PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero, weightedFunction2348,
    externalFamilyValue2344, if_neg hx, mul_zero]

theorem adaptiveN02701PlusP000Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ adaptiveN02701PlusPosition2542 - embedPair2542
            adaptiveN02701PlusP000Output2542.1‖ ≤ (adaptiveN02701PlusP000Output2542.2 : ℝ) := by
  have hz : embedPair2542 adaptiveN02701PlusP000Output2542.1 = 0 := by
    apply Complex.ext <;> norm_num [adaptiveN02701PlusP000Output2542, embedPair2542]
  rw [adaptiveN02701PlusP000Zero2542, hz]
  norm_num [adaptiveN02701PlusP000Output2542]

theorem adaptiveN02701PlusP000Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ adaptiveN02701PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN02701PlusP000Zero2542]
  norm_num

def adaptiveN02701PlusP001Output2542 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

def adaptiveN02701PlusP001Input2542 : RatPair2542 :=
  ((((-((340 * 10^40
        + 1125558694715412604882605546165965236561) * 10^40
        + 9325600687173468560131001925406640200979)) : ℚ) /
        ((941 * 10^40
        + 6102169216506454849034257242358098754684) * 10^40
        + 4000368461807982441421667880140800000000)),
    ((875774620147323865939848151 : ℚ) /
        3689348814741910323200000000))

theorem adaptiveN02701PlusP001Compute2542 : compactExp2542 adaptiveN02701PlusP001Input2542 9 =
    adaptiveN02701PlusP001Output2542 := by
  cbv

theorem adaptiveN02701PlusP001Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ adaptiveN02701PlusPosition2542 =
    Complex.exp ((2 : ℂ)^9 * embedPair2542 adaptiveN02701PlusP001Input2542) := by
  have hx : |adaptiveN02701PlusPosition2542| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [adaptiveN02701PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN02701PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN02701PlusP001Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN02701PlusP001Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ adaptiveN02701PlusPosition2542 - embedPair2542
            adaptiveN02701PlusP001Output2542.1‖ ≤ (adaptiveN02701PlusP001Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN02701PlusP001Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN02701PlusP001Input2542]
  rw [adaptiveN02701PlusP001Owner2542]
  have h := compactExp_error2542 adaptiveN02701PlusP001Input2542 hz 9
  simpa only [adaptiveN02701PlusP001Compute2542] using h

theorem adaptiveN02701PlusP001Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ adaptiveN02701PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN02701PlusP001Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN02701PlusP001Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN02701PlusP002Output2542 : RatState2542 :=
  (((((-73) : ℚ) /
        316912650057057350374175801344),
    (((-439) : ℚ) /
        1267650600228229401496703205376)),
    ((2199023255555 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

def adaptiveN02701PlusP002Input2542 : RatPair2542 :=
  ((((-((9033 * 10^40
        + 8109252320354666245907324545684805984286) * 10^40
        + 2898018879638657721153554737628069387539)) : ℚ) /
        ((36680 * 10^40
        + 5267114824128922047222362789138794665314) * 10^40
        + 902751818529719531373343041126400000000)),
    (((-875774620147323865939848151) : ℚ) /
        1844674407370955161600000000))

theorem adaptiveN02701PlusP002Compute2542 : compactExp2542 adaptiveN02701PlusP002Input2542 8 =
    adaptiveN02701PlusP002Output2542 := by
  cbv

theorem adaptiveN02701PlusP002Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ adaptiveN02701PlusPosition2542 =
    Complex.exp ((2 : ℂ)^8 * embedPair2542 adaptiveN02701PlusP002Input2542) := by
  have hx : |adaptiveN02701PlusPosition2542| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [adaptiveN02701PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN02701PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN02701PlusP002Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN02701PlusP002Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ adaptiveN02701PlusPosition2542 - embedPair2542
            adaptiveN02701PlusP002Output2542.1‖ ≤ (adaptiveN02701PlusP002Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN02701PlusP002Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN02701PlusP002Input2542]
  rw [adaptiveN02701PlusP002Owner2542]
  have h := compactExp_error2542 adaptiveN02701PlusP002Input2542 hz 8
  simpa only [adaptiveN02701PlusP002Compute2542] using h

theorem adaptiveN02701PlusP002Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ adaptiveN02701PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN02701PlusP002Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN02701PlusP002Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN02701PlusP003Output2542 : RatState2542 :=
  (((((-2510567225) : ℚ) /
        633825300114114700748351602688),
    (((-943866427) : ℚ) /
        158456325028528675187087900672)),
    ((1099527447149 : ℚ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888)))

def adaptiveN02701PlusP003Input2542 : RatPair2542 :=
  ((((-((1204018 * 10^40
        + 3199206753711006565389390034201102437777) * 10^40
        + 7349271424128768512973515705970498543953)) : ℚ) /
        ((6644764 * 10^40
        + 348595898346936727630550565694213304645) * 10^40
        + 356964576015918677191939509452800000000)),
    (((-875774620147323865939848151) : ℚ) /
        1844674407370955161600000000))

theorem adaptiveN02701PlusP003Compute2542 : compactExp2542 adaptiveN02701PlusP003Input2542 8 =
    adaptiveN02701PlusP003Output2542 := by
  cbv

theorem adaptiveN02701PlusP003Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ adaptiveN02701PlusPosition2542 =
    Complex.exp ((2 : ℂ)^8 * embedPair2542 adaptiveN02701PlusP003Input2542) := by
  have hx : |adaptiveN02701PlusPosition2542| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [adaptiveN02701PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN02701PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN02701PlusP003Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN02701PlusP003Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ adaptiveN02701PlusPosition2542 - embedPair2542
            adaptiveN02701PlusP003Output2542.1‖ ≤ (adaptiveN02701PlusP003Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN02701PlusP003Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN02701PlusP003Input2542]
  rw [adaptiveN02701PlusP003Owner2542]
  have h := compactExp_error2542 adaptiveN02701PlusP003Input2542 hz 8
  simpa only [adaptiveN02701PlusP003Compute2542] using h

theorem adaptiveN02701PlusP003Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ adaptiveN02701PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN02701PlusP003Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN02701PlusP003Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN02701PlusP004Output2542 : RatState2542 :=
  (((((-1259046090477) : ℚ) /
        633825300114114700748351602688),
    ((1893390980429 : ℚ) /
        633825300114114700748351602688)),
    ((553627271561 : ℚ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944)))

def adaptiveN02701PlusP004Input2542 : RatPair2542 :=
  ((((-((21030 * 10^40
        + 4978280417753696551825490501735319367009) * 10^40
        + 9100087780138783714176925758135881887539)) : ℚ) /
        ((134028 * 10^40
        + 5763226050861645114137505055527745988340) * 10^40
        + 4359916327702839531373343041126400000000)),
    ((875774620147323865939848151 : ℚ) /
        1844674407370955161600000000))

theorem adaptiveN02701PlusP004Compute2542 : compactExp2542 adaptiveN02701PlusP004Input2542 8 =
    adaptiveN02701PlusP004Output2542 := by
  cbv

theorem adaptiveN02701PlusP004Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ adaptiveN02701PlusPosition2542 =
    Complex.exp ((2 : ℂ)^8 * embedPair2542 adaptiveN02701PlusP004Input2542) := by
  have hx : |adaptiveN02701PlusPosition2542| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [adaptiveN02701PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN02701PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN02701PlusP004Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN02701PlusP004Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ adaptiveN02701PlusPosition2542 - embedPair2542
            adaptiveN02701PlusP004Output2542.1‖ ≤ (adaptiveN02701PlusP004Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN02701PlusP004Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN02701PlusP004Input2542]
  rw [adaptiveN02701PlusP004Owner2542]
  have h := compactExp_error2542 adaptiveN02701PlusP004Input2542 hz 8
  simpa only [adaptiveN02701PlusP004Compute2542] using h

theorem adaptiveN02701PlusP004Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ adaptiveN02701PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN02701PlusP004Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN02701PlusP004Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN02701PlusP005Output2542 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem adaptiveN02701PlusP005Zero2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ adaptiveN02701PlusPosition2542 = 0 := by
  have hx : ¬ |adaptiveN02701PlusPosition2542| < storedWidth ⟨5, by omega⟩ ^ 2 := by
    norm_num [adaptiveN02701PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero, weightedFunction2348,
    externalFamilyValue2344, if_neg hx, mul_zero]

theorem adaptiveN02701PlusP005Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ adaptiveN02701PlusPosition2542 - embedPair2542
            adaptiveN02701PlusP005Output2542.1‖ ≤ (adaptiveN02701PlusP005Output2542.2 : ℝ) := by
  have hz : embedPair2542 adaptiveN02701PlusP005Output2542.1 = 0 := by
    apply Complex.ext <;> norm_num [adaptiveN02701PlusP005Output2542, embedPair2542]
  rw [adaptiveN02701PlusP005Zero2542, hz]
  norm_num [adaptiveN02701PlusP005Output2542]

theorem adaptiveN02701PlusP005Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ adaptiveN02701PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN02701PlusP005Zero2542]
  norm_num

def adaptiveN02701PlusP006Output2542 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

def adaptiveN02701PlusP006Input2542 : RatPair2542 :=
  ((((-43838019295084218252511359948400647) : ℚ) /
        73447401531966028759865753600000000),
    ((0 : ℚ) /
        1))

theorem adaptiveN02701PlusP006Compute2542 : compactExp2542 adaptiveN02701PlusP006Input2542 7 =
    adaptiveN02701PlusP006Output2542 := by
  cbv

theorem adaptiveN02701PlusP006Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ adaptiveN02701PlusPosition2542 =
    Complex.exp ((2 : ℂ)^7 * embedPair2542 adaptiveN02701PlusP006Input2542) := by
  have hx : |adaptiveN02701PlusPosition2542| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [adaptiveN02701PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN02701PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN02701PlusP006Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN02701PlusP006Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ adaptiveN02701PlusPosition2542 - embedPair2542
            adaptiveN02701PlusP006Output2542.1‖ ≤ (adaptiveN02701PlusP006Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN02701PlusP006Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN02701PlusP006Input2542]
  rw [adaptiveN02701PlusP006Owner2542]
  have h := compactExp_error2542 adaptiveN02701PlusP006Input2542 hz 7
  simpa only [adaptiveN02701PlusP006Compute2542] using h

theorem adaptiveN02701PlusP006Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ adaptiveN02701PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN02701PlusP006Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN02701PlusP006Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN02701PlusP007Output2542 : RatState2542 :=
  ((((9067985245 : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1)),
    ((2199024573161 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

def adaptiveN02701PlusP007Input2542 : RatPair2542 :=
  ((((-((1204018 * 10^40
        + 3199206753711006565389390034201102437777) * 10^40
        + 7349271424128768512973515705970498543953)) : ℚ) /
        ((1661191 * 10^40
        + 87148974586734181907637641423553326161) * 10^40
        + 2589241144003979669297984877363200000000)),
    ((0 : ℚ) /
        1))

theorem adaptiveN02701PlusP007Compute2542 : compactExp2542 adaptiveN02701PlusP007Input2542 6 =
    adaptiveN02701PlusP007Output2542 := by
  cbv

theorem adaptiveN02701PlusP007Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ adaptiveN02701PlusPosition2542 =
    Complex.exp ((2 : ℂ)^6 * embedPair2542 adaptiveN02701PlusP007Input2542) := by
  have hx : |adaptiveN02701PlusPosition2542| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [adaptiveN02701PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN02701PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN02701PlusP007Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN02701PlusP007Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ adaptiveN02701PlusPosition2542 - embedPair2542
            adaptiveN02701PlusP007Output2542.1‖ ≤ (adaptiveN02701PlusP007Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN02701PlusP007Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN02701PlusP007Input2542]
  rw [adaptiveN02701PlusP007Owner2542]
  have h := compactExp_error2542 adaptiveN02701PlusP007Input2542 hz 6
  simpa only [adaptiveN02701PlusP007Compute2542] using h

theorem adaptiveN02701PlusP007Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ adaptiveN02701PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN02701PlusP007Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN02701PlusP007Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN02701PlusP008Output2542 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

def adaptiveN02701PlusP008Input2542 : RatPair2542 :=
  ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((630729240492097551551105443 : ℚ) /
        944473296573929042739200000000))

theorem adaptiveN02701PlusP008Compute2542 : compactExp2542 adaptiveN02701PlusP008Input2542 16 =
    adaptiveN02701PlusP008Output2542 := by
  cbv

theorem adaptiveN02701PlusP008Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ adaptiveN02701PlusPosition2542 =
    Complex.exp ((2 : ℂ)^16 * embedPair2542 adaptiveN02701PlusP008Input2542) := by
  have hx : |adaptiveN02701PlusPosition2542| < storedWidth ⟨8, by omega⟩ ^ 2 := by
    norm_num [adaptiveN02701PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN02701PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN02701PlusP008Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN02701PlusP008Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ adaptiveN02701PlusPosition2542 - embedPair2542
            adaptiveN02701PlusP008Output2542.1‖ ≤ (adaptiveN02701PlusP008Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN02701PlusP008Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN02701PlusP008Input2542]
  rw [adaptiveN02701PlusP008Owner2542]
  have h := compactExp_error2542 adaptiveN02701PlusP008Input2542 hz 16
  simpa only [adaptiveN02701PlusP008Compute2542] using h

theorem adaptiveN02701PlusP008Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ adaptiveN02701PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN02701PlusP008Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN02701PlusP008Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN02701PlusP009Output2542 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

def adaptiveN02701PlusP009Input2542 : RatPair2542 :=
  ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((938059634128117561826070909 : ℚ) /
        944473296573929042739200000000))

theorem adaptiveN02701PlusP009Compute2542 : compactExp2542 adaptiveN02701PlusP009Input2542 16 =
    adaptiveN02701PlusP009Output2542 := by
  cbv

theorem adaptiveN02701PlusP009Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ adaptiveN02701PlusPosition2542 =
    Complex.exp ((2 : ℂ)^16 * embedPair2542 adaptiveN02701PlusP009Input2542) := by
  have hx : |adaptiveN02701PlusPosition2542| < storedWidth ⟨9, by omega⟩ ^ 2 := by
    norm_num [adaptiveN02701PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN02701PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN02701PlusP009Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN02701PlusP009Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ adaptiveN02701PlusPosition2542 - embedPair2542
            adaptiveN02701PlusP009Output2542.1‖ ≤ (adaptiveN02701PlusP009Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN02701PlusP009Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN02701PlusP009Input2542]
  rw [adaptiveN02701PlusP009Owner2542]
  have h := compactExp_error2542 adaptiveN02701PlusP009Input2542 hz 16
  simpa only [adaptiveN02701PlusP009Compute2542] using h

theorem adaptiveN02701PlusP009Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ adaptiveN02701PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN02701PlusP009Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN02701PlusP009Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN02701PlusP010Output2542 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

def adaptiveN02701PlusP010Input2542 : RatPair2542 :=
  ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((558025679572758329216722299 : ℚ) /
        472236648286964521369600000000))

theorem adaptiveN02701PlusP010Compute2542 : compactExp2542 adaptiveN02701PlusP010Input2542 16 =
    adaptiveN02701PlusP010Output2542 := by
  cbv

theorem adaptiveN02701PlusP010Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ adaptiveN02701PlusPosition2542 =
    Complex.exp ((2 : ℂ)^16 * embedPair2542 adaptiveN02701PlusP010Input2542) := by
  have hx : |adaptiveN02701PlusPosition2542| < storedWidth ⟨10, by omega⟩ ^ 2 := by
    norm_num [adaptiveN02701PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN02701PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN02701PlusP010Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN02701PlusP010Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ adaptiveN02701PlusPosition2542 - embedPair2542
            adaptiveN02701PlusP010Output2542.1‖ ≤ (adaptiveN02701PlusP010Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN02701PlusP010Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN02701PlusP010Input2542]
  rw [adaptiveN02701PlusP010Owner2542]
  have h := compactExp_error2542 adaptiveN02701PlusP010Input2542 hz 16
  simpa only [adaptiveN02701PlusP010Compute2542] using h

theorem adaptiveN02701PlusP010Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ adaptiveN02701PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN02701PlusP010Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN02701PlusP010Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN02701PlusP011Output2542 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

def adaptiveN02701PlusP011Input2542 : RatPair2542 :=
  ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((617361885721254929729880619 : ℚ) /
        472236648286964521369600000000))

theorem adaptiveN02701PlusP011Compute2542 : compactExp2542 adaptiveN02701PlusP011Input2542 16 =
    adaptiveN02701PlusP011Output2542 := by
  cbv

theorem adaptiveN02701PlusP011Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ adaptiveN02701PlusPosition2542 =
    Complex.exp ((2 : ℂ)^16 * embedPair2542 adaptiveN02701PlusP011Input2542) := by
  have hx : |adaptiveN02701PlusPosition2542| < storedWidth ⟨11, by omega⟩ ^ 2 := by
    norm_num [adaptiveN02701PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN02701PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN02701PlusP011Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN02701PlusP011Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ adaptiveN02701PlusPosition2542 - embedPair2542
            adaptiveN02701PlusP011Output2542.1‖ ≤ (adaptiveN02701PlusP011Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN02701PlusP011Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN02701PlusP011Input2542]
  rw [adaptiveN02701PlusP011Owner2542]
  have h := compactExp_error2542 adaptiveN02701PlusP011Input2542 hz 16
  simpa only [adaptiveN02701PlusP011Compute2542] using h

theorem adaptiveN02701PlusP011Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ adaptiveN02701PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN02701PlusP011Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN02701PlusP011Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN02701PlusP012Output2542 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

def adaptiveN02701PlusP012Input2542 : RatPair2542 :=
  ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((13576393469632358173878271 : ℚ) /
        9444732965739290427392000000))

theorem adaptiveN02701PlusP012Compute2542 : compactExp2542 adaptiveN02701PlusP012Input2542 16 =
    adaptiveN02701PlusP012Output2542 := by
  cbv

theorem adaptiveN02701PlusP012Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ adaptiveN02701PlusPosition2542 =
    Complex.exp ((2 : ℂ)^16 * embedPair2542 adaptiveN02701PlusP012Input2542) := by
  have hx : |adaptiveN02701PlusPosition2542| < storedWidth ⟨12, by omega⟩ ^ 2 := by
    norm_num [adaptiveN02701PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN02701PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN02701PlusP012Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN02701PlusP012Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ adaptiveN02701PlusPosition2542 - embedPair2542
            adaptiveN02701PlusP012Output2542.1‖ ≤ (adaptiveN02701PlusP012Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN02701PlusP012Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN02701PlusP012Input2542]
  rw [adaptiveN02701PlusP012Owner2542]
  have h := compactExp_error2542 adaptiveN02701PlusP012Input2542 hz 16
  simpa only [adaptiveN02701PlusP012Compute2542] using h

theorem adaptiveN02701PlusP012Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ adaptiveN02701PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN02701PlusP012Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN02701PlusP012Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN02701PlusP013Output2542 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

def adaptiveN02701PlusP013Input2542 : RatPair2542 :=
  ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((146965053600227290725850929 : ℚ) /
        94447329657392904273920000000))

theorem adaptiveN02701PlusP013Compute2542 : compactExp2542 adaptiveN02701PlusP013Input2542 16 =
    adaptiveN02701PlusP013Output2542 := by
  cbv

theorem adaptiveN02701PlusP013Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ adaptiveN02701PlusPosition2542 =
    Complex.exp ((2 : ℂ)^16 * embedPair2542 adaptiveN02701PlusP013Input2542) := by
  have hx : |adaptiveN02701PlusPosition2542| < storedWidth ⟨13, by omega⟩ ^ 2 := by
    norm_num [adaptiveN02701PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN02701PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN02701PlusP013Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN02701PlusP013Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ adaptiveN02701PlusPosition2542 - embedPair2542
            adaptiveN02701PlusP013Output2542.1‖ ≤ (adaptiveN02701PlusP013Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN02701PlusP013Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN02701PlusP013Input2542]
  rw [adaptiveN02701PlusP013Owner2542]
  have h := compactExp_error2542 adaptiveN02701PlusP013Input2542 hz 16
  simpa only [adaptiveN02701PlusP013Compute2542] using h

theorem adaptiveN02701PlusP013Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ adaptiveN02701PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN02701PlusP013Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN02701PlusP013Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN02701PlusP014Output2542 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

def adaptiveN02701PlusP014Input2542 : RatPair2542 :=
  ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((838597898629083505249081609 : ℚ) /
        472236648286964521369600000000))

theorem adaptiveN02701PlusP014Compute2542 : compactExp2542 adaptiveN02701PlusP014Input2542 16 =
    adaptiveN02701PlusP014Output2542 := by
  cbv

theorem adaptiveN02701PlusP014Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ adaptiveN02701PlusPosition2542 =
    Complex.exp ((2 : ℂ)^16 * embedPair2542 adaptiveN02701PlusP014Input2542) := by
  have hx : |adaptiveN02701PlusPosition2542| < storedWidth ⟨14, by omega⟩ ^ 2 := by
    norm_num [adaptiveN02701PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN02701PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN02701PlusP014Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN02701PlusP014Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ adaptiveN02701PlusPosition2542 - embedPair2542
            adaptiveN02701PlusP014Output2542.1‖ ≤ (adaptiveN02701PlusP014Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN02701PlusP014Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN02701PlusP014Input2542]
  rw [adaptiveN02701PlusP014Owner2542]
  have h := compactExp_error2542 adaptiveN02701PlusP014Input2542 hz 16
  simpa only [adaptiveN02701PlusP014Compute2542] using h

theorem adaptiveN02701PlusP014Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ adaptiveN02701PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN02701PlusP014Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN02701PlusP014Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN02701PlusP015Output2542 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

def adaptiveN02701PlusP015Input2542 : RatPair2542 :=
  ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((912951341665564226630614693 : ℚ) /
        472236648286964521369600000000))

theorem adaptiveN02701PlusP015Compute2542 : compactExp2542 adaptiveN02701PlusP015Input2542 16 =
    adaptiveN02701PlusP015Output2542 := by
  cbv

theorem adaptiveN02701PlusP015Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ adaptiveN02701PlusPosition2542 =
    Complex.exp ((2 : ℂ)^16 * embedPair2542 adaptiveN02701PlusP015Input2542) := by
  have hx : |adaptiveN02701PlusPosition2542| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [adaptiveN02701PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN02701PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN02701PlusP015Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN02701PlusP015Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ adaptiveN02701PlusPosition2542 - embedPair2542
            adaptiveN02701PlusP015Output2542.1‖ ≤ (adaptiveN02701PlusP015Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN02701PlusP015Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN02701PlusP015Input2542]
  rw [adaptiveN02701PlusP015Owner2542]
  have h := compactExp_error2542 adaptiveN02701PlusP015Input2542 hz 16
  simpa only [adaptiveN02701PlusP015Compute2542] using h

theorem adaptiveN02701PlusP015Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ adaptiveN02701PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN02701PlusP015Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN02701PlusP015Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN02701PlusP016Output2542 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

def adaptiveN02701PlusP016Input2542 : RatPair2542 :=
  ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((483342473044070207188278171 : ℚ) /
        236118324143482260684800000000))

theorem adaptiveN02701PlusP016Compute2542 : compactExp2542 adaptiveN02701PlusP016Input2542 16 =
    adaptiveN02701PlusP016Output2542 := by
  cbv

theorem adaptiveN02701PlusP016Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ adaptiveN02701PlusPosition2542 =
    Complex.exp ((2 : ℂ)^16 * embedPair2542 adaptiveN02701PlusP016Input2542) := by
  have hx : |adaptiveN02701PlusPosition2542| < storedWidth ⟨16, by omega⟩ ^ 2 := by
    norm_num [adaptiveN02701PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN02701PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN02701PlusP016Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN02701PlusP016Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ adaptiveN02701PlusPosition2542 - embedPair2542
            adaptiveN02701PlusP016Output2542.1‖ ≤ (adaptiveN02701PlusP016Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN02701PlusP016Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN02701PlusP016Input2542]
  rw [adaptiveN02701PlusP016Owner2542]
  have h := compactExp_error2542 adaptiveN02701PlusP016Input2542 hz 16
  simpa only [adaptiveN02701PlusP016Compute2542] using h

theorem adaptiveN02701PlusP016Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ adaptiveN02701PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN02701PlusP016Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN02701PlusP016Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN02701PlusP017Output2542 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

def adaptiveN02701PlusP017Input2542 : RatPair2542 :=
  ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((1071059113331693339029979313 : ℚ) /
        472236648286964521369600000000))

theorem adaptiveN02701PlusP017Compute2542 : compactExp2542 adaptiveN02701PlusP017Input2542 16 =
    adaptiveN02701PlusP017Output2542 := by
  cbv

theorem adaptiveN02701PlusP017Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ adaptiveN02701PlusPosition2542 =
    Complex.exp ((2 : ℂ)^16 * embedPair2542 adaptiveN02701PlusP017Input2542) := by
  have hx : |adaptiveN02701PlusPosition2542| < storedWidth ⟨17, by omega⟩ ^ 2 := by
    norm_num [adaptiveN02701PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN02701PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN02701PlusP017Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN02701PlusP017Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ adaptiveN02701PlusPosition2542 - embedPair2542
            adaptiveN02701PlusP017Output2542.1‖ ≤ (adaptiveN02701PlusP017Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN02701PlusP017Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN02701PlusP017Input2542]
  rw [adaptiveN02701PlusP017Owner2542]
  have h := compactExp_error2542 adaptiveN02701PlusP017Input2542 hz 16
  simpa only [adaptiveN02701PlusP017Compute2542] using h

theorem adaptiveN02701PlusP017Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ adaptiveN02701PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN02701PlusP017Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN02701PlusP017Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN02701PlusP018Output2542 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

def adaptiveN02701PlusP018Input2542 : RatPair2542 :=
  ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((277630191250842385602313847 : ℚ) /
        118059162071741130342400000000))

theorem adaptiveN02701PlusP018Compute2542 : compactExp2542 adaptiveN02701PlusP018Input2542 16 =
    adaptiveN02701PlusP018Output2542 := by
  cbv

theorem adaptiveN02701PlusP018Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ adaptiveN02701PlusPosition2542 =
    Complex.exp ((2 : ℂ)^16 * embedPair2542 adaptiveN02701PlusP018Input2542) := by
  have hx : |adaptiveN02701PlusPosition2542| < storedWidth ⟨18, by omega⟩ ^ 2 := by
    norm_num [adaptiveN02701PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN02701PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN02701PlusP018Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN02701PlusP018Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ adaptiveN02701PlusPosition2542 - embedPair2542
            adaptiveN02701PlusP018Output2542.1‖ ≤ (adaptiveN02701PlusP018Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN02701PlusP018Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN02701PlusP018Input2542]
  rw [adaptiveN02701PlusP018Owner2542]
  have h := compactExp_error2542 adaptiveN02701PlusP018Input2542 hz 16
  simpa only [adaptiveN02701PlusP018Compute2542] using h

theorem adaptiveN02701PlusP018Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ adaptiveN02701PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN02701PlusP018Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN02701PlusP018Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN02701PlusP019Output2542 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

def adaptiveN02701PlusP019Input2542 : RatPair2542 :=
  ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((59091935462568230097122829 : ℚ) /
        23611832414348226068480000000))

theorem adaptiveN02701PlusP019Compute2542 : compactExp2542 adaptiveN02701PlusP019Input2542 16 =
    adaptiveN02701PlusP019Output2542 := by
  cbv

theorem adaptiveN02701PlusP019Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ adaptiveN02701PlusPosition2542 =
    Complex.exp ((2 : ℂ)^16 * embedPair2542 adaptiveN02701PlusP019Input2542) := by
  have hx : |adaptiveN02701PlusPosition2542| < storedWidth ⟨19, by omega⟩ ^ 2 := by
    norm_num [adaptiveN02701PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN02701PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN02701PlusP019Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN02701PlusP019Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ adaptiveN02701PlusPosition2542 - embedPair2542
            adaptiveN02701PlusP019Output2542.1‖ ≤ (adaptiveN02701PlusP019Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN02701PlusP019Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN02701PlusP019Input2542]
  rw [adaptiveN02701PlusP019Owner2542]
  have h := compactExp_error2542 adaptiveN02701PlusP019Input2542 hz 16
  simpa only [adaptiveN02701PlusP019Compute2542] using h

theorem adaptiveN02701PlusP019Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ adaptiveN02701PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN02701PlusP019Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN02701PlusP019Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN02701PlusP020Output2542 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

def adaptiveN02701PlusP020Input2542 : RatPair2542 :=
  ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((1259391271552815101014882561 : ℚ) /
        472236648286964521369600000000))

theorem adaptiveN02701PlusP020Compute2542 : compactExp2542 adaptiveN02701PlusP020Input2542 16 =
    adaptiveN02701PlusP020Output2542 := by
  cbv

theorem adaptiveN02701PlusP020Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ adaptiveN02701PlusPosition2542 =
    Complex.exp ((2 : ℂ)^16 * embedPair2542 adaptiveN02701PlusP020Input2542) := by
  have hx : |adaptiveN02701PlusPosition2542| < storedWidth ⟨20, by omega⟩ ^ 2 := by
    norm_num [adaptiveN02701PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN02701PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN02701PlusP020Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN02701PlusP020Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ adaptiveN02701PlusPosition2542 - embedPair2542
            adaptiveN02701PlusP020Output2542.1‖ ≤ (adaptiveN02701PlusP020Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN02701PlusP020Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN02701PlusP020Input2542]
  rw [adaptiveN02701PlusP020Owner2542]
  have h := compactExp_error2542 adaptiveN02701PlusP020Input2542 hz 16
  simpa only [adaptiveN02701PlusP020Compute2542] using h

theorem adaptiveN02701PlusP020Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ adaptiveN02701PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN02701PlusP020Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN02701PlusP020Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN02701PlusP021Output2542 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

def adaptiveN02701PlusP021Input2542 : RatPair2542 :=
  ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((1324111916357314294844085153 : ℚ) /
        472236648286964521369600000000))

theorem adaptiveN02701PlusP021Compute2542 : compactExp2542 adaptiveN02701PlusP021Input2542 16 =
    adaptiveN02701PlusP021Output2542 := by
  cbv

theorem adaptiveN02701PlusP021Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ adaptiveN02701PlusPosition2542 =
    Complex.exp ((2 : ℂ)^16 * embedPair2542 adaptiveN02701PlusP021Input2542) := by
  have hx : |adaptiveN02701PlusPosition2542| < storedWidth ⟨21, by omega⟩ ^ 2 := by
    norm_num [adaptiveN02701PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN02701PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN02701PlusP021Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN02701PlusP021Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ adaptiveN02701PlusPosition2542 - embedPair2542
            adaptiveN02701PlusP021Output2542.1‖ ≤ (adaptiveN02701PlusP021Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN02701PlusP021Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN02701PlusP021Input2542]
  rw [adaptiveN02701PlusP021Owner2542]
  have h := compactExp_error2542 adaptiveN02701PlusP021Input2542 hz 16
  simpa only [adaptiveN02701PlusP021Compute2542] using h

theorem adaptiveN02701PlusP021Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ adaptiveN02701PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN02701PlusP021Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN02701PlusP021Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN02701PlusP022Output2542 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

def adaptiveN02701PlusP022Input2542 : RatPair2542 :=
  ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((271447665815041436069447627 : ℚ) /
        94447329657392904273920000000))

theorem adaptiveN02701PlusP022Compute2542 : compactExp2542 adaptiveN02701PlusP022Input2542 16 =
    adaptiveN02701PlusP022Output2542 := by
  cbv

theorem adaptiveN02701PlusP022Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ adaptiveN02701PlusPosition2542 =
    Complex.exp ((2 : ℂ)^16 * embedPair2542 adaptiveN02701PlusP022Input2542) := by
  have hx : |adaptiveN02701PlusPosition2542| < storedWidth ⟨22, by omega⟩ ^ 2 := by
    norm_num [adaptiveN02701PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN02701PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN02701PlusP022Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN02701PlusP022Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ adaptiveN02701PlusPosition2542 - embedPair2542
            adaptiveN02701PlusP022Output2542.1‖ ≤ (adaptiveN02701PlusP022Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN02701PlusP022Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN02701PlusP022Input2542]
  rw [adaptiveN02701PlusP022Owner2542]
  have h := compactExp_error2542 adaptiveN02701PlusP022Input2542 hz 16
  simpa only [adaptiveN02701PlusP022Compute2542] using h

theorem adaptiveN02701PlusP022Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ adaptiveN02701PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN02701PlusP022Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN02701PlusP022Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN02701PlusP023Output2542 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

def adaptiveN02701PlusP023Input2542 : RatPair2542 :=
  ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((726373966280652557447321527 : ℚ) /
        236118324143482260684800000000))

theorem adaptiveN02701PlusP023Compute2542 : compactExp2542 adaptiveN02701PlusP023Input2542 16 =
    adaptiveN02701PlusP023Output2542 := by
  cbv

theorem adaptiveN02701PlusP023Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ adaptiveN02701PlusPosition2542 =
    Complex.exp ((2 : ℂ)^16 * embedPair2542 adaptiveN02701PlusP023Input2542) := by
  have hx : |adaptiveN02701PlusPosition2542| < storedWidth ⟨23, by omega⟩ ^ 2 := by
    norm_num [adaptiveN02701PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN02701PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN02701PlusP023Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN02701PlusP023Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ adaptiveN02701PlusPosition2542 - embedPair2542
            adaptiveN02701PlusP023Output2542.1‖ ≤ (adaptiveN02701PlusP023Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN02701PlusP023Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN02701PlusP023Input2542]
  rw [adaptiveN02701PlusP023Owner2542]
  have h := compactExp_error2542 adaptiveN02701PlusP023Input2542 hz 16
  simpa only [adaptiveN02701PlusP023Compute2542] using h

theorem adaptiveN02701PlusP023Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ adaptiveN02701PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN02701PlusP023Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN02701PlusP023Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN02701PlusP024Output2542 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

def adaptiveN02701PlusP024Input2542 : RatPair2542 :=
  ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((748320139291177557999687593 : ℚ) /
        236118324143482260684800000000))

theorem adaptiveN02701PlusP024Compute2542 : compactExp2542 adaptiveN02701PlusP024Input2542 16 =
    adaptiveN02701PlusP024Output2542 := by
  cbv

theorem adaptiveN02701PlusP024Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ adaptiveN02701PlusPosition2542 =
    Complex.exp ((2 : ℂ)^16 * embedPair2542 adaptiveN02701PlusP024Input2542) := by
  have hx : |adaptiveN02701PlusPosition2542| < storedWidth ⟨24, by omega⟩ ^ 2 := by
    norm_num [adaptiveN02701PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN02701PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN02701PlusP024Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN02701PlusP024Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ adaptiveN02701PlusPosition2542 - embedPair2542
            adaptiveN02701PlusP024Output2542.1‖ ≤ (adaptiveN02701PlusP024Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN02701PlusP024Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN02701PlusP024Input2542]
  rw [adaptiveN02701PlusP024Owner2542]
  have h := compactExp_error2542 adaptiveN02701PlusP024Input2542 hz 16
  simpa only [adaptiveN02701PlusP024Compute2542] using h

theorem adaptiveN02701PlusP024Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ adaptiveN02701PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN02701PlusP024Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN02701PlusP024Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN02701PlusP025Output2542 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

def adaptiveN02701PlusP025Input2542 : RatPair2542 :=
  ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((24244894162688885003625027 : ℚ) /
        7378697629483820646400000000))

theorem adaptiveN02701PlusP025Compute2542 : compactExp2542 adaptiveN02701PlusP025Input2542 16 =
    adaptiveN02701PlusP025Output2542 := by
  cbv

theorem adaptiveN02701PlusP025Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ adaptiveN02701PlusPosition2542 =
    Complex.exp ((2 : ℂ)^16 * embedPair2542 adaptiveN02701PlusP025Input2542) := by
  have hx : |adaptiveN02701PlusPosition2542| < storedWidth ⟨25, by omega⟩ ^ 2 := by
    norm_num [adaptiveN02701PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN02701PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN02701PlusP025Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN02701PlusP025Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ adaptiveN02701PlusPosition2542 - embedPair2542
            adaptiveN02701PlusP025Output2542.1‖ ≤ (adaptiveN02701PlusP025Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN02701PlusP025Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN02701PlusP025Input2542]
  rw [adaptiveN02701PlusP025Owner2542]
  have h := compactExp_error2542 adaptiveN02701PlusP025Input2542 hz 16
  simpa only [adaptiveN02701PlusP025Compute2542] using h

theorem adaptiveN02701PlusP025Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ adaptiveN02701PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN02701PlusP025Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN02701PlusP025Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN02701PlusP026Output2542 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

def adaptiveN02701PlusP026Input2542 : RatPair2542 :=
  ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((50247333217324293119390103 : ℚ) /
        14757395258967641292800000000))

theorem adaptiveN02701PlusP026Compute2542 : compactExp2542 adaptiveN02701PlusP026Input2542 16 =
    adaptiveN02701PlusP026Output2542 := by
  cbv

theorem adaptiveN02701PlusP026Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ adaptiveN02701PlusPosition2542 =
    Complex.exp ((2 : ℂ)^16 * embedPair2542 adaptiveN02701PlusP026Input2542) := by
  have hx : |adaptiveN02701PlusPosition2542| < storedWidth ⟨26, by omega⟩ ^ 2 := by
    norm_num [adaptiveN02701PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN02701PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN02701PlusP026Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN02701PlusP026Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ adaptiveN02701PlusPosition2542 - embedPair2542
            adaptiveN02701PlusP026Output2542.1‖ ≤ (adaptiveN02701PlusP026Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN02701PlusP026Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN02701PlusP026Input2542]
  rw [adaptiveN02701PlusP026Owner2542]
  have h := compactExp_error2542 adaptiveN02701PlusP026Input2542 hz 16
  simpa only [adaptiveN02701PlusP026Compute2542] using h

theorem adaptiveN02701PlusP026Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ adaptiveN02701PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN02701PlusP026Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN02701PlusP026Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN02701PlusP027Output2542 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

def adaptiveN02701PlusP027Input2542 : RatPair2542 :=
  ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((105567055574838531593598713 : ℚ) /
        29514790517935282585600000000))

theorem adaptiveN02701PlusP027Compute2542 : compactExp2542 adaptiveN02701PlusP027Input2542 16 =
    adaptiveN02701PlusP027Output2542 := by
  cbv

theorem adaptiveN02701PlusP027Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ adaptiveN02701PlusPosition2542 =
    Complex.exp ((2 : ℂ)^16 * embedPair2542 adaptiveN02701PlusP027Input2542) := by
  have hx : |adaptiveN02701PlusPosition2542| < storedWidth ⟨27, by omega⟩ ^ 2 := by
    norm_num [adaptiveN02701PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN02701PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN02701PlusP027Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN02701PlusP027Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ adaptiveN02701PlusPosition2542 - embedPair2542
            adaptiveN02701PlusP027Output2542.1‖ ≤ (adaptiveN02701PlusP027Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN02701PlusP027Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN02701PlusP027Input2542]
  rw [adaptiveN02701PlusP027Owner2542]
  have h := compactExp_error2542 adaptiveN02701PlusP027Input2542 hz 16
  simpa only [adaptiveN02701PlusP027Compute2542] using h

theorem adaptiveN02701PlusP027Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ adaptiveN02701PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN02701PlusP027Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN02701PlusP027Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN02701PlusP028Output2542 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

def adaptiveN02701PlusP028Input2542 : RatPair2542 :=
  ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((430301136886435135522330613 : ℚ) /
        118059162071741130342400000000))

theorem adaptiveN02701PlusP028Compute2542 : compactExp2542 adaptiveN02701PlusP028Input2542 16 =
    adaptiveN02701PlusP028Output2542 := by
  cbv

theorem adaptiveN02701PlusP028Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ adaptiveN02701PlusPosition2542 =
    Complex.exp ((2 : ℂ)^16 * embedPair2542 adaptiveN02701PlusP028Input2542) := by
  have hx : |adaptiveN02701PlusPosition2542| < storedWidth ⟨28, by omega⟩ ^ 2 := by
    norm_num [adaptiveN02701PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN02701PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN02701PlusP028Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN02701PlusP028Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ adaptiveN02701PlusPosition2542 - embedPair2542
            adaptiveN02701PlusP028Output2542.1‖ ≤ (adaptiveN02701PlusP028Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN02701PlusP028Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN02701PlusP028Input2542]
  rw [adaptiveN02701PlusP028Owner2542]
  have h := compactExp_error2542 adaptiveN02701PlusP028Input2542 hz 16
  simpa only [adaptiveN02701PlusP028Compute2542] using h

theorem adaptiveN02701PlusP028Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ adaptiveN02701PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN02701PlusP028Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN02701PlusP028Input2542, Complex.mul_re, Complex.mul_im]

def adaptiveN02701PlusP029Output2542 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)))

def adaptiveN02701PlusP029Input2542 : RatPair2542 :=
  ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((442530733595656525480647121 : ℚ) /
        118059162071741130342400000000))

theorem adaptiveN02701PlusP029Compute2542 : compactExp2542 adaptiveN02701PlusP029Input2542 16 =
    adaptiveN02701PlusP029Output2542 := by
  cbv

theorem adaptiveN02701PlusP029Owner2542 : weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ adaptiveN02701PlusPosition2542 =
    Complex.exp ((2 : ℂ)^16 * embedPair2542 adaptiveN02701PlusP029Input2542) := by
  have hx : |adaptiveN02701PlusPosition2542| < storedWidth ⟨29, by omega⟩ ^ 2 := by
    norm_num [adaptiveN02701PlusPosition2542, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  apply Complex.ext <;>
    norm_num [adaptiveN02701PlusPosition2542, storedWidth, nodeModulation2541, embedPair2542,
        adaptiveN02701PlusP029Input2542,
      Complex.mul_re, Complex.mul_im]

theorem adaptiveN02701PlusP029Error2542 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ adaptiveN02701PlusPosition2542 - embedPair2542
            adaptiveN02701PlusP029Output2542.1‖ ≤ (adaptiveN02701PlusP029Output2542.2 : ℝ) := by
  have hz : ‖embedPair2542 adaptiveN02701PlusP029Input2542‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, adaptiveN02701PlusP029Input2542]
  rw [adaptiveN02701PlusP029Owner2542]
  have h := compactExp_error2542 adaptiveN02701PlusP029Input2542 hz 16
  simpa only [adaptiveN02701PlusP029Compute2542] using h

theorem adaptiveN02701PlusP029Norm2542 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ adaptiveN02701PlusPosition2542‖ ≤ 1 := by
  rw [adaptiveN02701PlusP029Owner2542, Complex.norm_exp, Real.exp_le_one_iff]
  norm_num [embedPair2542, adaptiveN02701PlusP029Input2542, Complex.mul_re, Complex.mul_im]

noncomputable def adaptiveN02701PlusValue2542 (i : Fin 30) : ℂ :=
  match i.val with
  | 0 => embedPair2542 adaptiveN02701PlusP000Output2542.1
  | 1 => embedPair2542 adaptiveN02701PlusP001Output2542.1
  | 2 => embedPair2542 adaptiveN02701PlusP002Output2542.1
  | 3 => embedPair2542 adaptiveN02701PlusP003Output2542.1
  | 4 => embedPair2542 adaptiveN02701PlusP004Output2542.1
  | 5 => embedPair2542 adaptiveN02701PlusP005Output2542.1
  | 6 => embedPair2542 adaptiveN02701PlusP006Output2542.1
  | 7 => embedPair2542 adaptiveN02701PlusP007Output2542.1
  | 8 => embedPair2542 adaptiveN02701PlusP008Output2542.1
  | 9 => embedPair2542 adaptiveN02701PlusP009Output2542.1
  | 10 => embedPair2542 adaptiveN02701PlusP010Output2542.1
  | 11 => embedPair2542 adaptiveN02701PlusP011Output2542.1
  | 12 => embedPair2542 adaptiveN02701PlusP012Output2542.1
  | 13 => embedPair2542 adaptiveN02701PlusP013Output2542.1
  | 14 => embedPair2542 adaptiveN02701PlusP014Output2542.1
  | 15 => embedPair2542 adaptiveN02701PlusP015Output2542.1
  | 16 => embedPair2542 adaptiveN02701PlusP016Output2542.1
  | 17 => embedPair2542 adaptiveN02701PlusP017Output2542.1
  | 18 => embedPair2542 adaptiveN02701PlusP018Output2542.1
  | 19 => embedPair2542 adaptiveN02701PlusP019Output2542.1
  | 20 => embedPair2542 adaptiveN02701PlusP020Output2542.1
  | 21 => embedPair2542 adaptiveN02701PlusP021Output2542.1
  | 22 => embedPair2542 adaptiveN02701PlusP022Output2542.1
  | 23 => embedPair2542 adaptiveN02701PlusP023Output2542.1
  | 24 => embedPair2542 adaptiveN02701PlusP024Output2542.1
  | 25 => embedPair2542 adaptiveN02701PlusP025Output2542.1
  | 26 => embedPair2542 adaptiveN02701PlusP026Output2542.1
  | 27 => embedPair2542 adaptiveN02701PlusP027Output2542.1
  | 28 => embedPair2542 adaptiveN02701PlusP028Output2542.1
  | 29 => embedPair2542 adaptiveN02701PlusP029Output2542.1
  | _ => 0

noncomputable def adaptiveN02701PlusError2542 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => (adaptiveN02701PlusP000Output2542.2 : ℝ)
  | 1 => (adaptiveN02701PlusP001Output2542.2 : ℝ)
  | 2 => (adaptiveN02701PlusP002Output2542.2 : ℝ)
  | 3 => (adaptiveN02701PlusP003Output2542.2 : ℝ)
  | 4 => (adaptiveN02701PlusP004Output2542.2 : ℝ)
  | 5 => (adaptiveN02701PlusP005Output2542.2 : ℝ)
  | 6 => (adaptiveN02701PlusP006Output2542.2 : ℝ)
  | 7 => (adaptiveN02701PlusP007Output2542.2 : ℝ)
  | 8 => (adaptiveN02701PlusP008Output2542.2 : ℝ)
  | 9 => (adaptiveN02701PlusP009Output2542.2 : ℝ)
  | 10 => (adaptiveN02701PlusP010Output2542.2 : ℝ)
  | 11 => (adaptiveN02701PlusP011Output2542.2 : ℝ)
  | 12 => (adaptiveN02701PlusP012Output2542.2 : ℝ)
  | 13 => (adaptiveN02701PlusP013Output2542.2 : ℝ)
  | 14 => (adaptiveN02701PlusP014Output2542.2 : ℝ)
  | 15 => (adaptiveN02701PlusP015Output2542.2 : ℝ)
  | 16 => (adaptiveN02701PlusP016Output2542.2 : ℝ)
  | 17 => (adaptiveN02701PlusP017Output2542.2 : ℝ)
  | 18 => (adaptiveN02701PlusP018Output2542.2 : ℝ)
  | 19 => (adaptiveN02701PlusP019Output2542.2 : ℝ)
  | 20 => (adaptiveN02701PlusP020Output2542.2 : ℝ)
  | 21 => (adaptiveN02701PlusP021Output2542.2 : ℝ)
  | 22 => (adaptiveN02701PlusP022Output2542.2 : ℝ)
  | 23 => (adaptiveN02701PlusP023Output2542.2 : ℝ)
  | 24 => (adaptiveN02701PlusP024Output2542.2 : ℝ)
  | 25 => (adaptiveN02701PlusP025Output2542.2 : ℝ)
  | 26 => (adaptiveN02701PlusP026Output2542.2 : ℝ)
  | 27 => (adaptiveN02701PlusP027Output2542.2 : ℝ)
  | 28 => (adaptiveN02701PlusP028Output2542.2 : ℝ)
  | 29 => (adaptiveN02701PlusP029Output2542.2 : ℝ)
  | _ => 0

theorem adaptiveN02701PlusExp_error2542 (i : Fin 30) :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 i adaptiveN02701PlusPosition2542 - adaptiveN02701PlusValue2542 i‖ ≤
            adaptiveN02701PlusError2542 i := by
  fin_cases i
  · simpa only [adaptiveN02701PlusValue2542, adaptiveN02701PlusError2542] using
      adaptiveN02701PlusP000Error2542
  · simpa only [adaptiveN02701PlusValue2542, adaptiveN02701PlusError2542] using
      adaptiveN02701PlusP001Error2542
  · simpa only [adaptiveN02701PlusValue2542, adaptiveN02701PlusError2542] using
      adaptiveN02701PlusP002Error2542
  · simpa only [adaptiveN02701PlusValue2542, adaptiveN02701PlusError2542] using
      adaptiveN02701PlusP003Error2542
  · simpa only [adaptiveN02701PlusValue2542, adaptiveN02701PlusError2542] using
      adaptiveN02701PlusP004Error2542
  · simpa only [adaptiveN02701PlusValue2542, adaptiveN02701PlusError2542] using
      adaptiveN02701PlusP005Error2542
  · simpa only [adaptiveN02701PlusValue2542, adaptiveN02701PlusError2542] using
      adaptiveN02701PlusP006Error2542
  · simpa only [adaptiveN02701PlusValue2542, adaptiveN02701PlusError2542] using
      adaptiveN02701PlusP007Error2542
  · simpa only [adaptiveN02701PlusValue2542, adaptiveN02701PlusError2542] using
      adaptiveN02701PlusP008Error2542
  · simpa only [adaptiveN02701PlusValue2542, adaptiveN02701PlusError2542] using
      adaptiveN02701PlusP009Error2542
  · simpa only [adaptiveN02701PlusValue2542, adaptiveN02701PlusError2542] using
      adaptiveN02701PlusP010Error2542
  · simpa only [adaptiveN02701PlusValue2542, adaptiveN02701PlusError2542] using
      adaptiveN02701PlusP011Error2542
  · simpa only [adaptiveN02701PlusValue2542, adaptiveN02701PlusError2542] using
      adaptiveN02701PlusP012Error2542
  · simpa only [adaptiveN02701PlusValue2542, adaptiveN02701PlusError2542] using
      adaptiveN02701PlusP013Error2542
  · simpa only [adaptiveN02701PlusValue2542, adaptiveN02701PlusError2542] using
      adaptiveN02701PlusP014Error2542
  · simpa only [adaptiveN02701PlusValue2542, adaptiveN02701PlusError2542] using
      adaptiveN02701PlusP015Error2542
  · simpa only [adaptiveN02701PlusValue2542, adaptiveN02701PlusError2542] using
      adaptiveN02701PlusP016Error2542
  · simpa only [adaptiveN02701PlusValue2542, adaptiveN02701PlusError2542] using
      adaptiveN02701PlusP017Error2542
  · simpa only [adaptiveN02701PlusValue2542, adaptiveN02701PlusError2542] using
      adaptiveN02701PlusP018Error2542
  · simpa only [adaptiveN02701PlusValue2542, adaptiveN02701PlusError2542] using
      adaptiveN02701PlusP019Error2542
  · simpa only [adaptiveN02701PlusValue2542, adaptiveN02701PlusError2542] using
      adaptiveN02701PlusP020Error2542
  · simpa only [adaptiveN02701PlusValue2542, adaptiveN02701PlusError2542] using
      adaptiveN02701PlusP021Error2542
  · simpa only [adaptiveN02701PlusValue2542, adaptiveN02701PlusError2542] using
      adaptiveN02701PlusP022Error2542
  · simpa only [adaptiveN02701PlusValue2542, adaptiveN02701PlusError2542] using
      adaptiveN02701PlusP023Error2542
  · simpa only [adaptiveN02701PlusValue2542, adaptiveN02701PlusError2542] using
      adaptiveN02701PlusP024Error2542
  · simpa only [adaptiveN02701PlusValue2542, adaptiveN02701PlusError2542] using
      adaptiveN02701PlusP025Error2542
  · simpa only [adaptiveN02701PlusValue2542, adaptiveN02701PlusError2542] using
      adaptiveN02701PlusP026Error2542
  · simpa only [adaptiveN02701PlusValue2542, adaptiveN02701PlusError2542] using
      adaptiveN02701PlusP027Error2542
  · simpa only [adaptiveN02701PlusValue2542, adaptiveN02701PlusError2542] using
      adaptiveN02701PlusP028Error2542
  · simpa only [adaptiveN02701PlusValue2542, adaptiveN02701PlusError2542] using
      adaptiveN02701PlusP029Error2542

theorem adaptiveN02701PlusUnit_norm2542 (i : Fin 30) :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 i adaptiveN02701PlusPosition2542‖ ≤ 1 := by
  fin_cases i
  · simpa only [adaptiveN02701PlusValue2542, adaptiveN02701PlusError2542] using
      adaptiveN02701PlusP000Norm2542
  · simpa only [adaptiveN02701PlusValue2542, adaptiveN02701PlusError2542] using
      adaptiveN02701PlusP001Norm2542
  · simpa only [adaptiveN02701PlusValue2542, adaptiveN02701PlusError2542] using
      adaptiveN02701PlusP002Norm2542
  · simpa only [adaptiveN02701PlusValue2542, adaptiveN02701PlusError2542] using
      adaptiveN02701PlusP003Norm2542
  · simpa only [adaptiveN02701PlusValue2542, adaptiveN02701PlusError2542] using
      adaptiveN02701PlusP004Norm2542
  · simpa only [adaptiveN02701PlusValue2542, adaptiveN02701PlusError2542] using
      adaptiveN02701PlusP005Norm2542
  · simpa only [adaptiveN02701PlusValue2542, adaptiveN02701PlusError2542] using
      adaptiveN02701PlusP006Norm2542
  · simpa only [adaptiveN02701PlusValue2542, adaptiveN02701PlusError2542] using
      adaptiveN02701PlusP007Norm2542
  · simpa only [adaptiveN02701PlusValue2542, adaptiveN02701PlusError2542] using
      adaptiveN02701PlusP008Norm2542
  · simpa only [adaptiveN02701PlusValue2542, adaptiveN02701PlusError2542] using
      adaptiveN02701PlusP009Norm2542
  · simpa only [adaptiveN02701PlusValue2542, adaptiveN02701PlusError2542] using
      adaptiveN02701PlusP010Norm2542
  · simpa only [adaptiveN02701PlusValue2542, adaptiveN02701PlusError2542] using
      adaptiveN02701PlusP011Norm2542
  · simpa only [adaptiveN02701PlusValue2542, adaptiveN02701PlusError2542] using
      adaptiveN02701PlusP012Norm2542
  · simpa only [adaptiveN02701PlusValue2542, adaptiveN02701PlusError2542] using
      adaptiveN02701PlusP013Norm2542
  · simpa only [adaptiveN02701PlusValue2542, adaptiveN02701PlusError2542] using
      adaptiveN02701PlusP014Norm2542
  · simpa only [adaptiveN02701PlusValue2542, adaptiveN02701PlusError2542] using
      adaptiveN02701PlusP015Norm2542
  · simpa only [adaptiveN02701PlusValue2542, adaptiveN02701PlusError2542] using
      adaptiveN02701PlusP016Norm2542
  · simpa only [adaptiveN02701PlusValue2542, adaptiveN02701PlusError2542] using
      adaptiveN02701PlusP017Norm2542
  · simpa only [adaptiveN02701PlusValue2542, adaptiveN02701PlusError2542] using
      adaptiveN02701PlusP018Norm2542
  · simpa only [adaptiveN02701PlusValue2542, adaptiveN02701PlusError2542] using
      adaptiveN02701PlusP019Norm2542
  · simpa only [adaptiveN02701PlusValue2542, adaptiveN02701PlusError2542] using
      adaptiveN02701PlusP020Norm2542
  · simpa only [adaptiveN02701PlusValue2542, adaptiveN02701PlusError2542] using
      adaptiveN02701PlusP021Norm2542
  · simpa only [adaptiveN02701PlusValue2542, adaptiveN02701PlusError2542] using
      adaptiveN02701PlusP022Norm2542
  · simpa only [adaptiveN02701PlusValue2542, adaptiveN02701PlusError2542] using
      adaptiveN02701PlusP023Norm2542
  · simpa only [adaptiveN02701PlusValue2542, adaptiveN02701PlusError2542] using
      adaptiveN02701PlusP024Norm2542
  · simpa only [adaptiveN02701PlusValue2542, adaptiveN02701PlusError2542] using
      adaptiveN02701PlusP025Norm2542
  · simpa only [adaptiveN02701PlusValue2542, adaptiveN02701PlusError2542] using
      adaptiveN02701PlusP026Norm2542
  · simpa only [adaptiveN02701PlusValue2542, adaptiveN02701PlusError2542] using
      adaptiveN02701PlusP027Norm2542
  · simpa only [adaptiveN02701PlusValue2542, adaptiveN02701PlusError2542] using
      adaptiveN02701PlusP028Norm2542
  · simpa only [adaptiveN02701PlusValue2542, adaptiveN02701PlusError2542] using
      adaptiveN02701PlusP029Norm2542

noncomputable def adaptiveN02701PlusSumValue2542 : ℂ := ⟨(((((3 * 10^40
        + 4907321164271010595575771380791682059090) * 10^40
        + 3964178652798278352697658540498183731563) * 10^40
        + 9735522191408160291618558656221150437757) : ℝ) /
        (((43322963 * 10^40
        + 9706377321809127216272356828661943293027) * 10^40
        + 4713398703874344710345793446290035999960) * 10^40
        + 95377180907771737671271930809827721216)),
    ((((3594774251491775704324483554813776035418 * 10^40
        + 2511676801188337635466716338550470541876) * 10^40
        + 8677282898205925831514578245683984849535) : ℝ) /
        (((10830740 * 10^40
        + 9926594330452281804068089207165485823256) * 10^40
        + 8678349675968586177586448361572508999990) * 10^40
        + 23844295226942934417817982702456930304))⟩

noncomputable def adaptiveN02701PlusUpper2542 : ℝ := ((873 : ℝ) /
        10000000000)

theorem adaptiveN02701PlusSum_eq2542 :
    (∑ i : Fin 30, baseCoefficientCenter2540 i * adaptiveN02701PlusValue2542 i) =
      adaptiveN02701PlusSumValue2542 := by
  rw [sum30_chain2541]
  apply Complex.ext <;>
    norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, adaptiveN02701PlusValue2542,
      adaptiveN02701PlusSumValue2542, embedPair2542, adaptiveN02701PlusP000Output2542,
      adaptiveN02701PlusP001Output2542,
      adaptiveN02701PlusP002Output2542,
      adaptiveN02701PlusP003Output2542,
      adaptiveN02701PlusP004Output2542,
      adaptiveN02701PlusP005Output2542,
      adaptiveN02701PlusP006Output2542,
      adaptiveN02701PlusP007Output2542,
      adaptiveN02701PlusP008Output2542,
      adaptiveN02701PlusP009Output2542,
      adaptiveN02701PlusP010Output2542,
      adaptiveN02701PlusP011Output2542,
      adaptiveN02701PlusP012Output2542,
      adaptiveN02701PlusP013Output2542,
      adaptiveN02701PlusP014Output2542,
      adaptiveN02701PlusP015Output2542,
      adaptiveN02701PlusP016Output2542,
      adaptiveN02701PlusP017Output2542,
      adaptiveN02701PlusP018Output2542,
      adaptiveN02701PlusP019Output2542,
      adaptiveN02701PlusP020Output2542,
      adaptiveN02701PlusP021Output2542,
      adaptiveN02701PlusP022Output2542,
      adaptiveN02701PlusP023Output2542,
      adaptiveN02701PlusP024Output2542,
      adaptiveN02701PlusP025Output2542,
      adaptiveN02701PlusP026Output2542,
      adaptiveN02701PlusP027Output2542,
      adaptiveN02701PlusP028Output2542,
      adaptiveN02701PlusP029Output2542, Complex.mul_re, Complex.mul_im]

theorem adaptiveN02701PlusSum_norm2542 :
    ‖∑ i : Fin 30, baseCoefficientCenter2540 i * adaptiveN02701PlusValue2542 i‖ ≤
      ((109 : ℝ) /
        1250000000) := by
  rw [adaptiveN02701PlusSum_eq2542]
  apply complex_norm_le_of_sq2541 _ _ (by norm_num)
  norm_num [adaptiveN02701PlusSumValue2542]

theorem adaptiveN02701PlusEvaluation_charge2542 :
    (∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
      |(baseCoefficientCenter2540 i).im|) * adaptiveN02701PlusError2542 i) ≤ (1 : ℝ)/10^12 := by
  rw [sum30_chain2541]
  norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, adaptiveN02701PlusError2542,
      adaptiveN02701PlusP000Output2542,
      adaptiveN02701PlusP001Output2542,
      adaptiveN02701PlusP002Output2542,
      adaptiveN02701PlusP003Output2542,
      adaptiveN02701PlusP004Output2542,
      adaptiveN02701PlusP005Output2542,
      adaptiveN02701PlusP006Output2542,
      adaptiveN02701PlusP007Output2542,
      adaptiveN02701PlusP008Output2542,
      adaptiveN02701PlusP009Output2542,
      adaptiveN02701PlusP010Output2542,
      adaptiveN02701PlusP011Output2542,
      adaptiveN02701PlusP012Output2542,
      adaptiveN02701PlusP013Output2542,
      adaptiveN02701PlusP014Output2542,
      adaptiveN02701PlusP015Output2542,
      adaptiveN02701PlusP016Output2542,
      adaptiveN02701PlusP017Output2542,
      adaptiveN02701PlusP018Output2542,
      adaptiveN02701PlusP019Output2542,
      adaptiveN02701PlusP020Output2542,
      adaptiveN02701PlusP021Output2542,
      adaptiveN02701PlusP022Output2542,
      adaptiveN02701PlusP023Output2542,
      adaptiveN02701PlusP024Output2542,
      adaptiveN02701PlusP025Output2542,
      adaptiveN02701PlusP026Output2542,
      adaptiveN02701PlusP027Output2542,
      adaptiveN02701PlusP028Output2542,
      adaptiveN02701PlusP029Output2542]

theorem adaptiveN02701PlusSigned_le2542 :
    signedJetUpper2539 0 (((1 : ℝ) /
        2)) baseCoefficientCenter2540 baseCoefficientError2540
      nodeModulation2541 adaptiveN02701PlusPosition2542 ≤ adaptiveN02701PlusUpper2542 := by
  have hsum :
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i *
        weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 i adaptiveN02701PlusPosition2542‖ ≤
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i * adaptiveN02701PlusValue2542 i‖ +
        ∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
          |(baseCoefficientCenter2540 i).im|) * adaptiveN02701PlusError2542 i := by
    apply norm_sum_le_center_sum_add_error2531
    intro i _
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (Complex.norm_le_abs_re_add_abs_im _) (adaptiveN02701PlusExp_error2542 i)
      (norm_nonneg _) (by positivity)
  have heach : ∀ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 i adaptiveN02701PlusPosition2542‖ ≤
        (1 : ℝ)/10^30 := by
    intro i
    have h := mul_le_mul_of_nonneg_left (adaptiveN02701PlusUnit_norm2542 i)
      (by norm_num [baseCoefficientError2540] : 0 ≤ baseCoefficientError2540 i)
    simpa [baseCoefficientError2540] using h
  have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
  have he' : (∑ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 i adaptiveN02701PlusPosition2542‖) ≤
        (30 : ℝ)/10^30 := by simpa using he
  unfold signedJetUpper2539 adaptiveN02701PlusUpper2542
  linarith [adaptiveN02701PlusSum_norm2542, adaptiveN02701PlusEvaluation_charge2542]

theorem adaptiveN02701PlusPhysical_le2542 (coefficients : Fin 30 → ℂ)
    (hbox : ∀ i, (baseCoefficientBox2540 i).Mem (coefficients i)) :
    ‖weightedPhysical2539 (((1 : ℝ) /
        2)) coefficients nodeModulation2541 adaptiveN02701PlusPosition2542‖ ≤
      adaptiveN02701PlusUpper2542 := by
  have h := weightedPhysical2539_jet_le_center_error 0 (((1 : ℝ) /
        2)) coefficients
    baseCoefficientCenter2540 baseCoefficientError2540 nodeModulation2541
    (fun i => baseCoefficient_error_of_box2540 i (coefficients i) (hbox i))
        adaptiveN02701PlusPosition2542
  simpa only [iteratedDeriv_zero] using h.trans adaptiveN02701PlusSigned_le2542

theorem adaptiveN02701PlusGrid2542 :
    -stripRadius2303 + (2701 : ℝ)*(2*stripRadius2303/10240) = adaptiveN02701PlusPosition2542 := by
  norm_num [stripRadius2303, adaptiveN02701PlusPosition2542]

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.adaptiveN02701PlusSigned_le2542
#print axioms ConnesWeilRH.Dev.adaptiveN02701PlusPhysical_le2542
