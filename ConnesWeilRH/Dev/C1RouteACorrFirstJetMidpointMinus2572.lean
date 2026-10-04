import ConnesWeilRH.Dev.C1RouteACompactExp1602547
import ConnesWeilRH.Dev.C1RouteADerivativeMultiplier2543
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541
import ConnesWeilRH.Dev.C1RouteACorrMidpointBounds2701Minus2572
import ConnesWeilRH.Dev.C1RouteACorrectionCoefficientBoxes2570
import ConnesWeilRH.Dev.C1RouteACorrectionCenterNode2570

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

theorem firstJetCorrMinus_triangle2572 (a b c : ℂ) : ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖ := by
  calc
    ‖a - c‖ = ‖(a - b) + (b - c)‖ := by congr 1; ring
    _ ≤ _ := norm_add_le _ _

theorem fjcmZero2572 : embedPair2542 (0, 0) = 0 := by
  apply Complex.ext <;> norm_num [embedPair2542]

def fjcmP000Center2572 : RatPair2542 := (0, 0)

def fjcmP000Factor2572 : RatPair2542 := (0, 0)

noncomputable def fjcmP000Error2572 : ℝ := 0

theorem fjcmP000Exterior2572 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨0, by omega⟩
      corrC02701MinusMidpointPosition2572 = 0 := by
  have hx : storedWidth ⟨0, by omega⟩ ^ 2 ≤ |corrC02701MinusMidpointPosition2572| := by
    norm_num [storedWidth, corrC02701MinusMidpointPosition2572]
  exact weightedFamily_outside_zero2543 n (-1/2)
    (nodeModulation2541 ⟨0, by omega⟩)
    (pow_pos (storedWidth_pos ⟨0, by omega⟩) 2) hx

theorem fjcmP000BaseError2572 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨0, by omega⟩
      corrC02701MinusMidpointPosition2572 - embedPair2542 fjcmP000Center2572‖ ≤ fjcmP000Error2572
          := by
  rw [fjcmP000Exterior2572]
  norm_num [fjcmP000Center2572, fjcmP000Error2572, fjcmZero2572]

theorem fjcmP000DerivativeError2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨0, by omega⟩
      corrC02701MinusMidpointPosition2572 -
      embedPair2542 fjcmP000Factor2572 * embedPair2542 fjcmP000Center2572‖ ≤
        (pairMagnitude2542 fjcmP000Factor2572 : ℝ) * fjcmP000Error2572 := by
  rw [fjcmP000Exterior2572]
  norm_num [fjcmP000Factor2572, fjcmP000Center2572, fjcmP000Error2572, pairMagnitude2542,
      fjcmZero2572]

def fjcmP000Rounded2572 : RatPair2542 := (0, 0)

noncomputable def fjcmP000Radius2572 : ℝ := 0

theorem fjcmP000RoundCompute2572 :
    pairRound2542 (pairMul2542 fjcmP000Factor2572 fjcmP000Center2572) = fjcmP000Rounded2572 := by
  cbv

theorem fjcmP000RoundedError2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨0, by omega⟩
      corrC02701MinusMidpointPosition2572 - embedPair2542 fjcmP000Rounded2572‖ ≤
          fjcmP000Radius2572 := by
  rw [fjcmP000Exterior2572]
  norm_num [fjcmP000Rounded2572, fjcmP000Radius2572, fjcmZero2572]

theorem fjcmP000DerivativeNorm2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨0, by omega⟩
      corrC02701MinusMidpointPosition2572‖ ≤ 1 := by
  rw [fjcmP000Exterior2572]
  norm_num

noncomputable def fjcmP001Input2572 : RatPair2542 := ((((-((668 * 10^40
        + 8254807723076288264152476722223017963933) * 10^40
        + 5477557306256771509133844063953846090683)) : ℚ) /
        ((1887 * 10^40
        + 2004981127838775906823533063469056624951) * 10^40
        + 8551390361977395865728009214361600000000)),
    ((1751187200352461984105434273 : ℚ) /
        7378697629483820646400000000))

def fjcmP001Center2572 : RatPair2542 := ((((-1) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def fjcmP001Factor2572 : RatPair2542 := ((((((3903074178866463970116 * 10^40
        + 494228160867265181625928195569744545081) * 10^40
        + 7217159877690898072678728215490204216683) * 10^40
        + 9286974124956906064265068507388575584319) : ℚ) /
        (((6478377545276343123 * 10^40
        + 8485895986441204058168162300927097868968) * 10^40
        + 3254352661281389773706632614815033590864) * 10^40
        + 4792987927627307871469862985222848831362)),
    (((-5524291025718029) : ℚ) /
        140737488355328))

noncomputable def fjcmP001Error2572 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjcmP001BaseError2572 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨1, by omega⟩
      corrC02701MinusMidpointPosition2572 - embedPair2542 fjcmP001Center2572‖ ≤ fjcmP001Error2572
          := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hz : ‖embedPair2542 fjcmP001Input2572‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjcmP001Input2572]
  have hc : (compactExp2547 fjcmP001Input2572 9).1 = fjcmP001Center2572 := by cbv
  have he : ((compactExp2547 fjcmP001Input2572 9).2 : ℝ) = fjcmP001Error2572 := by
    have hq : (compactExp2547 fjcmP001Input2572 9).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjcmP001Error2572]
  have h := compactExp_error2547 fjcmP001Input2572 hz 9
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨1, by omega⟩
      corrC02701MinusMidpointPosition2572 = Complex.exp ((2 : ℂ)^9 * embedPair2542
          fjcmP001Input2572) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrC02701MinusMidpointPosition2572, storedWidth,
      nodeModulation2541, embedPair2542, fjcmP001Input2572, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjcmP001DerivativeError2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨1, by omega⟩
      corrC02701MinusMidpointPosition2572 -
      embedPair2542 fjcmP001Factor2572 * embedPair2542 fjcmP001Center2572‖ ≤
        (pairMagnitude2542 fjcmP001Factor2572 : ℝ) * fjcmP001Error2572 := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hf : weightedMultiplier2543 1 (-1/2)
      (nodeModulation2541 ⟨1, by omega⟩)
      (storedWidth ⟨1, by omega⟩ ^ 2) corrC02701MinusMidpointPosition2572 =
      embedPair2542 fjcmP001Factor2572 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrC02701MinusMidpointPosition2572, storedWidth, nodeModulation2541, embedPair2542,
      fjcmP001Factor2572, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (-1/2)
    (nodeModulation2541 ⟨1, by omega⟩) (pow_pos (storedWidth_pos ⟨1, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjcmP001BaseError2572
    (embedPair_magnitude2542 fjcmP001Factor2572)

def fjcmP001Rounded2572 : RatPair2542 :=
  ((((-1) : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def fjcmP001Radius2572 : ℝ := ((2199023255553 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjcmP001RoundCompute2572 :
    pairRound2542 (pairMul2542 fjcmP001Factor2572 fjcmP001Center2572) = fjcmP001Rounded2572 := by
  cbv

theorem fjcmP001RoundedError2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨1, by omega⟩
      corrC02701MinusMidpointPosition2572 - embedPair2542 fjcmP001Rounded2572‖ ≤
          fjcmP001Radius2572 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjcmP001Factor2572 fjcmP001Center2572)
  rw [fjcmP001RoundCompute2572, embedPair_mul2542] at hr
  have h := (firstJetCorrMinus_triangle2572
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨1, by omega⟩
      corrC02701MinusMidpointPosition2572)
    (embedPair2542 fjcmP001Factor2572 * embedPair2542 fjcmP001Center2572)
    (embedPair2542 fjcmP001Rounded2572)).trans (add_le_add fjcmP001DerivativeError2572 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjcmP001Factor2572, fjcmP001Error2572, rounding2542,
      fjcmP001Radius2572]

theorem fjcmP001DerivativeNorm2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨1, by omega⟩
      corrC02701MinusMidpointPosition2572‖ ≤ 1 := by
  have h := firstJetCorrMinus_triangle2572
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨1, by omega⟩
      corrC02701MinusMidpointPosition2572)
    (embedPair2542 fjcmP001Rounded2572) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjcmP001RoundedError2572 (embedPair_magnitude2542
      fjcmP001Rounded2572))
  apply h'.trans
  norm_num [fjcmP001Radius2572, pairMagnitude2542, fjcmP001Rounded2572]

noncomputable def fjcmP002Input2572 : RatPair2542 := ((((-((350 * 10^40
        + 6167159465445660897322667704655111564849) * 10^40
        + 7899260685951668685791997936374732229547)) : ℚ) /
        ((1497 * 10^40
        + 8141619820548260689071119881802050250108) * 10^40
        + 126749615182671161751511708467200000000)),
    (((-1751187200352461984105434273) : ℚ) /
        3689348814741910323200000000))

def fjcmP002Center2572 : RatPair2542 := ((((-7340606510045565236433) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-5832109500717769467319) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)))

def fjcmP002Factor2572 : RatPair2542 := ((((((671976218636209858518 * 10^40
        + 64980523736610905007224314425038565412) * 10^40
        + 4635664528527358433616170540282145798720) * 10^40
        + 6694744656238919402295920007467882241439) : ℚ) /
        (((16323227201312003109 * 10^40
        + 2929548297561250449861611946859862272662) * 10^40
        + 2019364707157271596877517213649746322568) * 10^40
        + 2343001276173681195408159985064235517122)),
    ((5524291025718029 : ℚ) /
        140737488355328))

noncomputable def fjcmP002Error2572 : ℝ := ((6359855276339487927 : ℝ) /
        (20086725553237378444 * 10^40
        + 2745261542645325315275374222849104412672))

theorem fjcmP002BaseError2572 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨2, by omega⟩
      corrC02701MinusMidpointPosition2572 - embedPair2542 fjcmP002Center2572‖ ≤ fjcmP002Error2572
          := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hz : ‖embedPair2542 fjcmP002Input2572‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjcmP002Input2572]
  have hc : (compactExp2547 fjcmP002Input2572 8).1 = fjcmP002Center2572 := by cbv
  have he : ((compactExp2547 fjcmP002Input2572 8).2 : ℝ) = fjcmP002Error2572 := by
    have hq : (compactExp2547 fjcmP002Input2572 8).2 =
        ((6359855276339487927 : ℚ) /
        (20086725553237378444 * 10^40
        + 2745261542645325315275374222849104412672)) := by cbv
    rw [hq]
    norm_num [fjcmP002Error2572]
  have h := compactExp_error2547 fjcmP002Input2572 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨2, by omega⟩
      corrC02701MinusMidpointPosition2572 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          fjcmP002Input2572) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrC02701MinusMidpointPosition2572, storedWidth,
      nodeModulation2541, embedPair2542, fjcmP002Input2572, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjcmP002DerivativeError2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨2, by omega⟩
      corrC02701MinusMidpointPosition2572 -
      embedPair2542 fjcmP002Factor2572 * embedPair2542 fjcmP002Center2572‖ ≤
        (pairMagnitude2542 fjcmP002Factor2572 : ℝ) * fjcmP002Error2572 := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hf : weightedMultiplier2543 1 (-1/2)
      (nodeModulation2541 ⟨2, by omega⟩)
      (storedWidth ⟨2, by omega⟩ ^ 2) corrC02701MinusMidpointPosition2572 =
      embedPair2542 fjcmP002Factor2572 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrC02701MinusMidpointPosition2572, storedWidth, nodeModulation2541, embedPair2542,
      fjcmP002Factor2572, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (-1/2)
    (nodeModulation2541 ⟨2, by omega⟩) (pow_pos (storedWidth_pos ⟨2, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjcmP002BaseError2572
    (embedPair_magnitude2542 fjcmP002Factor2572)

def fjcmP002Rounded2572 : RatPair2542 :=
  (((33753 : ℚ) /
        316912650057057350374175801344),
    (((-666409) : ℚ) /
        1267650600228229401496703205376))

noncomputable def fjcmP002Radius2572 : ℝ := ((2199023259101 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjcmP002RoundCompute2572 :
    pairRound2542 (pairMul2542 fjcmP002Factor2572 fjcmP002Center2572) = fjcmP002Rounded2572 := by
  cbv

theorem fjcmP002RoundedError2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨2, by omega⟩
      corrC02701MinusMidpointPosition2572 - embedPair2542 fjcmP002Rounded2572‖ ≤
          fjcmP002Radius2572 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjcmP002Factor2572 fjcmP002Center2572)
  rw [fjcmP002RoundCompute2572, embedPair_mul2542] at hr
  have h := (firstJetCorrMinus_triangle2572
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨2, by omega⟩
      corrC02701MinusMidpointPosition2572)
    (embedPair2542 fjcmP002Factor2572 * embedPair2542 fjcmP002Center2572)
    (embedPair2542 fjcmP002Rounded2572)).trans (add_le_add fjcmP002DerivativeError2572 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjcmP002Factor2572, fjcmP002Error2572, rounding2542,
      fjcmP002Radius2572]

theorem fjcmP002DerivativeNorm2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨2, by omega⟩
      corrC02701MinusMidpointPosition2572‖ ≤ 1 := by
  have h := firstJetCorrMinus_triangle2572
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨2, by omega⟩
      corrC02701MinusMidpointPosition2572)
    (embedPair2542 fjcmP002Rounded2572) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjcmP002RoundedError2572 (embedPair_magnitude2542
      fjcmP002Rounded2572))
  apply h'.trans
  norm_num [fjcmP002Radius2572, pairMagnitude2542, fjcmP002Rounded2572]

noncomputable def fjcmP003Input2572 : RatPair2542 := ((((-((45863 * 10^40
        + 2648834366119055615025041831922191898173) * 10^40
        + 965668249849210782996703504146014186969)) : ℚ) /
        ((271270 * 10^40
        + 3087127989071126638748716684898100330217) * 10^40
        + 4625034212383035136128999122534400000000)),
    (((-1751187200352461984105434273) : ℚ) /
        3689348814741910323200000000))

def fjcmP003Center2572 : RatPair2542 := ((((-124248799378105233681111054157) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-197431261930242224312065802635) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def fjcmP003Factor2572 : RatPair2542 := ((((((22192970882888546430944162 * 10^40
        + 7885100455256178716419951856610578186510) * 10^40
        + 4140984879883813869469594732907097283971) * 10^40
        + 7801122271213209106076265718078599851893) : ℚ) /
        (((1606260347525033779466620 * 10^40
        + 5166467254346026671607727341022095991267) * 10^40
        + 7695615647830152909098794229549722205493) * 10^40
        + 8076859457573581787847468563842800296214)),
    ((5524291025718029 : ℚ) /
        140737488355328))

noncomputable def fjcmP003Error2572 : ℝ := ((806976511608363622744226945 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjcmP003BaseError2572 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨3, by omega⟩
      corrC02701MinusMidpointPosition2572 - embedPair2542 fjcmP003Center2572‖ ≤ fjcmP003Error2572
          := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hz : ‖embedPair2542 fjcmP003Input2572‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjcmP003Input2572]
  have hc : (compactExp2547 fjcmP003Input2572 8).1 = fjcmP003Center2572 := by cbv
  have he : ((compactExp2547 fjcmP003Input2572 8).2 : ℝ) = fjcmP003Error2572 := by
    have hq : (compactExp2547 fjcmP003Input2572 8).2 =
        ((806976511608363622744226945 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjcmP003Error2572]
  have h := compactExp_error2547 fjcmP003Input2572 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨3, by omega⟩
      corrC02701MinusMidpointPosition2572 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          fjcmP003Input2572) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrC02701MinusMidpointPosition2572, storedWidth,
      nodeModulation2541, embedPair2542, fjcmP003Input2572, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjcmP003DerivativeError2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨3, by omega⟩
      corrC02701MinusMidpointPosition2572 -
      embedPair2542 fjcmP003Factor2572 * embedPair2542 fjcmP003Center2572‖ ≤
        (pairMagnitude2542 fjcmP003Factor2572 : ℝ) * fjcmP003Error2572 := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hf : weightedMultiplier2543 1 (-1/2)
      (nodeModulation2541 ⟨3, by omega⟩)
      (storedWidth ⟨3, by omega⟩ ^ 2) corrC02701MinusMidpointPosition2572 =
      embedPair2542 fjcmP003Factor2572 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrC02701MinusMidpointPosition2572, storedWidth, nodeModulation2541, embedPair2542,
      fjcmP003Factor2572, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (-1/2)
    (nodeModulation2541 ⟨3, by omega⟩) (pow_pos (storedWidth_pos ⟨3, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjcmP003BaseError2572
    (embedPair_magnitude2542 fjcmP003Factor2572)

def fjcmP003Rounded2572 : RatPair2542 :=
  (((2616384164945 : ℚ) /
        633825300114114700748351602688),
    (((-6596188727801) : ℚ) /
        1267650600228229401496703205376))

noncomputable def fjcmP003Radius2572 : ℝ := ((17470065603 : ℝ) /
        (1 * 10^40
        + 889035741470030830827987437816582766592))

theorem fjcmP003RoundCompute2572 :
    pairRound2542 (pairMul2542 fjcmP003Factor2572 fjcmP003Center2572) = fjcmP003Rounded2572 := by
  cbv

theorem fjcmP003RoundedError2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨3, by omega⟩
      corrC02701MinusMidpointPosition2572 - embedPair2542 fjcmP003Rounded2572‖ ≤
          fjcmP003Radius2572 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjcmP003Factor2572 fjcmP003Center2572)
  rw [fjcmP003RoundCompute2572, embedPair_mul2542] at hr
  have h := (firstJetCorrMinus_triangle2572
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨3, by omega⟩
      corrC02701MinusMidpointPosition2572)
    (embedPair2542 fjcmP003Factor2572 * embedPair2542 fjcmP003Center2572)
    (embedPair2542 fjcmP003Rounded2572)).trans (add_le_add fjcmP003DerivativeError2572 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjcmP003Factor2572, fjcmP003Error2572, rounding2542,
      fjcmP003Radius2572]

theorem fjcmP003DerivativeNorm2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨3, by omega⟩
      corrC02701MinusMidpointPosition2572‖ ≤ 1 := by
  have h := firstJetCorrMinus_triangle2572
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨3, by omega⟩
      corrC02701MinusMidpointPosition2572)
    (embedPair2542 fjcmP003Rounded2572) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjcmP003RoundedError2572 (embedPair_magnitude2542
      fjcmP003Rounded2572))
  apply h'.trans
  norm_num [fjcmP003Radius2572, pairMagnitude2542, fjcmP003Rounded2572]

noncomputable def fjcmP004Input2572 : RatPair2542 := ((((-((38818 * 10^40
        + 9869011026983687992946176473055787532810) * 10^40
        + 4481020112683669260999281426307191747803)) : ℚ) /
        ((268088 * 10^40
        + 9931593660330219898315158741078364901345) * 10^40
        + 3125060162297126925824073714892800000000)),
    ((1751187200352461984105434273 : ℚ) /
        3689348814741910323200000000))

def fjcmP004Center2572 : RatPair2542 := ((((-15506492841082746575794339206295) : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)),
    ((98559228420736481491679132241355 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def fjcmP004Factor2572 : RatPair2542 := ((((((3485635103813537515116547 * 10^40
        + 2956948287952892729957549906404144653391) * 10^40
        + 9605592616309696120377943794644294845359) * 10^40
        + 298552743954356786653458291713386695039) : ℚ) /
        (((522935502909259286010183 * 10^40
        + 3798095078935136997935374007107063007048) * 10^40
        + 469585152326299585236868043123535726413) * 10^40
        + 3850148666208406426693083416573226609922)),
    (((-5524291025718029) : ℚ) /
        140737488355328))

noncomputable def fjcmP004Error2572 : ℝ := ((98297418978311525453437400183 : ℝ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))

theorem fjcmP004BaseError2572 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨4, by omega⟩
      corrC02701MinusMidpointPosition2572 - embedPair2542 fjcmP004Center2572‖ ≤ fjcmP004Error2572
          := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hz : ‖embedPair2542 fjcmP004Input2572‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjcmP004Input2572]
  have hc : (compactExp2547 fjcmP004Input2572 8).1 = fjcmP004Center2572 := by cbv
  have he : ((compactExp2547 fjcmP004Input2572 8).2 : ℝ) = fjcmP004Error2572 := by
    have hq : (compactExp2547 fjcmP004Input2572 8).2 =
        ((98297418978311525453437400183 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344)) := by cbv
    rw [hq]
    norm_num [fjcmP004Error2572]
  have h := compactExp_error2547 fjcmP004Input2572 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨4, by omega⟩
      corrC02701MinusMidpointPosition2572 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          fjcmP004Input2572) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrC02701MinusMidpointPosition2572, storedWidth,
      nodeModulation2541, embedPair2542, fjcmP004Input2572, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjcmP004DerivativeError2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨4, by omega⟩
      corrC02701MinusMidpointPosition2572 -
      embedPair2542 fjcmP004Factor2572 * embedPair2542 fjcmP004Center2572‖ ≤
        (pairMagnitude2542 fjcmP004Factor2572 : ℝ) * fjcmP004Error2572 := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hf : weightedMultiplier2543 1 (-1/2)
      (nodeModulation2541 ⟨4, by omega⟩)
      (storedWidth ⟨4, by omega⟩ ^ 2) corrC02701MinusMidpointPosition2572 =
      embedPair2542 fjcmP004Factor2572 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrC02701MinusMidpointPosition2572, storedWidth, nodeModulation2541, embedPair2542,
      fjcmP004Factor2572, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (-1/2)
    (nodeModulation2541 ⟨4, by omega⟩) (pow_pos (storedWidth_pos ⟨4, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjcmP004BaseError2572
    (embedPair_magnitude2542 fjcmP004Factor2572)

def fjcmP004Rounded2572 : RatPair2542 :=
  (((749239196032041 : ℚ) /
        316912650057057350374175801344),
    ((167597023104859 : ℚ) /
        79228162514264337593543950336))

noncomputable def fjcmP004Radius2572 : ℝ := ((8929389745559 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem fjcmP004RoundCompute2572 :
    pairRound2542 (pairMul2542 fjcmP004Factor2572 fjcmP004Center2572) = fjcmP004Rounded2572 := by
  cbv

theorem fjcmP004RoundedError2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨4, by omega⟩
      corrC02701MinusMidpointPosition2572 - embedPair2542 fjcmP004Rounded2572‖ ≤
          fjcmP004Radius2572 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjcmP004Factor2572 fjcmP004Center2572)
  rw [fjcmP004RoundCompute2572, embedPair_mul2542] at hr
  have h := (firstJetCorrMinus_triangle2572
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨4, by omega⟩
      corrC02701MinusMidpointPosition2572)
    (embedPair2542 fjcmP004Factor2572 * embedPair2542 fjcmP004Center2572)
    (embedPair2542 fjcmP004Rounded2572)).trans (add_le_add fjcmP004DerivativeError2572 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjcmP004Factor2572, fjcmP004Error2572, rounding2542,
      fjcmP004Radius2572]

theorem fjcmP004DerivativeNorm2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨4, by omega⟩
      corrC02701MinusMidpointPosition2572‖ ≤ 1 := by
  have h := firstJetCorrMinus_triangle2572
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨4, by omega⟩
      corrC02701MinusMidpointPosition2572)
    (embedPair2542 fjcmP004Rounded2572) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjcmP004RoundedError2572 (embedPair_magnitude2542
      fjcmP004Rounded2572))
  apply h'.trans
  norm_num [fjcmP004Radius2572, pairMagnitude2542, fjcmP004Rounded2572]

def fjcmP005Center2572 : RatPair2542 := (0, 0)

def fjcmP005Factor2572 : RatPair2542 := (0, 0)

noncomputable def fjcmP005Error2572 : ℝ := 0

theorem fjcmP005Exterior2572 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨5, by omega⟩
      corrC02701MinusMidpointPosition2572 = 0 := by
  have hx : storedWidth ⟨5, by omega⟩ ^ 2 ≤ |corrC02701MinusMidpointPosition2572| := by
    norm_num [storedWidth, corrC02701MinusMidpointPosition2572]
  exact weightedFamily_outside_zero2543 n (-1/2)
    (nodeModulation2541 ⟨5, by omega⟩)
    (pow_pos (storedWidth_pos ⟨5, by omega⟩) 2) hx

theorem fjcmP005BaseError2572 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨5, by omega⟩
      corrC02701MinusMidpointPosition2572 - embedPair2542 fjcmP005Center2572‖ ≤ fjcmP005Error2572
          := by
  rw [fjcmP005Exterior2572]
  norm_num [fjcmP005Center2572, fjcmP005Error2572, fjcmZero2572]

theorem fjcmP005DerivativeError2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨5, by omega⟩
      corrC02701MinusMidpointPosition2572 -
      embedPair2542 fjcmP005Factor2572 * embedPair2542 fjcmP005Center2572‖ ≤
        (pairMagnitude2542 fjcmP005Factor2572 : ℝ) * fjcmP005Error2572 := by
  rw [fjcmP005Exterior2572]
  norm_num [fjcmP005Factor2572, fjcmP005Center2572, fjcmP005Error2572, pairMagnitude2542,
      fjcmZero2572]

def fjcmP005Rounded2572 : RatPair2542 := (0, 0)

noncomputable def fjcmP005Radius2572 : ℝ := 0

theorem fjcmP005RoundCompute2572 :
    pairRound2542 (pairMul2542 fjcmP005Factor2572 fjcmP005Center2572) = fjcmP005Rounded2572 := by
  cbv

theorem fjcmP005RoundedError2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨5, by omega⟩
      corrC02701MinusMidpointPosition2572 - embedPair2542 fjcmP005Rounded2572‖ ≤
          fjcmP005Radius2572 := by
  rw [fjcmP005Exterior2572]
  norm_num [fjcmP005Rounded2572, fjcmP005Radius2572, fjcmZero2572]

theorem fjcmP005DerivativeNorm2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨5, by omega⟩
      corrC02701MinusMidpointPosition2572‖ ≤ 1 := by
  rw [fjcmP005Exterior2572]
  norm_num

noncomputable def fjcmP006Input2572 : RatPair2542 := ((((-336487691127537234939509440202342751) :
    ℚ) /
        587942314986765992027147468800000000),
    ((0 : ℚ) /
        1))

def fjcmP006Center2572 : RatPair2542 := (((11194442015994273 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1))

def fjcmP006Factor2572 : RatPair2542 := ((((21633004 * 10^40
        + 2221724994059956495011484584821902481413) : ℚ) /
        (301815 * 10^40
        + 156293974360727009977030830356195037174)),
    ((0 : ℚ) /
        1))

noncomputable def fjcmP006Error2572 : ℝ := ((7783662310233 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjcmP006BaseError2572 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨6, by omega⟩
      corrC02701MinusMidpointPosition2572 - embedPair2542 fjcmP006Center2572‖ ≤ fjcmP006Error2572
          := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hz : ‖embedPair2542 fjcmP006Input2572‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjcmP006Input2572]
  have hc : (compactExp2547 fjcmP006Input2572 7).1 = fjcmP006Center2572 := by cbv
  have he : ((compactExp2547 fjcmP006Input2572 7).2 : ℝ) = fjcmP006Error2572 := by
    have hq : (compactExp2547 fjcmP006Input2572 7).2 =
        ((7783662310233 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjcmP006Error2572]
  have h := compactExp_error2547 fjcmP006Input2572 hz 7
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨6, by omega⟩
      corrC02701MinusMidpointPosition2572 = Complex.exp ((2 : ℂ)^7 * embedPair2542
          fjcmP006Input2572) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrC02701MinusMidpointPosition2572, storedWidth,
      nodeModulation2541, embedPair2542, fjcmP006Input2572, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjcmP006DerivativeError2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨6, by omega⟩
      corrC02701MinusMidpointPosition2572 -
      embedPair2542 fjcmP006Factor2572 * embedPair2542 fjcmP006Center2572‖ ≤
        (pairMagnitude2542 fjcmP006Factor2572 : ℝ) * fjcmP006Error2572 := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hf : weightedMultiplier2543 1 (-1/2)
      (nodeModulation2541 ⟨6, by omega⟩)
      (storedWidth ⟨6, by omega⟩ ^ 2) corrC02701MinusMidpointPosition2572 =
      embedPair2542 fjcmP006Factor2572 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrC02701MinusMidpointPosition2572, storedWidth, nodeModulation2541, embedPair2542,
      fjcmP006Factor2572, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (-1/2)
    (nodeModulation2541 ⟨6, by omega⟩) (pow_pos (storedWidth_pos ⟨6, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjcmP006BaseError2572
    (embedPair_magnitude2542 fjcmP006Factor2572)

def fjcmP006Rounded2572 : RatPair2542 :=
  (((1 : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def fjcmP006Radius2572 : ℝ := ((2199023255553 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjcmP006RoundCompute2572 :
    pairRound2542 (pairMul2542 fjcmP006Factor2572 fjcmP006Center2572) = fjcmP006Rounded2572 := by
  cbv

theorem fjcmP006RoundedError2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨6, by omega⟩
      corrC02701MinusMidpointPosition2572 - embedPair2542 fjcmP006Rounded2572‖ ≤
          fjcmP006Radius2572 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjcmP006Factor2572 fjcmP006Center2572)
  rw [fjcmP006RoundCompute2572, embedPair_mul2542] at hr
  have h := (firstJetCorrMinus_triangle2572
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨6, by omega⟩
      corrC02701MinusMidpointPosition2572)
    (embedPair2542 fjcmP006Factor2572 * embedPair2542 fjcmP006Center2572)
    (embedPair2542 fjcmP006Rounded2572)).trans (add_le_add fjcmP006DerivativeError2572 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjcmP006Factor2572, fjcmP006Error2572, rounding2542,
      fjcmP006Radius2572]

theorem fjcmP006DerivativeNorm2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨6, by omega⟩
      corrC02701MinusMidpointPosition2572‖ ≤ 1 := by
  have h := firstJetCorrMinus_triangle2572
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨6, by omega⟩
      corrC02701MinusMidpointPosition2572)
    (embedPair2542 fjcmP006Rounded2572) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjcmP006RoundedError2572 (embedPair_magnitude2542
      fjcmP006Rounded2572))
  apply h'.trans
  norm_num [fjcmP006Radius2572, pairMagnitude2542, fjcmP006Rounded2572]

noncomputable def fjcmP007Input2572 : RatPair2542 := ((((-((45863 * 10^40
        + 2648834366119055615025041831922191898173) * 10^40
        + 965668249849210782996703504146014186969)) : ℚ) /
        ((67817 * 10^40
        + 5771781997267781659687179171224525082554) * 10^40
        + 3656258553095758784032249780633600000000)),
    ((0 : ℚ) /
        1))

def fjcmP007Center2572 : RatPair2542 := (((233274232040893355353989339387 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def fjcmP007Factor2572 : RatPair2542 := ((((((22192970882888546430944162 * 10^40
        + 7885100455256178716419951856610578186510) * 10^40
        + 4140984879883813869469594732907097283971) * 10^40
        + 7801122271213209106076265718078599851893) : ℚ) /
        (((1606260347525033779466620 * 10^40
        + 5166467254346026671607727341022095991267) * 10^40
        + 7695615647830152909098794229549722205493) * 10^40
        + 8076859457573581787847468563842800296214)),
    ((0 : ℚ) /
        1))

noncomputable def fjcmP007Error2572 : ℝ := ((16140561693539335055957957 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem fjcmP007BaseError2572 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨7, by omega⟩
      corrC02701MinusMidpointPosition2572 - embedPair2542 fjcmP007Center2572‖ ≤ fjcmP007Error2572
          := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hz : ‖embedPair2542 fjcmP007Input2572‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjcmP007Input2572]
  have hc : (compactExp2547 fjcmP007Input2572 6).1 = fjcmP007Center2572 := by cbv
  have he : ((compactExp2547 fjcmP007Input2572 6).2 : ℝ) = fjcmP007Error2572 := by
    have hq : (compactExp2547 fjcmP007Input2572 6).2 =
        ((16140561693539335055957957 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)) := by cbv
    rw [hq]
    norm_num [fjcmP007Error2572]
  have h := compactExp_error2547 fjcmP007Input2572 hz 6
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨7, by omega⟩
      corrC02701MinusMidpointPosition2572 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          fjcmP007Input2572) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrC02701MinusMidpointPosition2572, storedWidth,
      nodeModulation2541, embedPair2542, fjcmP007Input2572, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjcmP007DerivativeError2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨7, by omega⟩
      corrC02701MinusMidpointPosition2572 -
      embedPair2542 fjcmP007Factor2572 * embedPair2542 fjcmP007Center2572‖ ≤
        (pairMagnitude2542 fjcmP007Factor2572 : ℝ) * fjcmP007Error2572 := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hf : weightedMultiplier2543 1 (-1/2)
      (nodeModulation2541 ⟨7, by omega⟩)
      (storedWidth ⟨7, by omega⟩ ^ 2) corrC02701MinusMidpointPosition2572 =
      embedPair2542 fjcmP007Factor2572 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrC02701MinusMidpointPosition2572, storedWidth, nodeModulation2541, embedPair2542,
      fjcmP007Factor2572, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (-1/2)
    (nodeModulation2541 ⟨7, by omega⟩) (pow_pos (storedWidth_pos ⟨7, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjcmP007BaseError2572
    (embedPair_magnitude2542 fjcmP007Factor2572)

def fjcmP007Rounded2572 : RatPair2542 :=
  (((349443161993 : ℚ) /
        158456325028528675187087900672),
    ((0 : ℚ) /
        1))

noncomputable def fjcmP007Radius2572 : ℝ := ((1099705055361 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem fjcmP007RoundCompute2572 :
    pairRound2542 (pairMul2542 fjcmP007Factor2572 fjcmP007Center2572) = fjcmP007Rounded2572 := by
  cbv

theorem fjcmP007RoundedError2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨7, by omega⟩
      corrC02701MinusMidpointPosition2572 - embedPair2542 fjcmP007Rounded2572‖ ≤
          fjcmP007Radius2572 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjcmP007Factor2572 fjcmP007Center2572)
  rw [fjcmP007RoundCompute2572, embedPair_mul2542] at hr
  have h := (firstJetCorrMinus_triangle2572
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨7, by omega⟩
      corrC02701MinusMidpointPosition2572)
    (embedPair2542 fjcmP007Factor2572 * embedPair2542 fjcmP007Center2572)
    (embedPair2542 fjcmP007Rounded2572)).trans (add_le_add fjcmP007DerivativeError2572 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjcmP007Factor2572, fjcmP007Error2572, rounding2542,
      fjcmP007Radius2572]

theorem fjcmP007DerivativeNorm2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨7, by omega⟩
      corrC02701MinusMidpointPosition2572‖ ≤ 1 := by
  have h := firstJetCorrMinus_triangle2572
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨7, by omega⟩
      corrC02701MinusMidpointPosition2572)
    (embedPair2542 fjcmP007Rounded2572) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjcmP007RoundedError2572 (embedPair_magnitude2542
      fjcmP007Rounded2572))
  apply h'.trans
  norm_num [fjcmP007Radius2572, pairMagnitude2542, fjcmP007Rounded2572]

noncomputable def fjcmP008Input2572 : RatPair2542 := ((((-((770889 * 10^40
        + 3381634557173160365454331760519832708453) * 10^40
        + 8445081731115744698509100587432038911481)) : ℚ) /
        ((1043539 * 10^40
        + 9494850363077843158719362614051723272667) * 10^40
        + 9765981577832661801082496535756800000000)),
    ((1261197741322974723791937589 : ℚ) /
        944473296573929042739200000000))

def fjcmP008Center2572 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjcmP008Factor2572 : RatPair2542 := ((((((18287110242590252447880554564 * 10^40
        + 3096719781200154055536277499850834687716) * 10^40
        + 9868174371958028754305932466956652974581) * 10^40
        + 2972738437505500261821781699491681895093) : ℚ) /
        (((1450806976117078933368 * 10^40
        + 6938549699731298507206310750329531504355) * 10^40
        + 7684528508351137377988959013790724929283) * 10^40
        + 1232558896135239476356436601016636209814)),
    (((-3978571430081297) : ℚ) /
        281474976710656))

noncomputable def fjcmP008Error2572 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjcmP008BaseError2572 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨8, by omega⟩
      corrC02701MinusMidpointPosition2572 - embedPair2542 fjcmP008Center2572‖ ≤ fjcmP008Error2572
          := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨8, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hz : ‖embedPair2542 fjcmP008Input2572‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjcmP008Input2572]
  have hc : (compactExp2547 fjcmP008Input2572 15).1 = fjcmP008Center2572 := by cbv
  have he : ((compactExp2547 fjcmP008Input2572 15).2 : ℝ) = fjcmP008Error2572 := by
    have hq : (compactExp2547 fjcmP008Input2572 15).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjcmP008Error2572]
  have h := compactExp_error2547 fjcmP008Input2572 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨8, by omega⟩
      corrC02701MinusMidpointPosition2572 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          fjcmP008Input2572) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrC02701MinusMidpointPosition2572, storedWidth,
      nodeModulation2541, embedPair2542, fjcmP008Input2572, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjcmP008DerivativeError2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨8, by omega⟩
      corrC02701MinusMidpointPosition2572 -
      embedPair2542 fjcmP008Factor2572 * embedPair2542 fjcmP008Center2572‖ ≤
        (pairMagnitude2542 fjcmP008Factor2572 : ℝ) * fjcmP008Error2572 := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨8, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hf : weightedMultiplier2543 1 (-1/2)
      (nodeModulation2541 ⟨8, by omega⟩)
      (storedWidth ⟨8, by omega⟩ ^ 2) corrC02701MinusMidpointPosition2572 =
      embedPair2542 fjcmP008Factor2572 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrC02701MinusMidpointPosition2572, storedWidth, nodeModulation2541, embedPair2542,
      fjcmP008Factor2572, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (-1/2)
    (nodeModulation2541 ⟨8, by omega⟩) (pow_pos (storedWidth_pos ⟨8, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjcmP008BaseError2572
    (embedPair_magnitude2542 fjcmP008Factor2572)

def fjcmP008Rounded2572 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjcmP008Radius2572 : ℝ := ((2199023255577 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjcmP008RoundCompute2572 :
    pairRound2542 (pairMul2542 fjcmP008Factor2572 fjcmP008Center2572) = fjcmP008Rounded2572 := by
  cbv

theorem fjcmP008RoundedError2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨8, by omega⟩
      corrC02701MinusMidpointPosition2572 - embedPair2542 fjcmP008Rounded2572‖ ≤
          fjcmP008Radius2572 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjcmP008Factor2572 fjcmP008Center2572)
  rw [fjcmP008RoundCompute2572, embedPair_mul2542] at hr
  have h := (firstJetCorrMinus_triangle2572
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨8, by omega⟩
      corrC02701MinusMidpointPosition2572)
    (embedPair2542 fjcmP008Factor2572 * embedPair2542 fjcmP008Center2572)
    (embedPair2542 fjcmP008Rounded2572)).trans (add_le_add fjcmP008DerivativeError2572 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjcmP008Factor2572, fjcmP008Error2572, rounding2542,
      fjcmP008Radius2572]

theorem fjcmP008DerivativeNorm2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨8, by omega⟩
      corrC02701MinusMidpointPosition2572‖ ≤ 1 := by
  have h := firstJetCorrMinus_triangle2572
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨8, by omega⟩
      corrC02701MinusMidpointPosition2572)
    (embedPair2542 fjcmP008Rounded2572) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjcmP008RoundedError2572 (embedPair_magnitude2542
      fjcmP008Rounded2572))
  apply h'.trans
  norm_num [fjcmP008Radius2572, pairMagnitude2542, fjcmP008Rounded2572]

noncomputable def fjcmP009Input2572 : RatPair2542 := ((((-((770889 * 10^40
        + 3381634557173160365454331760519832708453) * 10^40
        + 8445081731115744698509100587432038911481)) : ℚ) /
        ((1043539 * 10^40
        + 9494850363077843158719362614051723272667) * 10^40
        + 9765981577832661801082496535756800000000)),
    ((1875731480065194149050312107 : ℚ) /
        944473296573929042739200000000))

def fjcmP009Center2572 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjcmP009Factor2572 : RatPair2542 := ((((((18287110242590252447880554564 * 10^40
        + 3096719781200154055536277499850834687716) * 10^40
        + 9868174371958028754305932466956652974581) * 10^40
        + 2972738437505500261821781699491681895093) : ℚ) /
        (((1450806976117078933368 * 10^40
        + 6938549699731298507206310750329531504355) * 10^40
        + 7684528508351137377988959013790724929283) * 10^40
        + 1232558896135239476356436601016636209814)),
    (((-5917178117733711) : ℚ) /
        281474976710656))

noncomputable def fjcmP009Error2572 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjcmP009BaseError2572 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨9, by omega⟩
      corrC02701MinusMidpointPosition2572 - embedPair2542 fjcmP009Center2572‖ ≤ fjcmP009Error2572
          := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨9, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hz : ‖embedPair2542 fjcmP009Input2572‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjcmP009Input2572]
  have hc : (compactExp2547 fjcmP009Input2572 15).1 = fjcmP009Center2572 := by cbv
  have he : ((compactExp2547 fjcmP009Input2572 15).2 : ℝ) = fjcmP009Error2572 := by
    have hq : (compactExp2547 fjcmP009Input2572 15).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjcmP009Error2572]
  have h := compactExp_error2547 fjcmP009Input2572 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨9, by omega⟩
      corrC02701MinusMidpointPosition2572 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          fjcmP009Input2572) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrC02701MinusMidpointPosition2572, storedWidth,
      nodeModulation2541, embedPair2542, fjcmP009Input2572, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjcmP009DerivativeError2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨9, by omega⟩
      corrC02701MinusMidpointPosition2572 -
      embedPair2542 fjcmP009Factor2572 * embedPair2542 fjcmP009Center2572‖ ≤
        (pairMagnitude2542 fjcmP009Factor2572 : ℝ) * fjcmP009Error2572 := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨9, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hf : weightedMultiplier2543 1 (-1/2)
      (nodeModulation2541 ⟨9, by omega⟩)
      (storedWidth ⟨9, by omega⟩ ^ 2) corrC02701MinusMidpointPosition2572 =
      embedPair2542 fjcmP009Factor2572 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrC02701MinusMidpointPosition2572, storedWidth, nodeModulation2541, embedPair2542,
      fjcmP009Factor2572, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (-1/2)
    (nodeModulation2541 ⟨9, by omega⟩) (pow_pos (storedWidth_pos ⟨9, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjcmP009BaseError2572
    (embedPair_magnitude2542 fjcmP009Factor2572)

def fjcmP009Rounded2572 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjcmP009Radius2572 : ℝ := ((2199023255577 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjcmP009RoundCompute2572 :
    pairRound2542 (pairMul2542 fjcmP009Factor2572 fjcmP009Center2572) = fjcmP009Rounded2572 := by
  cbv

theorem fjcmP009RoundedError2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨9, by omega⟩
      corrC02701MinusMidpointPosition2572 - embedPair2542 fjcmP009Rounded2572‖ ≤
          fjcmP009Radius2572 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjcmP009Factor2572 fjcmP009Center2572)
  rw [fjcmP009RoundCompute2572, embedPair_mul2542] at hr
  have h := (firstJetCorrMinus_triangle2572
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨9, by omega⟩
      corrC02701MinusMidpointPosition2572)
    (embedPair2542 fjcmP009Factor2572 * embedPair2542 fjcmP009Center2572)
    (embedPair2542 fjcmP009Rounded2572)).trans (add_le_add fjcmP009DerivativeError2572 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjcmP009Factor2572, fjcmP009Error2572, rounding2542,
      fjcmP009Radius2572]

theorem fjcmP009DerivativeNorm2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨9, by omega⟩
      corrC02701MinusMidpointPosition2572‖ ≤ 1 := by
  have h := firstJetCorrMinus_triangle2572
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨9, by omega⟩
      corrC02701MinusMidpointPosition2572)
    (embedPair2542 fjcmP009Rounded2572) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjcmP009RoundedError2572 (embedPair_magnitude2542
      fjcmP009Rounded2572))
  apply h'.trans
  norm_num [fjcmP009Radius2572, pairMagnitude2542, fjcmP009Rounded2572]

noncomputable def fjcmP010Input2572 : RatPair2542 := ((((-((770889 * 10^40
        + 3381634557173160365454331760519832708453) * 10^40
        + 8445081731115744698509100587432038911481)) : ℚ) /
        ((1043539 * 10^40
        + 9494850363077843158719362614051723272667) * 10^40
        + 9765981577832661801082496535756800000000)),
    ((1115820674697574220099746077 : ℚ) /
        472236648286964521369600000000))

def fjcmP010Center2572 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjcmP010Factor2572 : RatPair2542 := ((((((18287110242590252447880554564 * 10^40
        + 3096719781200154055536277499850834687716) * 10^40
        + 9868174371958028754305932466956652974581) * 10^40
        + 2972738437505500261821781699491681895093) : ℚ) /
        (((1450806976117078933368 * 10^40
        + 6938549699731298507206310750329531504355) * 10^40
        + 7684528508351137377988959013790724929283) * 10^40
        + 1232558896135239476356436601016636209814)),
    (((-3519965277442521) : ℚ) /
        140737488355328))

noncomputable def fjcmP010Error2572 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjcmP010BaseError2572 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨10, by omega⟩
      corrC02701MinusMidpointPosition2572 - embedPair2542 fjcmP010Center2572‖ ≤ fjcmP010Error2572
          := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨10, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hz : ‖embedPair2542 fjcmP010Input2572‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjcmP010Input2572]
  have hc : (compactExp2547 fjcmP010Input2572 15).1 = fjcmP010Center2572 := by cbv
  have he : ((compactExp2547 fjcmP010Input2572 15).2 : ℝ) = fjcmP010Error2572 := by
    have hq : (compactExp2547 fjcmP010Input2572 15).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjcmP010Error2572]
  have h := compactExp_error2547 fjcmP010Input2572 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨10, by omega⟩
      corrC02701MinusMidpointPosition2572 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          fjcmP010Input2572) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrC02701MinusMidpointPosition2572, storedWidth,
      nodeModulation2541, embedPair2542, fjcmP010Input2572, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjcmP010DerivativeError2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨10, by omega⟩
      corrC02701MinusMidpointPosition2572 -
      embedPair2542 fjcmP010Factor2572 * embedPair2542 fjcmP010Center2572‖ ≤
        (pairMagnitude2542 fjcmP010Factor2572 : ℝ) * fjcmP010Error2572 := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨10, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hf : weightedMultiplier2543 1 (-1/2)
      (nodeModulation2541 ⟨10, by omega⟩)
      (storedWidth ⟨10, by omega⟩ ^ 2) corrC02701MinusMidpointPosition2572 =
      embedPair2542 fjcmP010Factor2572 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrC02701MinusMidpointPosition2572, storedWidth, nodeModulation2541, embedPair2542,
      fjcmP010Factor2572, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (-1/2)
    (nodeModulation2541 ⟨10, by omega⟩) (pow_pos (storedWidth_pos ⟨10, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjcmP010BaseError2572
    (embedPair_magnitude2542 fjcmP010Factor2572)

def fjcmP010Rounded2572 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjcmP010Radius2572 : ℝ := ((2199023255577 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjcmP010RoundCompute2572 :
    pairRound2542 (pairMul2542 fjcmP010Factor2572 fjcmP010Center2572) = fjcmP010Rounded2572 := by
  cbv

theorem fjcmP010RoundedError2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨10, by omega⟩
      corrC02701MinusMidpointPosition2572 - embedPair2542 fjcmP010Rounded2572‖ ≤
          fjcmP010Radius2572 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjcmP010Factor2572 fjcmP010Center2572)
  rw [fjcmP010RoundCompute2572, embedPair_mul2542] at hr
  have h := (firstJetCorrMinus_triangle2572
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨10, by omega⟩
      corrC02701MinusMidpointPosition2572)
    (embedPair2542 fjcmP010Factor2572 * embedPair2542 fjcmP010Center2572)
    (embedPair2542 fjcmP010Rounded2572)).trans (add_le_add fjcmP010DerivativeError2572 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjcmP010Factor2572, fjcmP010Error2572, rounding2542,
      fjcmP010Radius2572]

theorem fjcmP010DerivativeNorm2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨10, by omega⟩
      corrC02701MinusMidpointPosition2572‖ ≤ 1 := by
  have h := firstJetCorrMinus_triangle2572
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨10, by omega⟩
      corrC02701MinusMidpointPosition2572)
    (embedPair2542 fjcmP010Rounded2572) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjcmP010RoundedError2572 (embedPair_magnitude2542
      fjcmP010Rounded2572))
  apply h'.trans
  norm_num [fjcmP010Radius2572, pairMagnitude2542, fjcmP010Rounded2572]

noncomputable def fjcmP011Input2572 : RatPair2542 := ((((-((770889 * 10^40
        + 3381634557173160365454331760519832708453) * 10^40
        + 8445081731115744698509100587432038911481)) : ℚ) /
        ((1043539 * 10^40
        + 9494850363077843158719362614051723272667) * 10^40
        + 9765981577832661801082496535756800000000)),
    ((1234468557765072383258963437 : ℚ) /
        472236648286964521369600000000))

def fjcmP011Center2572 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjcmP011Factor2572 : RatPair2542 := ((((((18287110242590252447880554564 * 10^40
        + 3096719781200154055536277499850834687716) * 10^40
        + 9868174371958028754305932466956652974581) * 10^40
        + 2972738437505500261821781699491681895093) : ℚ) /
        (((1450806976117078933368 * 10^40
        + 6938549699731298507206310750329531504355) * 10^40
        + 7684528508351137377988959013790724929283) * 10^40
        + 1232558896135239476356436601016636209814)),
    (((-3894251610461801) : ℚ) /
        140737488355328))

noncomputable def fjcmP011Error2572 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjcmP011BaseError2572 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨11, by omega⟩
      corrC02701MinusMidpointPosition2572 - embedPair2542 fjcmP011Center2572‖ ≤ fjcmP011Error2572
          := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨11, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hz : ‖embedPair2542 fjcmP011Input2572‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjcmP011Input2572]
  have hc : (compactExp2547 fjcmP011Input2572 15).1 = fjcmP011Center2572 := by cbv
  have he : ((compactExp2547 fjcmP011Input2572 15).2 : ℝ) = fjcmP011Error2572 := by
    have hq : (compactExp2547 fjcmP011Input2572 15).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjcmP011Error2572]
  have h := compactExp_error2547 fjcmP011Input2572 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨11, by omega⟩
      corrC02701MinusMidpointPosition2572 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          fjcmP011Input2572) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrC02701MinusMidpointPosition2572, storedWidth,
      nodeModulation2541, embedPair2542, fjcmP011Input2572, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjcmP011DerivativeError2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨11, by omega⟩
      corrC02701MinusMidpointPosition2572 -
      embedPair2542 fjcmP011Factor2572 * embedPair2542 fjcmP011Center2572‖ ≤
        (pairMagnitude2542 fjcmP011Factor2572 : ℝ) * fjcmP011Error2572 := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨11, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hf : weightedMultiplier2543 1 (-1/2)
      (nodeModulation2541 ⟨11, by omega⟩)
      (storedWidth ⟨11, by omega⟩ ^ 2) corrC02701MinusMidpointPosition2572 =
      embedPair2542 fjcmP011Factor2572 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrC02701MinusMidpointPosition2572, storedWidth, nodeModulation2541, embedPair2542,
      fjcmP011Factor2572, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (-1/2)
    (nodeModulation2541 ⟨11, by omega⟩) (pow_pos (storedWidth_pos ⟨11, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjcmP011BaseError2572
    (embedPair_magnitude2542 fjcmP011Factor2572)

def fjcmP011Rounded2572 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjcmP011Radius2572 : ℝ := ((2199023255577 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjcmP011RoundCompute2572 :
    pairRound2542 (pairMul2542 fjcmP011Factor2572 fjcmP011Center2572) = fjcmP011Rounded2572 := by
  cbv

theorem fjcmP011RoundedError2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨11, by omega⟩
      corrC02701MinusMidpointPosition2572 - embedPair2542 fjcmP011Rounded2572‖ ≤
          fjcmP011Radius2572 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjcmP011Factor2572 fjcmP011Center2572)
  rw [fjcmP011RoundCompute2572, embedPair_mul2542] at hr
  have h := (firstJetCorrMinus_triangle2572
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨11, by omega⟩
      corrC02701MinusMidpointPosition2572)
    (embedPair2542 fjcmP011Factor2572 * embedPair2542 fjcmP011Center2572)
    (embedPair2542 fjcmP011Rounded2572)).trans (add_le_add fjcmP011DerivativeError2572 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjcmP011Factor2572, fjcmP011Error2572, rounding2542,
      fjcmP011Radius2572]

theorem fjcmP011DerivativeNorm2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨11, by omega⟩
      corrC02701MinusMidpointPosition2572‖ ≤ 1 := by
  have h := firstJetCorrMinus_triangle2572
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨11, by omega⟩
      corrC02701MinusMidpointPosition2572)
    (embedPair2542 fjcmP011Rounded2572) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjcmP011RoundedError2572 (embedPair_magnitude2542
      fjcmP011Rounded2572))
  apply h'.trans
  norm_num [fjcmP011Radius2572, pairMagnitude2542, fjcmP011Rounded2572]

noncomputable def fjcmP012Input2572 : RatPair2542 := ((((-((770889 * 10^40
        + 3381634557173160365454331760519832708453) * 10^40
        + 8445081731115744698509100587432038911481)) : ℚ) /
        ((1043539 * 10^40
        + 9494850363077843158719362614051723272667) * 10^40
        + 9765981577832661801082496535756800000000)),
    ((27147174540145397472943033 : ℚ) /
        9444732965739290427392000000))

def fjcmP012Center2572 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjcmP012Factor2572 : RatPair2542 := ((((((18287110242590252447880554564 * 10^40
        + 3096719781200154055536277499850834687716) * 10^40
        + 9868174371958028754305932466956652974581) * 10^40
        + 2972738437505500261821781699491681895093) : ℚ) /
        (((1450806976117078933368 * 10^40
        + 6938549699731298507206310750329531504355) * 10^40
        + 7684528508351137377988959013790724929283) * 10^40
        + 1232558896135239476356436601016636209814)),
    (((-2140960324737725) : ℚ) /
        70368744177664))

noncomputable def fjcmP012Error2572 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjcmP012BaseError2572 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨12, by omega⟩
      corrC02701MinusMidpointPosition2572 - embedPair2542 fjcmP012Center2572‖ ≤ fjcmP012Error2572
          := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨12, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hz : ‖embedPair2542 fjcmP012Input2572‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjcmP012Input2572]
  have hc : (compactExp2547 fjcmP012Input2572 15).1 = fjcmP012Center2572 := by cbv
  have he : ((compactExp2547 fjcmP012Input2572 15).2 : ℝ) = fjcmP012Error2572 := by
    have hq : (compactExp2547 fjcmP012Input2572 15).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjcmP012Error2572]
  have h := compactExp_error2547 fjcmP012Input2572 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨12, by omega⟩
      corrC02701MinusMidpointPosition2572 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          fjcmP012Input2572) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrC02701MinusMidpointPosition2572, storedWidth,
      nodeModulation2541, embedPair2542, fjcmP012Input2572, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjcmP012DerivativeError2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨12, by omega⟩
      corrC02701MinusMidpointPosition2572 -
      embedPair2542 fjcmP012Factor2572 * embedPair2542 fjcmP012Center2572‖ ≤
        (pairMagnitude2542 fjcmP012Factor2572 : ℝ) * fjcmP012Error2572 := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨12, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hf : weightedMultiplier2543 1 (-1/2)
      (nodeModulation2541 ⟨12, by omega⟩)
      (storedWidth ⟨12, by omega⟩ ^ 2) corrC02701MinusMidpointPosition2572 =
      embedPair2542 fjcmP012Factor2572 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrC02701MinusMidpointPosition2572, storedWidth, nodeModulation2541, embedPair2542,
      fjcmP012Factor2572, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (-1/2)
    (nodeModulation2541 ⟨12, by omega⟩) (pow_pos (storedWidth_pos ⟨12, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjcmP012BaseError2572
    (embedPair_magnitude2542 fjcmP012Factor2572)

def fjcmP012Rounded2572 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjcmP012Radius2572 : ℝ := ((2199023255577 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjcmP012RoundCompute2572 :
    pairRound2542 (pairMul2542 fjcmP012Factor2572 fjcmP012Center2572) = fjcmP012Rounded2572 := by
  cbv

theorem fjcmP012RoundedError2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨12, by omega⟩
      corrC02701MinusMidpointPosition2572 - embedPair2542 fjcmP012Rounded2572‖ ≤
          fjcmP012Radius2572 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjcmP012Factor2572 fjcmP012Center2572)
  rw [fjcmP012RoundCompute2572, embedPair_mul2542] at hr
  have h := (firstJetCorrMinus_triangle2572
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨12, by omega⟩
      corrC02701MinusMidpointPosition2572)
    (embedPair2542 fjcmP012Factor2572 * embedPair2542 fjcmP012Center2572)
    (embedPair2542 fjcmP012Rounded2572)).trans (add_le_add fjcmP012DerivativeError2572 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjcmP012Factor2572, fjcmP012Error2572, rounding2542,
      fjcmP012Radius2572]

theorem fjcmP012DerivativeNorm2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨12, by omega⟩
      corrC02701MinusMidpointPosition2572‖ ≤ 1 := by
  have h := firstJetCorrMinus_triangle2572
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨12, by omega⟩
      corrC02701MinusMidpointPosition2572)
    (embedPair2542 fjcmP012Rounded2572) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjcmP012RoundedError2572 (embedPair_magnitude2542
      fjcmP012Rounded2572))
  apply h'.trans
  norm_num [fjcmP012Radius2572, pairMagnitude2542, fjcmP012Rounded2572]

noncomputable def fjcmP013Input2572 : RatPair2542 := ((((-((770889 * 10^40
        + 3381634557173160365454331760519832708453) * 10^40
        + 8445081731115744698509100587432038911481)) : ℚ) /
        ((1043539 * 10^40
        + 9494850363077843158719362614051723272667) * 10^40
        + 9765981577832661801082496535756800000000)),
    ((293869352734311453179388567 : ℚ) /
        94447329657392904273920000000))

def fjcmP013Center2572 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjcmP013Factor2572 : RatPair2542 := ((((((18287110242590252447880554564 * 10^40
        + 3096719781200154055536277499850834687716) * 10^40
        + 9868174371958028754305932466956652974581) * 10^40
        + 2972738437505500261821781699491681895093) : ℚ) /
        (((1450806976117078933368 * 10^40
        + 6938549699731298507206310750329531504355) * 10^40
        + 7684528508351137377988959013790724929283) * 10^40
        + 1232558896135239476356436601016636209814)),
    (((-4635197846686455) : ℚ) /
        140737488355328))

noncomputable def fjcmP013Error2572 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjcmP013BaseError2572 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨13, by omega⟩
      corrC02701MinusMidpointPosition2572 - embedPair2542 fjcmP013Center2572‖ ≤ fjcmP013Error2572
          := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨13, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hz : ‖embedPair2542 fjcmP013Input2572‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjcmP013Input2572]
  have hc : (compactExp2547 fjcmP013Input2572 15).1 = fjcmP013Center2572 := by cbv
  have he : ((compactExp2547 fjcmP013Input2572 15).2 : ℝ) = fjcmP013Error2572 := by
    have hq : (compactExp2547 fjcmP013Input2572 15).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjcmP013Error2572]
  have h := compactExp_error2547 fjcmP013Input2572 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨13, by omega⟩
      corrC02701MinusMidpointPosition2572 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          fjcmP013Input2572) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrC02701MinusMidpointPosition2572, storedWidth,
      nodeModulation2541, embedPair2542, fjcmP013Input2572, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjcmP013DerivativeError2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨13, by omega⟩
      corrC02701MinusMidpointPosition2572 -
      embedPair2542 fjcmP013Factor2572 * embedPair2542 fjcmP013Center2572‖ ≤
        (pairMagnitude2542 fjcmP013Factor2572 : ℝ) * fjcmP013Error2572 := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨13, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hf : weightedMultiplier2543 1 (-1/2)
      (nodeModulation2541 ⟨13, by omega⟩)
      (storedWidth ⟨13, by omega⟩ ^ 2) corrC02701MinusMidpointPosition2572 =
      embedPair2542 fjcmP013Factor2572 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrC02701MinusMidpointPosition2572, storedWidth, nodeModulation2541, embedPair2542,
      fjcmP013Factor2572, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (-1/2)
    (nodeModulation2541 ⟨13, by omega⟩) (pow_pos (storedWidth_pos ⟨13, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjcmP013BaseError2572
    (embedPair_magnitude2542 fjcmP013Factor2572)

def fjcmP013Rounded2572 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjcmP013Radius2572 : ℝ := ((2199023255577 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjcmP013RoundCompute2572 :
    pairRound2542 (pairMul2542 fjcmP013Factor2572 fjcmP013Center2572) = fjcmP013Rounded2572 := by
  cbv

theorem fjcmP013RoundedError2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨13, by omega⟩
      corrC02701MinusMidpointPosition2572 - embedPair2542 fjcmP013Rounded2572‖ ≤
          fjcmP013Radius2572 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjcmP013Factor2572 fjcmP013Center2572)
  rw [fjcmP013RoundCompute2572, embedPair_mul2542] at hr
  have h := (firstJetCorrMinus_triangle2572
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨13, by omega⟩
      corrC02701MinusMidpointPosition2572)
    (embedPair2542 fjcmP013Factor2572 * embedPair2542 fjcmP013Center2572)
    (embedPair2542 fjcmP013Rounded2572)).trans (add_le_add fjcmP013DerivativeError2572 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjcmP013Factor2572, fjcmP013Error2572, rounding2542,
      fjcmP013Radius2572]

theorem fjcmP013DerivativeNorm2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨13, by omega⟩
      corrC02701MinusMidpointPosition2572‖ ≤ 1 := by
  have h := firstJetCorrMinus_triangle2572
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨13, by omega⟩
      corrC02701MinusMidpointPosition2572)
    (embedPair2542 fjcmP013Rounded2572) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjcmP013RoundedError2572 (embedPair_magnitude2542
      fjcmP013Rounded2572))
  apply h'.trans
  norm_num [fjcmP013Radius2572, pairMagnitude2542, fjcmP013Rounded2572]

noncomputable def fjcmP014Input2572 : RatPair2542 := ((((-((770889 * 10^40
        + 3381634557173160365454331760519832708453) * 10^40
        + 8445081731115744698509100587432038911481)) : ℚ) /
        ((1043539 * 10^40
        + 9494850363077843158719362614051723272667) * 10^40
        + 9765981577832661801082496535756800000000)),
    ((1676849125948274871802318207 : ℚ) /
        472236648286964521369600000000))

def fjcmP014Center2572 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjcmP014Factor2572 : RatPair2542 := ((((((18287110242590252447880554564 * 10^40
        + 3096719781200154055536277499850834687716) * 10^40
        + 9868174371958028754305932466956652974581) * 10^40
        + 2972738437505500261821781699491681895093) : ℚ) /
        (((1450806976117078933368 * 10^40
        + 6938549699731298507206310750329531504355) * 10^40
        + 7684528508351137377988959013790724929283) * 10^40
        + 1232558896135239476356436601016636209814)),
    (((-5289784310949011) : ℚ) /
        140737488355328))

noncomputable def fjcmP014Error2572 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjcmP014BaseError2572 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨14, by omega⟩
      corrC02701MinusMidpointPosition2572 - embedPair2542 fjcmP014Center2572‖ ≤ fjcmP014Error2572
          := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨14, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hz : ‖embedPair2542 fjcmP014Input2572‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjcmP014Input2572]
  have hc : (compactExp2547 fjcmP014Input2572 15).1 = fjcmP014Center2572 := by cbv
  have he : ((compactExp2547 fjcmP014Input2572 15).2 : ℝ) = fjcmP014Error2572 := by
    have hq : (compactExp2547 fjcmP014Input2572 15).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjcmP014Error2572]
  have h := compactExp_error2547 fjcmP014Input2572 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨14, by omega⟩
      corrC02701MinusMidpointPosition2572 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          fjcmP014Input2572) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrC02701MinusMidpointPosition2572, storedWidth,
      nodeModulation2541, embedPair2542, fjcmP014Input2572, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjcmP014DerivativeError2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨14, by omega⟩
      corrC02701MinusMidpointPosition2572 -
      embedPair2542 fjcmP014Factor2572 * embedPair2542 fjcmP014Center2572‖ ≤
        (pairMagnitude2542 fjcmP014Factor2572 : ℝ) * fjcmP014Error2572 := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨14, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hf : weightedMultiplier2543 1 (-1/2)
      (nodeModulation2541 ⟨14, by omega⟩)
      (storedWidth ⟨14, by omega⟩ ^ 2) corrC02701MinusMidpointPosition2572 =
      embedPair2542 fjcmP014Factor2572 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrC02701MinusMidpointPosition2572, storedWidth, nodeModulation2541, embedPair2542,
      fjcmP014Factor2572, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (-1/2)
    (nodeModulation2541 ⟨14, by omega⟩) (pow_pos (storedWidth_pos ⟨14, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjcmP014BaseError2572
    (embedPair_magnitude2542 fjcmP014Factor2572)

def fjcmP014Rounded2572 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjcmP014Radius2572 : ℝ := ((2199023255577 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjcmP014RoundCompute2572 :
    pairRound2542 (pairMul2542 fjcmP014Factor2572 fjcmP014Center2572) = fjcmP014Rounded2572 := by
  cbv

theorem fjcmP014RoundedError2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨14, by omega⟩
      corrC02701MinusMidpointPosition2572 - embedPair2542 fjcmP014Rounded2572‖ ≤
          fjcmP014Radius2572 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjcmP014Factor2572 fjcmP014Center2572)
  rw [fjcmP014RoundCompute2572, embedPair_mul2542] at hr
  have h := (firstJetCorrMinus_triangle2572
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨14, by omega⟩
      corrC02701MinusMidpointPosition2572)
    (embedPair2542 fjcmP014Factor2572 * embedPair2542 fjcmP014Center2572)
    (embedPair2542 fjcmP014Rounded2572)).trans (add_le_add fjcmP014DerivativeError2572 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjcmP014Factor2572, fjcmP014Error2572, rounding2542,
      fjcmP014Radius2572]

theorem fjcmP014DerivativeNorm2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨14, by omega⟩
      corrC02701MinusMidpointPosition2572‖ ≤ 1 := by
  have h := firstJetCorrMinus_triangle2572
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨14, by omega⟩
      corrC02701MinusMidpointPosition2572)
    (embedPair2542 fjcmP014Rounded2572) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjcmP014RoundedError2572 (embedPair_magnitude2542
      fjcmP014Rounded2572))
  apply h'.trans
  norm_num [fjcmP014Radius2572, pairMagnitude2542, fjcmP014Rounded2572]

noncomputable def fjcmP015Input2572 : RatPair2542 := ((((-((770889 * 10^40
        + 3381634557173160365454331760519832708453) * 10^40
        + 8445081731115744698509100587432038911481)) : ℚ) /
        ((1043539 * 10^40
        + 9494850363077843158719362614051723272667) * 10^40
        + 9765981577832661801082496535756800000000)),
    ((1825525274756649096408550339 : ℚ) /
        472236648286964521369600000000))

def fjcmP015Center2572 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjcmP015Factor2572 : RatPair2542 := ((((((18287110242590252447880554564 * 10^40
        + 3096719781200154055536277499850834687716) * 10^40
        + 9868174371958028754305932466956652974581) * 10^40
        + 2972738437505500261821781699491681895093) : ℚ) /
        (((1450806976117078933368 * 10^40
        + 6938549699731298507206310750329531504355) * 10^40
        + 7684528508351137377988959013790724929283) * 10^40
        + 1232558896135239476356436601016636209814)),
    (((-5758797740487047) : ℚ) /
        140737488355328))

noncomputable def fjcmP015Error2572 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjcmP015BaseError2572 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨15, by omega⟩
      corrC02701MinusMidpointPosition2572 - embedPair2542 fjcmP015Center2572‖ ≤ fjcmP015Error2572
          := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hz : ‖embedPair2542 fjcmP015Input2572‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjcmP015Input2572]
  have hc : (compactExp2547 fjcmP015Input2572 15).1 = fjcmP015Center2572 := by cbv
  have he : ((compactExp2547 fjcmP015Input2572 15).2 : ℝ) = fjcmP015Error2572 := by
    have hq : (compactExp2547 fjcmP015Input2572 15).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjcmP015Error2572]
  have h := compactExp_error2547 fjcmP015Input2572 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨15, by omega⟩
      corrC02701MinusMidpointPosition2572 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          fjcmP015Input2572) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrC02701MinusMidpointPosition2572, storedWidth,
      nodeModulation2541, embedPair2542, fjcmP015Input2572, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjcmP015DerivativeError2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨15, by omega⟩
      corrC02701MinusMidpointPosition2572 -
      embedPair2542 fjcmP015Factor2572 * embedPair2542 fjcmP015Center2572‖ ≤
        (pairMagnitude2542 fjcmP015Factor2572 : ℝ) * fjcmP015Error2572 := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hf : weightedMultiplier2543 1 (-1/2)
      (nodeModulation2541 ⟨15, by omega⟩)
      (storedWidth ⟨15, by omega⟩ ^ 2) corrC02701MinusMidpointPosition2572 =
      embedPair2542 fjcmP015Factor2572 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrC02701MinusMidpointPosition2572, storedWidth, nodeModulation2541, embedPair2542,
      fjcmP015Factor2572, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (-1/2)
    (nodeModulation2541 ⟨15, by omega⟩) (pow_pos (storedWidth_pos ⟨15, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjcmP015BaseError2572
    (embedPair_magnitude2542 fjcmP015Factor2572)

def fjcmP015Rounded2572 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjcmP015Radius2572 : ℝ := ((2199023255577 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjcmP015RoundCompute2572 :
    pairRound2542 (pairMul2542 fjcmP015Factor2572 fjcmP015Center2572) = fjcmP015Rounded2572 := by
  cbv

theorem fjcmP015RoundedError2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨15, by omega⟩
      corrC02701MinusMidpointPosition2572 - embedPair2542 fjcmP015Rounded2572‖ ≤
          fjcmP015Radius2572 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjcmP015Factor2572 fjcmP015Center2572)
  rw [fjcmP015RoundCompute2572, embedPair_mul2542] at hr
  have h := (firstJetCorrMinus_triangle2572
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨15, by omega⟩
      corrC02701MinusMidpointPosition2572)
    (embedPair2542 fjcmP015Factor2572 * embedPair2542 fjcmP015Center2572)
    (embedPair2542 fjcmP015Rounded2572)).trans (add_le_add fjcmP015DerivativeError2572 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjcmP015Factor2572, fjcmP015Error2572, rounding2542,
      fjcmP015Radius2572]

theorem fjcmP015DerivativeNorm2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨15, by omega⟩
      corrC02701MinusMidpointPosition2572‖ ≤ 1 := by
  have h := firstJetCorrMinus_triangle2572
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨15, by omega⟩
      corrC02701MinusMidpointPosition2572)
    (embedPair2542 fjcmP015Rounded2572) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjcmP015RoundedError2572 (embedPair_magnitude2542
      fjcmP015Rounded2572))
  apply h'.trans
  norm_num [fjcmP015Radius2572, pairMagnitude2542, fjcmP015Rounded2572]

noncomputable def fjcmP016Input2572 : RatPair2542 := ((((-((770889 * 10^40
        + 3381634557173160365454331760519832708453) * 10^40
        + 8445081731115744698509100587432038911481)) : ℚ) /
        ((1043539 * 10^40
        + 9494850363077843158719362614051723272667) * 10^40
        + 9765981577832661801082496535756800000000)),
    ((966485135227022568073460733 : ℚ) /
        236118324143482260684800000000))

def fjcmP016Center2572 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjcmP016Factor2572 : RatPair2542 := ((((((18287110242590252447880554564 * 10^40
        + 3096719781200154055536277499850834687716) * 10^40
        + 9868174371958028754305932466956652974581) * 10^40
        + 2972738437505500261821781699491681895093) : ℚ) /
        (((1450806976117078933368 * 10^40
        + 6938549699731298507206310750329531504355) * 10^40
        + 7684528508351137377988959013790724929283) * 10^40
        + 1232558896135239476356436601016636209814)),
    (((-3048871735671609) : ℚ) /
        70368744177664))

noncomputable def fjcmP016Error2572 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjcmP016BaseError2572 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨16, by omega⟩
      corrC02701MinusMidpointPosition2572 - embedPair2542 fjcmP016Center2572‖ ≤ fjcmP016Error2572
          := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨16, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hz : ‖embedPair2542 fjcmP016Input2572‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjcmP016Input2572]
  have hc : (compactExp2547 fjcmP016Input2572 15).1 = fjcmP016Center2572 := by cbv
  have he : ((compactExp2547 fjcmP016Input2572 15).2 : ℝ) = fjcmP016Error2572 := by
    have hq : (compactExp2547 fjcmP016Input2572 15).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjcmP016Error2572]
  have h := compactExp_error2547 fjcmP016Input2572 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨16, by omega⟩
      corrC02701MinusMidpointPosition2572 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          fjcmP016Input2572) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrC02701MinusMidpointPosition2572, storedWidth,
      nodeModulation2541, embedPair2542, fjcmP016Input2572, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjcmP016DerivativeError2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨16, by omega⟩
      corrC02701MinusMidpointPosition2572 -
      embedPair2542 fjcmP016Factor2572 * embedPair2542 fjcmP016Center2572‖ ≤
        (pairMagnitude2542 fjcmP016Factor2572 : ℝ) * fjcmP016Error2572 := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨16, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hf : weightedMultiplier2543 1 (-1/2)
      (nodeModulation2541 ⟨16, by omega⟩)
      (storedWidth ⟨16, by omega⟩ ^ 2) corrC02701MinusMidpointPosition2572 =
      embedPair2542 fjcmP016Factor2572 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrC02701MinusMidpointPosition2572, storedWidth, nodeModulation2541, embedPair2542,
      fjcmP016Factor2572, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (-1/2)
    (nodeModulation2541 ⟨16, by omega⟩) (pow_pos (storedWidth_pos ⟨16, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjcmP016BaseError2572
    (embedPair_magnitude2542 fjcmP016Factor2572)

def fjcmP016Rounded2572 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjcmP016Radius2572 : ℝ := ((2199023255577 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjcmP016RoundCompute2572 :
    pairRound2542 (pairMul2542 fjcmP016Factor2572 fjcmP016Center2572) = fjcmP016Rounded2572 := by
  cbv

theorem fjcmP016RoundedError2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨16, by omega⟩
      corrC02701MinusMidpointPosition2572 - embedPair2542 fjcmP016Rounded2572‖ ≤
          fjcmP016Radius2572 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjcmP016Factor2572 fjcmP016Center2572)
  rw [fjcmP016RoundCompute2572, embedPair_mul2542] at hr
  have h := (firstJetCorrMinus_triangle2572
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨16, by omega⟩
      corrC02701MinusMidpointPosition2572)
    (embedPair2542 fjcmP016Factor2572 * embedPair2542 fjcmP016Center2572)
    (embedPair2542 fjcmP016Rounded2572)).trans (add_le_add fjcmP016DerivativeError2572 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjcmP016Factor2572, fjcmP016Error2572, rounding2542,
      fjcmP016Radius2572]

theorem fjcmP016DerivativeNorm2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨16, by omega⟩
      corrC02701MinusMidpointPosition2572‖ ≤ 1 := by
  have h := firstJetCorrMinus_triangle2572
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨16, by omega⟩
      corrC02701MinusMidpointPosition2572)
    (embedPair2542 fjcmP016Rounded2572) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjcmP016RoundedError2572 (embedPair_magnitude2542
      fjcmP016Rounded2572))
  apply h'.trans
  norm_num [fjcmP016Radius2572, pairMagnitude2542, fjcmP016Rounded2572]

noncomputable def fjcmP017Input2572 : RatPair2542 := ((((-((770889 * 10^40
        + 3381634557173160365454331760519832708453) * 10^40
        + 8445081731115744698509100587432038911481)) : ℚ) /
        ((1043539 * 10^40
        + 9494850363077843158719362614051723272667) * 10^40
        + 9765981577832661801082496535756800000000)),
    ((2141675457290368202103352599 : ℚ) /
        472236648286964521369600000000))

def fjcmP017Center2572 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjcmP017Factor2572 : RatPair2542 := ((((((18287110242590252447880554564 * 10^40
        + 3096719781200154055536277499850834687716) * 10^40
        + 9868174371958028754305932466956652974581) * 10^40
        + 2972738437505500261821781699491681895093) : ℚ) /
        (((1450806976117078933368 * 10^40
        + 6938549699731298507206310750329531504355) * 10^40
        + 7684528508351137377988959013790724929283) * 10^40
        + 1232558896135239476356436601016636209814)),
    (((-6756124363134027) : ℚ) /
        140737488355328))

noncomputable def fjcmP017Error2572 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjcmP017BaseError2572 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨17, by omega⟩
      corrC02701MinusMidpointPosition2572 - embedPair2542 fjcmP017Center2572‖ ≤ fjcmP017Error2572
          := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨17, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hz : ‖embedPair2542 fjcmP017Input2572‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjcmP017Input2572]
  have hc : (compactExp2547 fjcmP017Input2572 15).1 = fjcmP017Center2572 := by cbv
  have he : ((compactExp2547 fjcmP017Input2572 15).2 : ℝ) = fjcmP017Error2572 := by
    have hq : (compactExp2547 fjcmP017Input2572 15).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjcmP017Error2572]
  have h := compactExp_error2547 fjcmP017Input2572 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨17, by omega⟩
      corrC02701MinusMidpointPosition2572 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          fjcmP017Input2572) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrC02701MinusMidpointPosition2572, storedWidth,
      nodeModulation2541, embedPair2542, fjcmP017Input2572, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjcmP017DerivativeError2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨17, by omega⟩
      corrC02701MinusMidpointPosition2572 -
      embedPair2542 fjcmP017Factor2572 * embedPair2542 fjcmP017Center2572‖ ≤
        (pairMagnitude2542 fjcmP017Factor2572 : ℝ) * fjcmP017Error2572 := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨17, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hf : weightedMultiplier2543 1 (-1/2)
      (nodeModulation2541 ⟨17, by omega⟩)
      (storedWidth ⟨17, by omega⟩ ^ 2) corrC02701MinusMidpointPosition2572 =
      embedPair2542 fjcmP017Factor2572 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrC02701MinusMidpointPosition2572, storedWidth, nodeModulation2541, embedPair2542,
      fjcmP017Factor2572, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (-1/2)
    (nodeModulation2541 ⟨17, by omega⟩) (pow_pos (storedWidth_pos ⟨17, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjcmP017BaseError2572
    (embedPair_magnitude2542 fjcmP017Factor2572)

def fjcmP017Rounded2572 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjcmP017Radius2572 : ℝ := ((2199023255577 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjcmP017RoundCompute2572 :
    pairRound2542 (pairMul2542 fjcmP017Factor2572 fjcmP017Center2572) = fjcmP017Rounded2572 := by
  cbv

theorem fjcmP017RoundedError2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨17, by omega⟩
      corrC02701MinusMidpointPosition2572 - embedPair2542 fjcmP017Rounded2572‖ ≤
          fjcmP017Radius2572 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjcmP017Factor2572 fjcmP017Center2572)
  rw [fjcmP017RoundCompute2572, embedPair_mul2542] at hr
  have h := (firstJetCorrMinus_triangle2572
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨17, by omega⟩
      corrC02701MinusMidpointPosition2572)
    (embedPair2542 fjcmP017Factor2572 * embedPair2542 fjcmP017Center2572)
    (embedPair2542 fjcmP017Rounded2572)).trans (add_le_add fjcmP017DerivativeError2572 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjcmP017Factor2572, fjcmP017Error2572, rounding2542,
      fjcmP017Radius2572]

theorem fjcmP017DerivativeNorm2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨17, by omega⟩
      corrC02701MinusMidpointPosition2572‖ ≤ 1 := by
  have h := firstJetCorrMinus_triangle2572
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨17, by omega⟩
      corrC02701MinusMidpointPosition2572)
    (embedPair2542 fjcmP017Rounded2572) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjcmP017RoundedError2572 (embedPair_magnitude2542
      fjcmP017Rounded2572))
  apply h'.trans
  norm_num [fjcmP017Radius2572, pairMagnitude2542, fjcmP017Rounded2572]

noncomputable def fjcmP018Input2572 : RatPair2542 := ((((-((770889 * 10^40
        + 3381634557173160365454331760519832708453) * 10^40
        + 8445081731115744698509100587432038911481)) : ℚ) /
        ((1043539 * 10^40
        + 9494850363077843158719362614051723272667) * 10^40
        + 9765981577832661801082496535756800000000)),
    ((555145611856273095972878081 : ℚ) /
        118059162071741130342400000000))

def fjcmP018Center2572 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjcmP018Factor2572 : RatPair2542 := ((((((18287110242590252447880554564 * 10^40
        + 3096719781200154055536277499850834687716) * 10^40
        + 9868174371958028754305932466956652974581) * 10^40
        + 2972738437505500261821781699491681895093) : ℚ) /
        (((1450806976117078933368 * 10^40
        + 6938549699731298507206310750329531504355) * 10^40
        + 7684528508351137377988959013790724929283) * 10^40
        + 1232558896135239476356436601016636209814)),
    (((-1751261042181613) : ℚ) /
        35184372088832))

noncomputable def fjcmP018Error2572 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjcmP018BaseError2572 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨18, by omega⟩
      corrC02701MinusMidpointPosition2572 - embedPair2542 fjcmP018Center2572‖ ≤ fjcmP018Error2572
          := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨18, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hz : ‖embedPair2542 fjcmP018Input2572‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjcmP018Input2572]
  have hc : (compactExp2547 fjcmP018Input2572 15).1 = fjcmP018Center2572 := by cbv
  have he : ((compactExp2547 fjcmP018Input2572 15).2 : ℝ) = fjcmP018Error2572 := by
    have hq : (compactExp2547 fjcmP018Input2572 15).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjcmP018Error2572]
  have h := compactExp_error2547 fjcmP018Input2572 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨18, by omega⟩
      corrC02701MinusMidpointPosition2572 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          fjcmP018Input2572) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrC02701MinusMidpointPosition2572, storedWidth,
      nodeModulation2541, embedPair2542, fjcmP018Input2572, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjcmP018DerivativeError2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨18, by omega⟩
      corrC02701MinusMidpointPosition2572 -
      embedPair2542 fjcmP018Factor2572 * embedPair2542 fjcmP018Center2572‖ ≤
        (pairMagnitude2542 fjcmP018Factor2572 : ℝ) * fjcmP018Error2572 := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨18, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hf : weightedMultiplier2543 1 (-1/2)
      (nodeModulation2541 ⟨18, by omega⟩)
      (storedWidth ⟨18, by omega⟩ ^ 2) corrC02701MinusMidpointPosition2572 =
      embedPair2542 fjcmP018Factor2572 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrC02701MinusMidpointPosition2572, storedWidth, nodeModulation2541, embedPair2542,
      fjcmP018Factor2572, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (-1/2)
    (nodeModulation2541 ⟨18, by omega⟩) (pow_pos (storedWidth_pos ⟨18, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjcmP018BaseError2572
    (embedPair_magnitude2542 fjcmP018Factor2572)

def fjcmP018Rounded2572 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjcmP018Radius2572 : ℝ := ((2199023255577 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjcmP018RoundCompute2572 :
    pairRound2542 (pairMul2542 fjcmP018Factor2572 fjcmP018Center2572) = fjcmP018Rounded2572 := by
  cbv

theorem fjcmP018RoundedError2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨18, by omega⟩
      corrC02701MinusMidpointPosition2572 - embedPair2542 fjcmP018Rounded2572‖ ≤
          fjcmP018Radius2572 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjcmP018Factor2572 fjcmP018Center2572)
  rw [fjcmP018RoundCompute2572, embedPair_mul2542] at hr
  have h := (firstJetCorrMinus_triangle2572
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨18, by omega⟩
      corrC02701MinusMidpointPosition2572)
    (embedPair2542 fjcmP018Factor2572 * embedPair2542 fjcmP018Center2572)
    (embedPair2542 fjcmP018Rounded2572)).trans (add_le_add fjcmP018DerivativeError2572 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjcmP018Factor2572, fjcmP018Error2572, rounding2542,
      fjcmP018Radius2572]

theorem fjcmP018DerivativeNorm2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨18, by omega⟩
      corrC02701MinusMidpointPosition2572‖ ≤ 1 := by
  have h := firstJetCorrMinus_triangle2572
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨18, by omega⟩
      corrC02701MinusMidpointPosition2572)
    (embedPair2542 fjcmP018Rounded2572) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjcmP018RoundedError2572 (embedPair_magnitude2542
      fjcmP018Rounded2572))
  apply h'.trans
  norm_num [fjcmP018Radius2572, pairMagnitude2542, fjcmP018Rounded2572]

noncomputable def fjcmP019Input2572 : RatPair2542 := ((((-((770889 * 10^40
        + 3381634557173160365454331760519832708453) * 10^40
        + 8445081731115744698509100587432038911481)) : ℚ) /
        ((1043539 * 10^40
        + 9494850363077843158719362614051723272667) * 10^40
        + 9765981577832661801082496535756800000000)),
    ((118159442675668676717562267 : ℚ) /
        23611832414348226068480000000))

def fjcmP019Center2572 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjcmP019Factor2572 : RatPair2542 := ((((((18287110242590252447880554564 * 10^40
        + 3096719781200154055536277499850834687716) * 10^40
        + 9868174371958028754305932466956652974581) * 10^40
        + 2972738437505500261821781699491681895093) : ℚ) /
        (((1450806976117078933368 * 10^40
        + 6938549699731298507206310750329531504355) * 10^40
        + 7684528508351137377988959013790724929283) * 10^40
        + 1232558896135239476356436601016636209814)),
    (((-1863727500536955) : ℚ) /
        35184372088832))

noncomputable def fjcmP019Error2572 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjcmP019BaseError2572 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨19, by omega⟩
      corrC02701MinusMidpointPosition2572 - embedPair2542 fjcmP019Center2572‖ ≤ fjcmP019Error2572
          := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨19, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hz : ‖embedPair2542 fjcmP019Input2572‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjcmP019Input2572]
  have hc : (compactExp2547 fjcmP019Input2572 15).1 = fjcmP019Center2572 := by cbv
  have he : ((compactExp2547 fjcmP019Input2572 15).2 : ℝ) = fjcmP019Error2572 := by
    have hq : (compactExp2547 fjcmP019Input2572 15).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjcmP019Error2572]
  have h := compactExp_error2547 fjcmP019Input2572 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨19, by omega⟩
      corrC02701MinusMidpointPosition2572 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          fjcmP019Input2572) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrC02701MinusMidpointPosition2572, storedWidth,
      nodeModulation2541, embedPair2542, fjcmP019Input2572, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjcmP019DerivativeError2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨19, by omega⟩
      corrC02701MinusMidpointPosition2572 -
      embedPair2542 fjcmP019Factor2572 * embedPair2542 fjcmP019Center2572‖ ≤
        (pairMagnitude2542 fjcmP019Factor2572 : ℝ) * fjcmP019Error2572 := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨19, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hf : weightedMultiplier2543 1 (-1/2)
      (nodeModulation2541 ⟨19, by omega⟩)
      (storedWidth ⟨19, by omega⟩ ^ 2) corrC02701MinusMidpointPosition2572 =
      embedPair2542 fjcmP019Factor2572 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrC02701MinusMidpointPosition2572, storedWidth, nodeModulation2541, embedPair2542,
      fjcmP019Factor2572, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (-1/2)
    (nodeModulation2541 ⟨19, by omega⟩) (pow_pos (storedWidth_pos ⟨19, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjcmP019BaseError2572
    (embedPair_magnitude2542 fjcmP019Factor2572)

def fjcmP019Rounded2572 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjcmP019Radius2572 : ℝ := ((2199023255577 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjcmP019RoundCompute2572 :
    pairRound2542 (pairMul2542 fjcmP019Factor2572 fjcmP019Center2572) = fjcmP019Rounded2572 := by
  cbv

theorem fjcmP019RoundedError2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨19, by omega⟩
      corrC02701MinusMidpointPosition2572 - embedPair2542 fjcmP019Rounded2572‖ ≤
          fjcmP019Radius2572 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjcmP019Factor2572 fjcmP019Center2572)
  rw [fjcmP019RoundCompute2572, embedPair_mul2542] at hr
  have h := (firstJetCorrMinus_triangle2572
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨19, by omega⟩
      corrC02701MinusMidpointPosition2572)
    (embedPair2542 fjcmP019Factor2572 * embedPair2542 fjcmP019Center2572)
    (embedPair2542 fjcmP019Rounded2572)).trans (add_le_add fjcmP019DerivativeError2572 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjcmP019Factor2572, fjcmP019Error2572, rounding2542,
      fjcmP019Radius2572]

theorem fjcmP019DerivativeNorm2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨19, by omega⟩
      corrC02701MinusMidpointPosition2572‖ ≤ 1 := by
  have h := firstJetCorrMinus_triangle2572
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨19, by omega⟩
      corrC02701MinusMidpointPosition2572)
    (embedPair2542 fjcmP019Rounded2572) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjcmP019RoundedError2572 (embedPair_magnitude2542
      fjcmP019Rounded2572))
  apply h'.trans
  norm_num [fjcmP019Radius2572, pairMagnitude2542, fjcmP019Rounded2572]

noncomputable def fjcmP020Input2572 : RatPair2542 := ((((-((770889 * 10^40
        + 3381634557173160365454331760519832708453) * 10^40
        + 8445081731115744698509100587432038911481)) : ℚ) /
        ((1043539 * 10^40
        + 9494850363077843158719362614051723272667) * 10^40
        + 9765981577832661801082496535756800000000)),
    ((2518261918355091626130213703 : ℚ) /
        472236648286964521369600000000))

def fjcmP020Center2572 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjcmP020Factor2572 : RatPair2542 := ((((((18287110242590252447880554564 * 10^40
        + 3096719781200154055536277499850834687716) * 10^40
        + 9868174371958028754305932466956652974581) * 10^40
        + 2972738437505500261821781699491681895093) : ℚ) /
        (((1450806976117078933368 * 10^40
        + 6938549699731298507206310750329531504355) * 10^40
        + 7684528508351137377988959013790724929283) * 10^40
        + 1232558896135239476356436601016636209814)),
    (((-7944103127967419) : ℚ) /
        140737488355328))

noncomputable def fjcmP020Error2572 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjcmP020BaseError2572 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨20, by omega⟩
      corrC02701MinusMidpointPosition2572 - embedPair2542 fjcmP020Center2572‖ ≤ fjcmP020Error2572
          := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨20, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hz : ‖embedPair2542 fjcmP020Input2572‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjcmP020Input2572]
  have hc : (compactExp2547 fjcmP020Input2572 15).1 = fjcmP020Center2572 := by cbv
  have he : ((compactExp2547 fjcmP020Input2572 15).2 : ℝ) = fjcmP020Error2572 := by
    have hq : (compactExp2547 fjcmP020Input2572 15).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjcmP020Error2572]
  have h := compactExp_error2547 fjcmP020Input2572 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨20, by omega⟩
      corrC02701MinusMidpointPosition2572 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          fjcmP020Input2572) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrC02701MinusMidpointPosition2572, storedWidth,
      nodeModulation2541, embedPair2542, fjcmP020Input2572, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjcmP020DerivativeError2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨20, by omega⟩
      corrC02701MinusMidpointPosition2572 -
      embedPair2542 fjcmP020Factor2572 * embedPair2542 fjcmP020Center2572‖ ≤
        (pairMagnitude2542 fjcmP020Factor2572 : ℝ) * fjcmP020Error2572 := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨20, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hf : weightedMultiplier2543 1 (-1/2)
      (nodeModulation2541 ⟨20, by omega⟩)
      (storedWidth ⟨20, by omega⟩ ^ 2) corrC02701MinusMidpointPosition2572 =
      embedPair2542 fjcmP020Factor2572 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrC02701MinusMidpointPosition2572, storedWidth, nodeModulation2541, embedPair2542,
      fjcmP020Factor2572, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (-1/2)
    (nodeModulation2541 ⟨20, by omega⟩) (pow_pos (storedWidth_pos ⟨20, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjcmP020BaseError2572
    (embedPair_magnitude2542 fjcmP020Factor2572)

def fjcmP020Rounded2572 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjcmP020Radius2572 : ℝ := ((2199023255577 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjcmP020RoundCompute2572 :
    pairRound2542 (pairMul2542 fjcmP020Factor2572 fjcmP020Center2572) = fjcmP020Rounded2572 := by
  cbv

theorem fjcmP020RoundedError2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨20, by omega⟩
      corrC02701MinusMidpointPosition2572 - embedPair2542 fjcmP020Rounded2572‖ ≤
          fjcmP020Radius2572 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjcmP020Factor2572 fjcmP020Center2572)
  rw [fjcmP020RoundCompute2572, embedPair_mul2542] at hr
  have h := (firstJetCorrMinus_triangle2572
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨20, by omega⟩
      corrC02701MinusMidpointPosition2572)
    (embedPair2542 fjcmP020Factor2572 * embedPair2542 fjcmP020Center2572)
    (embedPair2542 fjcmP020Rounded2572)).trans (add_le_add fjcmP020DerivativeError2572 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjcmP020Factor2572, fjcmP020Error2572, rounding2542,
      fjcmP020Radius2572]

theorem fjcmP020DerivativeNorm2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨20, by omega⟩
      corrC02701MinusMidpointPosition2572‖ ≤ 1 := by
  have h := firstJetCorrMinus_triangle2572
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨20, by omega⟩
      corrC02701MinusMidpointPosition2572)
    (embedPair2542 fjcmP020Rounded2572) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjcmP020RoundedError2572 (embedPair_magnitude2542
      fjcmP020Rounded2572))
  apply h'.trans
  norm_num [fjcmP020Radius2572, pairMagnitude2542, fjcmP020Rounded2572]

noncomputable def fjcmP021Input2572 : RatPair2542 := ((((-((770889 * 10^40
        + 3381634557173160365454331760519832708453) * 10^40
        + 8445081731115744698509100587432038911481)) : ℚ) /
        ((1043539 * 10^40
        + 9494850363077843158719362614051723272667) * 10^40
        + 9765981577832661801082496535756800000000)),
    ((2647676452840152643307498919 : ℚ) /
        472236648286964521369600000000))

def fjcmP021Center2572 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjcmP021Factor2572 : RatPair2542 := ((((((18287110242590252447880554564 * 10^40
        + 3096719781200154055536277499850834687716) * 10^40
        + 9868174371958028754305932466956652974581) * 10^40
        + 2972738437505500261821781699491681895093) : ℚ) /
        (((1450806976117078933368 * 10^40
        + 6938549699731298507206310750329531504355) * 10^40
        + 7684528508351137377988959013790724929283) * 10^40
        + 1232558896135239476356436601016636209814)),
    (((-8352353914239387) : ℚ) /
        140737488355328))

noncomputable def fjcmP021Error2572 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjcmP021BaseError2572 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨21, by omega⟩
      corrC02701MinusMidpointPosition2572 - embedPair2542 fjcmP021Center2572‖ ≤ fjcmP021Error2572
          := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨21, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hz : ‖embedPair2542 fjcmP021Input2572‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjcmP021Input2572]
  have hc : (compactExp2547 fjcmP021Input2572 15).1 = fjcmP021Center2572 := by cbv
  have he : ((compactExp2547 fjcmP021Input2572 15).2 : ℝ) = fjcmP021Error2572 := by
    have hq : (compactExp2547 fjcmP021Input2572 15).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjcmP021Error2572]
  have h := compactExp_error2547 fjcmP021Input2572 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨21, by omega⟩
      corrC02701MinusMidpointPosition2572 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          fjcmP021Input2572) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrC02701MinusMidpointPosition2572, storedWidth,
      nodeModulation2541, embedPair2542, fjcmP021Input2572, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjcmP021DerivativeError2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨21, by omega⟩
      corrC02701MinusMidpointPosition2572 -
      embedPair2542 fjcmP021Factor2572 * embedPair2542 fjcmP021Center2572‖ ≤
        (pairMagnitude2542 fjcmP021Factor2572 : ℝ) * fjcmP021Error2572 := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨21, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hf : weightedMultiplier2543 1 (-1/2)
      (nodeModulation2541 ⟨21, by omega⟩)
      (storedWidth ⟨21, by omega⟩ ^ 2) corrC02701MinusMidpointPosition2572 =
      embedPair2542 fjcmP021Factor2572 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrC02701MinusMidpointPosition2572, storedWidth, nodeModulation2541, embedPair2542,
      fjcmP021Factor2572, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (-1/2)
    (nodeModulation2541 ⟨21, by omega⟩) (pow_pos (storedWidth_pos ⟨21, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjcmP021BaseError2572
    (embedPair_magnitude2542 fjcmP021Factor2572)

def fjcmP021Rounded2572 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjcmP021Radius2572 : ℝ := ((2199023255577 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjcmP021RoundCompute2572 :
    pairRound2542 (pairMul2542 fjcmP021Factor2572 fjcmP021Center2572) = fjcmP021Rounded2572 := by
  cbv

theorem fjcmP021RoundedError2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨21, by omega⟩
      corrC02701MinusMidpointPosition2572 - embedPair2542 fjcmP021Rounded2572‖ ≤
          fjcmP021Radius2572 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjcmP021Factor2572 fjcmP021Center2572)
  rw [fjcmP021RoundCompute2572, embedPair_mul2542] at hr
  have h := (firstJetCorrMinus_triangle2572
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨21, by omega⟩
      corrC02701MinusMidpointPosition2572)
    (embedPair2542 fjcmP021Factor2572 * embedPair2542 fjcmP021Center2572)
    (embedPair2542 fjcmP021Rounded2572)).trans (add_le_add fjcmP021DerivativeError2572 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjcmP021Factor2572, fjcmP021Error2572, rounding2542,
      fjcmP021Radius2572]

theorem fjcmP021DerivativeNorm2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨21, by omega⟩
      corrC02701MinusMidpointPosition2572‖ ≤ 1 := by
  have h := firstJetCorrMinus_triangle2572
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨21, by omega⟩
      corrC02701MinusMidpointPosition2572)
    (embedPair2542 fjcmP021Rounded2572) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjcmP021RoundedError2572 (embedPair_magnitude2542
      fjcmP021Rounded2572))
  apply h'.trans
  norm_num [fjcmP021Radius2572, pairMagnitude2542, fjcmP021Rounded2572]

noncomputable def fjcmP022Input2572 : RatPair2542 := ((((-((770889 * 10^40
        + 3381634557173160365454331760519832708453) * 10^40
        + 8445081731115744698509100587432038911481)) : ℚ) /
        ((1043539 * 10^40
        + 9494850363077843158719362614051723272667) * 10^40
        + 9765981577832661801082496535756800000000)),
    ((542783116803371403996659021 : ℚ) /
        94447329657392904273920000000))

def fjcmP022Center2572 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjcmP022Factor2572 : RatPair2542 := ((((((18287110242590252447880554564 * 10^40
        + 3096719781200154055536277499850834687716) * 10^40
        + 9868174371958028754305932466956652974581) * 10^40
        + 2972738437505500261821781699491681895093) : ℚ) /
        (((1450806976117078933368 * 10^40
        + 6938549699731298507206310750329531504355) * 10^40
        + 7684528508351137377988959013790724929283) * 10^40
        + 1232558896135239476356436601016636209814)),
    (((-8561311721741165) : ℚ) /
        140737488355328))

noncomputable def fjcmP022Error2572 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjcmP022BaseError2572 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨22, by omega⟩
      corrC02701MinusMidpointPosition2572 - embedPair2542 fjcmP022Center2572‖ ≤ fjcmP022Error2572
          := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨22, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hz : ‖embedPair2542 fjcmP022Input2572‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjcmP022Input2572]
  have hc : (compactExp2547 fjcmP022Input2572 15).1 = fjcmP022Center2572 := by cbv
  have he : ((compactExp2547 fjcmP022Input2572 15).2 : ℝ) = fjcmP022Error2572 := by
    have hq : (compactExp2547 fjcmP022Input2572 15).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjcmP022Error2572]
  have h := compactExp_error2547 fjcmP022Input2572 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨22, by omega⟩
      corrC02701MinusMidpointPosition2572 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          fjcmP022Input2572) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrC02701MinusMidpointPosition2572, storedWidth,
      nodeModulation2541, embedPair2542, fjcmP022Input2572, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjcmP022DerivativeError2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨22, by omega⟩
      corrC02701MinusMidpointPosition2572 -
      embedPair2542 fjcmP022Factor2572 * embedPair2542 fjcmP022Center2572‖ ≤
        (pairMagnitude2542 fjcmP022Factor2572 : ℝ) * fjcmP022Error2572 := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨22, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hf : weightedMultiplier2543 1 (-1/2)
      (nodeModulation2541 ⟨22, by omega⟩)
      (storedWidth ⟨22, by omega⟩ ^ 2) corrC02701MinusMidpointPosition2572 =
      embedPair2542 fjcmP022Factor2572 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrC02701MinusMidpointPosition2572, storedWidth, nodeModulation2541, embedPair2542,
      fjcmP022Factor2572, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (-1/2)
    (nodeModulation2541 ⟨22, by omega⟩) (pow_pos (storedWidth_pos ⟨22, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjcmP022BaseError2572
    (embedPair_magnitude2542 fjcmP022Factor2572)

def fjcmP022Rounded2572 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjcmP022Radius2572 : ℝ := ((2199023255577 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjcmP022RoundCompute2572 :
    pairRound2542 (pairMul2542 fjcmP022Factor2572 fjcmP022Center2572) = fjcmP022Rounded2572 := by
  cbv

theorem fjcmP022RoundedError2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨22, by omega⟩
      corrC02701MinusMidpointPosition2572 - embedPair2542 fjcmP022Rounded2572‖ ≤
          fjcmP022Radius2572 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjcmP022Factor2572 fjcmP022Center2572)
  rw [fjcmP022RoundCompute2572, embedPair_mul2542] at hr
  have h := (firstJetCorrMinus_triangle2572
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨22, by omega⟩
      corrC02701MinusMidpointPosition2572)
    (embedPair2542 fjcmP022Factor2572 * embedPair2542 fjcmP022Center2572)
    (embedPair2542 fjcmP022Rounded2572)).trans (add_le_add fjcmP022DerivativeError2572 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjcmP022Factor2572, fjcmP022Error2572, rounding2542,
      fjcmP022Radius2572]

theorem fjcmP022DerivativeNorm2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨22, by omega⟩
      corrC02701MinusMidpointPosition2572‖ ≤ 1 := by
  have h := firstJetCorrMinus_triangle2572
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨22, by omega⟩
      corrC02701MinusMidpointPosition2572)
    (embedPair2542 fjcmP022Rounded2572) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjcmP022RoundedError2572 (embedPair_magnitude2542
      fjcmP022Rounded2572))
  apply h'.trans
  norm_num [fjcmP022Radius2572, pairMagnitude2542, fjcmP022Rounded2572]

noncomputable def fjcmP023Input2572 : RatPair2542 := ((((-((770889 * 10^40
        + 3381634557173160365454331760519832708453) * 10^40
        + 8445081731115744698509100587432038911481)) : ℚ) /
        ((1043539 * 10^40
        + 9494850363077843158719362614051723272667) * 10^40
        + 9765981577832661801082496535756800000000)),
    ((1452447653947712451580278721 : ℚ) /
        236118324143482260684800000000))

def fjcmP023Center2572 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjcmP023Factor2572 : RatPair2542 := ((((((18287110242590252447880554564 * 10^40
        + 3096719781200154055536277499850834687716) * 10^40
        + 9868174371958028754305932466956652974581) * 10^40
        + 2972738437505500261821781699491681895093) : ℚ) /
        (((1450806976117078933368 * 10^40
        + 6938549699731298507206310750329531504355) * 10^40
        + 7684528508351137377988959013790724929283) * 10^40
        + 1232558896135239476356436601016636209814)),
    (((-4581887954876333) : ℚ) /
        70368744177664))

noncomputable def fjcmP023Error2572 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjcmP023BaseError2572 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨23, by omega⟩
      corrC02701MinusMidpointPosition2572 - embedPair2542 fjcmP023Center2572‖ ≤ fjcmP023Error2572
          := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨23, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hz : ‖embedPair2542 fjcmP023Input2572‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjcmP023Input2572]
  have hc : (compactExp2547 fjcmP023Input2572 15).1 = fjcmP023Center2572 := by cbv
  have he : ((compactExp2547 fjcmP023Input2572 15).2 : ℝ) = fjcmP023Error2572 := by
    have hq : (compactExp2547 fjcmP023Input2572 15).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjcmP023Error2572]
  have h := compactExp_error2547 fjcmP023Input2572 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨23, by omega⟩
      corrC02701MinusMidpointPosition2572 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          fjcmP023Input2572) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrC02701MinusMidpointPosition2572, storedWidth,
      nodeModulation2541, embedPair2542, fjcmP023Input2572, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjcmP023DerivativeError2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨23, by omega⟩
      corrC02701MinusMidpointPosition2572 -
      embedPair2542 fjcmP023Factor2572 * embedPair2542 fjcmP023Center2572‖ ≤
        (pairMagnitude2542 fjcmP023Factor2572 : ℝ) * fjcmP023Error2572 := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨23, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hf : weightedMultiplier2543 1 (-1/2)
      (nodeModulation2541 ⟨23, by omega⟩)
      (storedWidth ⟨23, by omega⟩ ^ 2) corrC02701MinusMidpointPosition2572 =
      embedPair2542 fjcmP023Factor2572 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrC02701MinusMidpointPosition2572, storedWidth, nodeModulation2541, embedPair2542,
      fjcmP023Factor2572, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (-1/2)
    (nodeModulation2541 ⟨23, by omega⟩) (pow_pos (storedWidth_pos ⟨23, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjcmP023BaseError2572
    (embedPair_magnitude2542 fjcmP023Factor2572)

def fjcmP023Rounded2572 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjcmP023Radius2572 : ℝ := ((2199023255577 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjcmP023RoundCompute2572 :
    pairRound2542 (pairMul2542 fjcmP023Factor2572 fjcmP023Center2572) = fjcmP023Rounded2572 := by
  cbv

theorem fjcmP023RoundedError2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨23, by omega⟩
      corrC02701MinusMidpointPosition2572 - embedPair2542 fjcmP023Rounded2572‖ ≤
          fjcmP023Radius2572 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjcmP023Factor2572 fjcmP023Center2572)
  rw [fjcmP023RoundCompute2572, embedPair_mul2542] at hr
  have h := (firstJetCorrMinus_triangle2572
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨23, by omega⟩
      corrC02701MinusMidpointPosition2572)
    (embedPair2542 fjcmP023Factor2572 * embedPair2542 fjcmP023Center2572)
    (embedPair2542 fjcmP023Rounded2572)).trans (add_le_add fjcmP023DerivativeError2572 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjcmP023Factor2572, fjcmP023Error2572, rounding2542,
      fjcmP023Radius2572]

theorem fjcmP023DerivativeNorm2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨23, by omega⟩
      corrC02701MinusMidpointPosition2572‖ ≤ 1 := by
  have h := firstJetCorrMinus_triangle2572
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨23, by omega⟩
      corrC02701MinusMidpointPosition2572)
    (embedPair2542 fjcmP023Rounded2572) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjcmP023RoundedError2572 (embedPair_magnitude2542
      fjcmP023Rounded2572))
  apply h'.trans
  norm_num [fjcmP023Radius2572, pairMagnitude2542, fjcmP023Rounded2572]

noncomputable def fjcmP024Input2572 : RatPair2542 := ((((-((770889 * 10^40
        + 3381634557173160365454331760519832708453) * 10^40
        + 8445081731115744698509100587432038911481)) : ℚ) /
        ((1043539 * 10^40
        + 9494850363077843158719362614051723272667) * 10^40
        + 9765981577832661801082496535756800000000)),
    ((1496330927553297167442947039 : ℚ) /
        236118324143482260684800000000))

def fjcmP024Center2572 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjcmP024Factor2572 : RatPair2542 := ((((((18287110242590252447880554564 * 10^40
        + 3096719781200154055536277499850834687716) * 10^40
        + 9868174371958028754305932466956652974581) * 10^40
        + 2972738437505500261821781699491681895093) : ℚ) /
        (((1450806976117078933368 * 10^40
        + 6938549699731298507206310750329531504355) * 10^40
        + 7684528508351137377988959013790724929283) * 10^40
        + 1232558896135239476356436601016636209814)),
    (((-4720322026636147) : ℚ) /
        70368744177664))

noncomputable def fjcmP024Error2572 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjcmP024BaseError2572 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨24, by omega⟩
      corrC02701MinusMidpointPosition2572 - embedPair2542 fjcmP024Center2572‖ ≤ fjcmP024Error2572
          := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨24, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hz : ‖embedPair2542 fjcmP024Input2572‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjcmP024Input2572]
  have hc : (compactExp2547 fjcmP024Input2572 15).1 = fjcmP024Center2572 := by cbv
  have he : ((compactExp2547 fjcmP024Input2572 15).2 : ℝ) = fjcmP024Error2572 := by
    have hq : (compactExp2547 fjcmP024Input2572 15).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjcmP024Error2572]
  have h := compactExp_error2547 fjcmP024Input2572 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨24, by omega⟩
      corrC02701MinusMidpointPosition2572 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          fjcmP024Input2572) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrC02701MinusMidpointPosition2572, storedWidth,
      nodeModulation2541, embedPair2542, fjcmP024Input2572, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjcmP024DerivativeError2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨24, by omega⟩
      corrC02701MinusMidpointPosition2572 -
      embedPair2542 fjcmP024Factor2572 * embedPair2542 fjcmP024Center2572‖ ≤
        (pairMagnitude2542 fjcmP024Factor2572 : ℝ) * fjcmP024Error2572 := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨24, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hf : weightedMultiplier2543 1 (-1/2)
      (nodeModulation2541 ⟨24, by omega⟩)
      (storedWidth ⟨24, by omega⟩ ^ 2) corrC02701MinusMidpointPosition2572 =
      embedPair2542 fjcmP024Factor2572 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrC02701MinusMidpointPosition2572, storedWidth, nodeModulation2541, embedPair2542,
      fjcmP024Factor2572, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (-1/2)
    (nodeModulation2541 ⟨24, by omega⟩) (pow_pos (storedWidth_pos ⟨24, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjcmP024BaseError2572
    (embedPair_magnitude2542 fjcmP024Factor2572)

def fjcmP024Rounded2572 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjcmP024Radius2572 : ℝ := ((2199023255577 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjcmP024RoundCompute2572 :
    pairRound2542 (pairMul2542 fjcmP024Factor2572 fjcmP024Center2572) = fjcmP024Rounded2572 := by
  cbv

theorem fjcmP024RoundedError2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨24, by omega⟩
      corrC02701MinusMidpointPosition2572 - embedPair2542 fjcmP024Rounded2572‖ ≤
          fjcmP024Radius2572 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjcmP024Factor2572 fjcmP024Center2572)
  rw [fjcmP024RoundCompute2572, embedPair_mul2542] at hr
  have h := (firstJetCorrMinus_triangle2572
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨24, by omega⟩
      corrC02701MinusMidpointPosition2572)
    (embedPair2542 fjcmP024Factor2572 * embedPair2542 fjcmP024Center2572)
    (embedPair2542 fjcmP024Rounded2572)).trans (add_le_add fjcmP024DerivativeError2572 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjcmP024Factor2572, fjcmP024Error2572, rounding2542,
      fjcmP024Radius2572]

theorem fjcmP024DerivativeNorm2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨24, by omega⟩
      corrC02701MinusMidpointPosition2572‖ ≤ 1 := by
  have h := firstJetCorrMinus_triangle2572
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨24, by omega⟩
      corrC02701MinusMidpointPosition2572)
    (embedPair2542 fjcmP024Rounded2572) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjcmP024RoundedError2572 (embedPair_magnitude2542
      fjcmP024Rounded2572))
  apply h'.trans
  norm_num [fjcmP024Radius2572, pairMagnitude2542, fjcmP024Rounded2572]

noncomputable def fjcmP025Input2572 : RatPair2542 := ((((-((770889 * 10^40
        + 3381634557173160365454331760519832708453) * 10^40
        + 8445081731115744698509100587432038911481)) : ℚ) /
        ((1043539 * 10^40
        + 9494850363077843158719362614051723272667) * 10^40
        + 9765981577832661801082496535756800000000)),
    ((48479765632462230989059221 : ℚ) /
        7378697629483820646400000000))

def fjcmP025Center2572 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjcmP025Factor2572 : RatPair2542 := ((((((18287110242590252447880554564 * 10^40
        + 3096719781200154055536277499850834687716) * 10^40
        + 9868174371958028754305932466956652974581) * 10^40
        + 2972738437505500261821781699491681895093) : ℚ) /
        (((1450806976117078933368 * 10^40
        + 6938549699731298507206310750329531504355) * 10^40
        + 7684528508351137377988959013790724929283) * 10^40
        + 1232558896135239476356436601016636209814)),
    (((-152934154702833) : ℚ) /
        2199023255552))

noncomputable def fjcmP025Error2572 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjcmP025BaseError2572 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨25, by omega⟩
      corrC02701MinusMidpointPosition2572 - embedPair2542 fjcmP025Center2572‖ ≤ fjcmP025Error2572
          := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨25, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hz : ‖embedPair2542 fjcmP025Input2572‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjcmP025Input2572]
  have hc : (compactExp2547 fjcmP025Input2572 15).1 = fjcmP025Center2572 := by cbv
  have he : ((compactExp2547 fjcmP025Input2572 15).2 : ℝ) = fjcmP025Error2572 := by
    have hq : (compactExp2547 fjcmP025Input2572 15).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjcmP025Error2572]
  have h := compactExp_error2547 fjcmP025Input2572 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨25, by omega⟩
      corrC02701MinusMidpointPosition2572 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          fjcmP025Input2572) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrC02701MinusMidpointPosition2572, storedWidth,
      nodeModulation2541, embedPair2542, fjcmP025Input2572, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjcmP025DerivativeError2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨25, by omega⟩
      corrC02701MinusMidpointPosition2572 -
      embedPair2542 fjcmP025Factor2572 * embedPair2542 fjcmP025Center2572‖ ≤
        (pairMagnitude2542 fjcmP025Factor2572 : ℝ) * fjcmP025Error2572 := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨25, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hf : weightedMultiplier2543 1 (-1/2)
      (nodeModulation2541 ⟨25, by omega⟩)
      (storedWidth ⟨25, by omega⟩ ^ 2) corrC02701MinusMidpointPosition2572 =
      embedPair2542 fjcmP025Factor2572 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrC02701MinusMidpointPosition2572, storedWidth, nodeModulation2541, embedPair2542,
      fjcmP025Factor2572, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (-1/2)
    (nodeModulation2541 ⟨25, by omega⟩) (pow_pos (storedWidth_pos ⟨25, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjcmP025BaseError2572
    (embedPair_magnitude2542 fjcmP025Factor2572)

def fjcmP025Rounded2572 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjcmP025Radius2572 : ℝ := ((2199023255577 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjcmP025RoundCompute2572 :
    pairRound2542 (pairMul2542 fjcmP025Factor2572 fjcmP025Center2572) = fjcmP025Rounded2572 := by
  cbv

theorem fjcmP025RoundedError2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨25, by omega⟩
      corrC02701MinusMidpointPosition2572 - embedPair2542 fjcmP025Rounded2572‖ ≤
          fjcmP025Radius2572 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjcmP025Factor2572 fjcmP025Center2572)
  rw [fjcmP025RoundCompute2572, embedPair_mul2542] at hr
  have h := (firstJetCorrMinus_triangle2572
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨25, by omega⟩
      corrC02701MinusMidpointPosition2572)
    (embedPair2542 fjcmP025Factor2572 * embedPair2542 fjcmP025Center2572)
    (embedPair2542 fjcmP025Rounded2572)).trans (add_le_add fjcmP025DerivativeError2572 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjcmP025Factor2572, fjcmP025Error2572, rounding2542,
      fjcmP025Radius2572]

theorem fjcmP025DerivativeNorm2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨25, by omega⟩
      corrC02701MinusMidpointPosition2572‖ ≤ 1 := by
  have h := firstJetCorrMinus_triangle2572
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨25, by omega⟩
      corrC02701MinusMidpointPosition2572)
    (embedPair2542 fjcmP025Rounded2572) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjcmP025RoundedError2572 (embedPair_magnitude2542
      fjcmP025Rounded2572))
  apply h'.trans
  norm_num [fjcmP025Radius2572, pairMagnitude2542, fjcmP025Rounded2572]

noncomputable def fjcmP026Input2572 : RatPair2542 := ((((-((770889 * 10^40
        + 3381634557173160365454331760519832708453) * 10^40
        + 8445081731115744698509100587432038911481)) : ℚ) /
        ((1043539 * 10^40
        + 9494850363077843158719362614051723272667) * 10^40
        + 9765981577832661801082496535756800000000)),
    ((100473894490366930888172769 : ℚ) /
        14757395258967641292800000000))

def fjcmP026Center2572 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjcmP026Factor2572 : RatPair2542 := ((((((18287110242590252447880554564 * 10^40
        + 3096719781200154055536277499850834687716) * 10^40
        + 9868174371958028754305932466956652974581) * 10^40
        + 2972738437505500261821781699491681895093) : ℚ) /
        (((1450806976117078933368 * 10^40
        + 6938549699731298507206310750329531504355) * 10^40
        + 7684528508351137377988959013790724929283) * 10^40
        + 1232558896135239476356436601016636209814)),
    (((-316954711375437) : ℚ) /
        4398046511104))

noncomputable def fjcmP026Error2572 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjcmP026BaseError2572 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨26, by omega⟩
      corrC02701MinusMidpointPosition2572 - embedPair2542 fjcmP026Center2572‖ ≤ fjcmP026Error2572
          := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨26, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hz : ‖embedPair2542 fjcmP026Input2572‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjcmP026Input2572]
  have hc : (compactExp2547 fjcmP026Input2572 15).1 = fjcmP026Center2572 := by cbv
  have he : ((compactExp2547 fjcmP026Input2572 15).2 : ℝ) = fjcmP026Error2572 := by
    have hq : (compactExp2547 fjcmP026Input2572 15).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjcmP026Error2572]
  have h := compactExp_error2547 fjcmP026Input2572 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨26, by omega⟩
      corrC02701MinusMidpointPosition2572 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          fjcmP026Input2572) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrC02701MinusMidpointPosition2572, storedWidth,
      nodeModulation2541, embedPair2542, fjcmP026Input2572, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjcmP026DerivativeError2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨26, by omega⟩
      corrC02701MinusMidpointPosition2572 -
      embedPair2542 fjcmP026Factor2572 * embedPair2542 fjcmP026Center2572‖ ≤
        (pairMagnitude2542 fjcmP026Factor2572 : ℝ) * fjcmP026Error2572 := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨26, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hf : weightedMultiplier2543 1 (-1/2)
      (nodeModulation2541 ⟨26, by omega⟩)
      (storedWidth ⟨26, by omega⟩ ^ 2) corrC02701MinusMidpointPosition2572 =
      embedPair2542 fjcmP026Factor2572 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrC02701MinusMidpointPosition2572, storedWidth, nodeModulation2541, embedPair2542,
      fjcmP026Factor2572, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (-1/2)
    (nodeModulation2541 ⟨26, by omega⟩) (pow_pos (storedWidth_pos ⟨26, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjcmP026BaseError2572
    (embedPair_magnitude2542 fjcmP026Factor2572)

def fjcmP026Rounded2572 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjcmP026Radius2572 : ℝ := ((2199023255577 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjcmP026RoundCompute2572 :
    pairRound2542 (pairMul2542 fjcmP026Factor2572 fjcmP026Center2572) = fjcmP026Rounded2572 := by
  cbv

theorem fjcmP026RoundedError2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨26, by omega⟩
      corrC02701MinusMidpointPosition2572 - embedPair2542 fjcmP026Rounded2572‖ ≤
          fjcmP026Radius2572 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjcmP026Factor2572 fjcmP026Center2572)
  rw [fjcmP026RoundCompute2572, embedPair_mul2542] at hr
  have h := (firstJetCorrMinus_triangle2572
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨26, by omega⟩
      corrC02701MinusMidpointPosition2572)
    (embedPair2542 fjcmP026Factor2572 * embedPair2542 fjcmP026Center2572)
    (embedPair2542 fjcmP026Rounded2572)).trans (add_le_add fjcmP026DerivativeError2572 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjcmP026Factor2572, fjcmP026Error2572, rounding2542,
      fjcmP026Radius2572]

theorem fjcmP026DerivativeNorm2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨26, by omega⟩
      corrC02701MinusMidpointPosition2572‖ ≤ 1 := by
  have h := firstJetCorrMinus_triangle2572
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨26, by omega⟩
      corrC02701MinusMidpointPosition2572)
    (embedPair2542 fjcmP026Rounded2572) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjcmP026RoundedError2572 (embedPair_magnitude2542
      fjcmP026Rounded2572))
  apply h'.trans
  norm_num [fjcmP026Radius2572, pairMagnitude2542, fjcmP026Rounded2572]

noncomputable def fjcmP027Input2572 : RatPair2542 := ((((-((770889 * 10^40
        + 3381634557173160365454331760519832708453) * 10^40
        + 8445081731115744698509100587432038911481)) : ℚ) /
        ((1043539 * 10^40
        + 9494850363077843158719362614051723272667) * 10^40
        + 9765981577832661801082496535756800000000)),
    ((211090470366057865778518799 : ℚ) /
        29514790517935282585600000000))

def fjcmP027Center2572 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjcmP027Factor2572 : RatPair2542 := ((((((18287110242590252447880554564 * 10^40
        + 3096719781200154055536277499850834687716) * 10^40
        + 9868174371958028754305932466956652974581) * 10^40
        + 2972738437505500261821781699491681895093) : ℚ) /
        (((1450806976117078933368 * 10^40
        + 6938549699731298507206310750329531504355) * 10^40
        + 7684528508351137377988959013790724929283) * 10^40
        + 1232558896135239476356436601016636209814)),
    (((-665905501606627) : ℚ) /
        8796093022208))

noncomputable def fjcmP027Error2572 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjcmP027BaseError2572 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨27, by omega⟩
      corrC02701MinusMidpointPosition2572 - embedPair2542 fjcmP027Center2572‖ ≤ fjcmP027Error2572
          := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨27, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hz : ‖embedPair2542 fjcmP027Input2572‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjcmP027Input2572]
  have hc : (compactExp2547 fjcmP027Input2572 15).1 = fjcmP027Center2572 := by cbv
  have he : ((compactExp2547 fjcmP027Input2572 15).2 : ℝ) = fjcmP027Error2572 := by
    have hq : (compactExp2547 fjcmP027Input2572 15).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjcmP027Error2572]
  have h := compactExp_error2547 fjcmP027Input2572 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨27, by omega⟩
      corrC02701MinusMidpointPosition2572 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          fjcmP027Input2572) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrC02701MinusMidpointPosition2572, storedWidth,
      nodeModulation2541, embedPair2542, fjcmP027Input2572, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjcmP027DerivativeError2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨27, by omega⟩
      corrC02701MinusMidpointPosition2572 -
      embedPair2542 fjcmP027Factor2572 * embedPair2542 fjcmP027Center2572‖ ≤
        (pairMagnitude2542 fjcmP027Factor2572 : ℝ) * fjcmP027Error2572 := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨27, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hf : weightedMultiplier2543 1 (-1/2)
      (nodeModulation2541 ⟨27, by omega⟩)
      (storedWidth ⟨27, by omega⟩ ^ 2) corrC02701MinusMidpointPosition2572 =
      embedPair2542 fjcmP027Factor2572 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrC02701MinusMidpointPosition2572, storedWidth, nodeModulation2541, embedPair2542,
      fjcmP027Factor2572, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (-1/2)
    (nodeModulation2541 ⟨27, by omega⟩) (pow_pos (storedWidth_pos ⟨27, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjcmP027BaseError2572
    (embedPair_magnitude2542 fjcmP027Factor2572)

def fjcmP027Rounded2572 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjcmP027Radius2572 : ℝ := ((2199023255577 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjcmP027RoundCompute2572 :
    pairRound2542 (pairMul2542 fjcmP027Factor2572 fjcmP027Center2572) = fjcmP027Rounded2572 := by
  cbv

theorem fjcmP027RoundedError2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨27, by omega⟩
      corrC02701MinusMidpointPosition2572 - embedPair2542 fjcmP027Rounded2572‖ ≤
          fjcmP027Radius2572 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjcmP027Factor2572 fjcmP027Center2572)
  rw [fjcmP027RoundCompute2572, embedPair_mul2542] at hr
  have h := (firstJetCorrMinus_triangle2572
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨27, by omega⟩
      corrC02701MinusMidpointPosition2572)
    (embedPair2542 fjcmP027Factor2572 * embedPair2542 fjcmP027Center2572)
    (embedPair2542 fjcmP027Rounded2572)).trans (add_le_add fjcmP027DerivativeError2572 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjcmP027Factor2572, fjcmP027Error2572, rounding2542,
      fjcmP027Radius2572]

theorem fjcmP027DerivativeNorm2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨27, by omega⟩
      corrC02701MinusMidpointPosition2572‖ ≤ 1 := by
  have h := firstJetCorrMinus_triangle2572
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨27, by omega⟩
      corrC02701MinusMidpointPosition2572)
    (embedPair2542 fjcmP027Rounded2572) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjcmP027RoundedError2572 (embedPair_magnitude2542
      fjcmP027Rounded2572))
  apply h'.trans
  norm_num [fjcmP027Radius2572, pairMagnitude2542, fjcmP027Rounded2572]

noncomputable def fjcmP028Input2572 : RatPair2542 := ((((-((770889 * 10^40
        + 3381634557173160365454331760519832708453) * 10^40
        + 8445081731115744698509100587432038911481)) : ℚ) /
        ((1043539 * 10^40
        + 9494850363077843158719362614051723272667) * 10^40
        + 9765981577832661801082496535756800000000)),
    ((860424389879986254866272499 : ℚ) /
        118059162071741130342400000000))

def fjcmP028Center2572 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjcmP028Factor2572 : RatPair2542 := ((((((18287110242590252447880554564 * 10^40
        + 3096719781200154055536277499850834687716) * 10^40
        + 9868174371958028754305932466956652974581) * 10^40
        + 2972738437505500261821781699491681895093) : ℚ) /
        (((1450806976117078933368 * 10^40
        + 6938549699731298507206310750329531504355) * 10^40
        + 7684528508351137377988959013790724929283) * 10^40
        + 1232558896135239476356436601016636209814)),
    (((-2714292757716727) : ℚ) /
        35184372088832))

noncomputable def fjcmP028Error2572 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjcmP028BaseError2572 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨28, by omega⟩
      corrC02701MinusMidpointPosition2572 - embedPair2542 fjcmP028Center2572‖ ≤ fjcmP028Error2572
          := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨28, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hz : ‖embedPair2542 fjcmP028Input2572‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjcmP028Input2572]
  have hc : (compactExp2547 fjcmP028Input2572 15).1 = fjcmP028Center2572 := by cbv
  have he : ((compactExp2547 fjcmP028Input2572 15).2 : ℝ) = fjcmP028Error2572 := by
    have hq : (compactExp2547 fjcmP028Input2572 15).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjcmP028Error2572]
  have h := compactExp_error2547 fjcmP028Input2572 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨28, by omega⟩
      corrC02701MinusMidpointPosition2572 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          fjcmP028Input2572) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrC02701MinusMidpointPosition2572, storedWidth,
      nodeModulation2541, embedPair2542, fjcmP028Input2572, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjcmP028DerivativeError2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨28, by omega⟩
      corrC02701MinusMidpointPosition2572 -
      embedPair2542 fjcmP028Factor2572 * embedPair2542 fjcmP028Center2572‖ ≤
        (pairMagnitude2542 fjcmP028Factor2572 : ℝ) * fjcmP028Error2572 := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨28, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hf : weightedMultiplier2543 1 (-1/2)
      (nodeModulation2541 ⟨28, by omega⟩)
      (storedWidth ⟨28, by omega⟩ ^ 2) corrC02701MinusMidpointPosition2572 =
      embedPair2542 fjcmP028Factor2572 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrC02701MinusMidpointPosition2572, storedWidth, nodeModulation2541, embedPair2542,
      fjcmP028Factor2572, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (-1/2)
    (nodeModulation2541 ⟨28, by omega⟩) (pow_pos (storedWidth_pos ⟨28, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjcmP028BaseError2572
    (embedPair_magnitude2542 fjcmP028Factor2572)

def fjcmP028Rounded2572 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjcmP028Radius2572 : ℝ := ((2199023255577 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjcmP028RoundCompute2572 :
    pairRound2542 (pairMul2542 fjcmP028Factor2572 fjcmP028Center2572) = fjcmP028Rounded2572 := by
  cbv

theorem fjcmP028RoundedError2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨28, by omega⟩
      corrC02701MinusMidpointPosition2572 - embedPair2542 fjcmP028Rounded2572‖ ≤
          fjcmP028Radius2572 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjcmP028Factor2572 fjcmP028Center2572)
  rw [fjcmP028RoundCompute2572, embedPair_mul2542] at hr
  have h := (firstJetCorrMinus_triangle2572
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨28, by omega⟩
      corrC02701MinusMidpointPosition2572)
    (embedPair2542 fjcmP028Factor2572 * embedPair2542 fjcmP028Center2572)
    (embedPair2542 fjcmP028Rounded2572)).trans (add_le_add fjcmP028DerivativeError2572 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjcmP028Factor2572, fjcmP028Error2572, rounding2542,
      fjcmP028Radius2572]

theorem fjcmP028DerivativeNorm2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨28, by omega⟩
      corrC02701MinusMidpointPosition2572‖ ≤ 1 := by
  have h := firstJetCorrMinus_triangle2572
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨28, by omega⟩
      corrC02701MinusMidpointPosition2572)
    (embedPair2542 fjcmP028Rounded2572) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjcmP028RoundedError2572 (embedPair_magnitude2542
      fjcmP028Rounded2572))
  apply h'.trans
  norm_num [fjcmP028Radius2572, pairMagnitude2542, fjcmP028Rounded2572]

noncomputable def fjcmP029Input2572 : RatPair2542 := ((((-((770889 * 10^40
        + 3381634557173160365454331760519832708453) * 10^40
        + 8445081731115744698509100587432038911481)) : ℚ) /
        ((1043539 * 10^40
        + 9494850363077843158719362614051723272667) * 10^40
        + 9765981577832661801082496535756800000000)),
    ((884878527656961808081806583 : ℚ) /
        118059162071741130342400000000))

def fjcmP029Center2572 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjcmP029Factor2572 : RatPair2542 := ((((((18287110242590252447880554564 * 10^40
        + 3096719781200154055536277499850834687716) * 10^40
        + 9868174371958028754305932466956652974581) * 10^40
        + 2972738437505500261821781699491681895093) : ℚ) /
        (((1450806976117078933368 * 10^40
        + 6938549699731298507206310750329531504355) * 10^40
        + 7684528508351137377988959013790724929283) * 10^40
        + 1232558896135239476356436601016636209814)),
    (((-2791435723263659) : ℚ) /
        35184372088832))

noncomputable def fjcmP029Error2572 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjcmP029BaseError2572 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨29, by omega⟩
      corrC02701MinusMidpointPosition2572 - embedPair2542 fjcmP029Center2572‖ ≤ fjcmP029Error2572
          := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨29, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hz : ‖embedPair2542 fjcmP029Input2572‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjcmP029Input2572]
  have hc : (compactExp2547 fjcmP029Input2572 15).1 = fjcmP029Center2572 := by cbv
  have he : ((compactExp2547 fjcmP029Input2572 15).2 : ℝ) = fjcmP029Error2572 := by
    have hq : (compactExp2547 fjcmP029Input2572 15).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjcmP029Error2572]
  have h := compactExp_error2547 fjcmP029Input2572 hz 15
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨29, by omega⟩
      corrC02701MinusMidpointPosition2572 = Complex.exp ((2 : ℂ)^15 * embedPair2542
          fjcmP029Input2572) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [corrC02701MinusMidpointPosition2572, storedWidth,
      nodeModulation2541, embedPair2542, fjcmP029Input2572, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjcmP029DerivativeError2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨29, by omega⟩
      corrC02701MinusMidpointPosition2572 -
      embedPair2542 fjcmP029Factor2572 * embedPair2542 fjcmP029Center2572‖ ≤
        (pairMagnitude2542 fjcmP029Factor2572 : ℝ) * fjcmP029Error2572 := by
  have hx : |corrC02701MinusMidpointPosition2572| < storedWidth ⟨29, by omega⟩ ^ 2 := by
    norm_num [corrC02701MinusMidpointPosition2572, storedWidth]
  have hf : weightedMultiplier2543 1 (-1/2)
      (nodeModulation2541 ⟨29, by omega⟩)
      (storedWidth ⟨29, by omega⟩ ^ 2) corrC02701MinusMidpointPosition2572 =
      embedPair2542 fjcmP029Factor2572 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      corrC02701MinusMidpointPosition2572, storedWidth, nodeModulation2541, embedPair2542,
      fjcmP029Factor2572, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (-1/2)
    (nodeModulation2541 ⟨29, by omega⟩) (pow_pos (storedWidth_pos ⟨29, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjcmP029BaseError2572
    (embedPair_magnitude2542 fjcmP029Factor2572)

def fjcmP029Rounded2572 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjcmP029Radius2572 : ℝ := ((2199023255577 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjcmP029RoundCompute2572 :
    pairRound2542 (pairMul2542 fjcmP029Factor2572 fjcmP029Center2572) = fjcmP029Rounded2572 := by
  cbv

theorem fjcmP029RoundedError2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨29, by omega⟩
      corrC02701MinusMidpointPosition2572 - embedPair2542 fjcmP029Rounded2572‖ ≤
          fjcmP029Radius2572 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjcmP029Factor2572 fjcmP029Center2572)
  rw [fjcmP029RoundCompute2572, embedPair_mul2542] at hr
  have h := (firstJetCorrMinus_triangle2572
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨29, by omega⟩
      corrC02701MinusMidpointPosition2572)
    (embedPair2542 fjcmP029Factor2572 * embedPair2542 fjcmP029Center2572)
    (embedPair2542 fjcmP029Rounded2572)).trans (add_le_add fjcmP029DerivativeError2572 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjcmP029Factor2572, fjcmP029Error2572, rounding2542,
      fjcmP029Radius2572]

theorem fjcmP029DerivativeNorm2572 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨29, by omega⟩
      corrC02701MinusMidpointPosition2572‖ ≤ 1 := by
  have h := firstJetCorrMinus_triangle2572
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨29, by omega⟩
      corrC02701MinusMidpointPosition2572)
    (embedPair2542 fjcmP029Rounded2572) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjcmP029RoundedError2572 (embedPair_magnitude2542
      fjcmP029Rounded2572))
  apply h'.trans
  norm_num [fjcmP029Radius2572, pairMagnitude2542, fjcmP029Rounded2572]

noncomputable def fjcmValue2572 (i : Fin 30) : ℂ :=
  match i.val with
  | 0 => embedPair2542 fjcmP000Rounded2572
  | 1 => embedPair2542 fjcmP001Rounded2572
  | 2 => embedPair2542 fjcmP002Rounded2572
  | 3 => embedPair2542 fjcmP003Rounded2572
  | 4 => embedPair2542 fjcmP004Rounded2572
  | 5 => embedPair2542 fjcmP005Rounded2572
  | 6 => embedPair2542 fjcmP006Rounded2572
  | 7 => embedPair2542 fjcmP007Rounded2572
  | 8 => embedPair2542 fjcmP008Rounded2572
  | 9 => embedPair2542 fjcmP009Rounded2572
  | 10 => embedPair2542 fjcmP010Rounded2572
  | 11 => embedPair2542 fjcmP011Rounded2572
  | 12 => embedPair2542 fjcmP012Rounded2572
  | 13 => embedPair2542 fjcmP013Rounded2572
  | 14 => embedPair2542 fjcmP014Rounded2572
  | 15 => embedPair2542 fjcmP015Rounded2572
  | 16 => embedPair2542 fjcmP016Rounded2572
  | 17 => embedPair2542 fjcmP017Rounded2572
  | 18 => embedPair2542 fjcmP018Rounded2572
  | 19 => embedPair2542 fjcmP019Rounded2572
  | 20 => embedPair2542 fjcmP020Rounded2572
  | 21 => embedPair2542 fjcmP021Rounded2572
  | 22 => embedPair2542 fjcmP022Rounded2572
  | 23 => embedPair2542 fjcmP023Rounded2572
  | 24 => embedPair2542 fjcmP024Rounded2572
  | 25 => embedPair2542 fjcmP025Rounded2572
  | 26 => embedPair2542 fjcmP026Rounded2572
  | 27 => embedPair2542 fjcmP027Rounded2572
  | 28 => embedPair2542 fjcmP028Rounded2572
  | 29 => embedPair2542 fjcmP029Rounded2572
  | _ => 0

noncomputable def fjcmError2572 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => fjcmP000Radius2572
  | 1 => fjcmP001Radius2572
  | 2 => fjcmP002Radius2572
  | 3 => fjcmP003Radius2572
  | 4 => fjcmP004Radius2572
  | 5 => fjcmP005Radius2572
  | 6 => fjcmP006Radius2572
  | 7 => fjcmP007Radius2572
  | 8 => fjcmP008Radius2572
  | 9 => fjcmP009Radius2572
  | 10 => fjcmP010Radius2572
  | 11 => fjcmP011Radius2572
  | 12 => fjcmP012Radius2572
  | 13 => fjcmP013Radius2572
  | 14 => fjcmP014Radius2572
  | 15 => fjcmP015Radius2572
  | 16 => fjcmP016Radius2572
  | 17 => fjcmP017Radius2572
  | 18 => fjcmP018Radius2572
  | 19 => fjcmP019Radius2572
  | 20 => fjcmP020Radius2572
  | 21 => fjcmP021Radius2572
  | 22 => fjcmP022Radius2572
  | 23 => fjcmP023Radius2572
  | 24 => fjcmP024Radius2572
  | 25 => fjcmP025Radius2572
  | 26 => fjcmP026Radius2572
  | 27 => fjcmP027Radius2572
  | 28 => fjcmP028Radius2572
  | 29 => fjcmP029Radius2572
  | _ => 0

theorem fjcmExpError2572 (i : Fin 30) :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 i corrC02701MinusMidpointPosition2572 -
        fjcmValue2572 i‖ ≤ fjcmError2572 i := by
  fin_cases i
  · simpa only [fjcmValue2572, fjcmError2572] using fjcmP000RoundedError2572
  · simpa only [fjcmValue2572, fjcmError2572] using fjcmP001RoundedError2572
  · simpa only [fjcmValue2572, fjcmError2572] using fjcmP002RoundedError2572
  · simpa only [fjcmValue2572, fjcmError2572] using fjcmP003RoundedError2572
  · simpa only [fjcmValue2572, fjcmError2572] using fjcmP004RoundedError2572
  · simpa only [fjcmValue2572, fjcmError2572] using fjcmP005RoundedError2572
  · simpa only [fjcmValue2572, fjcmError2572] using fjcmP006RoundedError2572
  · simpa only [fjcmValue2572, fjcmError2572] using fjcmP007RoundedError2572
  · simpa only [fjcmValue2572, fjcmError2572] using fjcmP008RoundedError2572
  · simpa only [fjcmValue2572, fjcmError2572] using fjcmP009RoundedError2572
  · simpa only [fjcmValue2572, fjcmError2572] using fjcmP010RoundedError2572
  · simpa only [fjcmValue2572, fjcmError2572] using fjcmP011RoundedError2572
  · simpa only [fjcmValue2572, fjcmError2572] using fjcmP012RoundedError2572
  · simpa only [fjcmValue2572, fjcmError2572] using fjcmP013RoundedError2572
  · simpa only [fjcmValue2572, fjcmError2572] using fjcmP014RoundedError2572
  · simpa only [fjcmValue2572, fjcmError2572] using fjcmP015RoundedError2572
  · simpa only [fjcmValue2572, fjcmError2572] using fjcmP016RoundedError2572
  · simpa only [fjcmValue2572, fjcmError2572] using fjcmP017RoundedError2572
  · simpa only [fjcmValue2572, fjcmError2572] using fjcmP018RoundedError2572
  · simpa only [fjcmValue2572, fjcmError2572] using fjcmP019RoundedError2572
  · simpa only [fjcmValue2572, fjcmError2572] using fjcmP020RoundedError2572
  · simpa only [fjcmValue2572, fjcmError2572] using fjcmP021RoundedError2572
  · simpa only [fjcmValue2572, fjcmError2572] using fjcmP022RoundedError2572
  · simpa only [fjcmValue2572, fjcmError2572] using fjcmP023RoundedError2572
  · simpa only [fjcmValue2572, fjcmError2572] using fjcmP024RoundedError2572
  · simpa only [fjcmValue2572, fjcmError2572] using fjcmP025RoundedError2572
  · simpa only [fjcmValue2572, fjcmError2572] using fjcmP026RoundedError2572
  · simpa only [fjcmValue2572, fjcmError2572] using fjcmP027RoundedError2572
  · simpa only [fjcmValue2572, fjcmError2572] using fjcmP028RoundedError2572
  · simpa only [fjcmValue2572, fjcmError2572] using fjcmP029RoundedError2572

theorem fjcmUnitNorm2572 (i : Fin 30) :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 i corrC02701MinusMidpointPosition2572‖ ≤ 1 :=
        by
  fin_cases i
  · simpa only [fjcmValue2572, fjcmError2572] using fjcmP000DerivativeNorm2572
  · simpa only [fjcmValue2572, fjcmError2572] using fjcmP001DerivativeNorm2572
  · simpa only [fjcmValue2572, fjcmError2572] using fjcmP002DerivativeNorm2572
  · simpa only [fjcmValue2572, fjcmError2572] using fjcmP003DerivativeNorm2572
  · simpa only [fjcmValue2572, fjcmError2572] using fjcmP004DerivativeNorm2572
  · simpa only [fjcmValue2572, fjcmError2572] using fjcmP005DerivativeNorm2572
  · simpa only [fjcmValue2572, fjcmError2572] using fjcmP006DerivativeNorm2572
  · simpa only [fjcmValue2572, fjcmError2572] using fjcmP007DerivativeNorm2572
  · simpa only [fjcmValue2572, fjcmError2572] using fjcmP008DerivativeNorm2572
  · simpa only [fjcmValue2572, fjcmError2572] using fjcmP009DerivativeNorm2572
  · simpa only [fjcmValue2572, fjcmError2572] using fjcmP010DerivativeNorm2572
  · simpa only [fjcmValue2572, fjcmError2572] using fjcmP011DerivativeNorm2572
  · simpa only [fjcmValue2572, fjcmError2572] using fjcmP012DerivativeNorm2572
  · simpa only [fjcmValue2572, fjcmError2572] using fjcmP013DerivativeNorm2572
  · simpa only [fjcmValue2572, fjcmError2572] using fjcmP014DerivativeNorm2572
  · simpa only [fjcmValue2572, fjcmError2572] using fjcmP015DerivativeNorm2572
  · simpa only [fjcmValue2572, fjcmError2572] using fjcmP016DerivativeNorm2572
  · simpa only [fjcmValue2572, fjcmError2572] using fjcmP017DerivativeNorm2572
  · simpa only [fjcmValue2572, fjcmError2572] using fjcmP018DerivativeNorm2572
  · simpa only [fjcmValue2572, fjcmError2572] using fjcmP019DerivativeNorm2572
  · simpa only [fjcmValue2572, fjcmError2572] using fjcmP020DerivativeNorm2572
  · simpa only [fjcmValue2572, fjcmError2572] using fjcmP021DerivativeNorm2572
  · simpa only [fjcmValue2572, fjcmError2572] using fjcmP022DerivativeNorm2572
  · simpa only [fjcmValue2572, fjcmError2572] using fjcmP023DerivativeNorm2572
  · simpa only [fjcmValue2572, fjcmError2572] using fjcmP024DerivativeNorm2572
  · simpa only [fjcmValue2572, fjcmError2572] using fjcmP025DerivativeNorm2572
  · simpa only [fjcmValue2572, fjcmError2572] using fjcmP026DerivativeNorm2572
  · simpa only [fjcmValue2572, fjcmError2572] using fjcmP027DerivativeNorm2572
  · simpa only [fjcmValue2572, fjcmError2572] using fjcmP028DerivativeNorm2572
  · simpa only [fjcmValue2572, fjcmError2572] using fjcmP029DerivativeNorm2572

noncomputable def fjcmSum2572 : ℂ := ⟨(((-(((471354177847 * 10^40
        + 922095678796542185494485605462727093688) * 10^40
        + 5562488469124456187469192642118913158882) * 10^40
        + 5735950974858791891127000934685770496457)) : ℝ) /
        (((1419606883389 * 10^40
        + 8572081041480622812588561594557825924180) * 10^40
        + 8648728554527468610959648031899646689592) * 10^40
        + 5319463985864300012238628776434768805888)),
    (((-(((739938771177 * 10^40
        + 8036434076633835564896489787625354495821) * 10^40
        + 7871407459603893228889639139986995459100) * 10^40
        + 2793484015317201855127694714789864406979)) : ℝ) /
        (((1419606883389 * 10^40
        + 8572081041480622812588561594557825924180) * 10^40
        + 8648728554527468610959648031899646689592) * 10^40
        + 5319463985864300012238628776434768805888))⟩

noncomputable def fjcmUpper2572 : ℝ := ((1931249 : ℝ) /
        3125000)

theorem fjcmSum_eq2572 :
    (∑ i : Fin 30, correctionCoefficientCenter2570 i * fjcmValue2572 i) =
      fjcmSum2572 := by
  rw [sum30_chain2541]
  apply Complex.ext <;>
    norm_num [correctionCoefficientCenter2570, correctionCoefficientBox2570, fjcmValue2572,
      fjcmSum2572, embedPair2542, fjcmP000Rounded2572,
      fjcmP001Rounded2572,
      fjcmP002Rounded2572,
      fjcmP003Rounded2572,
      fjcmP004Rounded2572,
      fjcmP005Rounded2572,
      fjcmP006Rounded2572,
      fjcmP007Rounded2572,
      fjcmP008Rounded2572,
      fjcmP009Rounded2572,
      fjcmP010Rounded2572,
      fjcmP011Rounded2572,
      fjcmP012Rounded2572,
      fjcmP013Rounded2572,
      fjcmP014Rounded2572,
      fjcmP015Rounded2572,
      fjcmP016Rounded2572,
      fjcmP017Rounded2572,
      fjcmP018Rounded2572,
      fjcmP019Rounded2572,
      fjcmP020Rounded2572,
      fjcmP021Rounded2572,
      fjcmP022Rounded2572,
      fjcmP023Rounded2572,
      fjcmP024Rounded2572,
      fjcmP025Rounded2572,
      fjcmP026Rounded2572,
      fjcmP027Rounded2572,
      fjcmP028Rounded2572,
      fjcmP029Rounded2572, Complex.mul_re, Complex.mul_im]

theorem fjcmSum_norm2572 :
    ‖∑ i : Fin 30, correctionCoefficientCenter2570 i * fjcmValue2572 i‖ ≤ ((30899979 : ℝ) /
        50000000) := by
  rw [fjcmSum_eq2572]
  apply complex_norm_le_of_sq2541 _ _ (by norm_num)
  norm_num [fjcmSum2572]

theorem fjcmCharge2572 :
    (∑ i : Fin 30, (|(correctionCoefficientCenter2570 i).re| +
      |(correctionCoefficientCenter2570 i).im|) * fjcmError2572 i) ≤ (1 : ℝ)/10^8 := by
  rw [sum30_chain2541]
  norm_num [correctionCoefficientCenter2570, correctionCoefficientBox2570, fjcmError2572,
      fjcmP000Radius2572,
      fjcmP001Radius2572,
      fjcmP002Radius2572,
      fjcmP003Radius2572,
      fjcmP004Radius2572,
      fjcmP005Radius2572,
      fjcmP006Radius2572,
      fjcmP007Radius2572,
      fjcmP008Radius2572,
      fjcmP009Radius2572,
      fjcmP010Radius2572,
      fjcmP011Radius2572,
      fjcmP012Radius2572,
      fjcmP013Radius2572,
      fjcmP014Radius2572,
      fjcmP015Radius2572,
      fjcmP016Radius2572,
      fjcmP017Radius2572,
      fjcmP018Radius2572,
      fjcmP019Radius2572,
      fjcmP020Radius2572,
      fjcmP021Radius2572,
      fjcmP022Radius2572,
      fjcmP023Radius2572,
      fjcmP024Radius2572,
      fjcmP025Radius2572,
      fjcmP026Radius2572,
      fjcmP027Radius2572,
      fjcmP028Radius2572,
      fjcmP029Radius2572]

theorem firstJetCorrMinusUpper_le2572 :
    signedJetUpper2539 1 (-1/2) correctionCoefficientCenter2570 correctionCoefficientError2570
      nodeModulation2541 corrC02701MinusMidpointPosition2572 ≤ fjcmUpper2572 := by
  have hsum :
      ‖∑ i : Fin 30, correctionCoefficientCenter2570 i *
        weightedUnitJet2539 1 (-1/2) nodeModulation2541 i corrC02701MinusMidpointPosition2572‖ ≤
      ‖∑ i : Fin 30, correctionCoefficientCenter2570 i * fjcmValue2572 i‖ +
        ∑ i : Fin 30, (|(correctionCoefficientCenter2570 i).re| +
          |(correctionCoefficientCenter2570 i).im|) * fjcmError2572 i := by
    apply norm_sum_le_center_sum_add_error2531
    intro i _
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (Complex.norm_le_abs_re_add_abs_im _) (fjcmExpError2572 i)
      (norm_nonneg _) (by positivity)
  have heach : ∀ i : Fin 30, correctionCoefficientError2570 i *
      ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 i corrC02701MinusMidpointPosition2572‖ ≤
        (1 : ℝ)/10^28 := by
    intro i
    have h := mul_le_mul_of_nonneg_left (fjcmUnitNorm2572 i)
      (by norm_num [correctionCoefficientError2570] : 0 ≤ correctionCoefficientError2570 i)
    simpa [correctionCoefficientError2570] using h
  have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
  have he' : (∑ i : Fin 30, correctionCoefficientError2570 i *
      ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 i corrC02701MinusMidpointPosition2572‖) ≤
        (30 : ℝ)/10^28 := by simpa using he
  unfold signedJetUpper2539 fjcmUpper2572
  linarith [fjcmSum_norm2572, fjcmCharge2572]

theorem weightedPhysicalFirstJetMidpointMinus_le2572 (coefficients : Fin 30 → ℂ)
    (hbox : ∀ i, (correctionCoefficientBox2570 i).Mem (coefficients i)) :
    ‖iteratedDeriv 1 (weightedPhysical2539 (-1/2) coefficients nodeModulation2541)
        corrC02701MinusMidpointPosition2572‖ ≤
      fjcmUpper2572 := by
  have h := weightedPhysical2539_jet_le_center_error 1 (-1/2) coefficients
    correctionCoefficientCenter2570 correctionCoefficientError2570 nodeModulation2541
    (fun i => corrError_of_box2570 i (coefficients i) (hbox i))
        corrC02701MinusMidpointPosition2572
  exact h.trans firstJetCorrMinusUpper_le2572

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.fjcmExpError2572
#print axioms ConnesWeilRH.Dev.fjcmSum_eq2572
#print axioms ConnesWeilRH.Dev.fjcmSum_norm2572
#print axioms ConnesWeilRH.Dev.fjcmCharge2572
#print axioms ConnesWeilRH.Dev.firstJetCorrMinusUpper_le2572
#print axioms ConnesWeilRH.Dev.weightedPhysicalFirstJetMidpointMinus_le2572
