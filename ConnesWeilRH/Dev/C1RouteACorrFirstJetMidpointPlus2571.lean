import ConnesWeilRH.Dev.C1RouteACompactExp1602547
import ConnesWeilRH.Dev.C1RouteADerivativeMultiplier2543
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541
import ConnesWeilRH.Dev.C1RouteABoundaryMidpoint2548
import ConnesWeilRH.Dev.C1RouteACorrectionCoefficientBoxes2570
import ConnesWeilRH.Dev.C1RouteACorrectionCenterNode2570

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

theorem firstJetCorrPlus_triangle2571 (a b c : ℂ) : ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖ := by
  calc
    ‖a - c‖ = ‖(a - b) + (b - c)‖ := by congr 1; ring
    _ ≤ _ := norm_add_le _ _

theorem fjcpZero2571 : embedPair2542 (0, 0) = 0 := by
  apply Complex.ext <;> norm_num [embedPair2542]

def fjcpP000Center2571 : RatPair2542 := (0, 0)

def fjcpP000Factor2571 : RatPair2542 := (0, 0)

noncomputable def fjcpP000Error2571 : ℝ := 0

theorem fjcpP000Exterior2571 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨0, by omega⟩
      edgeMidpointPosition2548 = 0 := by
  have hx : storedWidth ⟨0, by omega⟩ ^ 2 ≤ |edgeMidpointPosition2548| := by
    norm_num [storedWidth, edgeMidpointPosition2548]
  exact weightedFamily_outside_zero2543 n (1/2)
    (nodeModulation2541 ⟨0, by omega⟩)
    (pow_pos (storedWidth_pos ⟨0, by omega⟩) 2) hx

theorem fjcpP000BaseError2571 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨0, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcpP000Center2571‖ ≤ fjcpP000Error2571 := by
  rw [fjcpP000Exterior2571]
  norm_num [fjcpP000Center2571, fjcpP000Error2571, fjcpZero2571]

theorem fjcpP000DerivativeError2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨0, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjcpP000Factor2571 * embedPair2542 fjcpP000Center2571‖ ≤
        (pairMagnitude2542 fjcpP000Factor2571 : ℝ) * fjcpP000Error2571 := by
  rw [fjcpP000Exterior2571]
  norm_num [fjcpP000Factor2571, fjcpP000Center2571, fjcpP000Error2571, pairMagnitude2542,
      fjcpZero2571]

def fjcpP000Rounded2571 : RatPair2542 := (0, 0)

noncomputable def fjcpP000Radius2571 : ℝ := 0

theorem fjcpP000RoundCompute2571 :
    pairRound2542 (pairMul2542 fjcpP000Factor2571 fjcpP000Center2571) = fjcpP000Rounded2571 := by
  cbv

theorem fjcpP000RoundedError2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨0, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcpP000Rounded2571‖ ≤ fjcpP000Radius2571 := by
  rw [fjcpP000Exterior2571]
  norm_num [fjcpP000Rounded2571, fjcpP000Radius2571, fjcpZero2571]

theorem fjcpP000DerivativeNorm2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨0, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  rw [fjcpP000Exterior2571]
  norm_num

noncomputable def fjcpP001Input2571 : RatPair2542 := ((((-((75 * 10^40
        + 5793610062624408994825365663891066264162) * 10^40
        + 9918580294757314292856548188915782259599)) : ℚ) /
        ((208 * 10^40
        + 8043940912794372598641292711490528776820) * 10^40
        + 5100987153752063079186153183641600000000)),
    ((1751911280236833479653958331 : ℚ) /
        7378697629483820646400000000))

def fjcpP001Center2571 : RatPair2542 := ((((-1) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def fjcpP001Factor2571 : RatPair2542 := ((((((48285684764685279210 * 10^40
        + 694469654141666716653755739374361511957) * 10^40
        + 1983023933887071209369055503369610426160) * 10^40
        + 7153470032678510502599646667891762695281) : ℚ) /
        (((79306619212413954 * 10^40
        + 6135590275954697994891057369985995860880) * 10^40
        + 3799340399814374588299513654302616835559) * 10^40
        + 5354338069519581005199293335783525390562)),
    (((-5524291025718029) : ℚ) /
        140737488355328))

noncomputable def fjcpP001Error2571 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjcpP001BaseError2571 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨1, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcpP001Center2571‖ ≤ fjcpP001Error2571 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjcpP001Input2571‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjcpP001Input2571]
  have hc : (compactExp2547 fjcpP001Input2571 9).1 = fjcpP001Center2571 := by cbv
  have he : ((compactExp2547 fjcpP001Input2571 9).2 : ℝ) = fjcpP001Error2571 := by
    have hq : (compactExp2547 fjcpP001Input2571 9).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjcpP001Error2571]
  have h := compactExp_error2547 fjcpP001Input2571 hz 9
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨1, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^9 * embedPair2542 fjcpP001Input2571) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjcpP001Input2571, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjcpP001DerivativeError2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨1, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjcpP001Factor2571 * embedPair2542 fjcpP001Center2571‖ ≤
        (pairMagnitude2542 fjcpP001Factor2571 : ℝ) * fjcpP001Error2571 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (1/2)
      (nodeModulation2541 ⟨1, by omega⟩)
      (storedWidth ⟨1, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjcpP001Factor2571 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjcpP001Factor2571, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (1/2)
    (nodeModulation2541 ⟨1, by omega⟩) (pow_pos (storedWidth_pos ⟨1, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjcpP001BaseError2571
    (embedPair_magnitude2542 fjcpP001Factor2571)

def fjcpP001Rounded2571 : RatPair2542 :=
  ((((-1) : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def fjcpP001Radius2571 : ℝ := ((2199023255553 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjcpP001RoundCompute2571 :
    pairRound2542 (pairMul2542 fjcpP001Factor2571 fjcpP001Center2571) = fjcpP001Rounded2571 := by
  cbv

theorem fjcpP001RoundedError2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨1, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcpP001Rounded2571‖ ≤ fjcpP001Radius2571 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjcpP001Factor2571 fjcpP001Center2571)
  rw [fjcpP001RoundCompute2571, embedPair_mul2542] at hr
  have h := (firstJetCorrPlus_triangle2571
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨1, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcpP001Factor2571 * embedPair2542 fjcpP001Center2571)
    (embedPair2542 fjcpP001Rounded2571)).trans (add_le_add fjcpP001DerivativeError2571 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjcpP001Factor2571, fjcpP001Error2571, rounding2542,
      fjcpP001Radius2571]

theorem fjcpP001DerivativeNorm2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨1, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetCorrPlus_triangle2571
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨1, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcpP001Rounded2571) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjcpP001RoundedError2571 (embedPair_magnitude2542
      fjcpP001Rounded2571))
  apply h'.trans
  norm_num [fjcpP001Radius2571, pairMagnitude2542, fjcpP001Rounded2571]

noncomputable def fjcpP002Input2571 : RatPair2542 := ((((-((2007 * 10^40
        + 5023240729250299860289918989155247824672) * 10^40
        + 8628363056985938976693269865273365762959)) : ℚ) /
        ((8147 * 10^40
        + 6895918656149932623563298325318453465194) * 10^40
        + 9452298146475584633489225469132800000000)),
    (((-1751911280236833479653958331) : ℚ) /
        3689348814741910323200000000))

def fjcpP002Center2571 : RatPair2542 := ((((-339364505114828529043) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-241773850067246350091) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)))

def fjcpP002Factor2571 : RatPair2542 := ((((((20410471496658769252947 * 10^40
        + 201616653836564308804866838098672716556) * 10^40
        + 8352564845593485597351628508576556609708) * 10^40
        + 1861792055619879599051472905736806632561) : ℚ) /
        (((483013323431043476903 * 10^40
        + 7511499335200218287611909907279225454881) * 10^40
        + 746082615335519961120361053248712426867) * 10^40
        + 9194345188221519198102945811473613265122)),
    ((5524291025718029 : ℚ) /
        140737488355328))

noncomputable def fjcpP002Error2571 : ℝ := ((2191587035296828369 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjcpP002BaseError2571 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨2, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcpP002Center2571‖ ≤ fjcpP002Error2571 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjcpP002Input2571‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjcpP002Input2571]
  have hc : (compactExp2547 fjcpP002Input2571 8).1 = fjcpP002Center2571 := by cbv
  have he : ((compactExp2547 fjcpP002Input2571 8).2 : ℝ) = fjcpP002Error2571 := by
    have hq : (compactExp2547 fjcpP002Input2571 8).2 =
        ((2191587035296828369 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjcpP002Error2571]
  have h := compactExp_error2547 fjcpP002Input2571 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨2, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^8 * embedPair2542 fjcpP002Input2571) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjcpP002Input2571, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjcpP002DerivativeError2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨2, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjcpP002Factor2571 * embedPair2542 fjcpP002Center2571‖ ≤
        (pairMagnitude2542 fjcpP002Factor2571 : ℝ) * fjcpP002Error2571 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (1/2)
      (nodeModulation2541 ⟨2, by omega⟩)
      (storedWidth ⟨2, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjcpP002Factor2571 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjcpP002Factor2571, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (1/2)
    (nodeModulation2541 ⟨2, by omega⟩) (pow_pos (storedWidth_pos ⟨2, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjcpP002BaseError2571
    (embedPair_magnitude2542 fjcpP002Factor2571)

def fjcpP002Rounded2571 : RatPair2542 :=
  (((503 : ℚ) /
        158456325028528675187087900672),
    (((-29277) : ℚ) /
        1267650600228229401496703205376))

noncomputable def fjcpP002Radius2571 : ℝ := ((2199023255707 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjcpP002RoundCompute2571 :
    pairRound2542 (pairMul2542 fjcpP002Factor2571 fjcpP002Center2571) = fjcpP002Rounded2571 := by
  cbv

theorem fjcpP002RoundedError2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨2, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcpP002Rounded2571‖ ≤ fjcpP002Radius2571 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjcpP002Factor2571 fjcpP002Center2571)
  rw [fjcpP002RoundCompute2571, embedPair_mul2542] at hr
  have h := (firstJetCorrPlus_triangle2571
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨2, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcpP002Factor2571 * embedPair2542 fjcpP002Center2571)
    (embedPair2542 fjcpP002Rounded2571)).trans (add_le_add fjcpP002DerivativeError2571 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjcpP002Factor2571, fjcpP002Error2571, rounding2542,
      fjcpP002Radius2571]

theorem fjcpP002DerivativeNorm2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨2, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetCorrPlus_triangle2571
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨2, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcpP002Rounded2571) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjcpP002RoundedError2571 (embedPair_magnitude2542
      fjcpP002Rounded2571))
  apply h'.trans
  norm_num [fjcpP002Radius2571, pairMagnitude2542, fjcpP002Rounded2571]

noncomputable def fjcpP003Input2571 : RatPair2542 := ((((-((7224110 * 10^40
        + 4406628376595866370136231705353501324162) * 10^40
        + 1511332573809066646429207955160645591911)) : ℚ) /
        ((39860431 * 10^40
        + 3525369205518296877772896888819194996209) * 10^40
        + 8027785848626107559175480881971200000000)),
    (((-1751911280236833479653958331) : ℚ) /
        3689348814741910323200000000))

def fjcpP003Center2571 : RatPair2542 := ((((-5949091438372091633409808421) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-132447442184126730267608627) : ℚ) /
        (2283596 * 10^40
        + 3083295358096932575511191922182123945984)))

def fjcpP003Factor2571 : RatPair2542 := ((((((171489622156943000195426447198 * 10^40
        + 6062598187743684290659208420886884284629) * 10^40
        + 1535621732405997006189222369556390501971) * 10^40
        + 5719713847345472865924858164472905824001) : ℚ) /
        (((11560434268978921445520672852 * 10^40
        + 3151491610707945740034502288795420775469) * 10^40
        + 9342842308133684351566010846049001848136) * 10^40
        + 2052163694690945731849716328945811648002)),
    ((5524291025718029 : ℚ) /
        140737488355328))

noncomputable def fjcpP003Error2571 : ℝ := ((17997678379747832815547905 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem fjcpP003BaseError2571 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨3, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcpP003Center2571‖ ≤ fjcpP003Error2571 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjcpP003Input2571‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjcpP003Input2571]
  have hc : (compactExp2547 fjcpP003Input2571 8).1 = fjcpP003Center2571 := by cbv
  have he : ((compactExp2547 fjcpP003Input2571 8).2 : ℝ) = fjcpP003Error2571 := by
    have hq : (compactExp2547 fjcpP003Input2571 8).2 =
        ((17997678379747832815547905 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)) := by cbv
    rw [hq]
    norm_num [fjcpP003Error2571]
  have h := compactExp_error2547 fjcpP003Input2571 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨3, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^8 * embedPair2542 fjcpP003Input2571) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjcpP003Input2571, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjcpP003DerivativeError2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨3, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjcpP003Factor2571 * embedPair2542 fjcpP003Center2571‖ ≤
        (pairMagnitude2542 fjcpP003Factor2571 : ℝ) * fjcpP003Error2571 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (1/2)
      (nodeModulation2541 ⟨3, by omega⟩)
      (storedWidth ⟨3, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjcpP003Factor2571 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjcpP003Factor2571, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (1/2)
    (nodeModulation2541 ⟨3, by omega⟩) (pow_pos (storedWidth_pos ⟨3, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjcpP003BaseError2571
    (embedPair_magnitude2542 fjcpP003Factor2571)

def fjcpP003Rounded2571 : RatPair2542 :=
  (((53012890685 : ℚ) /
        316912650057057350374175801344),
    (((-77902180797) : ℚ) /
        316912650057057350374175801344))

noncomputable def fjcpP003Radius2571 : ℝ := ((550177973521 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem fjcpP003RoundCompute2571 :
    pairRound2542 (pairMul2542 fjcpP003Factor2571 fjcpP003Center2571) = fjcpP003Rounded2571 := by
  cbv

theorem fjcpP003RoundedError2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨3, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcpP003Rounded2571‖ ≤ fjcpP003Radius2571 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjcpP003Factor2571 fjcpP003Center2571)
  rw [fjcpP003RoundCompute2571, embedPair_mul2542] at hr
  have h := (firstJetCorrPlus_triangle2571
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨3, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcpP003Factor2571 * embedPair2542 fjcpP003Center2571)
    (embedPair2542 fjcpP003Rounded2571)).trans (add_le_add fjcpP003DerivativeError2571 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjcpP003Factor2571, fjcpP003Error2571, rounding2542,
      fjcpP003Radius2571]

theorem fjcpP003DerivativeNorm2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨3, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetCorrPlus_triangle2571
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨3, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcpP003Rounded2571) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjcpP003RoundedError2571 (embedPair_magnitude2542
      fjcpP003Rounded2571))
  apply h'.trans
  norm_num [fjcpP003Radius2571, pairMagnitude2542, fjcpP003Rounded2571]

noncomputable def fjcpP004Input2571 : RatPair2542 := ((((-((4673 * 10^40
        + 4597880448384906672533435637131642652828) * 10^40
        + 431693750250106491058255045937428262959)) : ℚ) /
        ((29780 * 10^40
        + 5895054484312759971766663273404887092534) * 10^40
        + 1331668037402944633489225469132800000000)),
    ((1751911280236833479653958331 : ℚ) /
        3689348814741910323200000000))

def fjcpP004Center2571 : RatPair2542 := ((((-1498581575969300851911523103931) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((4270544877866285909173470095625 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def fjcpP004Factor2571 : RatPair2542 := ((((((49506120272990836016484 * 10^40
        + 538440731705255384998620093587205991356) * 10^40
        + 1801622978639223413569344746755076688363) * 10^40
        + 9685227492010182942675068950658681632561) : ℚ) /
        (((6452926836878943435502 * 10^40
        + 5270363476754729271482605203204217239397) * 10^40
        + 2433289965035647104971396368485606800583) * 10^40
        + 9158788578070925885350137901317363265122)),
    (((-5524291025718029) : ℚ) /
        140737488355328))

noncomputable def fjcpP004Error2571 : ℝ := ((17699073006843670952439380847 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjcpP004BaseError2571 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨4, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcpP004Center2571‖ ≤ fjcpP004Error2571 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjcpP004Input2571‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjcpP004Input2571]
  have hc : (compactExp2547 fjcpP004Input2571 8).1 = fjcpP004Center2571 := by cbv
  have he : ((compactExp2547 fjcpP004Input2571 8).2 : ℝ) = fjcpP004Error2571 := by
    have hq : (compactExp2547 fjcpP004Input2571 8).2 =
        ((17699073006843670952439380847 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjcpP004Error2571]
  have h := compactExp_error2547 fjcpP004Input2571 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨4, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^8 * embedPair2542 fjcpP004Input2571) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjcpP004Input2571, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjcpP004DerivativeError2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨4, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjcpP004Factor2571 * embedPair2542 fjcpP004Center2571‖ ≤
        (pairMagnitude2542 fjcpP004Factor2571 : ℝ) * fjcpP004Error2571 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (1/2)
      (nodeModulation2541 ⟨4, by omega⟩)
      (storedWidth ⟨4, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjcpP004Factor2571 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjcpP004Factor2571, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (1/2)
    (nodeModulation2541 ⟨4, by omega⟩) (pow_pos (storedWidth_pos ⟨4, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjcpP004BaseError2571
    (embedPair_magnitude2542 fjcpP004Factor2571)

def fjcpP004Rounded2571 : RatPair2542 :=
  (((62725627062873 : ℚ) /
        633825300114114700748351602688),
    ((16307390202537 : ℚ) /
        158456325028528675187087900672))

noncomputable def fjcpP004Radius2571 : ℝ := ((2919382120955 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjcpP004RoundCompute2571 :
    pairRound2542 (pairMul2542 fjcpP004Factor2571 fjcpP004Center2571) = fjcpP004Rounded2571 := by
  cbv

theorem fjcpP004RoundedError2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨4, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcpP004Rounded2571‖ ≤ fjcpP004Radius2571 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjcpP004Factor2571 fjcpP004Center2571)
  rw [fjcpP004RoundCompute2571, embedPair_mul2542] at hr
  have h := (firstJetCorrPlus_triangle2571
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨4, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcpP004Factor2571 * embedPair2542 fjcpP004Center2571)
    (embedPair2542 fjcpP004Rounded2571)).trans (add_le_add fjcpP004DerivativeError2571 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjcpP004Factor2571, fjcpP004Error2571, rounding2542,
      fjcpP004Radius2571]

theorem fjcpP004DerivativeNorm2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨4, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetCorrPlus_triangle2571
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨4, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcpP004Rounded2571) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjcpP004RoundedError2571 (embedPair_magnitude2542
      fjcpP004Rounded2571))
  apply h'.trans
  norm_num [fjcpP004Radius2571, pairMagnitude2542, fjcpP004Rounded2571]

def fjcpP005Center2571 : RatPair2542 := (0, 0)

def fjcpP005Factor2571 : RatPair2542 := (0, 0)

noncomputable def fjcpP005Error2571 : ℝ := 0

theorem fjcpP005Exterior2571 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨5, by omega⟩
      edgeMidpointPosition2548 = 0 := by
  have hx : storedWidth ⟨5, by omega⟩ ^ 2 ≤ |edgeMidpointPosition2548| := by
    norm_num [storedWidth, edgeMidpointPosition2548]
  exact weightedFamily_outside_zero2543 n (1/2)
    (nodeModulation2541 ⟨5, by omega⟩)
    (pow_pos (storedWidth_pos ⟨5, by omega⟩) 2) hx

theorem fjcpP005BaseError2571 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨5, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcpP005Center2571‖ ≤ fjcpP005Error2571 := by
  rw [fjcpP005Exterior2571]
  norm_num [fjcpP005Center2571, fjcpP005Error2571, fjcpZero2571]

theorem fjcpP005DerivativeError2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨5, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjcpP005Factor2571 * embedPair2542 fjcpP005Center2571‖ ≤
        (pairMagnitude2542 fjcpP005Factor2571 : ℝ) * fjcpP005Error2571 := by
  rw [fjcpP005Exterior2571]
  norm_num [fjcpP005Factor2571, fjcpP005Center2571, fjcpP005Error2571, pairMagnitude2542,
      fjcpZero2571]

def fjcpP005Rounded2571 : RatPair2542 := (0, 0)

noncomputable def fjcpP005Radius2571 : ℝ := 0

theorem fjcpP005RoundCompute2571 :
    pairRound2542 (pairMul2542 fjcpP005Factor2571 fjcpP005Center2571) = fjcpP005Rounded2571 := by
  cbv

theorem fjcpP005RoundedError2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨5, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcpP005Rounded2571‖ ≤ fjcpP005Radius2571 := by
  rw [fjcpP005Exterior2571]
  norm_num [fjcpP005Rounded2571, fjcpP005Radius2571, fjcpZero2571]

theorem fjcpP005DerivativeNorm2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨5, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  rw [fjcpP005Exterior2571]
  norm_num

noncomputable def fjcpP006Input2571 : RatPair2542 := ((((-1052103689295998182959213518129206281) :
    ℚ) /
        1761648103394083163919587737600000000),
    ((0 : ℚ) /
        1))

def fjcpP006Center2571 : RatPair2542 := (((922862892562499 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def fjcpP006Factor2571 : RatPair2542 := ((((65830361 * 10^40
        + 5132605816725219886317410093330580982241) : ℚ) /
        (903209 * 10^40
        + 4502448949280199772634820186661161964482)),
    ((0 : ℚ) /
        1))

noncomputable def fjcpP006Error2571 : ℝ := ((1217513621385 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem fjcpP006BaseError2571 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨6, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcpP006Center2571‖ ≤ fjcpP006Error2571 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjcpP006Input2571‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjcpP006Input2571]
  have hc : (compactExp2547 fjcpP006Input2571 7).1 = fjcpP006Center2571 := by cbv
  have he : ((compactExp2547 fjcpP006Input2571 7).2 : ℝ) = fjcpP006Error2571 := by
    have hq : (compactExp2547 fjcpP006Input2571 7).2 =
        ((1217513621385 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)) := by cbv
    rw [hq]
    norm_num [fjcpP006Error2571]
  have h := compactExp_error2547 fjcpP006Input2571 hz 7
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨6, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^7 * embedPair2542 fjcpP006Input2571) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjcpP006Input2571, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjcpP006DerivativeError2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨6, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjcpP006Factor2571 * embedPair2542 fjcpP006Center2571‖ ≤
        (pairMagnitude2542 fjcpP006Factor2571 : ℝ) * fjcpP006Error2571 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (1/2)
      (nodeModulation2541 ⟨6, by omega⟩)
      (storedWidth ⟨6, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjcpP006Factor2571 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjcpP006Factor2571, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (1/2)
    (nodeModulation2541 ⟨6, by omega⟩) (pow_pos (storedWidth_pos ⟨6, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjcpP006BaseError2571
    (embedPair_magnitude2542 fjcpP006Factor2571)

def fjcpP006Rounded2571 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjcpP006Radius2571 : ℝ := ((2199023255553 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjcpP006RoundCompute2571 :
    pairRound2542 (pairMul2542 fjcpP006Factor2571 fjcpP006Center2571) = fjcpP006Rounded2571 := by
  cbv

theorem fjcpP006RoundedError2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨6, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcpP006Rounded2571‖ ≤ fjcpP006Radius2571 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjcpP006Factor2571 fjcpP006Center2571)
  rw [fjcpP006RoundCompute2571, embedPair_mul2542] at hr
  have h := (firstJetCorrPlus_triangle2571
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨6, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcpP006Factor2571 * embedPair2542 fjcpP006Center2571)
    (embedPair2542 fjcpP006Rounded2571)).trans (add_le_add fjcpP006DerivativeError2571 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjcpP006Factor2571, fjcpP006Error2571, rounding2542,
      fjcpP006Radius2571]

theorem fjcpP006DerivativeNorm2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨6, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetCorrPlus_triangle2571
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨6, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcpP006Rounded2571) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjcpP006RoundedError2571 (embedPair_magnitude2542
      fjcpP006Rounded2571))
  apply h'.trans
  norm_num [fjcpP006Radius2571, pairMagnitude2542, fjcpP006Rounded2571]

noncomputable def fjcpP007Input2571 : RatPair2542 := ((((-((7224110 * 10^40
        + 4406628376595866370136231705353501324162) * 10^40
        + 1511332573809066646429207955160645591911)) : ℚ) /
        ((9965107 * 10^40
        + 8381342301379574219443224222204798749052) * 10^40
        + 4506946462156526889793870220492800000000)),
    ((0 : ℚ) /
        1))

def fjcpP007Center2571 : RatPair2542 := (((10355918689374196829550765419 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def fjcpP007Factor2571 : RatPair2542 := ((((((171489622156943000195426447198 * 10^40
        + 6062598187743684290659208420886884284629) * 10^40
        + 1535621732405997006189222369556390501971) * 10^40
        + 5719713847345472865924858164472905824001) : ℚ) /
        (((11560434268978921445520672852 * 10^40
        + 3151491610707945740034502288795420775469) * 10^40
        + 9342842308133684351566010846049001848136) * 10^40
        + 2052163694690945731849716328945811648002)),
    ((0 : ℚ) /
        1))

noncomputable def fjcpP007Error2571 : ℝ := ((1504548178364114737319599 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjcpP007BaseError2571 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨7, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcpP007Center2571‖ ≤ fjcpP007Error2571 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjcpP007Input2571‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjcpP007Input2571]
  have hc : (compactExp2547 fjcpP007Input2571 6).1 = fjcpP007Center2571 := by cbv
  have he : ((compactExp2547 fjcpP007Input2571 6).2 : ℝ) = fjcpP007Error2571 := by
    have hq : (compactExp2547 fjcpP007Input2571 6).2 =
        ((1504548178364114737319599 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjcpP007Error2571]
  have h := compactExp_error2547 fjcpP007Input2571 hz 6
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨7, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^6 * embedPair2542 fjcpP007Input2571) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjcpP007Input2571, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjcpP007DerivativeError2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨7, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjcpP007Factor2571 * embedPair2542 fjcpP007Center2571‖ ≤
        (pairMagnitude2542 fjcpP007Factor2571 : ℝ) * fjcpP007Error2571 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (1/2)
      (nodeModulation2541 ⟨7, by omega⟩)
      (storedWidth ⟨7, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjcpP007Factor2571 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjcpP007Factor2571, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (1/2)
    (nodeModulation2541 ⟨7, by omega⟩) (pow_pos (storedWidth_pos ⟨7, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjcpP007BaseError2571
    (embedPair_magnitude2542 fjcpP007Factor2571)

def fjcpP007Rounded2571 : RatPair2542 :=
  (((66622755513 : ℚ) /
        633825300114114700748351602688),
    ((0 : ℚ) /
        1))

noncomputable def fjcpP007Radius2571 : ℝ := ((2199042613979 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjcpP007RoundCompute2571 :
    pairRound2542 (pairMul2542 fjcpP007Factor2571 fjcpP007Center2571) = fjcpP007Rounded2571 := by
  cbv

theorem fjcpP007RoundedError2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨7, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcpP007Rounded2571‖ ≤ fjcpP007Radius2571 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjcpP007Factor2571 fjcpP007Center2571)
  rw [fjcpP007RoundCompute2571, embedPair_mul2542] at hr
  have h := (firstJetCorrPlus_triangle2571
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨7, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcpP007Factor2571 * embedPair2542 fjcpP007Center2571)
    (embedPair2542 fjcpP007Rounded2571)).trans (add_le_add fjcpP007DerivativeError2571 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjcpP007Factor2571, fjcpP007Error2571, rounding2542,
      fjcpP007Radius2571]

theorem fjcpP007DerivativeNorm2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨7, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetCorrPlus_triangle2571
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨7, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcpP007Rounded2571) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjcpP007RoundedError2571 (embedPair_magnitude2542
      fjcpP007Rounded2571))
  apply h'.trans
  norm_num [fjcpP007Radius2571, pairMagnitude2542, fjcpP007Rounded2571]

noncomputable def fjcpP008Input2571 : RatPair2542 := ((((-((2312865 * 10^40
        + 2146202435957712102129842483917578410111) * 10^40
        + 4883202856058925867669125359945801841911)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((1261719220645415482412484183 : ℚ) /
        3777893186295716170956800000000))

def fjcpP008Center2571 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjcpP008Factor2571 : RatPair2542 := ((((((54884017178483696463843476644 * 10^40
        + 3898147926987883407731067498735338895921) * 10^40
        + 9215765718423453974090306379227006153950) * 10^40
        + 6214940542152917628175240386152593324001) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-3978571430081297) : ℚ) /
        281474976710656))

noncomputable def fjcpP008Error2571 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjcpP008BaseError2571 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨8, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcpP008Center2571‖ ≤ fjcpP008Error2571 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨8, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjcpP008Input2571‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjcpP008Input2571]
  have hc : (compactExp2547 fjcpP008Input2571 17).1 = fjcpP008Center2571 := by cbv
  have he : ((compactExp2547 fjcpP008Input2571 17).2 : ℝ) = fjcpP008Error2571 := by
    have hq : (compactExp2547 fjcpP008Input2571 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjcpP008Error2571]
  have h := compactExp_error2547 fjcpP008Input2571 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨8, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjcpP008Input2571) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjcpP008Input2571, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjcpP008DerivativeError2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨8, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjcpP008Factor2571 * embedPair2542 fjcpP008Center2571‖ ≤
        (pairMagnitude2542 fjcpP008Factor2571 : ℝ) * fjcpP008Error2571 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨8, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (1/2)
      (nodeModulation2541 ⟨8, by omega⟩)
      (storedWidth ⟨8, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjcpP008Factor2571 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjcpP008Factor2571, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (1/2)
    (nodeModulation2541 ⟨8, by omega⟩) (pow_pos (storedWidth_pos ⟨8, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjcpP008BaseError2571
    (embedPair_magnitude2542 fjcpP008Factor2571)

def fjcpP008Rounded2571 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjcpP008Radius2571 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjcpP008RoundCompute2571 :
    pairRound2542 (pairMul2542 fjcpP008Factor2571 fjcpP008Center2571) = fjcpP008Rounded2571 := by
  cbv

theorem fjcpP008RoundedError2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨8, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcpP008Rounded2571‖ ≤ fjcpP008Radius2571 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjcpP008Factor2571 fjcpP008Center2571)
  rw [fjcpP008RoundCompute2571, embedPair_mul2542] at hr
  have h := (firstJetCorrPlus_triangle2571
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨8, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcpP008Factor2571 * embedPair2542 fjcpP008Center2571)
    (embedPair2542 fjcpP008Rounded2571)).trans (add_le_add fjcpP008DerivativeError2571 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjcpP008Factor2571, fjcpP008Error2571, rounding2542,
      fjcpP008Radius2571]

theorem fjcpP008DerivativeNorm2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨8, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetCorrPlus_triangle2571
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨8, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcpP008Rounded2571) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjcpP008RoundedError2571 (embedPair_magnitude2542
      fjcpP008Rounded2571))
  apply h'.trans
  norm_num [fjcpP008Radius2571, pairMagnitude2542, fjcpP008Rounded2571]

noncomputable def fjcpP009Input2571 : RatPair2542 := ((((-((2312865 * 10^40
        + 2146202435957712102129842483917578410111) * 10^40
        + 4883202856058925867669125359945801841911)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((1876507056447276098253971529 : ℚ) /
        3777893186295716170956800000000))

def fjcpP009Center2571 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjcpP009Factor2571 : RatPair2542 := ((((((54884017178483696463843476644 * 10^40
        + 3898147926987883407731067498735338895921) * 10^40
        + 9215765718423453974090306379227006153950) * 10^40
        + 6214940542152917628175240386152593324001) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-5917178117733711) : ℚ) /
        281474976710656))

noncomputable def fjcpP009Error2571 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjcpP009BaseError2571 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨9, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcpP009Center2571‖ ≤ fjcpP009Error2571 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨9, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjcpP009Input2571‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjcpP009Input2571]
  have hc : (compactExp2547 fjcpP009Input2571 17).1 = fjcpP009Center2571 := by cbv
  have he : ((compactExp2547 fjcpP009Input2571 17).2 : ℝ) = fjcpP009Error2571 := by
    have hq : (compactExp2547 fjcpP009Input2571 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjcpP009Error2571]
  have h := compactExp_error2547 fjcpP009Input2571 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨9, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjcpP009Input2571) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjcpP009Input2571, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjcpP009DerivativeError2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨9, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjcpP009Factor2571 * embedPair2542 fjcpP009Center2571‖ ≤
        (pairMagnitude2542 fjcpP009Factor2571 : ℝ) * fjcpP009Error2571 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨9, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (1/2)
      (nodeModulation2541 ⟨9, by omega⟩)
      (storedWidth ⟨9, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjcpP009Factor2571 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjcpP009Factor2571, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (1/2)
    (nodeModulation2541 ⟨9, by omega⟩) (pow_pos (storedWidth_pos ⟨9, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjcpP009BaseError2571
    (embedPair_magnitude2542 fjcpP009Factor2571)

def fjcpP009Rounded2571 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjcpP009Radius2571 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjcpP009RoundCompute2571 :
    pairRound2542 (pairMul2542 fjcpP009Factor2571 fjcpP009Center2571) = fjcpP009Rounded2571 := by
  cbv

theorem fjcpP009RoundedError2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨9, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcpP009Rounded2571‖ ≤ fjcpP009Radius2571 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjcpP009Factor2571 fjcpP009Center2571)
  rw [fjcpP009RoundCompute2571, embedPair_mul2542] at hr
  have h := (firstJetCorrPlus_triangle2571
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨9, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcpP009Factor2571 * embedPair2542 fjcpP009Center2571)
    (embedPair2542 fjcpP009Rounded2571)).trans (add_le_add fjcpP009DerivativeError2571 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjcpP009Factor2571, fjcpP009Error2571, rounding2542,
      fjcpP009Radius2571]

theorem fjcpP009DerivativeNorm2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨9, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetCorrPlus_triangle2571
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨9, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcpP009Rounded2571) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjcpP009RoundedError2571 (embedPair_magnitude2542
      fjcpP009Rounded2571))
  apply h'.trans
  norm_num [fjcpP009Radius2571, pairMagnitude2542, fjcpP009Rounded2571]

noncomputable def fjcpP010Input2571 : RatPair2542 := ((((-((2312865 * 10^40
        + 2146202435957712102129842483917578410111) * 10^40
        + 4883202856058925867669125359945801841911)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((1116282043593459096767143119 : ℚ) /
        1888946593147858085478400000000))

def fjcpP010Center2571 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjcpP010Factor2571 : RatPair2542 := ((((((54884017178483696463843476644 * 10^40
        + 3898147926987883407731067498735338895921) * 10^40
        + 9215765718423453974090306379227006153950) * 10^40
        + 6214940542152917628175240386152593324001) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-3519965277442521) : ℚ) /
        140737488355328))

noncomputable def fjcpP010Error2571 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjcpP010BaseError2571 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨10, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcpP010Center2571‖ ≤ fjcpP010Error2571 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨10, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjcpP010Input2571‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjcpP010Input2571]
  have hc : (compactExp2547 fjcpP010Input2571 17).1 = fjcpP010Center2571 := by cbv
  have he : ((compactExp2547 fjcpP010Input2571 17).2 : ℝ) = fjcpP010Error2571 := by
    have hq : (compactExp2547 fjcpP010Input2571 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjcpP010Error2571]
  have h := compactExp_error2547 fjcpP010Input2571 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨10, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjcpP010Input2571) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjcpP010Input2571, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjcpP010DerivativeError2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨10, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjcpP010Factor2571 * embedPair2542 fjcpP010Center2571‖ ≤
        (pairMagnitude2542 fjcpP010Factor2571 : ℝ) * fjcpP010Error2571 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨10, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (1/2)
      (nodeModulation2541 ⟨10, by omega⟩)
      (storedWidth ⟨10, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjcpP010Factor2571 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjcpP010Factor2571, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (1/2)
    (nodeModulation2541 ⟨10, by omega⟩) (pow_pos (storedWidth_pos ⟨10, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjcpP010BaseError2571
    (embedPair_magnitude2542 fjcpP010Factor2571)

def fjcpP010Rounded2571 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjcpP010Radius2571 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjcpP010RoundCompute2571 :
    pairRound2542 (pairMul2542 fjcpP010Factor2571 fjcpP010Center2571) = fjcpP010Rounded2571 := by
  cbv

theorem fjcpP010RoundedError2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨10, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcpP010Rounded2571‖ ≤ fjcpP010Radius2571 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjcpP010Factor2571 fjcpP010Center2571)
  rw [fjcpP010RoundCompute2571, embedPair_mul2542] at hr
  have h := (firstJetCorrPlus_triangle2571
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨10, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcpP010Factor2571 * embedPair2542 fjcpP010Center2571)
    (embedPair2542 fjcpP010Rounded2571)).trans (add_le_add fjcpP010DerivativeError2571 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjcpP010Factor2571, fjcpP010Error2571, rounding2542,
      fjcpP010Radius2571]

theorem fjcpP010DerivativeNorm2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨10, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetCorrPlus_triangle2571
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨10, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcpP010Rounded2571) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjcpP010RoundedError2571 (embedPair_magnitude2542
      fjcpP010Rounded2571))
  apply h'.trans
  norm_num [fjcpP010Radius2571, pairMagnitude2542, fjcpP010Rounded2571]

noncomputable def fjcpP011Input2571 : RatPair2542 := ((((-((2312865 * 10^40
        + 2146202435957712102129842483917578410111) * 10^40
        + 4883202856058925867669125359945801841911)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((1234978985119947335660559039 : ℚ) /
        1888946593147858085478400000000))

def fjcpP011Center2571 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjcpP011Factor2571 : RatPair2542 := ((((((54884017178483696463843476644 * 10^40
        + 3898147926987883407731067498735338895921) * 10^40
        + 9215765718423453974090306379227006153950) * 10^40
        + 6214940542152917628175240386152593324001) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-3894251610461801) : ℚ) /
        140737488355328))

noncomputable def fjcpP011Error2571 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjcpP011BaseError2571 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨11, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcpP011Center2571‖ ≤ fjcpP011Error2571 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨11, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjcpP011Input2571‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjcpP011Input2571]
  have hc : (compactExp2547 fjcpP011Input2571 17).1 = fjcpP011Center2571 := by cbv
  have he : ((compactExp2547 fjcpP011Input2571 17).2 : ℝ) = fjcpP011Error2571 := by
    have hq : (compactExp2547 fjcpP011Input2571 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjcpP011Error2571]
  have h := compactExp_error2547 fjcpP011Input2571 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨11, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjcpP011Input2571) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjcpP011Input2571, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjcpP011DerivativeError2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨11, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjcpP011Factor2571 * embedPair2542 fjcpP011Center2571‖ ≤
        (pairMagnitude2542 fjcpP011Factor2571 : ℝ) * fjcpP011Error2571 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨11, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (1/2)
      (nodeModulation2541 ⟨11, by omega⟩)
      (storedWidth ⟨11, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjcpP011Factor2571 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjcpP011Factor2571, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (1/2)
    (nodeModulation2541 ⟨11, by omega⟩) (pow_pos (storedWidth_pos ⟨11, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjcpP011BaseError2571
    (embedPair_magnitude2542 fjcpP011Factor2571)

def fjcpP011Rounded2571 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjcpP011Radius2571 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjcpP011RoundCompute2571 :
    pairRound2542 (pairMul2542 fjcpP011Factor2571 fjcpP011Center2571) = fjcpP011Rounded2571 := by
  cbv

theorem fjcpP011RoundedError2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨11, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcpP011Rounded2571‖ ≤ fjcpP011Radius2571 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjcpP011Factor2571 fjcpP011Center2571)
  rw [fjcpP011RoundCompute2571, embedPair_mul2542] at hr
  have h := (firstJetCorrPlus_triangle2571
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨11, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcpP011Factor2571 * embedPair2542 fjcpP011Center2571)
    (embedPair2542 fjcpP011Rounded2571)).trans (add_le_add fjcpP011DerivativeError2571 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjcpP011Factor2571, fjcpP011Error2571, rounding2542,
      fjcpP011Radius2571]

theorem fjcpP011DerivativeNorm2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨11, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetCorrPlus_triangle2571
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨11, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcpP011Rounded2571) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjcpP011RoundedError2571 (embedPair_magnitude2542
      fjcpP011Rounded2571))
  apply h'.trans
  norm_num [fjcpP011Radius2571, pairMagnitude2542, fjcpP011Rounded2571]

noncomputable def fjcpP012Input2571 : RatPair2542 := ((((-((2312865 * 10^40
        + 2146202435957712102129842483917578410111) * 10^40
        + 4883202856058925867669125359945801841911)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((27158399338384035222570051 : ℚ) /
        37778931862957161709568000000))

def fjcpP012Center2571 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjcpP012Factor2571 : RatPair2542 := ((((((54884017178483696463843476644 * 10^40
        + 3898147926987883407731067498735338895921) * 10^40
        + 9215765718423453974090306379227006153950) * 10^40
        + 6214940542152917628175240386152593324001) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-2140960324737725) : ℚ) /
        70368744177664))

noncomputable def fjcpP012Error2571 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjcpP012BaseError2571 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨12, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcpP012Center2571‖ ≤ fjcpP012Error2571 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨12, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjcpP012Input2571‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjcpP012Input2571]
  have hc : (compactExp2547 fjcpP012Input2571 17).1 = fjcpP012Center2571 := by cbv
  have he : ((compactExp2547 fjcpP012Input2571 17).2 : ℝ) = fjcpP012Error2571 := by
    have hq : (compactExp2547 fjcpP012Input2571 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjcpP012Error2571]
  have h := compactExp_error2547 fjcpP012Input2571 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨12, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjcpP012Input2571) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjcpP012Input2571, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjcpP012DerivativeError2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨12, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjcpP012Factor2571 * embedPair2542 fjcpP012Center2571‖ ≤
        (pairMagnitude2542 fjcpP012Factor2571 : ℝ) * fjcpP012Error2571 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨12, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (1/2)
      (nodeModulation2541 ⟨12, by omega⟩)
      (storedWidth ⟨12, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjcpP012Factor2571 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjcpP012Factor2571, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (1/2)
    (nodeModulation2541 ⟨12, by omega⟩) (pow_pos (storedWidth_pos ⟨12, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjcpP012BaseError2571
    (embedPair_magnitude2542 fjcpP012Factor2571)

def fjcpP012Rounded2571 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjcpP012Radius2571 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjcpP012RoundCompute2571 :
    pairRound2542 (pairMul2542 fjcpP012Factor2571 fjcpP012Center2571) = fjcpP012Rounded2571 := by
  cbv

theorem fjcpP012RoundedError2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨12, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcpP012Rounded2571‖ ≤ fjcpP012Radius2571 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjcpP012Factor2571 fjcpP012Center2571)
  rw [fjcpP012RoundCompute2571, embedPair_mul2542] at hr
  have h := (firstJetCorrPlus_triangle2571
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨12, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcpP012Factor2571 * embedPair2542 fjcpP012Center2571)
    (embedPair2542 fjcpP012Rounded2571)).trans (add_le_add fjcpP012DerivativeError2571 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjcpP012Factor2571, fjcpP012Error2571, rounding2542,
      fjcpP012Radius2571]

theorem fjcpP012DerivativeNorm2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨12, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetCorrPlus_triangle2571
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨12, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcpP012Rounded2571) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjcpP012RoundedError2571 (embedPair_magnitude2542
      fjcpP012Rounded2571))
  apply h'.trans
  norm_num [fjcpP012Radius2571, pairMagnitude2542, fjcpP012Rounded2571]

noncomputable def fjcpP013Input2571 : RatPair2542 := ((((-((2312865 * 10^40
        + 2146202435957712102129842483917578410111) * 10^40
        + 4883202856058925867669125359945801841911)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((293990861666597709724015149 : ℚ) /
        377789318629571617095680000000))

def fjcpP013Center2571 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjcpP013Factor2571 : RatPair2542 := ((((((54884017178483696463843476644 * 10^40
        + 3898147926987883407731067498735338895921) * 10^40
        + 9215765718423453974090306379227006153950) * 10^40
        + 6214940542152917628175240386152593324001) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-4635197846686455) : ℚ) /
        140737488355328))

noncomputable def fjcpP013Error2571 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjcpP013BaseError2571 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨13, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcpP013Center2571‖ ≤ fjcpP013Error2571 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨13, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjcpP013Input2571‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjcpP013Input2571]
  have hc : (compactExp2547 fjcpP013Input2571 17).1 = fjcpP013Center2571 := by cbv
  have he : ((compactExp2547 fjcpP013Input2571 17).2 : ℝ) = fjcpP013Error2571 := by
    have hq : (compactExp2547 fjcpP013Input2571 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjcpP013Error2571]
  have h := compactExp_error2547 fjcpP013Input2571 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨13, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjcpP013Input2571) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjcpP013Input2571, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjcpP013DerivativeError2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨13, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjcpP013Factor2571 * embedPair2542 fjcpP013Center2571‖ ≤
        (pairMagnitude2542 fjcpP013Factor2571 : ℝ) * fjcpP013Error2571 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨13, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (1/2)
      (nodeModulation2541 ⟨13, by omega⟩)
      (storedWidth ⟨13, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjcpP013Factor2571 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjcpP013Factor2571, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (1/2)
    (nodeModulation2541 ⟨13, by omega⟩) (pow_pos (storedWidth_pos ⟨13, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjcpP013BaseError2571
    (embedPair_magnitude2542 fjcpP013Factor2571)

def fjcpP013Rounded2571 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjcpP013Radius2571 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjcpP013RoundCompute2571 :
    pairRound2542 (pairMul2542 fjcpP013Factor2571 fjcpP013Center2571) = fjcpP013Rounded2571 := by
  cbv

theorem fjcpP013RoundedError2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨13, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcpP013Rounded2571‖ ≤ fjcpP013Radius2571 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjcpP013Factor2571 fjcpP013Center2571)
  rw [fjcpP013RoundCompute2571, embedPair_mul2542] at hr
  have h := (firstJetCorrPlus_triangle2571
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨13, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcpP013Factor2571 * embedPair2542 fjcpP013Center2571)
    (embedPair2542 fjcpP013Rounded2571)).trans (add_le_add fjcpP013DerivativeError2571 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjcpP013Factor2571, fjcpP013Error2571, rounding2542,
      fjcpP013Radius2571]

theorem fjcpP013DerivativeNorm2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨13, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetCorrPlus_triangle2571
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨13, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcpP013Rounded2571) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjcpP013RoundedError2571 (embedPair_magnitude2542
      fjcpP013Rounded2571))
  apply h'.trans
  norm_num [fjcpP013Radius2571, pairMagnitude2542, fjcpP013Rounded2571]

noncomputable def fjcpP014Input2571 : RatPair2542 := ((((-((2312865 * 10^40
        + 2146202435957712102129842483917578410111) * 10^40
        + 4883202856058925867669125359945801841911)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((1677542468568059149194008229 : ℚ) /
        1888946593147858085478400000000))

def fjcpP014Center2571 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjcpP014Factor2571 : RatPair2542 := ((((((54884017178483696463843476644 * 10^40
        + 3898147926987883407731067498735338895921) * 10^40
        + 9215765718423453974090306379227006153950) * 10^40
        + 6214940542152917628175240386152593324001) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-5289784310949011) : ℚ) /
        140737488355328))

noncomputable def fjcpP014Error2571 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjcpP014BaseError2571 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨14, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcpP014Center2571‖ ≤ fjcpP014Error2571 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨14, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjcpP014Input2571‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjcpP014Input2571]
  have hc : (compactExp2547 fjcpP014Input2571 17).1 = fjcpP014Center2571 := by cbv
  have he : ((compactExp2547 fjcpP014Input2571 17).2 : ℝ) = fjcpP014Error2571 := by
    have hq : (compactExp2547 fjcpP014Input2571 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjcpP014Error2571]
  have h := compactExp_error2547 fjcpP014Input2571 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨14, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjcpP014Input2571) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjcpP014Input2571, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjcpP014DerivativeError2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨14, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjcpP014Factor2571 * embedPair2542 fjcpP014Center2571‖ ≤
        (pairMagnitude2542 fjcpP014Factor2571 : ℝ) * fjcpP014Error2571 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨14, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (1/2)
      (nodeModulation2541 ⟨14, by omega⟩)
      (storedWidth ⟨14, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjcpP014Factor2571 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjcpP014Factor2571, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (1/2)
    (nodeModulation2541 ⟨14, by omega⟩) (pow_pos (storedWidth_pos ⟨14, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjcpP014BaseError2571
    (embedPair_magnitude2542 fjcpP014Factor2571)

def fjcpP014Rounded2571 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjcpP014Radius2571 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjcpP014RoundCompute2571 :
    pairRound2542 (pairMul2542 fjcpP014Factor2571 fjcpP014Center2571) = fjcpP014Rounded2571 := by
  cbv

theorem fjcpP014RoundedError2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨14, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcpP014Rounded2571‖ ≤ fjcpP014Radius2571 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjcpP014Factor2571 fjcpP014Center2571)
  rw [fjcpP014RoundCompute2571, embedPair_mul2542] at hr
  have h := (firstJetCorrPlus_triangle2571
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨14, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcpP014Factor2571 * embedPair2542 fjcpP014Center2571)
    (embedPair2542 fjcpP014Rounded2571)).trans (add_le_add fjcpP014DerivativeError2571 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjcpP014Factor2571, fjcpP014Error2571, rounding2542,
      fjcpP014Radius2571]

theorem fjcpP014DerivativeNorm2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨14, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetCorrPlus_triangle2571
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨14, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcpP014Rounded2571) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjcpP014RoundedError2571 (embedPair_magnitude2542
      fjcpP014Rounded2571))
  apply h'.trans
  norm_num [fjcpP014Radius2571, pairMagnitude2542, fjcpP014Rounded2571]

noncomputable def fjcpP015Input2571 : RatPair2542 := ((((-((2312865 * 10^40
        + 2146202435957712102129842483917578410111) * 10^40
        + 4883202856058925867669125359945801841911)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((1826280091905607810113908433 : ℚ) /
        1888946593147858085478400000000))

def fjcpP015Center2571 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjcpP015Factor2571 : RatPair2542 := ((((((54884017178483696463843476644 * 10^40
        + 3898147926987883407731067498735338895921) * 10^40
        + 9215765718423453974090306379227006153950) * 10^40
        + 6214940542152917628175240386152593324001) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-5758797740487047) : ℚ) /
        140737488355328))

noncomputable def fjcpP015Error2571 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjcpP015BaseError2571 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨15, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcpP015Center2571‖ ≤ fjcpP015Error2571 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjcpP015Input2571‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjcpP015Input2571]
  have hc : (compactExp2547 fjcpP015Input2571 17).1 = fjcpP015Center2571 := by cbv
  have he : ((compactExp2547 fjcpP015Input2571 17).2 : ℝ) = fjcpP015Error2571 := by
    have hq : (compactExp2547 fjcpP015Input2571 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjcpP015Error2571]
  have h := compactExp_error2547 fjcpP015Input2571 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨15, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjcpP015Input2571) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjcpP015Input2571, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjcpP015DerivativeError2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨15, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjcpP015Factor2571 * embedPair2542 fjcpP015Center2571‖ ≤
        (pairMagnitude2542 fjcpP015Factor2571 : ℝ) * fjcpP015Error2571 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (1/2)
      (nodeModulation2541 ⟨15, by omega⟩)
      (storedWidth ⟨15, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjcpP015Factor2571 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjcpP015Factor2571, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (1/2)
    (nodeModulation2541 ⟨15, by omega⟩) (pow_pos (storedWidth_pos ⟨15, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjcpP015BaseError2571
    (embedPair_magnitude2542 fjcpP015Factor2571)

def fjcpP015Rounded2571 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjcpP015Radius2571 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjcpP015RoundCompute2571 :
    pairRound2542 (pairMul2542 fjcpP015Factor2571 fjcpP015Center2571) = fjcpP015Rounded2571 := by
  cbv

theorem fjcpP015RoundedError2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨15, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcpP015Rounded2571‖ ≤ fjcpP015Radius2571 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjcpP015Factor2571 fjcpP015Center2571)
  rw [fjcpP015RoundCompute2571, embedPair_mul2542] at hr
  have h := (firstJetCorrPlus_triangle2571
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨15, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcpP015Factor2571 * embedPair2542 fjcpP015Center2571)
    (embedPair2542 fjcpP015Rounded2571)).trans (add_le_add fjcpP015DerivativeError2571 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjcpP015Factor2571, fjcpP015Error2571, rounding2542,
      fjcpP015Radius2571]

theorem fjcpP015DerivativeNorm2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨15, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetCorrPlus_triangle2571
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨15, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcpP015Rounded2571) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjcpP015RoundedError2571 (embedPair_magnitude2542
      fjcpP015Rounded2571))
  apply h'.trans
  norm_num [fjcpP015Radius2571, pairMagnitude2542, fjcpP015Rounded2571]

noncomputable def fjcpP016Input2571 : RatPair2542 := ((((-((2312865 * 10^40
        + 2146202435957712102129842483917578410111) * 10^40
        + 4883202856058925867669125359945801841911)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((966884756949258260679651951 : ℚ) /
        944473296573929042739200000000))

def fjcpP016Center2571 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjcpP016Factor2571 : RatPair2542 := ((((((54884017178483696463843476644 * 10^40
        + 3898147926987883407731067498735338895921) * 10^40
        + 9215765718423453974090306379227006153950) * 10^40
        + 6214940542152917628175240386152593324001) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-3048871735671609) : ℚ) /
        70368744177664))

noncomputable def fjcpP016Error2571 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjcpP016BaseError2571 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨16, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcpP016Center2571‖ ≤ fjcpP016Error2571 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨16, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjcpP016Input2571‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjcpP016Input2571]
  have hc : (compactExp2547 fjcpP016Input2571 17).1 = fjcpP016Center2571 := by cbv
  have he : ((compactExp2547 fjcpP016Input2571 17).2 : ℝ) = fjcpP016Error2571 := by
    have hq : (compactExp2547 fjcpP016Input2571 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjcpP016Error2571]
  have h := compactExp_error2547 fjcpP016Input2571 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨16, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjcpP016Input2571) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjcpP016Input2571, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjcpP016DerivativeError2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨16, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjcpP016Factor2571 * embedPair2542 fjcpP016Center2571‖ ≤
        (pairMagnitude2542 fjcpP016Factor2571 : ℝ) * fjcpP016Error2571 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨16, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (1/2)
      (nodeModulation2541 ⟨16, by omega⟩)
      (storedWidth ⟨16, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjcpP016Factor2571 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjcpP016Factor2571, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (1/2)
    (nodeModulation2541 ⟨16, by omega⟩) (pow_pos (storedWidth_pos ⟨16, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjcpP016BaseError2571
    (embedPair_magnitude2542 fjcpP016Factor2571)

def fjcpP016Rounded2571 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjcpP016Radius2571 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjcpP016RoundCompute2571 :
    pairRound2542 (pairMul2542 fjcpP016Factor2571 fjcpP016Center2571) = fjcpP016Rounded2571 := by
  cbv

theorem fjcpP016RoundedError2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨16, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcpP016Rounded2571‖ ≤ fjcpP016Radius2571 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjcpP016Factor2571 fjcpP016Center2571)
  rw [fjcpP016RoundCompute2571, embedPair_mul2542] at hr
  have h := (firstJetCorrPlus_triangle2571
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨16, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcpP016Factor2571 * embedPair2542 fjcpP016Center2571)
    (embedPair2542 fjcpP016Rounded2571)).trans (add_le_add fjcpP016DerivativeError2571 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjcpP016Factor2571, fjcpP016Error2571, rounding2542,
      fjcpP016Radius2571]

theorem fjcpP016DerivativeNorm2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨16, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetCorrPlus_triangle2571
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨16, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcpP016Rounded2571) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjcpP016RoundedError2571 (embedPair_magnitude2542
      fjcpP016Rounded2571))
  apply h'.trans
  norm_num [fjcpP016Radius2571, pairMagnitude2542, fjcpP016Rounded2571]

noncomputable def fjcpP017Input2571 : RatPair2542 := ((((-((2312865 * 10^40
        + 2146202435957712102129842483917578410111) * 10^40
        + 4883202856058925867669125359945801841911)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((2142560996036405154016564653 : ℚ) /
        1888946593147858085478400000000))

def fjcpP017Center2571 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjcpP017Factor2571 : RatPair2542 := ((((((54884017178483696463843476644 * 10^40
        + 3898147926987883407731067498735338895921) * 10^40
        + 9215765718423453974090306379227006153950) * 10^40
        + 6214940542152917628175240386152593324001) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-6756124363134027) : ℚ) /
        140737488355328))

noncomputable def fjcpP017Error2571 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjcpP017BaseError2571 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨17, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcpP017Center2571‖ ≤ fjcpP017Error2571 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨17, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjcpP017Input2571‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjcpP017Input2571]
  have hc : (compactExp2547 fjcpP017Input2571 17).1 = fjcpP017Center2571 := by cbv
  have he : ((compactExp2547 fjcpP017Input2571 17).2 : ℝ) = fjcpP017Error2571 := by
    have hq : (compactExp2547 fjcpP017Input2571 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjcpP017Error2571]
  have h := compactExp_error2547 fjcpP017Input2571 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨17, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjcpP017Input2571) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjcpP017Input2571, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjcpP017DerivativeError2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨17, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjcpP017Factor2571 * embedPair2542 fjcpP017Center2571‖ ≤
        (pairMagnitude2542 fjcpP017Factor2571 : ℝ) * fjcpP017Error2571 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨17, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (1/2)
      (nodeModulation2541 ⟨17, by omega⟩)
      (storedWidth ⟨17, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjcpP017Factor2571 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjcpP017Factor2571, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (1/2)
    (nodeModulation2541 ⟨17, by omega⟩) (pow_pos (storedWidth_pos ⟨17, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjcpP017BaseError2571
    (embedPair_magnitude2542 fjcpP017Factor2571)

def fjcpP017Rounded2571 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjcpP017Radius2571 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjcpP017RoundCompute2571 :
    pairRound2542 (pairMul2542 fjcpP017Factor2571 fjcpP017Center2571) = fjcpP017Rounded2571 := by
  cbv

theorem fjcpP017RoundedError2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨17, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcpP017Rounded2571‖ ≤ fjcpP017Radius2571 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjcpP017Factor2571 fjcpP017Center2571)
  rw [fjcpP017RoundCompute2571, embedPair_mul2542] at hr
  have h := (firstJetCorrPlus_triangle2571
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨17, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcpP017Factor2571 * embedPair2542 fjcpP017Center2571)
    (embedPair2542 fjcpP017Rounded2571)).trans (add_le_add fjcpP017DerivativeError2571 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjcpP017Factor2571, fjcpP017Error2571, rounding2542,
      fjcpP017Radius2571]

theorem fjcpP017DerivativeNorm2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨17, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetCorrPlus_triangle2571
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨17, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcpP017Rounded2571) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjcpP017RoundedError2571 (embedPair_magnitude2542
      fjcpP017Rounded2571))
  apply h'.trans
  norm_num [fjcpP017Radius2571, pairMagnitude2542, fjcpP017Rounded2571]

noncomputable def fjcpP018Input2571 : RatPair2542 := ((((-((2312865 * 10^40
        + 2146202435957712102129842483917578410111) * 10^40
        + 4883202856058925867669125359945801841911)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((555375153147096446436377307 : ℚ) /
        472236648286964521369600000000))

def fjcpP018Center2571 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjcpP018Factor2571 : RatPair2542 := ((((((54884017178483696463843476644 * 10^40
        + 3898147926987883407731067498735338895921) * 10^40
        + 9215765718423453974090306379227006153950) * 10^40
        + 6214940542152917628175240386152593324001) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-1751261042181613) : ℚ) /
        35184372088832))

noncomputable def fjcpP018Error2571 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjcpP018BaseError2571 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨18, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcpP018Center2571‖ ≤ fjcpP018Error2571 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨18, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjcpP018Input2571‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjcpP018Input2571]
  have hc : (compactExp2547 fjcpP018Input2571 17).1 = fjcpP018Center2571 := by cbv
  have he : ((compactExp2547 fjcpP018Input2571 17).2 : ℝ) = fjcpP018Error2571 := by
    have hq : (compactExp2547 fjcpP018Input2571 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjcpP018Error2571]
  have h := compactExp_error2547 fjcpP018Input2571 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨18, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjcpP018Input2571) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjcpP018Input2571, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjcpP018DerivativeError2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨18, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjcpP018Factor2571 * embedPair2542 fjcpP018Center2571‖ ≤
        (pairMagnitude2542 fjcpP018Factor2571 : ℝ) * fjcpP018Error2571 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨18, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (1/2)
      (nodeModulation2541 ⟨18, by omega⟩)
      (storedWidth ⟨18, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjcpP018Factor2571 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjcpP018Factor2571, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (1/2)
    (nodeModulation2541 ⟨18, by omega⟩) (pow_pos (storedWidth_pos ⟨18, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjcpP018BaseError2571
    (embedPair_magnitude2542 fjcpP018Factor2571)

def fjcpP018Rounded2571 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjcpP018Radius2571 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjcpP018RoundCompute2571 :
    pairRound2542 (pairMul2542 fjcpP018Factor2571 fjcpP018Center2571) = fjcpP018Rounded2571 := by
  cbv

theorem fjcpP018RoundedError2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨18, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcpP018Rounded2571‖ ≤ fjcpP018Radius2571 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjcpP018Factor2571 fjcpP018Center2571)
  rw [fjcpP018RoundCompute2571, embedPair_mul2542] at hr
  have h := (firstJetCorrPlus_triangle2571
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨18, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcpP018Factor2571 * embedPair2542 fjcpP018Center2571)
    (embedPair2542 fjcpP018Rounded2571)).trans (add_le_add fjcpP018DerivativeError2571 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjcpP018Factor2571, fjcpP018Error2571, rounding2542,
      fjcpP018Radius2571]

theorem fjcpP018DerivativeNorm2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨18, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetCorrPlus_triangle2571
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨18, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcpP018Rounded2571) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjcpP018RoundedError2571 (embedPair_magnitude2542
      fjcpP018Rounded2571))
  apply h'.trans
  norm_num [fjcpP018Radius2571, pairMagnitude2542, fjcpP018Rounded2571]

noncomputable def fjcpP019Input2571 : RatPair2542 := ((((-((2312865 * 10^40
        + 2146202435957712102129842483917578410111) * 10^40
        + 4883202856058925867669125359945801841911)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((118208299174604243670929049 : ℚ) /
        94447329657392904273920000000))

def fjcpP019Center2571 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjcpP019Factor2571 : RatPair2542 := ((((((54884017178483696463843476644 * 10^40
        + 3898147926987883407731067498735338895921) * 10^40
        + 9215765718423453974090306379227006153950) * 10^40
        + 6214940542152917628175240386152593324001) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-1863727500536955) : ℚ) /
        35184372088832))

noncomputable def fjcpP019Error2571 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjcpP019BaseError2571 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨19, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcpP019Center2571‖ ≤ fjcpP019Error2571 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨19, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjcpP019Input2571‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjcpP019Input2571]
  have hc : (compactExp2547 fjcpP019Input2571 17).1 = fjcpP019Center2571 := by cbv
  have he : ((compactExp2547 fjcpP019Input2571 17).2 : ℝ) = fjcpP019Error2571 := by
    have hq : (compactExp2547 fjcpP019Input2571 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjcpP019Error2571]
  have h := compactExp_error2547 fjcpP019Input2571 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨19, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjcpP019Input2571) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjcpP019Input2571, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjcpP019DerivativeError2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨19, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjcpP019Factor2571 * embedPair2542 fjcpP019Center2571‖ ≤
        (pairMagnitude2542 fjcpP019Factor2571 : ℝ) * fjcpP019Error2571 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨19, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (1/2)
      (nodeModulation2541 ⟨19, by omega⟩)
      (storedWidth ⟨19, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjcpP019Factor2571 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjcpP019Factor2571, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (1/2)
    (nodeModulation2541 ⟨19, by omega⟩) (pow_pos (storedWidth_pos ⟨19, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjcpP019BaseError2571
    (embedPair_magnitude2542 fjcpP019Factor2571)

def fjcpP019Rounded2571 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjcpP019Radius2571 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjcpP019RoundCompute2571 :
    pairRound2542 (pairMul2542 fjcpP019Factor2571 fjcpP019Center2571) = fjcpP019Rounded2571 := by
  cbv

theorem fjcpP019RoundedError2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨19, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcpP019Rounded2571‖ ≤ fjcpP019Radius2571 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjcpP019Factor2571 fjcpP019Center2571)
  rw [fjcpP019RoundCompute2571, embedPair_mul2542] at hr
  have h := (firstJetCorrPlus_triangle2571
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨19, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcpP019Factor2571 * embedPair2542 fjcpP019Center2571)
    (embedPair2542 fjcpP019Rounded2571)).trans (add_le_add fjcpP019DerivativeError2571 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjcpP019Factor2571, fjcpP019Error2571, rounding2542,
      fjcpP019Radius2571]

theorem fjcpP019DerivativeNorm2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨19, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetCorrPlus_triangle2571
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨19, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcpP019Rounded2571) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjcpP019RoundedError2571 (embedPair_magnitude2542
      fjcpP019Rounded2571))
  apply h'.trans
  norm_num [fjcpP019Radius2571, pairMagnitude2542, fjcpP019Rounded2571]

noncomputable def fjcpP020Input2571 : RatPair2542 := ((((-((2312865 * 10^40
        + 2146202435957712102129842483917578410111) * 10^40
        + 4883202856058925867669125359945801841911)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((2519303167856168777929316541 : ℚ) /
        1888946593147858085478400000000))

def fjcpP020Center2571 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjcpP020Factor2571 : RatPair2542 := ((((((54884017178483696463843476644 * 10^40
        + 3898147926987883407731067498735338895921) * 10^40
        + 9215765718423453974090306379227006153950) * 10^40
        + 6214940542152917628175240386152593324001) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-7944103127967419) : ℚ) /
        140737488355328))

noncomputable def fjcpP020Error2571 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjcpP020BaseError2571 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨20, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcpP020Center2571‖ ≤ fjcpP020Error2571 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨20, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjcpP020Input2571‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjcpP020Input2571]
  have hc : (compactExp2547 fjcpP020Input2571 17).1 = fjcpP020Center2571 := by cbv
  have he : ((compactExp2547 fjcpP020Input2571 17).2 : ℝ) = fjcpP020Error2571 := by
    have hq : (compactExp2547 fjcpP020Input2571 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjcpP020Error2571]
  have h := compactExp_error2547 fjcpP020Input2571 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨20, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjcpP020Input2571) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjcpP020Input2571, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjcpP020DerivativeError2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨20, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjcpP020Factor2571 * embedPair2542 fjcpP020Center2571‖ ≤
        (pairMagnitude2542 fjcpP020Factor2571 : ℝ) * fjcpP020Error2571 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨20, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (1/2)
      (nodeModulation2541 ⟨20, by omega⟩)
      (storedWidth ⟨20, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjcpP020Factor2571 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjcpP020Factor2571, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (1/2)
    (nodeModulation2541 ⟨20, by omega⟩) (pow_pos (storedWidth_pos ⟨20, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjcpP020BaseError2571
    (embedPair_magnitude2542 fjcpP020Factor2571)

def fjcpP020Rounded2571 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjcpP020Radius2571 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjcpP020RoundCompute2571 :
    pairRound2542 (pairMul2542 fjcpP020Factor2571 fjcpP020Center2571) = fjcpP020Rounded2571 := by
  cbv

theorem fjcpP020RoundedError2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨20, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcpP020Rounded2571‖ ≤ fjcpP020Radius2571 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjcpP020Factor2571 fjcpP020Center2571)
  rw [fjcpP020RoundCompute2571, embedPair_mul2542] at hr
  have h := (firstJetCorrPlus_triangle2571
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨20, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcpP020Factor2571 * embedPair2542 fjcpP020Center2571)
    (embedPair2542 fjcpP020Rounded2571)).trans (add_le_add fjcpP020DerivativeError2571 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjcpP020Factor2571, fjcpP020Error2571, rounding2542,
      fjcpP020Radius2571]

theorem fjcpP020DerivativeNorm2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨20, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetCorrPlus_triangle2571
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨20, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcpP020Rounded2571) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjcpP020RoundedError2571 (embedPair_magnitude2542
      fjcpP020Rounded2571))
  apply h'.trans
  norm_num [fjcpP020Radius2571, pairMagnitude2542, fjcpP020Rounded2571]

noncomputable def fjcpP021Input2571 : RatPair2542 := ((((-((2312865 * 10^40
        + 2146202435957712102129842483917578410111) * 10^40
        + 4883202856058925867669125359945801841911)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((2648771212589104536068841693 : ℚ) /
        1888946593147858085478400000000))

def fjcpP021Center2571 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjcpP021Factor2571 : RatPair2542 := ((((((54884017178483696463843476644 * 10^40
        + 3898147926987883407731067498735338895921) * 10^40
        + 9215765718423453974090306379227006153950) * 10^40
        + 6214940542152917628175240386152593324001) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-8352353914239387) : ℚ) /
        140737488355328))

noncomputable def fjcpP021Error2571 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjcpP021BaseError2571 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨21, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcpP021Center2571‖ ≤ fjcpP021Error2571 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨21, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjcpP021Input2571‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjcpP021Input2571]
  have hc : (compactExp2547 fjcpP021Input2571 17).1 = fjcpP021Center2571 := by cbv
  have he : ((compactExp2547 fjcpP021Input2571 17).2 : ℝ) = fjcpP021Error2571 := by
    have hq : (compactExp2547 fjcpP021Input2571 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjcpP021Error2571]
  have h := compactExp_error2547 fjcpP021Input2571 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨21, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjcpP021Input2571) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjcpP021Input2571, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjcpP021DerivativeError2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨21, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjcpP021Factor2571 * embedPair2542 fjcpP021Center2571‖ ≤
        (pairMagnitude2542 fjcpP021Factor2571 : ℝ) * fjcpP021Error2571 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨21, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (1/2)
      (nodeModulation2541 ⟨21, by omega⟩)
      (storedWidth ⟨21, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjcpP021Factor2571 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjcpP021Factor2571, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (1/2)
    (nodeModulation2541 ⟨21, by omega⟩) (pow_pos (storedWidth_pos ⟨21, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjcpP021BaseError2571
    (embedPair_magnitude2542 fjcpP021Factor2571)

def fjcpP021Rounded2571 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjcpP021Radius2571 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjcpP021RoundCompute2571 :
    pairRound2542 (pairMul2542 fjcpP021Factor2571 fjcpP021Center2571) = fjcpP021Rounded2571 := by
  cbv

theorem fjcpP021RoundedError2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨21, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcpP021Rounded2571‖ ≤ fjcpP021Radius2571 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjcpP021Factor2571 fjcpP021Center2571)
  rw [fjcpP021RoundCompute2571, embedPair_mul2542] at hr
  have h := (firstJetCorrPlus_triangle2571
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨21, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcpP021Factor2571 * embedPair2542 fjcpP021Center2571)
    (embedPair2542 fjcpP021Rounded2571)).trans (add_le_add fjcpP021DerivativeError2571 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjcpP021Factor2571, fjcpP021Error2571, rounding2542,
      fjcpP021Radius2571]

theorem fjcpP021DerivativeNorm2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨21, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetCorrPlus_triangle2571
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨21, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcpP021Rounded2571) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjcpP021RoundedError2571 (embedPair_magnitude2542
      fjcpP021Rounded2571))
  apply h'.trans
  norm_num [fjcpP021Radius2571, pairMagnitude2542, fjcpP021Rounded2571]

noncomputable def fjcpP022Input2571 : RatPair2542 := ((((-((2312865 * 10^40
        + 2146202435957712102129842483917578410111) * 10^40
        + 4883202856058925867669125359945801841911)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((543007546456794340281131487 : ℚ) /
        377789318629571617095680000000))

def fjcpP022Center2571 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjcpP022Factor2571 : RatPair2542 := ((((((54884017178483696463843476644 * 10^40
        + 3898147926987883407731067498735338895921) * 10^40
        + 9215765718423453974090306379227006153950) * 10^40
        + 6214940542152917628175240386152593324001) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-8561311721741165) : ℚ) /
        140737488355328))

noncomputable def fjcpP022Error2571 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjcpP022BaseError2571 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨22, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcpP022Center2571‖ ≤ fjcpP022Error2571 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨22, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjcpP022Input2571‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjcpP022Input2571]
  have hc : (compactExp2547 fjcpP022Input2571 17).1 = fjcpP022Center2571 := by cbv
  have he : ((compactExp2547 fjcpP022Input2571 17).2 : ℝ) = fjcpP022Error2571 := by
    have hq : (compactExp2547 fjcpP022Input2571 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjcpP022Error2571]
  have h := compactExp_error2547 fjcpP022Input2571 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨22, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjcpP022Input2571) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjcpP022Input2571, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjcpP022DerivativeError2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨22, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjcpP022Factor2571 * embedPair2542 fjcpP022Center2571‖ ≤
        (pairMagnitude2542 fjcpP022Factor2571 : ℝ) * fjcpP022Error2571 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨22, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (1/2)
      (nodeModulation2541 ⟨22, by omega⟩)
      (storedWidth ⟨22, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjcpP022Factor2571 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjcpP022Factor2571, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (1/2)
    (nodeModulation2541 ⟨22, by omega⟩) (pow_pos (storedWidth_pos ⟨22, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjcpP022BaseError2571
    (embedPair_magnitude2542 fjcpP022Factor2571)

def fjcpP022Rounded2571 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjcpP022Radius2571 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjcpP022RoundCompute2571 :
    pairRound2542 (pairMul2542 fjcpP022Factor2571 fjcpP022Center2571) = fjcpP022Rounded2571 := by
  cbv

theorem fjcpP022RoundedError2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨22, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcpP022Rounded2571‖ ≤ fjcpP022Radius2571 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjcpP022Factor2571 fjcpP022Center2571)
  rw [fjcpP022RoundCompute2571, embedPair_mul2542] at hr
  have h := (firstJetCorrPlus_triangle2571
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨22, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcpP022Factor2571 * embedPair2542 fjcpP022Center2571)
    (embedPair2542 fjcpP022Rounded2571)).trans (add_le_add fjcpP022DerivativeError2571 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjcpP022Factor2571, fjcpP022Error2571, rounding2542,
      fjcpP022Radius2571]

theorem fjcpP022DerivativeNorm2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨22, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetCorrPlus_triangle2571
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨22, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcpP022Rounded2571) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjcpP022RoundedError2571 (embedPair_magnitude2542
      fjcpP022Rounded2571))
  apply h'.trans
  norm_num [fjcpP022Radius2571, pairMagnitude2542, fjcpP022Rounded2571]

noncomputable def fjcpP023Input2571 : RatPair2542 := ((((-((2312865 * 10^40
        + 2146202435957712102129842483917578410111) * 10^40
        + 4883202856058925867669125359945801841911)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((1453048211174897778209007387 : ℚ) /
        944473296573929042739200000000))

def fjcpP023Center2571 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjcpP023Factor2571 : RatPair2542 := ((((((54884017178483696463843476644 * 10^40
        + 3898147926987883407731067498735338895921) * 10^40
        + 9215765718423453974090306379227006153950) * 10^40
        + 6214940542152917628175240386152593324001) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-4581887954876333) : ℚ) /
        70368744177664))

noncomputable def fjcpP023Error2571 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjcpP023BaseError2571 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨23, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcpP023Center2571‖ ≤ fjcpP023Error2571 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨23, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjcpP023Input2571‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjcpP023Input2571]
  have hc : (compactExp2547 fjcpP023Input2571 17).1 = fjcpP023Center2571 := by cbv
  have he : ((compactExp2547 fjcpP023Input2571 17).2 : ℝ) = fjcpP023Error2571 := by
    have hq : (compactExp2547 fjcpP023Input2571 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjcpP023Error2571]
  have h := compactExp_error2547 fjcpP023Input2571 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨23, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjcpP023Input2571) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjcpP023Input2571, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjcpP023DerivativeError2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨23, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjcpP023Factor2571 * embedPair2542 fjcpP023Center2571‖ ≤
        (pairMagnitude2542 fjcpP023Factor2571 : ℝ) * fjcpP023Error2571 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨23, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (1/2)
      (nodeModulation2541 ⟨23, by omega⟩)
      (storedWidth ⟨23, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjcpP023Factor2571 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjcpP023Factor2571, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (1/2)
    (nodeModulation2541 ⟨23, by omega⟩) (pow_pos (storedWidth_pos ⟨23, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjcpP023BaseError2571
    (embedPair_magnitude2542 fjcpP023Factor2571)

def fjcpP023Rounded2571 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjcpP023Radius2571 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjcpP023RoundCompute2571 :
    pairRound2542 (pairMul2542 fjcpP023Factor2571 fjcpP023Center2571) = fjcpP023Rounded2571 := by
  cbv

theorem fjcpP023RoundedError2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨23, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcpP023Rounded2571‖ ≤ fjcpP023Radius2571 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjcpP023Factor2571 fjcpP023Center2571)
  rw [fjcpP023RoundCompute2571, embedPair_mul2542] at hr
  have h := (firstJetCorrPlus_triangle2571
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨23, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcpP023Factor2571 * embedPair2542 fjcpP023Center2571)
    (embedPair2542 fjcpP023Rounded2571)).trans (add_le_add fjcpP023DerivativeError2571 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjcpP023Factor2571, fjcpP023Error2571, rounding2542,
      fjcpP023Radius2571]

theorem fjcpP023DerivativeNorm2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨23, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetCorrPlus_triangle2571
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨23, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcpP023Rounded2571) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjcpP023RoundedError2571 (embedPair_magnitude2542
      fjcpP023Rounded2571))
  apply h'.trans
  norm_num [fjcpP023Radius2571, pairMagnitude2542, fjcpP023Rounded2571]

noncomputable def fjcpP024Input2571 : RatPair2542 := ((((-((2312865 * 10^40
        + 2146202435957712102129842483917578410111) * 10^40
        + 4883202856058925867669125359945801841911)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((1496949629611413064555803333 : ℚ) /
        944473296573929042739200000000))

def fjcpP024Center2571 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjcpP024Factor2571 : RatPair2542 := ((((((54884017178483696463843476644 * 10^40
        + 3898147926987883407731067498735338895921) * 10^40
        + 9215765718423453974090306379227006153950) * 10^40
        + 6214940542152917628175240386152593324001) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-4720322026636147) : ℚ) /
        70368744177664))

noncomputable def fjcpP024Error2571 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjcpP024BaseError2571 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨24, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcpP024Center2571‖ ≤ fjcpP024Error2571 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨24, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjcpP024Input2571‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjcpP024Input2571]
  have hc : (compactExp2547 fjcpP024Input2571 17).1 = fjcpP024Center2571 := by cbv
  have he : ((compactExp2547 fjcpP024Input2571 17).2 : ℝ) = fjcpP024Error2571 := by
    have hq : (compactExp2547 fjcpP024Input2571 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjcpP024Error2571]
  have h := compactExp_error2547 fjcpP024Input2571 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨24, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjcpP024Input2571) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjcpP024Input2571, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjcpP024DerivativeError2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨24, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjcpP024Factor2571 * embedPair2542 fjcpP024Center2571‖ ≤
        (pairMagnitude2542 fjcpP024Factor2571 : ℝ) * fjcpP024Error2571 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨24, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (1/2)
      (nodeModulation2541 ⟨24, by omega⟩)
      (storedWidth ⟨24, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjcpP024Factor2571 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjcpP024Factor2571, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (1/2)
    (nodeModulation2541 ⟨24, by omega⟩) (pow_pos (storedWidth_pos ⟨24, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjcpP024BaseError2571
    (embedPair_magnitude2542 fjcpP024Factor2571)

def fjcpP024Rounded2571 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjcpP024Radius2571 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjcpP024RoundCompute2571 :
    pairRound2542 (pairMul2542 fjcpP024Factor2571 fjcpP024Center2571) = fjcpP024Rounded2571 := by
  cbv

theorem fjcpP024RoundedError2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨24, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcpP024Rounded2571‖ ≤ fjcpP024Radius2571 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjcpP024Factor2571 fjcpP024Center2571)
  rw [fjcpP024RoundCompute2571, embedPair_mul2542] at hr
  have h := (firstJetCorrPlus_triangle2571
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨24, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcpP024Factor2571 * embedPair2542 fjcpP024Center2571)
    (embedPair2542 fjcpP024Rounded2571)).trans (add_le_add fjcpP024DerivativeError2571 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjcpP024Factor2571, fjcpP024Error2571, rounding2542,
      fjcpP024Radius2571]

theorem fjcpP024DerivativeNorm2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨24, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetCorrPlus_triangle2571
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨24, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcpP024Rounded2571) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjcpP024RoundedError2571 (embedPair_magnitude2542
      fjcpP024Rounded2571))
  apply h'.trans
  norm_num [fjcpP024Radius2571, pairMagnitude2542, fjcpP024Rounded2571]

noncomputable def fjcpP025Input2571 : RatPair2542 := ((((-((2312865 * 10^40
        + 2146202435957712102129842483917578410111) * 10^40
        + 4883202856058925867669125359945801841911)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((48499811018293309025440887 : ℚ) /
        29514790517935282585600000000))

def fjcpP025Center2571 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjcpP025Factor2571 : RatPair2542 := ((((((54884017178483696463843476644 * 10^40
        + 3898147926987883407731067498735338895921) * 10^40
        + 9215765718423453974090306379227006153950) * 10^40
        + 6214940542152917628175240386152593324001) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-152934154702833) : ℚ) /
        2199023255552))

noncomputable def fjcpP025Error2571 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjcpP025BaseError2571 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨25, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcpP025Center2571‖ ≤ fjcpP025Error2571 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨25, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjcpP025Input2571‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjcpP025Input2571]
  have hc : (compactExp2547 fjcpP025Input2571 17).1 = fjcpP025Center2571 := by cbv
  have he : ((compactExp2547 fjcpP025Input2571 17).2 : ℝ) = fjcpP025Error2571 := by
    have hq : (compactExp2547 fjcpP025Input2571 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjcpP025Error2571]
  have h := compactExp_error2547 fjcpP025Input2571 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨25, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjcpP025Input2571) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjcpP025Input2571, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjcpP025DerivativeError2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨25, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjcpP025Factor2571 * embedPair2542 fjcpP025Center2571‖ ≤
        (pairMagnitude2542 fjcpP025Factor2571 : ℝ) * fjcpP025Error2571 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨25, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (1/2)
      (nodeModulation2541 ⟨25, by omega⟩)
      (storedWidth ⟨25, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjcpP025Factor2571 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjcpP025Factor2571, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (1/2)
    (nodeModulation2541 ⟨25, by omega⟩) (pow_pos (storedWidth_pos ⟨25, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjcpP025BaseError2571
    (embedPair_magnitude2542 fjcpP025Factor2571)

def fjcpP025Rounded2571 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjcpP025Radius2571 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjcpP025RoundCompute2571 :
    pairRound2542 (pairMul2542 fjcpP025Factor2571 fjcpP025Center2571) = fjcpP025Rounded2571 := by
  cbv

theorem fjcpP025RoundedError2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨25, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcpP025Rounded2571‖ ≤ fjcpP025Radius2571 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjcpP025Factor2571 fjcpP025Center2571)
  rw [fjcpP025RoundCompute2571, embedPair_mul2542] at hr
  have h := (firstJetCorrPlus_triangle2571
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨25, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcpP025Factor2571 * embedPair2542 fjcpP025Center2571)
    (embedPair2542 fjcpP025Rounded2571)).trans (add_le_add fjcpP025DerivativeError2571 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjcpP025Factor2571, fjcpP025Error2571, rounding2542,
      fjcpP025Radius2571]

theorem fjcpP025DerivativeNorm2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨25, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetCorrPlus_triangle2571
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨25, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcpP025Rounded2571) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjcpP025RoundedError2571 (embedPair_magnitude2542
      fjcpP025Rounded2571))
  apply h'.trans
  norm_num [fjcpP025Radius2571, pairMagnitude2542, fjcpP025Rounded2571]

noncomputable def fjcpP026Input2571 : RatPair2542 := ((((-((2312865 * 10^40
        + 2146202435957712102129842483917578410111) * 10^40
        + 4883202856058925867669125359945801841911)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((100515438378930241589387643 : ℚ) /
        59029581035870565171200000000))

def fjcpP026Center2571 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjcpP026Factor2571 : RatPair2542 := ((((((54884017178483696463843476644 * 10^40
        + 3898147926987883407731067498735338895921) * 10^40
        + 9215765718423453974090306379227006153950) * 10^40
        + 6214940542152917628175240386152593324001) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-316954711375437) : ℚ) /
        4398046511104))

noncomputable def fjcpP026Error2571 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjcpP026BaseError2571 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨26, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcpP026Center2571‖ ≤ fjcpP026Error2571 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨26, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjcpP026Input2571‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjcpP026Input2571]
  have hc : (compactExp2547 fjcpP026Input2571 17).1 = fjcpP026Center2571 := by cbv
  have he : ((compactExp2547 fjcpP026Input2571 17).2 : ℝ) = fjcpP026Error2571 := by
    have hq : (compactExp2547 fjcpP026Input2571 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjcpP026Error2571]
  have h := compactExp_error2547 fjcpP026Input2571 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨26, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjcpP026Input2571) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjcpP026Input2571, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjcpP026DerivativeError2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨26, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjcpP026Factor2571 * embedPair2542 fjcpP026Center2571‖ ≤
        (pairMagnitude2542 fjcpP026Factor2571 : ℝ) * fjcpP026Error2571 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨26, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (1/2)
      (nodeModulation2541 ⟨26, by omega⟩)
      (storedWidth ⟨26, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjcpP026Factor2571 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjcpP026Factor2571, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (1/2)
    (nodeModulation2541 ⟨26, by omega⟩) (pow_pos (storedWidth_pos ⟨26, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjcpP026BaseError2571
    (embedPair_magnitude2542 fjcpP026Factor2571)

def fjcpP026Rounded2571 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjcpP026Radius2571 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjcpP026RoundCompute2571 :
    pairRound2542 (pairMul2542 fjcpP026Factor2571 fjcpP026Center2571) = fjcpP026Rounded2571 := by
  cbv

theorem fjcpP026RoundedError2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨26, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcpP026Rounded2571‖ ≤ fjcpP026Radius2571 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjcpP026Factor2571 fjcpP026Center2571)
  rw [fjcpP026RoundCompute2571, embedPair_mul2542] at hr
  have h := (firstJetCorrPlus_triangle2571
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨26, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcpP026Factor2571 * embedPair2542 fjcpP026Center2571)
    (embedPair2542 fjcpP026Rounded2571)).trans (add_le_add fjcpP026DerivativeError2571 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjcpP026Factor2571, fjcpP026Error2571, rounding2542,
      fjcpP026Radius2571]

theorem fjcpP026DerivativeNorm2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨26, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetCorrPlus_triangle2571
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨26, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcpP026Rounded2571) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjcpP026RoundedError2571 (embedPair_magnitude2542
      fjcpP026Rounded2571))
  apply h'.trans
  norm_num [fjcpP026Radius2571, pairMagnitude2542, fjcpP026Rounded2571]

noncomputable def fjcpP027Input2571 : RatPair2542 := ((((-((2312865 * 10^40
        + 2146202435957712102129842483917578410111) * 10^40
        + 4883202856058925867669125359945801841911)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((211177751933296260595876053 : ℚ) /
        118059162071741130342400000000))

def fjcpP027Center2571 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjcpP027Factor2571 : RatPair2542 := ((((((54884017178483696463843476644 * 10^40
        + 3898147926987883407731067498735338895921) * 10^40
        + 9215765718423453974090306379227006153950) * 10^40
        + 6214940542152917628175240386152593324001) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-665905501606627) : ℚ) /
        8796093022208))

noncomputable def fjcpP027Error2571 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjcpP027BaseError2571 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨27, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcpP027Center2571‖ ≤ fjcpP027Error2571 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨27, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjcpP027Input2571‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjcpP027Input2571]
  have hc : (compactExp2547 fjcpP027Input2571 17).1 = fjcpP027Center2571 := by cbv
  have he : ((compactExp2547 fjcpP027Input2571 17).2 : ℝ) = fjcpP027Error2571 := by
    have hq : (compactExp2547 fjcpP027Input2571 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjcpP027Error2571]
  have h := compactExp_error2547 fjcpP027Input2571 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨27, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjcpP027Input2571) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjcpP027Input2571, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjcpP027DerivativeError2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨27, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjcpP027Factor2571 * embedPair2542 fjcpP027Center2571‖ ≤
        (pairMagnitude2542 fjcpP027Factor2571 : ℝ) * fjcpP027Error2571 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨27, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (1/2)
      (nodeModulation2541 ⟨27, by omega⟩)
      (storedWidth ⟨27, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjcpP027Factor2571 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjcpP027Factor2571, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (1/2)
    (nodeModulation2541 ⟨27, by omega⟩) (pow_pos (storedWidth_pos ⟨27, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjcpP027BaseError2571
    (embedPair_magnitude2542 fjcpP027Factor2571)

def fjcpP027Rounded2571 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjcpP027Radius2571 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjcpP027RoundCompute2571 :
    pairRound2542 (pairMul2542 fjcpP027Factor2571 fjcpP027Center2571) = fjcpP027Rounded2571 := by
  cbv

theorem fjcpP027RoundedError2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨27, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcpP027Rounded2571‖ ≤ fjcpP027Radius2571 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjcpP027Factor2571 fjcpP027Center2571)
  rw [fjcpP027RoundCompute2571, embedPair_mul2542] at hr
  have h := (firstJetCorrPlus_triangle2571
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨27, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcpP027Factor2571 * embedPair2542 fjcpP027Center2571)
    (embedPair2542 fjcpP027Rounded2571)).trans (add_le_add fjcpP027DerivativeError2571 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjcpP027Factor2571, fjcpP027Error2571, rounding2542,
      fjcpP027Radius2571]

theorem fjcpP027DerivativeNorm2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨27, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetCorrPlus_triangle2571
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨27, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcpP027Rounded2571) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjcpP027RoundedError2571 (embedPair_magnitude2542
      fjcpP027Rounded2571))
  apply h'.trans
  norm_num [fjcpP027Radius2571, pairMagnitude2542, fjcpP027Rounded2571]

noncomputable def fjcpP028Input2571 : RatPair2542 := ((((-((2312865 * 10^40
        + 2146202435957712102129842483917578410111) * 10^40
        + 4883202856058925867669125359945801841911)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((860780157665754287223049953 : ℚ) /
        472236648286964521369600000000))

def fjcpP028Center2571 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjcpP028Factor2571 : RatPair2542 := ((((((54884017178483696463843476644 * 10^40
        + 3898147926987883407731067498735338895921) * 10^40
        + 9215765718423453974090306379227006153950) * 10^40
        + 6214940542152917628175240386152593324001) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-2714292757716727) : ℚ) /
        35184372088832))

noncomputable def fjcpP028Error2571 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjcpP028BaseError2571 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨28, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcpP028Center2571‖ ≤ fjcpP028Error2571 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨28, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjcpP028Input2571‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjcpP028Input2571]
  have hc : (compactExp2547 fjcpP028Input2571 17).1 = fjcpP028Center2571 := by cbv
  have he : ((compactExp2547 fjcpP028Input2571 17).2 : ℝ) = fjcpP028Error2571 := by
    have hq : (compactExp2547 fjcpP028Input2571 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjcpP028Error2571]
  have h := compactExp_error2547 fjcpP028Input2571 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨28, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjcpP028Input2571) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjcpP028Input2571, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjcpP028DerivativeError2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨28, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjcpP028Factor2571 * embedPair2542 fjcpP028Center2571‖ ≤
        (pairMagnitude2542 fjcpP028Factor2571 : ℝ) * fjcpP028Error2571 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨28, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (1/2)
      (nodeModulation2541 ⟨28, by omega⟩)
      (storedWidth ⟨28, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjcpP028Factor2571 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjcpP028Factor2571, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (1/2)
    (nodeModulation2541 ⟨28, by omega⟩) (pow_pos (storedWidth_pos ⟨28, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjcpP028BaseError2571
    (embedPair_magnitude2542 fjcpP028Factor2571)

def fjcpP028Rounded2571 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjcpP028Radius2571 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjcpP028RoundCompute2571 :
    pairRound2542 (pairMul2542 fjcpP028Factor2571 fjcpP028Center2571) = fjcpP028Rounded2571 := by
  cbv

theorem fjcpP028RoundedError2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨28, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcpP028Rounded2571‖ ≤ fjcpP028Radius2571 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjcpP028Factor2571 fjcpP028Center2571)
  rw [fjcpP028RoundCompute2571, embedPair_mul2542] at hr
  have h := (firstJetCorrPlus_triangle2571
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨28, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcpP028Factor2571 * embedPair2542 fjcpP028Center2571)
    (embedPair2542 fjcpP028Rounded2571)).trans (add_le_add fjcpP028DerivativeError2571 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjcpP028Factor2571, fjcpP028Error2571, rounding2542,
      fjcpP028Radius2571]

theorem fjcpP028DerivativeNorm2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨28, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetCorrPlus_triangle2571
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨28, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcpP028Rounded2571) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjcpP028RoundedError2571 (embedPair_magnitude2542
      fjcpP028Rounded2571))
  apply h'.trans
  norm_num [fjcpP028Radius2571, pairMagnitude2542, fjcpP028Rounded2571]

noncomputable def fjcpP029Input2571 : RatPair2542 := ((((-((2312865 * 10^40
        + 2146202435957712102129842483917578410111) * 10^40
        + 4883202856058925867669125359945801841911)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((885244406725664293840781901 : ℚ) /
        472236648286964521369600000000))

def fjcpP029Center2571 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjcpP029Factor2571 : RatPair2542 := ((((((54884017178483696463843476644 * 10^40
        + 3898147926987883407731067498735338895921) * 10^40
        + 9215765718423453974090306379227006153950) * 10^40
        + 6214940542152917628175240386152593324001) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-2791435723263659) : ℚ) /
        35184372088832))

noncomputable def fjcpP029Error2571 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjcpP029BaseError2571 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨29, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcpP029Center2571‖ ≤ fjcpP029Error2571 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨29, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjcpP029Input2571‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjcpP029Input2571]
  have hc : (compactExp2547 fjcpP029Input2571 17).1 = fjcpP029Center2571 := by cbv
  have he : ((compactExp2547 fjcpP029Input2571 17).2 : ℝ) = fjcpP029Error2571 := by
    have hq : (compactExp2547 fjcpP029Input2571 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjcpP029Error2571]
  have h := compactExp_error2547 fjcpP029Input2571 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨29, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjcpP029Input2571) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjcpP029Input2571, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjcpP029DerivativeError2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨29, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjcpP029Factor2571 * embedPair2542 fjcpP029Center2571‖ ≤
        (pairMagnitude2542 fjcpP029Factor2571 : ℝ) * fjcpP029Error2571 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨29, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (1/2)
      (nodeModulation2541 ⟨29, by omega⟩)
      (storedWidth ⟨29, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjcpP029Factor2571 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjcpP029Factor2571, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (1/2)
    (nodeModulation2541 ⟨29, by omega⟩) (pow_pos (storedWidth_pos ⟨29, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjcpP029BaseError2571
    (embedPair_magnitude2542 fjcpP029Factor2571)

def fjcpP029Rounded2571 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjcpP029Radius2571 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjcpP029RoundCompute2571 :
    pairRound2542 (pairMul2542 fjcpP029Factor2571 fjcpP029Center2571) = fjcpP029Rounded2571 := by
  cbv

theorem fjcpP029RoundedError2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨29, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcpP029Rounded2571‖ ≤ fjcpP029Radius2571 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjcpP029Factor2571 fjcpP029Center2571)
  rw [fjcpP029RoundCompute2571, embedPair_mul2542] at hr
  have h := (firstJetCorrPlus_triangle2571
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨29, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcpP029Factor2571 * embedPair2542 fjcpP029Center2571)
    (embedPair2542 fjcpP029Rounded2571)).trans (add_le_add fjcpP029DerivativeError2571 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjcpP029Factor2571, fjcpP029Error2571, rounding2542,
      fjcpP029Radius2571]

theorem fjcpP029DerivativeNorm2571 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨29, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetCorrPlus_triangle2571
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨29, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcpP029Rounded2571) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjcpP029RoundedError2571 (embedPair_magnitude2542
      fjcpP029Rounded2571))
  apply h'.trans
  norm_num [fjcpP029Radius2571, pairMagnitude2542, fjcpP029Rounded2571]

noncomputable def fjcpValue2571 (i : Fin 30) : ℂ :=
  match i.val with
  | 0 => embedPair2542 fjcpP000Rounded2571
  | 1 => embedPair2542 fjcpP001Rounded2571
  | 2 => embedPair2542 fjcpP002Rounded2571
  | 3 => embedPair2542 fjcpP003Rounded2571
  | 4 => embedPair2542 fjcpP004Rounded2571
  | 5 => embedPair2542 fjcpP005Rounded2571
  | 6 => embedPair2542 fjcpP006Rounded2571
  | 7 => embedPair2542 fjcpP007Rounded2571
  | 8 => embedPair2542 fjcpP008Rounded2571
  | 9 => embedPair2542 fjcpP009Rounded2571
  | 10 => embedPair2542 fjcpP010Rounded2571
  | 11 => embedPair2542 fjcpP011Rounded2571
  | 12 => embedPair2542 fjcpP012Rounded2571
  | 13 => embedPair2542 fjcpP013Rounded2571
  | 14 => embedPair2542 fjcpP014Rounded2571
  | 15 => embedPair2542 fjcpP015Rounded2571
  | 16 => embedPair2542 fjcpP016Rounded2571
  | 17 => embedPair2542 fjcpP017Rounded2571
  | 18 => embedPair2542 fjcpP018Rounded2571
  | 19 => embedPair2542 fjcpP019Rounded2571
  | 20 => embedPair2542 fjcpP020Rounded2571
  | 21 => embedPair2542 fjcpP021Rounded2571
  | 22 => embedPair2542 fjcpP022Rounded2571
  | 23 => embedPair2542 fjcpP023Rounded2571
  | 24 => embedPair2542 fjcpP024Rounded2571
  | 25 => embedPair2542 fjcpP025Rounded2571
  | 26 => embedPair2542 fjcpP026Rounded2571
  | 27 => embedPair2542 fjcpP027Rounded2571
  | 28 => embedPair2542 fjcpP028Rounded2571
  | 29 => embedPair2542 fjcpP029Rounded2571
  | _ => 0

noncomputable def fjcpError2571 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => fjcpP000Radius2571
  | 1 => fjcpP001Radius2571
  | 2 => fjcpP002Radius2571
  | 3 => fjcpP003Radius2571
  | 4 => fjcpP004Radius2571
  | 5 => fjcpP005Radius2571
  | 6 => fjcpP006Radius2571
  | 7 => fjcpP007Radius2571
  | 8 => fjcpP008Radius2571
  | 9 => fjcpP009Radius2571
  | 10 => fjcpP010Radius2571
  | 11 => fjcpP011Radius2571
  | 12 => fjcpP012Radius2571
  | 13 => fjcpP013Radius2571
  | 14 => fjcpP014Radius2571
  | 15 => fjcpP015Radius2571
  | 16 => fjcpP016Radius2571
  | 17 => fjcpP017Radius2571
  | 18 => fjcpP018Radius2571
  | 19 => fjcpP019Radius2571
  | 20 => fjcpP020Radius2571
  | 21 => fjcpP021Radius2571
  | 22 => fjcpP022Radius2571
  | 23 => fjcpP023Radius2571
  | 24 => fjcpP024Radius2571
  | 25 => fjcpP025Radius2571
  | 26 => fjcpP026Radius2571
  | 27 => fjcpP027Radius2571
  | 28 => fjcpP028Radius2571
  | 29 => fjcpP029Radius2571
  | _ => 0

theorem fjcpExpError2571 (i : Fin 30) :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 i edgeMidpointPosition2548 - fjcpValue2571 i‖
        ≤ fjcpError2571 i := by
  fin_cases i
  · simpa only [fjcpValue2571, fjcpError2571] using fjcpP000RoundedError2571
  · simpa only [fjcpValue2571, fjcpError2571] using fjcpP001RoundedError2571
  · simpa only [fjcpValue2571, fjcpError2571] using fjcpP002RoundedError2571
  · simpa only [fjcpValue2571, fjcpError2571] using fjcpP003RoundedError2571
  · simpa only [fjcpValue2571, fjcpError2571] using fjcpP004RoundedError2571
  · simpa only [fjcpValue2571, fjcpError2571] using fjcpP005RoundedError2571
  · simpa only [fjcpValue2571, fjcpError2571] using fjcpP006RoundedError2571
  · simpa only [fjcpValue2571, fjcpError2571] using fjcpP007RoundedError2571
  · simpa only [fjcpValue2571, fjcpError2571] using fjcpP008RoundedError2571
  · simpa only [fjcpValue2571, fjcpError2571] using fjcpP009RoundedError2571
  · simpa only [fjcpValue2571, fjcpError2571] using fjcpP010RoundedError2571
  · simpa only [fjcpValue2571, fjcpError2571] using fjcpP011RoundedError2571
  · simpa only [fjcpValue2571, fjcpError2571] using fjcpP012RoundedError2571
  · simpa only [fjcpValue2571, fjcpError2571] using fjcpP013RoundedError2571
  · simpa only [fjcpValue2571, fjcpError2571] using fjcpP014RoundedError2571
  · simpa only [fjcpValue2571, fjcpError2571] using fjcpP015RoundedError2571
  · simpa only [fjcpValue2571, fjcpError2571] using fjcpP016RoundedError2571
  · simpa only [fjcpValue2571, fjcpError2571] using fjcpP017RoundedError2571
  · simpa only [fjcpValue2571, fjcpError2571] using fjcpP018RoundedError2571
  · simpa only [fjcpValue2571, fjcpError2571] using fjcpP019RoundedError2571
  · simpa only [fjcpValue2571, fjcpError2571] using fjcpP020RoundedError2571
  · simpa only [fjcpValue2571, fjcpError2571] using fjcpP021RoundedError2571
  · simpa only [fjcpValue2571, fjcpError2571] using fjcpP022RoundedError2571
  · simpa only [fjcpValue2571, fjcpError2571] using fjcpP023RoundedError2571
  · simpa only [fjcpValue2571, fjcpError2571] using fjcpP024RoundedError2571
  · simpa only [fjcpValue2571, fjcpError2571] using fjcpP025RoundedError2571
  · simpa only [fjcpValue2571, fjcpError2571] using fjcpP026RoundedError2571
  · simpa only [fjcpValue2571, fjcpError2571] using fjcpP027RoundedError2571
  · simpa only [fjcpValue2571, fjcpError2571] using fjcpP028RoundedError2571
  · simpa only [fjcpValue2571, fjcpError2571] using fjcpP029RoundedError2571

theorem fjcpUnitNorm2571 (i : Fin 30) :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 i edgeMidpointPosition2548‖ ≤ 1 := by
  fin_cases i
  · simpa only [fjcpValue2571, fjcpError2571] using fjcpP000DerivativeNorm2571
  · simpa only [fjcpValue2571, fjcpError2571] using fjcpP001DerivativeNorm2571
  · simpa only [fjcpValue2571, fjcpError2571] using fjcpP002DerivativeNorm2571
  · simpa only [fjcpValue2571, fjcpError2571] using fjcpP003DerivativeNorm2571
  · simpa only [fjcpValue2571, fjcpError2571] using fjcpP004DerivativeNorm2571
  · simpa only [fjcpValue2571, fjcpError2571] using fjcpP005DerivativeNorm2571
  · simpa only [fjcpValue2571, fjcpError2571] using fjcpP006DerivativeNorm2571
  · simpa only [fjcpValue2571, fjcpError2571] using fjcpP007DerivativeNorm2571
  · simpa only [fjcpValue2571, fjcpError2571] using fjcpP008DerivativeNorm2571
  · simpa only [fjcpValue2571, fjcpError2571] using fjcpP009DerivativeNorm2571
  · simpa only [fjcpValue2571, fjcpError2571] using fjcpP010DerivativeNorm2571
  · simpa only [fjcpValue2571, fjcpError2571] using fjcpP011DerivativeNorm2571
  · simpa only [fjcpValue2571, fjcpError2571] using fjcpP012DerivativeNorm2571
  · simpa only [fjcpValue2571, fjcpError2571] using fjcpP013DerivativeNorm2571
  · simpa only [fjcpValue2571, fjcpError2571] using fjcpP014DerivativeNorm2571
  · simpa only [fjcpValue2571, fjcpError2571] using fjcpP015DerivativeNorm2571
  · simpa only [fjcpValue2571, fjcpError2571] using fjcpP016DerivativeNorm2571
  · simpa only [fjcpValue2571, fjcpError2571] using fjcpP017DerivativeNorm2571
  · simpa only [fjcpValue2571, fjcpError2571] using fjcpP018DerivativeNorm2571
  · simpa only [fjcpValue2571, fjcpError2571] using fjcpP019DerivativeNorm2571
  · simpa only [fjcpValue2571, fjcpError2571] using fjcpP020DerivativeNorm2571
  · simpa only [fjcpValue2571, fjcpError2571] using fjcpP021DerivativeNorm2571
  · simpa only [fjcpValue2571, fjcpError2571] using fjcpP022DerivativeNorm2571
  · simpa only [fjcpValue2571, fjcpError2571] using fjcpP023DerivativeNorm2571
  · simpa only [fjcpValue2571, fjcpError2571] using fjcpP024DerivativeNorm2571
  · simpa only [fjcpValue2571, fjcpError2571] using fjcpP025DerivativeNorm2571
  · simpa only [fjcpValue2571, fjcpError2571] using fjcpP026DerivativeNorm2571
  · simpa only [fjcpValue2571, fjcpError2571] using fjcpP027DerivativeNorm2571
  · simpa only [fjcpValue2571, fjcpError2571] using fjcpP028DerivativeNorm2571
  · simpa only [fjcpValue2571, fjcpError2571] using fjcpP029DerivativeNorm2571

noncomputable def fjcpSum2571 : ℂ := ⟨(((-(((18656894254 * 10^40
        + 850178295224684624120366351938347377979) * 10^40
        + 1046512849344300527083957338971921706038) * 10^40
        + 877205675319563129556854987682550765751)) : ℝ) /
        (((1419606883389 * 10^40
        + 8572081041480622812588561594557825924180) * 10^40
        + 8648728554527468610959648031899646689592) * 10^40
        + 5319463985864300012238628776434768805888)),
    (((-(((17399193140 * 10^40
        + 33283594020384824777082461552320688917) * 10^40
        + 7484015332668445100940566077086861823468) * 10^40
        + 3791268110002257153994453202314115782767)) : ℝ) /
        (((709803441694 * 10^40
        + 9286040520740311406294280797278912962090) * 10^40
        + 4324364277263734305479824015949823344796) * 10^40
        + 2659731992932150006119314388217384402944))⟩

noncomputable def fjcpUpper2571 : ℝ := ((2781363 : ℝ) /
        100000000)

theorem fjcpSum_eq2571 :
    (∑ i : Fin 30, correctionCoefficientCenter2570 i * fjcpValue2571 i) =
      fjcpSum2571 := by
  rw [sum30_chain2541]
  apply Complex.ext <;>
    norm_num [correctionCoefficientCenter2570, correctionCoefficientBox2570, fjcpValue2571,
      fjcpSum2571, embedPair2542, fjcpP000Rounded2571,
      fjcpP001Rounded2571,
      fjcpP002Rounded2571,
      fjcpP003Rounded2571,
      fjcpP004Rounded2571,
      fjcpP005Rounded2571,
      fjcpP006Rounded2571,
      fjcpP007Rounded2571,
      fjcpP008Rounded2571,
      fjcpP009Rounded2571,
      fjcpP010Rounded2571,
      fjcpP011Rounded2571,
      fjcpP012Rounded2571,
      fjcpP013Rounded2571,
      fjcpP014Rounded2571,
      fjcpP015Rounded2571,
      fjcpP016Rounded2571,
      fjcpP017Rounded2571,
      fjcpP018Rounded2571,
      fjcpP019Rounded2571,
      fjcpP020Rounded2571,
      fjcpP021Rounded2571,
      fjcpP022Rounded2571,
      fjcpP023Rounded2571,
      fjcpP024Rounded2571,
      fjcpP025Rounded2571,
      fjcpP026Rounded2571,
      fjcpP027Rounded2571,
      fjcpP028Rounded2571,
      fjcpP029Rounded2571, Complex.mul_re, Complex.mul_im]

theorem fjcpSum_norm2571 :
    ‖∑ i : Fin 30, correctionCoefficientCenter2570 i * fjcpValue2571 i‖ ≤ ((2781353 : ℝ) /
        100000000) := by
  rw [fjcpSum_eq2571]
  apply complex_norm_le_of_sq2541 _ _ (by norm_num)
  norm_num [fjcpSum2571]

theorem fjcpCharge2571 :
    (∑ i : Fin 30, (|(correctionCoefficientCenter2570 i).re| +
      |(correctionCoefficientCenter2570 i).im|) * fjcpError2571 i) ≤ (1 : ℝ)/10^8 := by
  rw [sum30_chain2541]
  norm_num [correctionCoefficientCenter2570, correctionCoefficientBox2570, fjcpError2571,
      fjcpP000Radius2571,
      fjcpP001Radius2571,
      fjcpP002Radius2571,
      fjcpP003Radius2571,
      fjcpP004Radius2571,
      fjcpP005Radius2571,
      fjcpP006Radius2571,
      fjcpP007Radius2571,
      fjcpP008Radius2571,
      fjcpP009Radius2571,
      fjcpP010Radius2571,
      fjcpP011Radius2571,
      fjcpP012Radius2571,
      fjcpP013Radius2571,
      fjcpP014Radius2571,
      fjcpP015Radius2571,
      fjcpP016Radius2571,
      fjcpP017Radius2571,
      fjcpP018Radius2571,
      fjcpP019Radius2571,
      fjcpP020Radius2571,
      fjcpP021Radius2571,
      fjcpP022Radius2571,
      fjcpP023Radius2571,
      fjcpP024Radius2571,
      fjcpP025Radius2571,
      fjcpP026Radius2571,
      fjcpP027Radius2571,
      fjcpP028Radius2571,
      fjcpP029Radius2571]

theorem firstJetCorrPlusUpper_le2571 :
    signedJetUpper2539 1 (1/2) correctionCoefficientCenter2570 correctionCoefficientError2570
      nodeModulation2541 edgeMidpointPosition2548 ≤ fjcpUpper2571 := by
  have hsum :
      ‖∑ i : Fin 30, correctionCoefficientCenter2570 i *
        weightedUnitJet2539 1 (1/2) nodeModulation2541 i edgeMidpointPosition2548‖ ≤
      ‖∑ i : Fin 30, correctionCoefficientCenter2570 i * fjcpValue2571 i‖ +
        ∑ i : Fin 30, (|(correctionCoefficientCenter2570 i).re| +
          |(correctionCoefficientCenter2570 i).im|) * fjcpError2571 i := by
    apply norm_sum_le_center_sum_add_error2531
    intro i _
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (Complex.norm_le_abs_re_add_abs_im _) (fjcpExpError2571 i)
      (norm_nonneg _) (by positivity)
  have heach : ∀ i : Fin 30, correctionCoefficientError2570 i *
      ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 i edgeMidpointPosition2548‖ ≤
        (1 : ℝ)/10^28 := by
    intro i
    have h := mul_le_mul_of_nonneg_left (fjcpUnitNorm2571 i)
      (by norm_num [correctionCoefficientError2570] : 0 ≤ correctionCoefficientError2570 i)
    simpa [correctionCoefficientError2570] using h
  have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
  have he' : (∑ i : Fin 30, correctionCoefficientError2570 i *
      ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 i edgeMidpointPosition2548‖) ≤
        (30 : ℝ)/10^28 := by simpa using he
  unfold signedJetUpper2539 fjcpUpper2571
  linarith [fjcpSum_norm2571, fjcpCharge2571]

theorem weightedPhysicalCorrPlusFirstJet_le2571 (coefficients : Fin 30 → ℂ)
    (hbox : ∀ i, (correctionCoefficientBox2570 i).Mem (coefficients i)) :
    ‖iteratedDeriv 1 (weightedPhysical2539 (1/2) coefficients nodeModulation2541)
        edgeMidpointPosition2548‖ ≤
      fjcpUpper2571 := by
  have h := weightedPhysical2539_jet_le_center_error 1 (1/2) coefficients
    correctionCoefficientCenter2570 correctionCoefficientError2570 nodeModulation2541
    (fun i => corrError_of_box2570 i (coefficients i) (hbox i))
        edgeMidpointPosition2548
  exact h.trans firstJetCorrPlusUpper_le2571

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.fjcpExpError2571
#print axioms ConnesWeilRH.Dev.fjcpSum_eq2571
#print axioms ConnesWeilRH.Dev.fjcpSum_norm2571
#print axioms ConnesWeilRH.Dev.fjcpCharge2571
#print axioms ConnesWeilRH.Dev.firstJetCorrPlusUpper_le2571
#print axioms ConnesWeilRH.Dev.weightedPhysicalCorrPlusFirstJet_le2571
